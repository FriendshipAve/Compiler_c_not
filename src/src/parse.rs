// L1 Compiler
//! Parser
// Author: Dan Cascaval <dcascava@andrew.cmu.edu>

// This implements a recursive descent algorithm. One of the nice things
// about this style of parser is that it can give you much more descriptive
// error messages, at the expense of having to do slightly more manual work.

// We implement expression operator precedence through a series of calls
// upward through the precedence hierarchy, effectively giving the operator
// at the bottom of the call stack the ability to choose if it matches into
// an expression or not.

use crate::ast::{self, C0mac, FieldList, Patt, Stmt, Typ, TypCtxt, Variant};
use crate::error::{errs, Error, Result};
use crate::lex::{BinOpPrecedence, Lexer, Token};
use std::collections::HashSet;
use std::convert::TryFrom;
use std::hash::Hash;
use std::io::Read;
use std::result;

use crate::util::c0spec::SourceFileType;

// for making general peek buffers.
use crate::util::datastructure::PeekBuffer;

pub struct Parser<R: Read> {
  // lexer: Lexer<R>,
  // next: Option<Result<Token>>, // LR(1) lookahead
  peekbuf: PeekBuffer<R>,
}

impl<R: Read> Parser<R> {
  pub fn new(lexer: Lexer<R>) -> Self {
    Parser {
      peekbuf: PeekBuffer::from_lexer(lexer),
    }
  }

  // ---------------------------- HELPER FUNCTIONS ----------------------------

  /// Get the next token from the lexer, except if we had previously peeked.
  /// This function ALWAYS moves the parser forward by one token every time
  /// it is called.
  fn token(&mut self) -> Result<Token> {
    self.peekbuf.token()
  }

  /// Look at the `n`th token in the stream, where `0` means immedate next.
  /// This function NEVER moves the parser, and can be called multiple times
  /// and will return the same result.
  fn peek(&mut self, n: usize) -> result::Result<&Token, &Error> {
    self.peekbuf.peek(n)
  }

  /// Skips to the next token without checking what it is
  fn skip(&mut self) -> Result<()> {
    self.token()?;
    Ok(())
  }

  /// Skips to the next token, verifying that this has the value we expect.
  fn munch(&mut self, tok: Token) -> Result<()> {
    let ltok = self.token()?;
    if ltok == tok {
      Ok(())
    } else {
      let helpmsg = self.peekbuf.get_helpmsg();
      errs(format!("Expected {:?}, got {:?}: \n{}", tok, ltok, helpmsg))
    }
  }

  // ------------------------------- Debug Info -------------------------------

  pub fn all_tokens(&mut self) -> Vec<Token> {
    let mut ret = Vec::<Token>::new();
    while let Ok(t) = self.token() {
      ret.push(t);
    }
    ret
  }

  // ------------------------ Function and Type Assist ------------------------

  /// Parses global stuff, ie. function declaration / definition,
  /// or type definition.
  ///
  /// ## Syntax
  /// `rettype ident (param_list); | rettype ident (param_list) {..}`
  fn glob(
    &mut self,
    sft: SourceFileType,
    current_typs: &mut ast::TypCtxt,
  ) -> Result<ast::Glob> {
    // typdef
    if self.peek(0)? == &Token::TYPEDEF {
      return self.typdef(current_typs);
    }

    let macros = if let Token::AT = self.peek(0)? {
      todo!("Expanding macro not impl'd");
    } else {
      Vec::<C0mac>::new()
    };

    let rt_raw = self.rettyp_noresolve()?;

    match (rt_raw, self.peek(0)?) {
      // struct decl
      (ast::RetTyp::T(ast::Typ::C0struct(struct_id)), Token::SEMICOLON) => {
        self.skip()?;
        Ok(ast::Glob::SDecl(ast::TypName(struct_id)))
      }

      // struct defn
      (ast::RetTyp::T(ast::Typ::C0struct(struct_id)), Token::LBRACE) => {
        self.munch(Token::LBRACE)?;
        let fl = self.field_list(current_typs)?;
        self.munch(Token::RBRACE)?;
        self.munch(Token::SEMICOLON)?;
        Ok(ast::Glob::SDefn(ast::TypName(struct_id), fl))
      }

      // enum
      (ast::RetTyp::T(ast::Typ::C0enum(enum_id)), Token::ASNEQUAL) => {
        self.skip()?;
        let mut variants = self.variants(current_typs)?;
        Ok(ast::Glob::EDefn(enum_id, variants))
      }

      // function
      (rt_raw, Token::Ident(..)) => {
        let (id, params_raw) = self.fn_head(current_typs)?;

        // resolve custom types
        let rt = current_typs.resolve_ret_typ(&rt_raw)?;
        let mut params = params_raw.clone();
        for param in params.0.iter_mut() {
          param.0 = current_typs.resolve_typ(&param.0)?;
        }

        match self.peek(0)? {
          // fn declare
          Token::SEMICOLON => {
            self.skip()?;
            use SourceFileType::*;
            match sft {
              Header => Ok(ast::Glob::HeadDecl(rt, id, params)),
              Impl => Ok(ast::Glob::FnDecl(rt, id, params)),
            }
          }

          // fn define
          Token::LBRACE => {
            if let SourceFileType::Header = sft {
              return errs(format!(
                "Cannot implement a function in header file! \n{}",
                self.peekbuf.get_helpmsg()
              ));
            }
            let fnbody = self.block(current_typs)?;
            Ok(ast::Glob::FnDefn(rt, id, params, fnbody))
          }

          // err
          _ => {
            return errs(format!(
              "Function signature must be followed by either `;` or body. \n{}",
              self.peekbuf.get_helpmsg()
            ));
          }
        }
      }

      // bad
      _ => errs(format!(
        "Global must be either typedef, struct, or function \n{}",
        self.peekbuf.get_helpmsg()
      )),
    }
  }

  /// Parses a function header, given its already parsed return type.
  ///
  /// ## Syntax
  /// `ident (param_list)`
  fn fn_head(
    &mut self,
    current_typs: &ast::TypCtxt,
  ) -> Result<(ast::FnName, ast::ParamList)> {
    let fname = self.ident()?;
    self.munch(Token::LPAREN)?;
    let params = self.param_list(current_typs)?;
    self.munch(Token::RPAREN)?;
    Ok((ast::FnName(fname), params))
  }

  /// Parses a typedef, inserts the defined type into current context.
  /// Will check for existing `typedef`s if the flag `ALLOW_TYPEDEF_SHADOWING`
  /// is turned off.
  ///
  /// ## Syntax
  /// `typedef typ ident`
  fn typdef(&mut self, current_typs: &mut ast::TypCtxt) -> Result<ast::Glob> {
    self.munch(Token::TYPEDEF)?;
    let t = self.typ(current_typs)?;
    let id = self.ident()?;
    self.munch(Token::SEMICOLON)?;

    current_typs.define(&t, &id)?;
    Ok(ast::Glob::TypDef(t, ast::TypName(id)))
  }

  /// Parses some struct declaration or definition.
  ///
  /// ## Syntax
  /// `struct ident; | struct ident {fields}`
  fn struct_decl_defn(&mut self) {
    unimplemented!()
  }

  /// Checks if the next token is , or ). Munches comma. Returns if the next
  /// token is rparen; Returns error if next token is neither.
  fn comma_paren_list_finished(&mut self) -> Result<bool> {
    let peek_result = self.peek(0)?.clone();
    match peek_result {
      Token::RPAREN => Ok(true),
      Token::COMMA => {
        self.munch(Token::COMMA)?;
        Ok(false)
      }
      x => errs(format!(
        "Expected either `)` or `,`, found `{:?}`\n{}",
        x,
        self.peekbuf.get_helpmsg()
      )),
    }
  }

  /// Parses a list of typed parameters. Used for function defn args.
  ///
  /// [note] This checks for repeated parameter names.
  ///
  /// ## Syntax
  /// `nil | param, param_list`
  fn param_list(
    &mut self,
    current_typs: &ast::TypCtxt,
  ) -> Result<ast::ParamList> {
    let mut existing_param_names = HashSet::<String>::new();
    let mut ret = Vec::<ast::Param>::new();

    // function with no params
    if let Token::RPAREN = self.peek(0)? {
      return Ok(ast::ParamList(ret));
    }

    // function with params
    loop {
      let current_param = self.param(current_typs)?;
      let current_param_name = current_param.1.clone();

      // chk param-name reuse
      if existing_param_names.contains(&current_param_name) {
        return errs(format!(
          "Function parameters cannot have repeated names: `{}`\n{}",
          current_param_name,
          self.peekbuf.get_helpmsg()
        ));
      }

      // update datastructure
      ret.push(current_param);
      existing_param_names.insert(current_param_name);

      if self.comma_paren_list_finished()? {
        return Ok(ast::ParamList(ret));
      }
    }
  }

  /// Parses a typed parameter.
  ///
  /// ## Syntax
  /// `type ident`
  fn param(&mut self, current_typs: &ast::TypCtxt) -> Result<ast::Param> {
    let t = self.typ(current_typs)?;
    let id = self.ident()?;
    Ok(ast::Param(t, id))
  }

  /// Parses a list of non-type-annotated parameters. Used for fn use args.
  ///
  /// ## Syntax
  /// `. | expr, arg_list`
  fn arg_list(&mut self, current_typs: &TypCtxt) -> Result<ast::ArgList> {
    let mut ret = Vec::<ast::Expr>::new();

    // fncall with no args
    if let Token::RPAREN = self.peek(0)? {
      return Ok(ast::ArgList(ret));
    }

    // fncall with args
    loop {
      ret.push(self.expr(current_typs)?);
      if self.comma_paren_list_finished()? {
        break Ok(ast::ArgList(ret));
      }
    }
  }

  /// Parses a list of struct fields.
  ///
  /// [note] This checks for repeated field types.
  ///
  /// ## Syntax
  /// `nil | field field_list`
  fn field_list(&mut self, current_typs: &ast::TypCtxt) -> Result<FieldList> {
    let mut existing_field_names = HashSet::<String>::new();
    let mut ret = Vec::<ast::Field>::new();

    loop {
      if let Token::RBRACE = self.peek(0)? {
        break Ok(FieldList(ret));
      }
      ret.push(self.field(current_typs)?);
    }
  }

  /// Parses a single struct field.
  ///
  /// ## Syntax
  /// `type ident;`
  fn field(&mut self, current_typs: &ast::TypCtxt) -> Result<ast::Field> {
    let t = self.typ(current_typs)?;
    let id = self.ident()?;
    self.munch(Token::SEMICOLON)?;
    Ok(ast::Field(t, id))
  }

  /// Parses an identifier without inferring its meaning.
  fn ident(&mut self) -> Result<String> {
    let s = self.token()?;
    match s {
      Token::Ident(s) => Ok(s),
      x => errs(format!(
        "Expected ident, found '{:?}'\n{}",
        x,
        self.peekbuf.get_helpmsg()
      )),
    }
  }

  /// Parses a list of enum variants until semicolon.
  ///
  /// ## Syntax
  /// `. | variant variants`
  fn variants(&mut self, current_typs: &TypCtxt) -> Result<Vec<Variant>> {
    let mut ret = Vec::<Variant>::new();
    'a: loop {
      let (v, last) = self.variant_term(current_typs)?;
      ret.push(v);
      if last {
        break 'a Ok(ret);
      }
    }
  }

  /// Parses a single variant and its terminator ( | or ; ). Returns a parsed
  /// variant paired with some bool indicating if it is the last variant.
  fn variant_term(
    &mut self,
    current_typs: &TypCtxt,
  ) -> Result<(Variant, bool)> {
    let variant_name = self.ident()?;
    let mut args = Vec::<Typ>::new();

    if let &Token::LPAREN = self.peek(0)? {
      self.skip()?;
      'a: loop {
        args.push(self.typ(current_typs)?);
        if self.comma_paren_list_finished()? {
          break 'a;
        }
      }
      self.munch(Token::RPAREN)?;
    }

    match self.token()? {
      Token::OR => Ok((Variant(variant_name, args), false)),
      Token::SEMICOLON => Ok((Variant(variant_name, args), true)),
      t => {
        return errs(format!(
          "Variants must end with `|` or `;`, not `{:?}`\n{}",
          t,
          self.peekbuf.get_helpmsg()
        ))
      }
    }
  }

  /// Parses some list of derived macros.
  ///
  /// ## Syntax
  /// `@(mac)`
  fn macros(&mut self) -> Result<Vec<C0mac>> {
    self.munch(Token::AT)?;
    self.munch(Token::LPAREN)?;
    let mut ret = Vec::<C0mac>::new();
    'a: loop {
      ret.push(self.munch_mac()?);
      if self.comma_paren_list_finished()? {
        break 'a;
      }
    }
    self.munch(Token::RPAREN)?;
    Ok(ret)
  }

  /// Takes a token and ensures that it is some derivable macro.
  fn munch_mac(&mut self) -> Result<C0mac> {
    let maybe_mac = self.token()?;
    match maybe_mac {
      Token::DEBUG => Ok(C0mac::Debug),
      Token::CLONE => Ok(C0mac::Clone),
      Token::HASH => Ok(C0mac::Hash),
      t => {
        let helpmsg = self.peekbuf.get_helpmsg();
        errs(format!("Expected macro, got {:?}: \n{}", t, helpmsg))
      }
    }
  }

  // ----------------------------- Type handling ------------------------------

  /// Peeks at the buffer and look for potentially-valid type signature.
  ///
  /// [note] This is used to handle the lhs of `simp`.
  fn peektyp(&mut self, current_typs: &ast::TypCtxt) -> Result<bool> {
    match self.peek(0)? {
      Token::INT | Token::BOOL | Token::STRUCT | Token::ENUM => Ok(true),
      Token::Ident(s) => Ok(current_typs.check_defined(s)),
      _ => Ok(false),
    }
  }

  /// Parses a type identifier.
  ///
  /// ## Syntax
  /// `int | bool | <type> * | <type> [] | struct ident`
  fn typ(&mut self, current_typs: &ast::TypCtxt) -> Result<ast::Typ> {
    let mut deduced_typ = match self.token()? {
      Token::INT => Ok(ast::Typ::Int),
      Token::BOOL => Ok(ast::Typ::Bool),
      Token::Ident(name) => {
        let t = current_typs.resolve_typ(&ast::Typ::Custom(name))?;
        Ok(t)
      }
      Token::STRUCT => Ok(ast::Typ::C0struct(self.ident()?)),
      Token::ENUM => Ok(ast::Typ::C0enum(self.ident()?)),
      x => errs(format!(
        "Expected typename, found '{:?}'\n{}",
        x,
        self.peekbuf.get_helpmsg()
      )),
    }?;

    loop {
      match self.peek(0)? {
        Token::TIMES => {
          self.skip()?;
          deduced_typ = ast::Typ::C0ptr(Box::new(deduced_typ));
        }
        Token::LSQBRACKET => {
          self.skip()?;
          self.munch(Token::RSQBRACKET)?;
          deduced_typ = ast::Typ::C0array(Box::new(deduced_typ));
        }
        _ => break Ok(deduced_typ),
      }
    }
  }

  /// Parses a type identifier without resolving it.
  ///
  /// ## Syntax
  /// `int | bool | ident | <type> * | <type> [] | struct ident | enum ident`
  fn typ_noresolve(&mut self) -> Result<ast::Typ> {
    let mut deduced_typ = match self.token()? {
      Token::INT => Ok(ast::Typ::Int),
      Token::BOOL => Ok(ast::Typ::Bool),
      Token::Ident(name) => Ok(ast::Typ::Custom(name)),
      Token::STRUCT => Ok(ast::Typ::C0struct(self.ident()?)),
      Token::ENUM => Ok(ast::Typ::C0enum(self.ident()?)),
      x => errs(format!(
        "Expected typename, found '{:?}'\n{}",
        x,
        self.peekbuf.get_helpmsg()
      )),
    }?;

    loop {
      match self.peek(0)? {
        Token::TIMES => {
          self.skip()?;
          deduced_typ = ast::Typ::C0ptr(Box::new(deduced_typ));
        }
        Token::LSQBRACKET => {
          self.skip()?;
          self.munch(Token::RSQBRACKET)?;
          deduced_typ = ast::Typ::C0array(Box::new(deduced_typ));
        }
        _ => break Ok(deduced_typ),
      }
    }
  }

  /// Parses a return type, which can be either a type or a void.
  ///
  /// ## Syntax
  /// `void | typ`
  fn rettyp(&mut self, current_typs: &ast::TypCtxt) -> Result<ast::RetTyp> {
    if let Token::VOID = self.peek(0)? {
      self.munch(Token::VOID)?;
      Ok(ast::RetTyp::Void)
    } else {
      Ok(ast::RetTyp::T(self.typ(current_typs)?))
    }
  }

  /// Parses a return type, which can be either a type or a void,
  /// without resolving it.
  ///
  /// ## Syntax
  /// `void | typ_noresolve`
  fn rettyp_noresolve(&mut self) -> Result<ast::RetTyp> {
    if let Token::VOID = self.peek(0)? {
      self.munch(Token::VOID)?;
      Ok(ast::RetTyp::Void)
    } else {
      Ok(ast::RetTyp::T(self.typ_noresolve()?))
    }
  }

  // ------------------------------- L? Grammar -------------------------------

  /// Parses the lexer token stream according to source file type, and updates
  /// the type context as parsing proceeds.
  pub fn parse(
    &mut self,
    sft: SourceFileType,
    current_typs: &mut ast::TypCtxt,
  ) -> Result<ast::Program> {
    let mut ret = Vec::<ast::Glob>::new();
    loop {
      // detect end of file
      match self.peek(0) {
        Ok(_) => ret.push(self.glob(sft, current_typs)?),
        Err(Error::EOF) => return Ok(ast::Program(ret)),
        Err(Error::Message(s)) => {
          eprintln!("Encountered error: {}", s);
          return Err(Error::Message(s.clone()));
        }
      }
    }
  }

  /// Parse `block`, which is a `Vec<Stmt>` wrapped within a pair of braces.
  /// If there is only one statement in the block, such a `Stmt` is returned
  /// instead of a block. (think the oneliners after an `if` statement)
  ///
  /// ## Syntax
  /// `{<stmts>*}`
  fn block(&mut self, current_typs: &ast::TypCtxt) -> Result<ast::Stmt> {
    let mut stmts = Vec::new();
    self.munch(Token::LBRACE)?;
    loop {
      match self.peek(0)? {
        Token::RBRACE => {
          self.munch(Token::RBRACE)?;
          // This turns { { stmt } } into { stmt }
          if stmts.len() == 1 {
            if let ast::Stmt::Block(_) = stmts[0] {
              return Ok(stmts.pop().unwrap());
            }
          };
          return Ok(ast::Stmt::Block(stmts));
        }
        _ => stmts.push(self.stmts(current_typs)?),
      }
    }
  }

  /// Parse a `block` if possible; else, parse a `Stmt`.
  ///
  /// ## Syntax
  /// `block | stmt`
  fn stmts(&mut self, current_typs: &ast::TypCtxt) -> Result<ast::Stmt> {
    match self.peek(0)? {
      Token::LBRACE => self.block(current_typs),
      _ => self.stmt(current_typs),
    }
  }

  /// Parse anything that is a `Stmt` but is not a `Block`.
  ///
  /// ## Syntax
  /// `if (expr) {_} <else {_}> | while (expr) {_} | for (<simp>; expr; <simp>)
  /// {_} | simp | return expr`
  ///
  /// [warning] This function has too many question marks, and may be hard
  /// to debug...
  fn stmt(&mut self, current_typs: &ast::TypCtxt) -> Result<ast::Stmt> {
    match self.peek(0)? {
      // --- control flows ---
      Token::RETURN => {
        self.munch(Token::RETURN)?;
        let item_to_ret = if let Token::SEMICOLON = self.peek(0)? {
          None
        } else {
          Some(self.expr(current_typs)?)
        };
        self.munch(Token::SEMICOLON)?;
        Ok(ast::Stmt::Ret(item_to_ret))
      }

      Token::IF => {
        use ast::{Expr, Stmt};

        self.munch(Token::IF)?;

        let condition: Expr = self.paren_expr(current_typs)?;
        let branch1: Box<Stmt> = Box::new(self.stmts(current_typs)?);
        let branch2: Option<Box<Stmt>> = match self.peek(0)? {
          Token::ELSE => {
            self.munch(Token::ELSE)?;
            Some(Box::new(self.stmts(current_typs)?))
          }

          _ => None,
        };

        Ok(ast::Stmt::If(condition, branch1, branch2))
      }

      Token::WHILE => {
        self.munch(Token::WHILE)?;
        let condition: ast::Expr = self.paren_expr(current_typs)?;
        let body: Box<ast::Stmt> = Box::new(self.stmts(current_typs)?);
        Ok(ast::Stmt::While(condition, body))
      }

      Token::FOR => {
        self.munch(Token::FOR)?;
        self.munch(Token::LPAREN)?;
        let e1 = self.simpopt(Token::SEMICOLON, current_typs)?;
        self.munch(Token::SEMICOLON)?;
        let e2 = self.expr(current_typs)?;
        self.munch(Token::SEMICOLON)?;
        let e3 = self.simpopt(Token::RPAREN, current_typs)?;
        let decl_checked_e3 = match e3 {
          Some(ast::Simp::Decl(_, _)) => {
            panic!(("Decl in for loop is not allowed."))
          }
          Some(ast::Simp::Defn(..)) => {
            panic!(("Def in for loop is not allowed."))
          }
          _ => e3,
        };
        self.munch(Token::RPAREN)?;
        let body = Box::new(self.stmts(current_typs)?);
        Ok(ast::Stmt::For(e1, e2, decl_checked_e3, body))
      }

      Token::MATCH => {
        self.skip()?;
        let e = self.expr(current_typs)?;
        let mut branches = Vec::<(Patt, HashSet<String>, Stmt)>::new();

        self.munch(Token::LBRACE)?;
        while self.peek(0)? != &Token::RBRACE {
          branches.push(self.patt_stmt(current_typs)?);
        }
        self.munch(Token::RBRACE)?;

        Ok(ast::Stmt::Match(e, branches))
      }

      Token::ASSERT => {
        self.munch(Token::ASSERT)?;
        let expr_to_chk = self.paren_expr(current_typs)?;
        self.munch(Token::SEMICOLON)?;
        Ok(ast::Stmt::Assert(expr_to_chk))
      }

      // --- detect and parse simp ---
      _ => {
        let parsed_simp = self.simp(current_typs)?;
        let semicolon_chk = self.munch(Token::SEMICOLON);
        if let Err(e) = semicolon_chk {
          println!("Simple statements shall end with `;`: \n{}", e);
          return errs(self.peekbuf.get_helpmsg());
        }
        Ok(ast::Stmt::Simp(parsed_simp))
      }
    }
  }

  /// Parses declaration, definition, assignment, post operation, or expression.
  ///
  /// ## Syntax
  /// `type ident <=expr> | lvalue asnop expr | lvalue postop | expr`
  fn simp(&mut self, current_typs: &ast::TypCtxt) -> Result<ast::Simp> {
    let declare = self.peektyp(current_typs)?;

    if declare {
      return self.decl_defn(current_typs);
    } else {
      let simp_left = self.expr(current_typs)?;
      match ast::Lval::try_from(simp_left.clone()) {
        Ok(lval) => {
          match self.peek(0)? {
            // postop
            Token::PP | Token::MM => {
              let op = self.postop()?;
              return Ok(ast::Simp::Post(lval, op));
            }

            // asnop
            Token::ASNEQUAL
            | Token::PLUSEQ
            | Token::MINUSEQ
            | Token::TIMESEQ
            | Token::DIVEQ
            | Token::MODEQ
            | Token::ANDEQ
            | Token::XOREQ
            | Token::OREQ
            | Token::SHLEQ
            | Token::SHREQ => {
              let op = self.asnop()?;
              let expr = self.expr(current_typs)?;
              return Ok(ast::Simp::Asgn(lval, op, expr));
            }

            // expr that looks like lvalue
            Token::SEMICOLON | Token::RPAREN => {
              return Ok(ast::Simp::E(simp_left));
            }

            // Err
            x => {
              println!("Expected postop or asnop, found {:?}\n", x);
              return errs(self.peekbuf.get_helpmsg());
            }
          }
        }

        // lhs is not a valid left value
        Err(_) => {
          match self.peek(0)? {
            // Warns users of not being allowed to assign. Just for HCI.
            Token::ASNEQUAL
            | Token::PLUSEQ
            | Token::MINUSEQ
            | Token::TIMESEQ
            | Token::DIVEQ
            | Token::MODEQ
            | Token::ANDEQ
            | Token::XOREQ
            | Token::OREQ
            | Token::SHLEQ
            | Token::SHREQ => {
              println!(
                "Cannot assign to `{}` because it's not a \
                valid lvalue \n",
                simp_left
              );
              return errs(self.peekbuf.get_helpmsg());
            }
            _ => Ok(ast::Simp::E(simp_left)),
          }
        }
      }
    }
  }

  /// Parses either declare or define.
  ///
  /// ## Syntax
  /// `typ ident | typ ident = expr`
  #[allow(dead_code)]
  fn decl_defn(&mut self, current_typs: &ast::TypCtxt) -> Result<ast::Simp> {
    let typ = self.typ(current_typs)?;

    let ident = match self.token()? {
      Token::Ident(s) => s,
      _ => {
        println!("Variable name must be an identifier.");
        return errs(self.peekbuf.get_helpmsg());
      }
    };

    match self.peek(0)? {
      Token::ASNEQUAL => {
        // defn
        self.munch(Token::ASNEQUAL)?;
        Ok(ast::Simp::Defn(typ, ident, self.expr(current_typs)?))
      }
      _ => Ok(ast::Simp::Decl(typ, ident)),
    }
  }

  /// Parses some optional `simp`, ie. return `Ok(None)` if encountered the
  /// given expected token. This is mainly used for `for` statement.
  ///
  /// ## Syntax
  /// `<simp>`
  fn simpopt(
    &mut self,
    expected_token: Token,
    current_typs: &ast::TypCtxt,
  ) -> Result<Option<ast::Simp>> {
    let peeked_token = self.peek(0)?;
    if *peeked_token == expected_token {
      Ok(None)
    } else {
      let simp_result = self.simp(current_typs)?;
      Ok(Some(simp_result))
    }
  }

  /// Parses some pair of match patterns and corresponding statements.
  fn patt_stmt(
    &mut self,
    current_typs: &TypCtxt,
  ) -> Result<(Patt, HashSet<String>, Stmt)> {
    let (p, s) = self.patt(current_typs)?;
    self.munch(Token::DARROW)?;
    Ok((p, s, self.block(current_typs)?))
  }

  /// Parses some pattern.
  fn patt(
    &mut self,
    current_typs: &TypCtxt,
  ) -> Result<(Patt, HashSet<String>)> {
    match self.token()? {
      Token::UNDERSCORE => Ok((Patt::Any, HashSet::<String>::new())),
      Token::Ident(id) => {
        match self.peek(0)? {
          Token::DOUBLECOLON => {
            self.skip()?;
            let variant_name = self.ident()?;

            let mut rec_patts = Vec::<(Patt, HashSet<String>)>::new();
            let mut used_vars = HashSet::<String>::new();

            // if there is a list of typs associated with variant...
            if let &Token::LPAREN = self.peek(0)? {
              self.skip()?;

              'a: loop {
                let rec_result = self.patt(current_typs)?;

                // check and make sure no var is repeatedly-defined.
                if !used_vars.is_disjoint(&rec_result.1) {
                  println!("Variable appeared more than once in pattern");
                  return errs(self.peekbuf.get_helpmsg());
                }

                // extend defined var
                used_vars.extend(rec_result.1.clone().into_iter());

                rec_patts.push(rec_result);
                if self.comma_paren_list_finished()? {
                  break 'a;
                }
              }
              self.munch(Token::RPAREN)?;
            }

            Ok((
              Patt::Variant(
                id,
                variant_name,
                rec_patts.into_iter().map(|x| x.0).collect(),
              ),
              used_vars,
            ))
          }
          _ => Ok((Patt::Variable(id.clone()), HashSet::from([id]))),
        }
      }
      tok => {
        println!("`{:?}` is not part of a pattern", tok);
        errs(self.peekbuf.get_helpmsg())
      }
    }
  }

  // --------------------------- Handling Operator ---------------------------

  /// Parses an assignment operator, which may be either a direct assignment
  /// (`=`), which is represented by `None`,
  /// or one of `+=, -=, *=, /=, %=, &=, ^=, |=, <<=, >>=`, which are
  /// wrapped by `Some()`.
  fn asnop(&mut self) -> Result<Option<ast::AsnOp>> {
    use ast::AsnOp::*;
    match self.token()? {
      Token::ASNEQUAL => Ok(None),
      Token::PLUSEQ => Ok(Some(PlusEq)),
      Token::MINUSEQ => Ok(Some(MinusEq)),
      Token::TIMESEQ => Ok(Some(TimesEq)),
      Token::DIVEQ => Ok(Some(DivEq)),
      Token::MODEQ => Ok(Some(ModEq)),
      Token::ANDEQ => Ok(Some(AndEq)),
      Token::XOREQ => Ok(Some(XorEq)),
      Token::OREQ => Ok(Some(OrEq)),
      Token::SHLEQ => Ok(Some(ShlEq)),
      Token::SHREQ => Ok(Some(ShrEq)),
      tok => {
        println!("Could not match {:?} in asnop", tok);
        errs(self.peekbuf.get_helpmsg())
      }
    }
  }

  /// Parses a postop, which is either a `++` or a `--`.
  fn postop(&mut self) -> Result<ast::PostOp> {
    match self.token()? {
      Token::PP => Ok(ast::PostOp::Pp),
      Token::MM => Ok(ast::PostOp::Mm),
      tok => {
        println!("Could not match {:?} in postop", tok);
        errs(self.peekbuf.get_helpmsg())
      }
    }
  }

  // --------------------- DEDICATED EXPRESSION PARSING -----------------------

  /// Parses some expression, but requires that such expression be wrapped in
  /// a pair of parenthesis. Typically used at control flow statements like
  /// `if, while, for`.
  ///
  /// ## Syntax
  /// `(expr)`
  fn paren_expr(&mut self, current_typs: &TypCtxt) -> Result<ast::Expr> {
    self.munch(Token::LPAREN)?;
    let expr = self.expr(current_typs)?;
    self.munch(Token::RPAREN)?;
    Ok(expr)
  }

  /// Parse a full recursive expression with precedence
  // We express operator precedence via a series of recursive 'tiers'.
  // Addition & Subtraction are the lowest-precedence operators in L1.
  // Rather than expressing binops directly, we handle them individually
  // at each tier.
  //
  // (Hint: this might be a place where rust macros start to make sense...)
  fn expr(&mut self, current_typs: &ast::TypCtxt) -> Result<ast::Expr> {
    self.conditional_expr(current_typs)
  }

  /// Parses a (possibly ternary) expression.
  ///
  /// ## Syntax
  /// `expr ? expr : expr | expr`
  fn conditional_expr(
    &mut self,
    current_typs: &ast::TypCtxt,
  ) -> Result<ast::Expr> {
    let e1 = self.any_binary(Some(BinOpPrecedence::lowest()), current_typs)?;

    match self.peek(0)? {
      Token::QUESTION => {
        // ternary op detected

        self.munch(Token::QUESTION)?;

        let e2 = self.conditional_expr(current_typs)?;
        // self.any_binary(Some(BinOpPrecedence::lowest()))?;

        let colon_chk = self.munch(Token::COLON);
        if colon_chk.is_err() {
          return errs(format!(
            "Ternary operator missing its third branch \n{}",
            self.peekbuf.get_helpmsg()
          ));
        }

        let e3 = self.expr(current_typs)?;

        Ok(ast::Expr::Terop(Box::new(e1), Box::new(e2), Box::new(e3)))
      }

      _ => Ok(e1), // ternary op not detected
    }
  }

  /// Parse a binary-op complex according to `BinOpPrecedence` specs.
  fn any_binary(
    &mut self,
    lvl: Option<BinOpPrecedence>,
    current_typs: &ast::TypCtxt,
  ) -> Result<ast::Expr> {
    match lvl {
      None => Ok(self.unary_expr(current_typs)?),

      Some(p) => {
        let mut expr = self.any_binary(p.next(), current_typs)?;
        loop {
          let op_tok = self.peek(0)?;
          let op = match p.filter_to_ast_binop(op_tok) {
            Some(op) => {
              self.skip()?;
              op
            }
            None => break, // no more opcode of level p detected
          };
          let rhs = self.any_binary(p.next(), current_typs)?;
          expr = ast::Expr::Binop(Box::new(expr), op, Box::new(rhs));
        }
        Ok(expr)
      }
    }
  }

  /// Verifies that `peek(0)` is not postop.
  fn verify_next_tok_is_not_postop(&mut self) -> Result<()> {
    match self.peek(0)? {
      Token::PP | Token::MM => errs(format!(
        "Postop does not work well with unary op: \n{}",
        self.peekbuf.get_helpmsg()
      )),
      _ => Ok(()),
    }
  }

  /// Parses unary expression.
  ///
  /// ## Syntax
  /// `-expr | !expr | ~expr | *expr`
  fn unary_expr(&mut self, current_typs: &ast::TypCtxt) -> Result<ast::Expr> {
    use ast::Expr::*;
    match self.peek(0)? {
      Token::MINUS => {
        self.skip()?;
        let expr = self.unary_expr(current_typs)?;
        self.verify_next_tok_is_not_postop()?;

        // Converts -(n) to -n.
        if let ast::Expr::Number(n) = expr {
          Ok(ast::Expr::Number(-n))
        } else {
          Ok(Unop(ast::UnOp::Neg, Box::new(expr)))
        }
      }

      Token::NOT => {
        self.skip()?;
        let expr = self.unary_expr(current_typs)?;
        self.verify_next_tok_is_not_postop()?;
        Ok(Unop(ast::UnOp::Not, Box::new(expr)))
      }

      Token::TILD => {
        self.skip()?;
        let expr = self.unary_expr(current_typs)?;
        self.verify_next_tok_is_not_postop()?;
        Ok(Unop(ast::UnOp::Tild, Box::new(expr)))
      }

      Token::TIMES => {
        self.skip()?;
        let expr = self.unary_expr(current_typs)?;
        self.verify_next_tok_is_not_postop()?;
        Ok(ast::Expr::Deref(Box::new(expr)))
      }

      _ => self.access_expr(current_typs),
    }
  }

  /// Access expressions
  fn access_expr(&mut self, current_typs: &ast::TypCtxt) -> Result<ast::Expr> {
    let mut expr = self.primary_expr(current_typs)?;
    loop {
      match self.peek(0)? {
        Token::LSQBRACKET => {
          self.skip()?;
          let idx_expr = self.expr(current_typs)?;
          self.munch(Token::RSQBRACKET)?;
          expr = ast::Expr::Idx(Box::new(expr), Box::new(idx_expr));
        }
        Token::ARROW => {
          self.skip()?;
          let field_id = self.ident()?;
          expr = ast::Expr::Arrow(Box::new(expr), field_id);
        }
        Token::DOT => {
          self.skip()?;
          let field_id = self.ident()?;
          expr = ast::Expr::Dot(Box::new(expr), field_id);
        }
        _ => return Ok(expr),
      }
    }
  }

  /// Base level for expressions (Loops back up)
  ///
  /// These expressions are "unsplittable", if one views them the right way.
  ///
  /// ## Syntax
  /// `[0-9] | ident | (<expr>) | unary_expr`
  fn primary_expr(&mut self, current_typs: &ast::TypCtxt) -> Result<ast::Expr> {
    // We don't want to skip() here because of the other
    // stuff that expressions could 'start' with
    match self.peek(0)? {
      // Numbers. Lexer already accounted for dec & hexnums
      &Token::Number(num) => {
        self.skip()?;
        Ok(ast::Expr::Number(num as i32))
      }

      // Bools.
      Token::TRUE => {
        self.skip()?;
        Ok(ast::Expr::True)
      }
      Token::FALSE => {
        self.skip()?;
        Ok(ast::Expr::False)
      }

      // function call or variables.
      Token::Ident(_) => {
        let s1 = self.ident()?;
        match self.peek(0)? {
          Token::LPAREN => {
            self.skip()?;
            let call_args = self.arg_list(current_typs)?;
            self.munch(Token::RPAREN)?;
            Ok(ast::Expr::FnCall(ast::FnName(s1), call_args))
          }
          Token::DOUBLECOLON => {
            self.skip()?;
            let s2 = self.ident()?;
            let args = match self.peek(0)? {
              Token::LPAREN => {
                self.skip()?;
                let ret = self.arg_list(current_typs)?;
                self.munch(Token::RPAREN)?;
                ret
              }
              _ => ast::ArgList(vec![]),
            };
            Ok(ast::Expr::EnumVar(s1, s2, args.0))
          }
          _ => Ok(ast::Expr::Variable(s1)),
        }
      }

      // takes an expression out of some pair of parenthesis.
      Token::LPAREN => {
        self.skip()?;
        let expr = self.expr(current_typs)?;
        self.munch(Token::RPAREN)?;
        Ok(expr)
      }

      // allocations
      Token::NULL => {
        self.skip()?;
        Ok(ast::Expr::Null)
      }
      Token::ALLOC => {
        self.skip()?;
        self.munch(Token::LPAREN)?;
        let t = self.typ(current_typs)?;
        self.munch(Token::RPAREN)?;
        Ok(ast::Expr::Alloc(t))
      }
      Token::ALLOCARR => {
        self.skip()?;
        self.munch(Token::LPAREN)?;
        let t = self.typ(current_typs)?;
        self.munch(Token::COMMA)?;
        let e = self.expr(current_typs)?;
        self.munch(Token::RPAREN)?;
        Ok(ast::Expr::AllocArr(t, Box::new(e)))
      }

      // unary expressions, including -, !, ~.
      Token::MINUS | Token::NOT | Token::TILD => self.unary_expr(current_typs),

      tok => {
        println!("Could not match {:?} in primary expression", tok);
        errs(self.peekbuf.get_helpmsg())
      }
    }
  }
}
