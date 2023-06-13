// L2 Compiler
//! Elaboration
// Author:

use std::collections::HashSet;
use std::convert::TryFrom;
use std::fmt::{Error, Formatter};

use std::rc::Rc;

use crate::elab_after_tc::TypCtx2;

use crate::ast::{self, FieldList, FieldName, Patt};

use crate::util::prettyprint::*;

use crate::tc::tc_info::TcInfoFn;

pub type Var = ast::Var;

type Typ = ast::Typ;
type UnOp = ast::UnOp;
type BinOp = ast::BinOp;
type Expr = ast::Expr;

/// Converts `x -> y` to `(*x).y` in expression
pub fn elab_arrow(e: Expr) -> Expr {
  // Helper function for recursively elaborating boxed expr.
  let rec = |e: Box<Expr>| Box::new(elab_arrow(*e));

  match e {
    // arrow case
    Expr::Arrow(e_child, field) => {
      Expr::Dot(Box::new(Expr::Deref(rec(e_child))), field)
    }

    // recursive cases
    Expr::Unop(op, e1) => Expr::Unop(op, rec(e1)),
    Expr::Binop(e1, op, e2) => Expr::Binop(rec(e1), op, rec(e2)),
    Expr::Terop(e1, e2, e3) => Expr::Terop(rec(e1), rec(e2), rec(e3)),
    Expr::AllocArr(t, e1) => Expr::AllocArr(t, rec(e1)),
    Expr::Dot(e1, field) => Expr::Dot(rec(e1), field),
    Expr::Deref(e1) => Expr::Deref(rec(e1)),
    Expr::Idx(e1, e2) => Expr::Idx(rec(e1), rec(e2)),

    // fncall, elab arrow of each arg.
    Expr::FnCall(fname, arglist) => Expr::FnCall(
      fname,
      ast::ArgList(arglist.0.into_iter().map(elab_arrow).collect()),
    ),

    // terminals
    Expr::True
    | Expr::False
    | Expr::Null
    | Expr::Number(_)
    | Expr::Variable(_)
    | Expr::Alloc(_)
    | Expr::EnumVar(..) => e,
  }
}

#[derive(Clone, Debug)]
pub enum ElabLval {
  Var(String),
  Dot(Box<ElabLval>, FieldName),
  Deref(Box<ElabLval>),
  Idx(Box<ElabLval>, Box<Expr>),
}

impl ElabLval {
  fn elab(lval: ast::Lval) -> Self {
    match lval {
      ast::Lval::Var(s) => ElabLval::Var(s),
      ast::Lval::Dot(lv, f) => ElabLval::Dot(Box::new(ElabLval::elab(*lv)), f),
      ast::Lval::Arrow(lv, f) => {
        let star_lv = ElabLval::Deref(Box::new(ElabLval::elab(*lv)));
        ElabLval::Dot(Box::new(star_lv), f)
      }
      ast::Lval::Deref(lv) => ElabLval::Deref(Box::new(ElabLval::elab(*lv))),
      ast::Lval::Idx(lv, e) => {
        ElabLval::Idx(Box::new(ElabLval::elab(*lv)), Box::new(elab_arrow(*e)))
      }
    }
  }

  pub fn is_var(&self) -> bool {
    match self {
      ElabLval::Var(_) => true,
      _ => false,
    }
  }

  pub fn get_var(&self) -> String {
    match self {
      ElabLval::Var(s) => s.clone(),
      _ => panic!("ElabLval::get_var called on non-var"),
    }
  }

  // Deduces the type of some elaborated lvalue.
  pub fn deduce_typ(
    &self,
    tc_info_fn: &TcInfoFn,
    typctx: &TypCtx2,
  ) -> ast::Typ {
    let rec = |x: &Box<ElabLval>| x.deduce_typ(tc_info_fn, typctx);
    match self {
      ElabLval::Var(s) => {
        typctx.get(s).expect("var did not exist in the ctx").clone()
      }
      ElabLval::Idx(arr, _) => {
        let arr_typ = rec(arr);
        match rec(arr) {
          ast::Typ::C0array(elt_typ) => *elt_typ,
          t => panic!("TC failed to catch invalid [] access `{}`", t),
        }
      }
      ElabLval::Deref(elv) => match rec(elv) {
        ast::Typ::C0ptr(t) => *t,
        t => panic!("TC failed to catch invalid deref `{}`", t),
      },
      ElabLval::Dot(s, fdname) => {
        let sname = s.deduce_struct_name(tc_info_fn, typctx);
        tc_info_fn.sf_typ(&sname, fdname)
      }
    }
  }

  /// Deduces the struct name of some `ElabLval`; panics if fails.
  pub fn deduce_struct_name(
    &self,
    tc_info_fn: &TcInfoFn,
    typctx: &TypCtx2,
  ) -> String {
    match self.deduce_typ(tc_info_fn, typctx) {
      ast::Typ::C0struct(s) => s,
      t => panic!("Cannot deduce `{}` as struct", t),
    }
  }

  /// Deduces the element typ of some array; panics if fails.
  pub fn deduce_c0array_elt_typ(
    &self,
    tc_info_fn: &TcInfoFn,
    typctx: &TypCtx2,
  ) -> ast::Typ {
    match self.deduce_typ(tc_info_fn, typctx) {
      ast::Typ::C0array(t) => *t,
      t => panic!("Cannot deduce `{}` as struct", t),
    }
  }
}

impl TryFrom<ast::Expr> for ElabLval {
  type Error = crate::error::Error;
  fn try_from(value: ast::Expr) -> Result<Self, Self::Error> {
    match value {
      ast::Expr::Variable(s) => Ok(ElabLval::Var(s)),
      ast::Expr::Deref(e) => Ok(ElabLval::Deref(Box::new(Self::try_from(*e)?))),
      ast::Expr::Idx(a, i) => {
        Ok(ElabLval::Idx(Box::new(Self::try_from(*a)?), i))
      }
      ast::Expr::Dot(s, f) => {
        Ok(ElabLval::Dot(Box::new(Self::try_from(*s)?), f))
      }
      e => Err(crate::error::Error::Message(format!(
        "Failed to convert expression `{}` to ElabLval",
        e
      ))),
    }
  }
}

#[derive(Clone, Debug)]
/// Elaborated statement, which encodes variable scope by construction, and
/// converts `for` loops to `while` loops.
pub enum ElabStmt {
  Declare(Var, Typ, Box<ElabStmt>, bool), // Bool is whether or not the variable initialized at assignment
  Assign(ElabLval, Expr),
  AssignEq(ElabLval, ast::AsnOp, Expr),
  If(Expr, Box<ElabStmt>, Box<ElabStmt>),
  While(Expr, Box<ElabStmt>),
  Match(Expr, Vec<(Patt, HashSet<String>, Box<ElabStmt>)>),
  Ret(Option<Expr>),
  Seq(Box<ElabStmt>, Box<ElabStmt>),
  Eval(Expr), // Effects for the win! Pure functions are heresy!
  Nop,
}

impl ElabStmt {
  /// Handles anything that does not start with a `Declare` (and therefore
  /// can stand alone influencing outer scope)
  fn elab_nondeclare(s: ast::Stmt) -> Self {
    match s {
      ast::Stmt::Assert(e) => {
        let e = elab_arrow(e);

        let s2 = ElabStmt::Eval(ast::Expr::FnCall(
          ast::FnName("c0_assert".to_string()),
          ast::ArgList(vec![ast::Expr::False]),
        ));
        ElabStmt::If(e, Box::new(ElabStmt::Nop), Box::new(s2))
      }

      ast::Stmt::If(e, s1, os2) => {
        let e = elab_arrow(e);

        let s1 = Self::elab_as_block(*s1);
        let s2 = Self::elab_as_optblock(os2);
        ElabStmt::If(e, Box::new(s1), Box::new(s2))
      }
      ast::Stmt::While(e, s) => {
        let e = elab_arrow(e);

        let s = Self::elab_as_block(*s);
        ElabStmt::While(e, Box::new(s))
      }
      ast::Stmt::Ret(e_opt) => {
        let e_opt = match e_opt {
          Some(e) => Some(elab_arrow(e)),
          None => None,
        };

        ElabStmt::Ret(e_opt)
      }
      ast::Stmt::Block(mut v) => {
        // Reverse v as per specs of elab_stmt_seq()
        v.reverse();

        Self::elab_stmt_seq(v)
      }
      ast::Stmt::For(sp1, e, sp2, s) => {
        let e = elab_arrow(e);

        let mut scope = Vec::<ast::Stmt>::new();
        let mut loopbody_v = Vec::<ast::Stmt>::new();

        if let Some(x) = sp1 {
          scope.push(ast::Stmt::Simp(x));
        }

        loopbody_v.push(*s);
        if let Some(x) = sp2 {
          loopbody_v.push(ast::Stmt::Simp(x));
        }

        scope.push(ast::Stmt::While(e, Box::new(ast::Stmt::Block(loopbody_v))));

        scope.reverse();
        Self::elab_stmt_seq(scope)
      }
      ast::Stmt::Simp(sp) => match sp {
        ast::Simp::Asgn(_, _, _) => Self::elab_asnop(sp),
        ast::Simp::Post(_, _) => Self::elab_post(sp),
        ast::Simp::E(expr) => Self::Eval(elab_arrow(expr)),
        _ => unreachable!(),
      },
      ast::Stmt::Match(e, psl) => ElabStmt::Match(
        e,
        psl
          .into_iter()
          .map(|(p, vars, s)| (p, vars, Box::new(Self::elab_as_block(s))))
          .collect(),
      ),
    }
  }

  // ------------ Elaborating branches of control flow statements -------------

  /// Elaborates some statement as a block on its own.
  fn elab_as_block(s: ast::Stmt) -> Self {
    match s {
      ast::Stmt::Block(_) => Self::elab_nondeclare(s),
      _ => Self::elab_stmt_seq(vec![s]),
    }
  }

  /// Elaborates some optional statement as a block on its own. Produces a
  /// `Self::Nop` variant in case of `None`.
  fn elab_as_optblock(os: Option<Box<ast::Stmt>>) -> Self {
    match os {
      Some(s) => Self::elab_as_block(*s),
      None => ElabStmt::Nop,
    }
  }

  // ----------------- Elaboration of declaration productions -----------------

  /// Iterates through an entire seq of statements (represented as a `vec`),
  /// and processes all of them while building up some elaborated tree.
  ///
  /// Note that `v` shall be reversed before put into function argument, ie.
  /// the tail shall be the first statement.
  ///
  /// [Note] Since `Declare` is highly scope-dependent, this function is the
  /// _only_ one allowed to handle such cases.
  fn elab_stmt_seq(mut v: Vec<ast::Stmt>) -> Self {
    match v.pop() {
      Some(head) => {
        let tail = Box::new(Self::elab_stmt_seq(v));

        match head {
          // ------ things that can produce a 'Declare' variant ------
          ast::Stmt::Simp(ast::Simp::Decl(t, x)) => {
            Self::Declare(x, t, tail, false)
          }

          ast::Stmt::Simp(ast::Simp::Defn(t, x, expr)) => {
            // special handling of 'Declare' variants, if expr is just a number,
            // I don't care about function shadowing in this case; otherwise i
            // need to care about function shadowing and I will set a flag true
            // for tc this part is not very elegant, but it works, please ask
            // Bob if things are not clear

            let expr = elab_arrow(expr);

            let rec = Self::Seq(
              Box::new(Self::Assign(ElabLval::Var(x.clone()), expr.clone())),
              tail,
            );

            match expr {
              ast::Expr::Variable(_) | ast::Expr::Number(_) => {
                Self::Declare(x, t, Box::new(rec), false)
              }
              _ => Self::Declare(x, t, Box::new(rec), true),
            }
          }

          // --- things that shall not produce a 'Declare' variant ---
          _ => Self::Seq(Box::new(Self::elab_nondeclare(head)), tail),
        }
      }

      None => Self::Nop, // empty seq
    }
  }

  // --------------------- Elaborating variants of Simp. ----------------------

  /// Converts some `ast::Simp::Post()` variant instance to `Self`. Will
  /// `panic!` if input argument is not the `Post()` variant.
  fn elab_post(ast_post: ast::Simp) -> Self {
    if let ast::Simp::Post(lval, postop) = ast_post {
      // elab x++ into x += 1
      let op = match postop {
        ast::PostOp::Pp => ast::AsnOp::PlusEq,
        ast::PostOp::Mm => ast::AsnOp::MinusEq,
      };

      Self::AssignEq(ElabLval::elab(lval), op, ast::Expr::Number(1))
      // done
    } else {
      panic!("Cannot pass `{:?}` to `from_ast_post()`!", ast_post)
    }
  }

  /// Converts some `ast::Simp::Asgn()` variant instance to `Self`. Will
  /// `panic!` if input argument is not the `Asgn()` variant.
  fn elab_asnop(ast_assign: ast::Simp) -> Self {
    if let ast::Simp::Asgn(x, asnop, expr) = ast_assign {
      let expr = elab_arrow(expr);

      match asnop {
        Some(op) => Self::AssignEq(ElabLval::elab(x), op, expr),
        None => Self::Assign(ElabLval::elab(x), expr),
      }
    } else {
      panic!("Cannot pass `{:?}` to `from_ast_assign()`!", ast_assign)
    }
  }

  // ---------------------------- Pretty Printing -----------------------------

  fn write_elab(&self, f: &mut Formatter, numtab: usize) -> Result<(), Error> {
    match self {
      Self::Nop => Ok(()),
      Self::Assign(x, e) => {
        tab_align(f, numtab)?;
        write!(f, "{} <- {}", x, e)
      }
      Self::AssignEq(lv, op, e) => {
        tab_align(f, numtab)?;
        write!(f, "{} {} {}", lv, op, e)
      }
      Self::Eval(e) => {
        tab_align(f, numtab)?;
        write!(f, "eval({})", e)
      }
      Self::Ret(Some(e)) => {
        tab_align(f, numtab)?;
        write!(f, "ret {}", e)
      }
      Self::Ret(None) => {
        tab_align(f, numtab)?;
        write!(f, "ret")
      }
      Self::Seq(s1, s2) => {
        s1.write_elab(f, numtab)?;
        write!(f, "\n")?;
        s2.write_elab(f, numtab)
      }
      Self::If(e, s1, s2) => {
        tab_align(f, numtab)?;
        write!(f, "if ({}) {{\n", e)?;

        s1.write_elab(f, numtab + 2)?;

        tab_align(f, numtab)?;
        write!(f, "}} else {{\n")?;

        s2.write_elab(f, numtab + 2)?;

        tab_align(f, numtab)?;
        write!(f, "}}")
      }
      Self::While(e, s) => {
        tab_align(f, numtab)?;
        write!(f, "while ({}) {{\n", e)?;

        s.write_elab(f, numtab + 2)?;

        tab_align(f, numtab)?;
        write!(f, "}}")
      }
      Self::Match(e, v) => {
        tab_align(f, numtab)?;
        write!(f, "match ({}) {{\n", e)?;

        for (p, _, s) in v {
          tab_align(f, numtab + 2)?;
          write!(f, "{} => {{\n", p)?;
          s.write_elab(f, numtab + 4)?;
          tab_align(f, numtab + 2)?;
          write!(f, "}}\n")?;
        }

        tab_align(f, numtab)?;
        write!(f, "}}")
      }
      Self::Declare(x, t, s, init) => {
        tab_align(f, numtab)?;
        if *init {
          write!(f, "Defn {} : {} = {{\n", x, t)?;
        } else {
          write!(f, "Decl {} : {} {{\n", x, t)?;
        }

        s.write_elab(f, numtab + 2)?;

        tab_align(f, numtab)?;
        write!(f, "}}\n")
      }
    }
  }
}

use ast::{FnName, ParamList, RetTyp, TypName};

/// Elaborated syntax tree global node.
pub enum ElabGlob {
  HeadDecl(RetTyp, FnName, ParamList),
  FnDecl(RetTyp, FnName, ParamList),
  FnDefn(RetTyp, FnName, ParamList, ElabStmt),
  TypDef(Typ, TypName),
  SDecl(TypName),
  SDefn(TypName, FieldList),
  EDefn(String, Vec<ast::Variant>),
}

impl ElabGlob {
  fn elab(g: ast::Glob) -> Self {
    match g {
      ast::Glob::FnDecl(rt, id, p) => ElabGlob::FnDecl(rt, id, p),
      ast::Glob::HeadDecl(rt, id, p) => ElabGlob::HeadDecl(rt, id, p),
      ast::Glob::TypDef(t, id) => ElabGlob::TypDef(t, id),
      ast::Glob::SDecl(tn) => ElabGlob::SDecl(tn),
      ast::Glob::SDefn(tn, fl) => ElabGlob::SDefn(tn, fl),
      ast::Glob::FnDefn(rt, id, p, body) => {
        // add return statement if it is void function
        match rt {
          RetTyp::Void => {
            let mut ret_stmt = vec![ast::Stmt::Ret(None)];
            let mut body_stmts = vec![body];
            ret_stmt.extend(body_stmts);

            let body = ElabStmt::elab_stmt_seq(ret_stmt);

            return ElabGlob::FnDefn(rt, id, p, body);
          }
          _ => ElabGlob::FnDefn(rt, id, p, ElabStmt::elab_stmt_seq(vec![body])),
        }
      }
      ast::Glob::EDefn(s, v) => ElabGlob::EDefn(s, v),
    }
  }

  fn write_elab(&self, f: &mut Formatter) -> Result<(), Error> {
    match self {
      ElabGlob::TypDef(t, TypName(id)) => {
        write!(f, "type {} means {}", id, t)
      }
      ElabGlob::HeadDecl(rt, id, p) => {
        write!(f, "{} _h_{}({});", rt, id, p)
      }
      ElabGlob::FnDecl(rt, id, p) => {
        write!(f, "{} _f_{}({});", rt, id, p)
      }
      ElabGlob::FnDefn(rt, id, p, body) => {
        write!(f, "{} _f_{}({}) {{\n", rt, id, p)?;
        body.write_elab(f, 1)?;
        write!(f, "\n}}\n")
      }
      ElabGlob::SDecl(TypName(tn)) => {
        write!(f, "struct {};", tn)
      }
      ElabGlob::SDefn(TypName(tn), fl) => {
        write!(f, "struct {} {{ {} }}", tn, fl)
      }
      ElabGlob::EDefn(s, v) => {
        write!(f, "enum {} = ", s)?;
        lst_print(f, &v, " | ")?;
        write!(f, ";")
      }
    }
  }
}

pub struct ElabProgram(pub Vec<ElabGlob>);

/// Elaborates function bodies in an ast one by one.
pub fn elab_program(p: ast::Program) -> ElabProgram {
  let mut v = Vec::<ElabGlob>::new();
  for g in p.0 {
    v.push(ElabGlob::elab(g));
  }
  ElabProgram(v)
}

impl std::fmt::Display for ElabStmt {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    self.write_elab(f, 0)
  }
}

impl std::fmt::Display for ElabLval {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    match self {
      ElabLval::Var(s) => write!(f, "{}", s),
      ElabLval::Dot(lv, s) => write!(f, "({}).({})", lv, s),
      ElabLval::Deref(lv) => write!(f, "*({})", lv),
      ElabLval::Idx(lv, e) => write!(f, "({})[{}]", lv, e),
    }
  }
}

impl std::fmt::Display for ElabGlob {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    self.write_elab(f)
  }
}

impl std::fmt::Display for ElabProgram {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    for item in &self.0 {
      write!(f, "\n{}\n", item)?;
    }
    Ok(())
  }
}
