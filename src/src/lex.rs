// L1 Compiler
//! Lexer
// Author: Dan Cascaval <dcascava@andrew.cmu.edu>

// Update this file to lex the necessary keywords and other tokens
// in order to make the grammar forward compatible with C0.

use crate::ast::BinOp;
use crate::error::{err, errs, Error, Result};

use std::io::{Bytes, Read};
use std::iter::Peekable;
use std::{char, vec};

#[derive(Eq, PartialEq, Debug, Clone)]
pub enum Token {
  Ident(String),
  Number(i32),

  // Fn args
  COMMA,

  // Type system
  TYPEDEF,
  VOID,

  // Contract
  ASSERT,

  // Syntactic
  LPAREN,
  RPAREN,
  LBRACE,
  RBRACE,
  SEMICOLON,

  // Operators
  PLUS,
  MINUS,
  TIMES,
  DIV,
  MOD,
  LT,
  LE,
  GT,
  GE,
  EQ,
  NE,
  AAND,
  OOR,
  AND,
  OR,
  XOR,
  SHL,
  SHR,

  // PostOp
  PP,
  MM,

  // Assignments
  ASNEQUAL, // =
  PLUSEQ,
  MINUSEQ,
  TIMESEQ,
  DIVEQ,
  MODEQ,
  ANDEQ,
  XOREQ,
  OREQ,
  SHLEQ,
  SHREQ,

  //Control flow
  RETURN,
  IF,
  ELSE,
  WHILE,
  FOR,

  // Reserved types
  INT,
  BOOL,

  // Bool values
  TRUE,
  FALSE,

  // Unary op, note that - is also included among the binary operators.
  NOT,
  TILD,

  // Ternary op
  QUESTION,
  COLON,

  // Array
  ALLOCARR,
  LSQBRACKET,
  RSQBRACKET,

  // Struct
  STRUCT,
  ARROW,
  DOT,

  // Memory
  ALLOC,
  NULL,

  // Lab 4 control
  CONTINUE,
  BREAK,

  // Lab 4 other new types
  CHAR,
  STRING,

  // Lab 6 enum, etc.
  ENUM,
  MATCH,
  UNDERSCORE,
  DARROW,
  DOUBLECOLON,
  AT,
  CLONE,
  DEBUG,
  HASH,
}

impl Token {
  pub fn to_ast_binop(&self) -> Option<BinOp> {
    match self {
      Self::PLUS => Some(BinOp::Add),
      Self::MINUS => Some(BinOp::Sub),
      Self::TIMES => Some(BinOp::Mul),
      Self::DIV => Some(BinOp::Div),
      Self::MOD => Some(BinOp::Mod),
      Self::LT => Some(BinOp::Lt),
      Self::LE => Some(BinOp::Le),
      Self::GT => Some(BinOp::Gt),
      Self::GE => Some(BinOp::Ge),
      Self::EQ => Some(BinOp::Eq),
      Self::NE => Some(BinOp::Ne),
      Self::AAND => Some(BinOp::AAnd),
      Self::OOR => Some(BinOp::OOr),
      Self::AND => Some(BinOp::And),
      Self::OR => Some(BinOp::Or),
      Self::XOR => Some(BinOp::Xor),
      Self::SHL => Some(BinOp::Shl),
      Self::SHR => Some(BinOp::Shr),
      _ => None,
    }
  }
}

/// An enum of all levels of C0 binop precedence, listed in increasing order.
pub enum BinOpPrecedence {
  LogOr,
  LogAnd,
  BwOr,
  BwXor,
  BwAnd,
  EqCmp,
  OrdCmp,
  ArithSh,
  Pm,
  MulDivMod,
}

impl BinOpPrecedence {
  /// Returns the lowest level of precedence.
  pub fn lowest() -> Self {
    Self::LogOr
  }

  /// Returns a higher binop precedence than `self`; returns `None` if `self` is
  /// the highest-priority binop.
  pub fn next(&self) -> Option<Self> {
    use BinOpPrecedence::*;
    match self {
      LogOr => Some(LogAnd),
      LogAnd => Some(BwOr),
      BwOr => Some(BwXor),
      BwXor => Some(BwAnd),
      BwAnd => Some(EqCmp),
      EqCmp => Some(OrdCmp),
      OrdCmp => Some(ArithSh),
      ArithSh => Some(Pm),
      Pm => Some(MulDivMod),
      MulDivMod => None,
    }
  }

  /// Returns a vec of tokens corresponding to the precedence level of `self`.
  fn tokens(&self) -> Vec<Token> {
    use BinOpPrecedence::*;
    use Token::*;
    match self {
      LogOr => vec![OOR],
      LogAnd => vec![AAND],
      BwOr => vec![OR],
      BwXor => vec![XOR],
      BwAnd => vec![AND],
      EqCmp => vec![EQ, NE],
      OrdCmp => vec![LT, LE, GT, GE],
      ArithSh => vec![SHL, SHR],
      Pm => vec![PLUS, MINUS],
      MulDivMod => vec![TIMES, DIV, MOD],
    }
  }

  /// Checks if a token belongs to the precedence level represented by `self`.
  fn is_lvl_of(&self, t: &Token) -> bool {
    self.tokens().contains(t)
  }

  /// Returns `Some(op)` if `t` belongs to the precedence level represented by
  /// `self`, and `op` is the `ast::BinOp` corredpondence of `t` (as computed
  /// by `Token::to_ast_binop()`). Returns `None` otherwise.
  pub fn filter_to_ast_binop(&self, t: &Token) -> Option<BinOp> {
    if self.is_lvl_of(t) {
      t.to_ast_binop()
    } else {
      None
    }
  }
}

pub struct Lexer<R: Read> {
  line_number: usize,
  line_buf: String,
  help_buf: String,
  stream: Peekable<Bytes<R>>,
}

impl<R: Read> Lexer<R> {
  pub fn new(r: R) -> Self {
    Lexer {
      line_number: 1,
      line_buf: String::new(),
      help_buf: String::new(),
      stream: r.bytes().peekable(),
    }
  }

  /// When parsing fails, provides error message indicating failed position.
  pub fn fail_msg(&mut self) -> String {
    self.stream.next(); // consume the already-logged char.
    while let Some(Ok(c)) = self.stream.next() {
      if c as char == '\n' {
        break;
      } else {
        self.line_buf.push(c as char);
      }
    }

    let mut ret = self.line_number.to_string();
    ret.push_str(" | ");

    let helpbuf_offset_len = ret.len();

    self.help_buf.pop();
    self.help_buf.pop();

    ret.push_str(&self.line_buf);
    ret.push('\n');
    ret.push_str(&format!("{:1$}", "", helpbuf_offset_len));
    ret.push_str(&self.help_buf);
    ret.push_str("^\n");
    ret
  }

  /// Calls `stream.next()` while properlly updating errmsg info
  fn errmsg_stream_next(
    &mut self,
  ) -> std::option::Option<std::result::Result<u8, std::io::Error>> {
    if let Ok('\n') = self.current() {
      self.line_number += 1;
      self.line_buf = String::new();
      self.help_buf = String::new();
    }

    let ret = self.stream.next();

    if let Ok(c) = self.current() {
      self.line_buf.push(c);
      self
        .help_buf
        .push(if c.is_ascii_whitespace() { c } else { ' ' });
    }

    ret
  }

  /// Advance the stream
  fn skip(&mut self) {
    self.errmsg_stream_next();
  }

  /// Advance the stream and return the token.
  fn single(&mut self, tok: Token) -> Result<Token> {
    self.skip();
    Ok(tok)
  }

  /// Peek at the stream. This will return the same value if called multiple times.
  fn current(&mut self) -> Result<char> {
    if let Some(&Ok(byte)) = self.stream.peek() {
      return Ok(byte as char);
    }
    Err(Error::EOF)
  }

  /// Analogous to 'drop'. Advances stream while predicate is met.
  fn skip_while<F: Fn(char) -> bool>(&mut self, pred: F) -> Result<()> {
    let mut ch = self.current()?;
    while pred(ch) {
      self.errmsg_stream_next();
      if let Some(&Ok(b)) = self.stream.peek() {
        ch = b as char;
      } else {
        break;
      }
    }
    Ok(())
  }

  /// Like skip_while, except that it returns what it skipped.
  fn take_while<F: Fn(char) -> bool>(&mut self, pred: F) -> Result<String> {
    let mut buffer = String::new();
    buffer.push(self.current()?);
    self.skip();
    let mut ch = self.current()?;
    while pred(ch) {
      buffer.push(ch);
      self.skip();
      if let Some(&Ok(b)) = self.stream.peek() {
        ch = b as char;
      } else {
        break;
      }
    }
    Ok(buffer)
  }

  // Advance the iterator until the next line is done.
  fn line_comment(&mut self) -> Result<()> {
    self.skip_while(|ch| ch != '\n')?;

    // update pos
    self.line_number += 1;

    self.skip(); // Skip the newline too!
    Ok(())
  }

  // Advance the iterator until '*/' is found again.
  // Need to pop onto a stack if we match '/*' again.
  fn block_comment(&mut self) -> Result<()> {
    self.skip();
    let mut levels = 1;
    loop {
      self
        .skip_while(|ch| ch != '*' && ch != '/')
        .map_err(|error| {
          if matches!(error, Error::EOF) {
            Error::Message("Reached EOF Inside Block Comment".to_string())
          } else {
            error
          }
        })?;

      match (self.errmsg_stream_next(), self.stream.peek()) {
        (Some(Ok(current)), Some(&Ok(ch))) => {
          match (current as char, ch as char) {
            ('*', '/') => {
              self.skip();
              levels -= 1;
              if levels == 0 {
                return Ok(());
              }
            }
            ('/', '*') => {
              self.skip();
              levels += 1;
            }
            (..) => (),
          }
        }
        _ => return err("Unexpected end of file in block comment"),
      }
    }
  }

  fn slash(&mut self) -> Result<Token> {
    self.skip();
    match self.current()? {
      '*' => {
        self.block_comment()?;
        self.token()
      }
      '/' => {
        self.line_comment()?;
        self.token()
      }
      '=' => self.single(Token::DIVEQ),
      _ => Ok(Token::DIV),
    }
  }

  fn minus(&mut self) -> Result<Token> {
    self.skip();
    match self.current()? {
      '-' => self.single(Token::MM),
      '=' => self.single(Token::MINUSEQ),
      '>' => self.single(Token::ARROW),
      _ => Ok(Token::MINUS),
    }
  }

  fn plus(&mut self) -> Result<Token> {
    self.skip();
    match self.current()? {
      '+' => self.single(Token::PP),
      '=' => self.single(Token::PLUSEQ),
      _ => Ok(Token::PLUS),
    }
  }

  fn and(&mut self) -> Result<Token> {
    self.skip();
    match self.current()? {
      '&' => self.single(Token::AAND),
      '=' => self.single(Token::ANDEQ),
      _ => Ok(Token::AND),
    }
  }

  fn or(&mut self) -> Result<Token> {
    self.skip();
    match self.current()? {
      '|' => self.single(Token::OOR),
      '=' => self.single(Token::OREQ),
      _ => Ok(Token::OR),
    }
  }

  fn langle(&mut self) -> Result<Token> {
    self.skip();
    match self.current()? {
      '<' => self.maybe_equals(Token::SHL, Token::SHLEQ),
      '=' => self.single(Token::LE),
      _ => Ok(Token::LT),
    }
  }

  fn rangle(&mut self) -> Result<Token> {
    self.skip();
    match self.current()? {
      '>' => self.maybe_equals(Token::SHR, Token::SHREQ),
      '=' => self.single(Token::GE),
      _ => Ok(Token::GT),
    }
  }

  fn maybe_equals(&mut self, t: Token, equals: Token) -> Result<Token> {
    self.skip();
    match self.current()? {
      '=' => self.single(equals),
      '>' => self.single(Token::DARROW),
      _ => Ok(t),
    }
  }

  fn colons(&mut self) -> Result<Token> {
    self.skip();
    match self.current()? {
      ':' => self.single(Token::DOUBLECOLON),
      _ => Ok(Token::COLON),
    }
  }

  fn hexadecimal(&mut self) -> Result<Token> {
    fn preceding_zeros(string: &str) -> usize {
      for (i, chr) in string.char_indices() {
        if chr != '0' {
          return i;
        }
      }
      string.len()
    }

    self.skip();
    match self.current()? {
      'x' | 'X' => {
        self.errmsg_stream_next();
        let buffer = self.take_while(|ch| ch.is_ascii_hexdigit())?;
        if buffer.len() - preceding_zeros(&buffer) > 8 {
          errs(format!("Number too large: 0x{}", buffer))
        } else {
          let result = i64::from_str_radix(&buffer, 16).unwrap();
          Ok(Token::Number(result as i32))
        }
      }
      _ => Ok(Token::Number(0)),
    }
  }

  fn number(&mut self) -> Result<Token> {
    static INT_MIN: i64 = -2_147_483_648;
    static INT_MAX: i64 = 2_147_483_648;

    let buffer = self.take_while(char::is_numeric)?;
    if buffer == "0" {
      self.hexadecimal()
    } else {
      let result: i64 = buffer.parse().unwrap();
      if result >= INT_MIN && result <= INT_MAX {
        Ok(Token::Number(result as i32))
      } else {
        errs(format!("Number too large: ({})", result))
      }
    }
  }

  fn ident(&mut self) -> Result<Token> {
    let ident = self.take_while(|ch| ch.is_alphanumeric() || ch == '_')?;
    match ident.as_str() {
      // L1-2 Keywwords.
      "int" => Ok(Token::INT),
      "bool" => Ok(Token::BOOL),
      "true" => Ok(Token::TRUE),
      "false" => Ok(Token::FALSE),
      "return" => Ok(Token::RETURN),
      "for" => Ok(Token::FOR),
      "while" => Ok(Token::WHILE),
      "if" => Ok(Token::IF),
      "else" => Ok(Token::ELSE),
      "typedef" => Ok(Token::TYPEDEF),
      "void" => Ok(Token::VOID),
      "assert" => Ok(Token::ASSERT),
      "continue" => Ok(Token::CONTINUE),
      "break" => Ok(Token::BREAK),
      "struct" => Ok(Token::STRUCT),
      "NULL" => Ok(Token::NULL),
      "alloc" => Ok(Token::ALLOC),
      "alloc_array" => Ok(Token::ALLOCARR),
      "char" => Ok(Token::CHAR),
      "string" => Ok(Token::STRING),
      "enum" => Ok(Token::ENUM),
      "match" => Ok(Token::MATCH),
      "clone" => Ok(Token::CLONE),
      "debug" => Ok(Token::DEBUG),
      "hash" => Ok(Token::HASH),
      "_" => Ok(Token::UNDERSCORE),
      _tok => Ok(Token::Ident(ident)),
    }
  }

  pub fn token(&mut self) -> Result<Token> {
    let c = self.current()?;
    if c.is_whitespace() {
      self.skip_while(|ch| ch.is_whitespace())?;
      self.token()
    } else {
      match c {
        '}' => self.single(Token::RBRACE),
        '{' => self.single(Token::LBRACE),
        '(' => self.single(Token::LPAREN),
        ')' => self.single(Token::RPAREN),
        '<' => self.langle(),
        '>' => self.rangle(),
        '&' => self.and(),
        '|' => self.or(),
        '^' => self.maybe_equals(Token::XOR, Token::XOREQ),
        ',' => self.single(Token::COMMA),
        ';' => self.single(Token::SEMICOLON),
        '=' => self.maybe_equals(Token::ASNEQUAL, Token::EQ),
        '/' => self.slash(), // Might be comment or /=
        '*' => self.maybe_equals(Token::TIMES, Token::TIMESEQ),
        '-' => self.minus(), // Might be -- or -= or ->
        '+' => self.plus(),  // Might be ++
        '%' => self.maybe_equals(Token::MOD, Token::MODEQ),
        '?' => self.single(Token::QUESTION),
        ':' => self.colons(),
        '!' => self.maybe_equals(Token::NOT, Token::NE),
        '~' => self.single(Token::TILD),
        '[' => self.single(Token::LSQBRACKET),
        ']' => self.single(Token::RSQBRACKET),
        '.' => self.single(Token::DOT),
        '@' => self.single(Token::AT),
        '0' => self.hexadecimal(),
        '1'..='9' => self.number(),
        'a'..='z' | 'A'..='Z' | '_' => self.ident(),
        _ => errs(format!("Failed to match char {:?}", c)),
      }
    }
  }
}
