// L2 Compiler
//! Abstract Syntax Trees
// Author: Dan Cascaval <dcascava@andrew.cmu.edu>

use std::{
  collections::{HashMap, HashSet},
  fmt::{Debug, Display, Formatter},
};

use crate::{
  elab_after_tc::TypCtx2,
  error::{errs, Error, Result},
  reg_alloc::x86_register::NamedReg,
  tc::tc_info::TcInfoFn,
  util::{
    c0spec::ALLOW_TYPEDEF_SHADOWING,
    prettyprint::{lst_paren_if_nonempty, lst_print},
  },
};

use crate::asm::DestSize;

pub type Var = String;
pub type FieldName = String;

#[derive(Clone, PartialEq, Eq)]
pub struct FnName(pub String);

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TypName(pub String);

/// A mapping of type names to its meanings.
pub struct TypCtxt(HashMap<String, Typ>);

impl TypCtxt {
  /// Creates an empty type context.
  pub fn new() -> Self {
    TypCtxt(HashMap::<String, Typ>::new())
  }

  /// Define some type name `ident` and make it equal to `typ`. When
  /// `ALLOW_TYPEDEF_SHADOWING` is turned on, this function simply overwrites a
  /// previously existing `typedef`; otherwise, an error is returned.
  pub fn define(&mut self, typ: &Typ, ident: &str) -> Result<()> {
    // chk shadowing
    if self.0.contains_key(ident) && !ALLOW_TYPEDEF_SHADOWING {
      let old_typ = self.0.get(ident).expect("std::HashMap integrity");
      return errs(format!(
        "Cannot redefine type `{}` as `{}` because it is \
      already defined as `{}`",
        ident, typ, old_typ
      ));
    }

    let old_typ = {
      match typ {
        Typ::Custom(s) => match self.0.get(s) {
          Some(x) => x.clone(),
          None => return errs(format!("Cannot resolve type `{}`", typ)),
        },
        Typ::Int
        | Typ::Bool
        | Typ::C0struct(_)
        | Typ::C0enum(_)
        | Typ::C0array(..)
        | Typ::C0ptr(_) => typ.clone(),
      }
    };
    assert!(
      old_typ.is_not_custom(),
      "typedef cannot resolve to primitive"
    );
    self.0.insert(ident.to_string(), old_typ.clone());
    Ok(())
  }

  pub fn check_defined(&self, typname: &str) -> bool {
    self.0.contains_key(typname)
  }

  /// Resolves the given type to its immediate meaning.
  pub fn resolve_typ(&self, t: &Typ) -> Result<Typ> {
    match &t {
      Typ::Custom(ref s) => match self.0.get(s) {
        Some(x) => Ok(x.clone()),
        None => errs(format!("Cannot resolve type `{}`", t)),
      },
      Typ::C0array(t) => Ok(Typ::C0array(Box::new(self.resolve_typ(t)?))),
      Typ::C0ptr(t) => Ok(Typ::C0ptr(Box::new(self.resolve_typ(t)?))),
      Typ::Int | Typ::Bool | Typ::C0struct(_) | Typ::C0enum(_) => Ok(t.clone()),
    }
  }

  pub fn resolve_ret_typ(&self, t: &RetTyp) -> Result<RetTyp> {
    match t {
      RetTyp::Void => Ok(RetTyp::Void),
      RetTyp::T(typ) => Ok(RetTyp::T(self.resolve_typ(&typ)?)),
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RetTyp {
  T(Typ),
  Void,
}

#[derive(Clone)]
pub enum Typ {
  Int,
  Bool,
  Custom(String),
  C0ptr(Box<Typ>),
  C0array(Box<Typ>),
  C0struct(String),
  C0enum(String),
}

impl Typ {
  /// Checks whether self is not custom type.
  pub fn is_not_custom(&self) -> bool {
    match self {
      Typ::Custom(_) => false,
      _ => true,
    }
  }

  /// Deduces the size of type in `bytes`.
  ///
  /// [warning] Does not handle custom type.
  pub fn size(&self, tc_info_fn: &TcInfoFn) -> usize {
    match self {
      Typ::Int | Typ::Bool => 4,
      Typ::C0ptr(_) | Typ::C0array(_) | Typ::C0enum(_) => 8,
      Typ::C0struct(sname) => tc_info_fn.struct_size(sname),
      Typ::Custom(_) => panic!("Custom shall be resolved b4 calling size()"),
    }
  }

  /// Similar to `size()` but returns only `DestSize` (and therefore only
  /// works for small types)
  pub fn dsize(&self, tc_info_fn: &TcInfoFn) -> DestSize {
    match self {
      Typ::Int | Typ::Bool => DestSize::quad,
      Typ::C0ptr(_) | Typ::C0array(_) | Typ::C0enum(_) => DestSize::oct,
      t => panic!("Cannot deduce the destsize of `{}`", t),
    }
  }

  pub fn smalltyp_size_bytes(&self) -> usize {
    match self {
      Typ::Int | Typ::Bool => 4,
      Typ::C0ptr(_) | Typ::C0array(_) | Typ::C0enum(_) => 8,
      t => panic!("`{}` is not a small type", t),
    }
  }

  pub fn get_dest_size(&self) -> DestSize {
    match self {
      Typ::Int | Typ::Bool => DestSize::quad,
      Typ::C0ptr(_) | Typ::C0array(_) | Typ::C0enum(_) => DestSize::oct,
      Typ::C0struct(_) => {
        panic!("Cannot get dest size of struct, check tc_info instead")
      }
      Typ::Custom(_) => {
        panic!("Custom shall be resolved b4 calling get_dest_size()")
      }
    }
  }

  pub fn is_struct(&self) -> bool {
    match self {
      Typ::C0struct(_) => true,
      _ => false,
    }
  }

  pub fn get_struct_name(&self) -> Option<&String> {
    match self {
      Typ::C0struct(s) => Some(s),
      _ => None,
    }
  }

  pub fn is_ptr(&self) -> bool {
    match self {
      Typ::C0ptr(_) => true,
      _ => false,
    }
  }

  pub fn get_ptr_type(&self) -> Option<&Typ> {
    match self {
      Typ::C0ptr(t) => Some(t),
      _ => None,
    }
  }

  pub fn is_array(&self) -> bool {
    match self {
      Typ::C0array(_) => true,
      _ => false,
    }
  }

  pub fn is_null(&self) -> bool {
    match self {
      Typ::C0ptr(s) => match s.as_ref() {
        Typ::C0struct(s) => s == "NULL",
        _ => false,
      },
      _ => false,
    }
  }
}

impl PartialEq for Typ {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (Typ::Int, Typ::Int) => true,
      (Typ::Bool, Typ::Bool) => true,
      (Typ::Custom(s1), Typ::Custom(s2)) => s1 == s2,
      (Typ::C0ptr(t1), Typ::C0ptr(t2)) => t1 == t2,
      (Typ::C0array(t1), Typ::C0array(t2)) => t1 == t2,
      (Typ::C0struct(s1), Typ::C0struct(s2)) => {
        s1 == s2 || s1 == "NULL" || s2 == "NULL"
      }
      (Typ::C0struct(s1), _) => s1 == "NULL",
      (_, Typ::C0struct(s2)) => s2 == "NULL",
      (Typ::C0enum(s1), Typ::C0enum(s2)) => s1 == s2,
      _ => false,
    }
  }
}

impl Eq for Typ {}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum BinOp {
  Add,  // +
  Sub,  // -
  Mul,  // *
  Div,  // /
  Mod,  // %
  Lt,   // <
  Le,   // <=
  Gt,   // >
  Ge,   // >=
  Eq,   // ==
  Ne,   // !=
  AAnd, // &&
  OOr,  // ||
  And,  // &
  Or,   // |
  Xor,  // ^
  Shl,  // <<
  Shr,  // >>
}

#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum UnOp {
  Neg,  // -
  Not,  // !
  Tild, // ~
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PostOp {
  Pp, // ++
  Mm, // --
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum AsnOp {
  PlusEq,  // +=
  MinusEq, // -=
  TimesEq, // *=
  DivEq,   // /=
  ModEq,   // %=
  AndEq,   // &=
  XorEq,   // ^=
  OrEq,    // |=
  ShlEq,   // <<=
  ShrEq,   // >>=
}

/// Helper function to convert assignment operators to their original operator.
#[allow(dead_code)]
pub fn to_op(op: AsnOp) -> BinOp {
  use AsnOp::*;
  use BinOp::*;

  match op {
    PlusEq => Add,
    MinusEq => Sub,
    TimesEq => Mul,
    DivEq => Div,
    ModEq => Mod,
    AndEq => And,
    XorEq => Xor,
    OrEq => Or,
    ShlEq => Shl,
    ShrEq => Shr,
  }
}

#[derive(Clone)]
pub struct Program(pub Vec<Glob>);

impl std::ops::Add for Program {
  type Output = Self;

  fn add(self, mut rhs: Self) -> Self::Output {
    let mut v = self.0;
    v.append(&mut rhs.0);
    Program(v)
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParamList(pub Vec<Param>);

impl ParamList {
  /// Extracts a vec of parameter var names, discarding their type annotations.
  pub fn to_vec_vars(&self) -> Vec<String> {
    self.0.iter().cloned().map(|pm| pm.1).collect()
  }

  pub fn new() -> Self {
    ParamList(Vec::new())
  }

  /// Returns a vec of pairs of parameter names and corresponding named
  /// registers. In particular, such a vector will always have a length of
  /// no more than six.
  pub fn param_name_reg_pairs(&self) -> Vec<(String, NamedReg)> {
    let param_vec = self.to_vec_vars();

    let reg_related_params = match param_vec.len() {
      0..=6 => &param_vec,
      _ => &param_vec[0..6],
    };

    let mut ret = Vec::<(String, NamedReg)>::new();

    for (argpos, name) in reg_related_params.into_iter().enumerate() {
      ret.push((name.clone(), NamedReg::from_first_six_function_arg(argpos)));
    }

    ret
  }
}

#[derive(Clone, Debug)]
pub struct Param(pub Typ, pub Var);

/// We only require Param to have same typ name, not same var name.
impl PartialEq for Param {
  fn eq(&self, other: &Self) -> bool {
    self.0 == other.0
  }
}
impl Eq for Param {}

#[derive(Clone, Debug)]
pub struct FieldList(pub Vec<Field>);

#[derive(Clone, Debug)]
pub struct Field(pub Typ, pub FieldName);

/// A variant of some `enum`, consisting of a name and a vector of fields.
#[derive(Clone, Debug)]
pub struct Variant(pub String, pub Vec<Typ>);

#[derive(Clone, Debug)]
pub enum C0mac {
  Clone,
  Debug,
  Hash,
}

#[derive(Clone, Debug)]
pub enum Glob {
  HeadDecl(RetTyp, FnName, ParamList),
  FnDecl(RetTyp, FnName, ParamList),
  FnDefn(RetTyp, FnName, ParamList, Stmt),
  TypDef(Typ, TypName),
  SDecl(TypName),
  SDefn(TypName, FieldList),
  EDefn(String, Vec<Variant>),
}

#[derive(Clone, Debug)]
pub enum Lval {
  Var(String),
  Dot(Box<Lval>, FieldName),
  Arrow(Box<Lval>, FieldName),
  Deref(Box<Lval>),
  Idx(Box<Lval>, Box<Expr>),
}

impl std::convert::TryFrom<Expr> for Lval {
  type Error = crate::error::Error;
  fn try_from(value: Expr) -> Result<Self> {
    match value {
      Expr::Variable(s) => Ok(Lval::Var(s)),
      Expr::Dot(lv, f) => Ok(Lval::Dot(Box::new(Lval::try_from(*lv)?), f)),
      Expr::Arrow(lv, f) => Ok(Lval::Arrow(Box::new(Lval::try_from(*lv)?), f)),
      Expr::Deref(lv) => Ok(Lval::Deref(Box::new(Lval::try_from(*lv)?))),
      Expr::Idx(lv, e) => Ok(Lval::Idx(Box::new(Lval::try_from(*lv)?), e)),
      e => Err(Error::Message(format!("Cannot convert {} to lvalue", e))),
    }
  }
}

#[derive(Clone, Debug)]
pub enum Simp {
  Decl(Typ, Var),
  Defn(Typ, Var, Expr),
  Asgn(Lval, Option<AsnOp>, Expr),
  Post(Lval, PostOp),
  E(Expr),
}

/// Patterns for matching, which can be a whid-card, a variable, or an
/// expansion of some variant of an enum.
#[derive(Clone, Debug)]
pub enum Patt {
  Any,
  Variable(String),
  Variant(String, String, Vec<Patt>),
}

impl Patt {
  /// Given some pattern, its associated type, and relevant tc info, returns
  /// a vector of defined variables, pairs with their types.
  pub fn vars_typs(
    &self,
    self_typ: &Typ,
    tc_info_fn: &TcInfoFn,
  ) -> Vec<(String, Typ)> {
    match self {
      Patt::Variant(e, v, patts) => {
        let mut ret = Vec::<(String, Typ)>::new();

        let n = patts.len();
        let typs = tc_info_fn.ev_typs(e, v);
        assert_eq!(n, typs.len());

        for i in 0..n {
          ret.extend(patts[i].vars_typs(&typs[i], tc_info_fn))
        }

        ret
      }
      Patt::Variable(x) => vec![(x.clone(), self_typ.clone())],
      Patt::Any => vec![],
    }
  }
}

/// Local statement (declare variable, define, assign, block, etc.)
#[derive(Clone, Debug)]
pub enum Stmt {
  // Simp
  Simp(Simp),

  // block
  Block(Vec<Stmt>),

  // controls
  Ret(Option<Expr>),
  If(Expr, Box<Stmt>, Option<Box<Stmt>>),
  While(Expr, Box<Stmt>),
  For(Option<Simp>, Expr, Option<Simp>, Box<Stmt>),
  Match(Expr, Vec<(Patt, HashSet<String>, Stmt)>),
  Assert(Expr),
}

/// Expression tree.
// This uses boxes to enable the recursive type. Pattern-matching against
// boxes requires #[feature(box_patterns)], which exists only in nightly Rust.
// You may want to adjust the starter code to make use of this, or adopt
// a different approach entirely.
// https://doc.rust-lang.org/unstable-book/language-features/box-patterns.html
#[derive(Clone, Debug)]
pub enum Expr {
  Number(i32),
  Variable(Var),
  True,
  False,
  Unop(UnOp, Box<Expr>),
  Binop(Box<Expr>, BinOp, Box<Expr>),
  Terop(Box<Expr>, Box<Expr>, Box<Expr>),

  // for function calls
  FnCall(FnName, ArgList),

  // lab4
  Null,
  Dot(Box<Expr>, FieldName),
  Arrow(Box<Expr>, FieldName),
  Deref(Box<Expr>),
  Idx(Box<Expr>, Box<Expr>),
  Alloc(Typ),
  AllocArr(Typ, Box<Expr>),

  // lab6
  EnumVar(String, String, Vec<Expr>),
}

impl Expr {
  /// Attempts to deduce type of expr.
  ///
  /// [warning] Only works after tc.
  pub fn deduce_typ(&self, tc_info_fn: &TcInfoFn, typctx: &TypCtx2) -> RetTyp {
    use Expr::*;
    use Typ::*;
    match self {
      Number(_) => RetTyp::T(Int),
      True | False => RetTyp::T(Bool),
      Null => RetTyp::T(C0ptr(Bool.into())),
      Alloc(t) => RetTyp::T(C0ptr(t.clone().into())),
      AllocArr(t, _) => RetTyp::T(C0array(t.clone().into())),
      FnCall(fname, _) => tc_info_fn.function_rettyp(&fname.0),
      Arrow(..) => panic!("Should not encounter arrow after TC"),
      Unop(.., e) | Binop(e, ..) | Terop(.., e) => {
        e.deduce_typ(tc_info_fn, typctx)
      }
      Variable(x) => RetTyp::T(
        typctx
          .get(x)
          .expect(format!("Cannot find {} in typctx: {:?}", x, typctx).as_str())
          .clone(),
      ),
      Dot(e, fdname) => {
        let sname = match e.deduce_typ(tc_info_fn, typctx) {
          RetTyp::T(C0struct(sname)) => sname,
          t => panic!("TC failed to catch invalid use of `{}` as struct", t),
        };
        RetTyp::T(tc_info_fn.sf_typ(&sname, fdname))
      }
      Deref(e) => match e.deduce_typ(tc_info_fn, typctx) {
        RetTyp::T(C0ptr(t)) => RetTyp::T(*t),
        t => panic!("TC failed to catch invalid deref of `{}`", e),
      },
      Idx(e, _) => match e.deduce_typ(tc_info_fn, typctx) {
        RetTyp::T(C0array(t)) => RetTyp::T(*t),
        t => panic!("TC failed to catch invalid arr-access of `{}`", e),
      },
      EnumVar(s, ..) => RetTyp::T(C0enum(s.clone())),
    }
  }

  /// Deduces the struct name of some `ElabLval`; panics if fails.
  pub fn deduce_struct_name(
    &self,
    tc_info_fn: &TcInfoFn,
    typctx: &TypCtx2,
  ) -> String {
    match self.deduce_typ(tc_info_fn, typctx) {
      RetTyp::T(Typ::C0struct(s)) => s,
      t => panic!("Cannot deduce `{}` as struct", t),
    }
  }

  /// Deduces the element typ of some array; panics if fails.
  pub fn deduce_c0array_elt_typ(
    &self,
    tc_info_fn: &TcInfoFn,
    typctx: &TypCtx2,
  ) -> Typ {
    match self.deduce_typ(tc_info_fn, typctx) {
      RetTyp::T(Typ::C0array(t)) => *t,
      t => panic!("Cannot deduce `{}` as struct", t),
    }
  }
}

impl From<Lval> for Expr {
  fn from(value: Lval) -> Self {
    match value {
      Lval::Var(s) => Expr::Variable(s),
      Lval::Dot(l, r) => Expr::Dot(Box::new(Expr::from(*l)), r),
      Lval::Arrow(l, r) => Expr::Arrow(Box::new(Expr::from(*l)), r),
      Lval::Deref(l) => Expr::Deref(Box::new(Expr::from(*l))),
      Lval::Idx(l, e) => Expr::Idx(Box::new(Expr::from(*l)), e),
    }
  }
}

/// List of args during function call
#[derive(Clone, Debug)]
pub struct ArgList(pub Vec<Expr>);

impl ArgList {
  /// Splits the argument into two slices of expressions, the first one
  /// should have length no more than 6, indicating the arguments that are
  /// passed by named registers; while the second (potentially empty) slice
  /// indicates the arguments that shall be pushed onto the stack before a
  /// function call.
  pub fn split_reg_stack<'a>(&'a self) -> (&'a [Expr], &'a [Expr]) {
    match self.0.len() {
      n @ 0..=6 => (&self.0[..n], &self.0[n..]),
      _ => (&self.0[..6], &self.0[6..]),
    }
  }

  /// Computes the number of bytes of needed to store the extra arguments, if
  /// any.
  ///
  /// [todo] Needs to change when type sizes differ.
  pub fn bytes_needed_on_stack(&self) -> usize {
    let n = self.0.len();
    if n <= 6 {
      0
    } else {
      8 * (n - 6)
    }
  }

  pub fn get_arity(&self) -> usize {
    self.0.len()
  }
}

// Some display functionality. You'll likely want to implement the Display
// trait in a way that you can print your compiler's version of the AST
// in a way that closely resembles indented and annotated source code.

impl Display for Stmt {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    match self {
      Stmt::Simp(smp) => write!(f, "{:?}", smp),
      Stmt::Block(v) => {
        write!(f, "Block(\n")?;
        for stmt in v {
          write!(f, "{},\n", stmt)?;
        }
        write!(f, ")\n")
      }
      Stmt::For(smp1, e, smp2, body) => {
        write!(f, "For({:?}, {}, {:?}, {})", smp1, e, smp2, body)
      }
      Stmt::While(e, body) => {
        write!(f, "While({}, {})", e, body)
      }
      Stmt::If(e, branch1, Some(branch2)) => {
        write!(f, "If({}, {}, {})", e, branch1, branch2)
      }
      Stmt::If(e, branch1, None) => {
        write!(f, "If({}, {}, None)", e, branch1)
      }
      Stmt::Match(e, branches) => {
        write!(f, "match {} ", e)?;
        for (patt, _, branch) in branches {
          write!(f, "{} => {},", patt, branch)?;
        }
        Ok(())
      }
      Stmt::Assert(e) => write!(f, "Assert({})", e),
      Stmt::Ret(Some(e)) => write!(f, "Ret({})", e),
      Stmt::Ret(None) => write!(f, "Ret"),
    }
  }
}

impl Display for ArgList {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    for arg in &self.0 {
      write!(f, "{},", arg)?;
    }
    Ok(())
  }
}

impl Display for Lval {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(f, "let {}", Expr::from(self.clone()))
  }
}

impl Display for Expr {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    match self {
      Expr::True => write!(f, "true"),
      Expr::False => write!(f, "false"),
      Expr::Number(n) => write!(f, "{}", n),
      Expr::Variable(varname) => write!(f, "${}", varname),
      Expr::Unop(op, e) => write!(f, "{}({})", op, e),
      Expr::Binop(e1, op, e2) => write!(f, "{}({}, {})", op, e1, e2),
      Expr::Terop(cond, e1, e2) => write!(f, "Terop({}, {}, {})", cond, e1, e2),
      Expr::FnCall(FnName(fname), args) => write!(f, "{}({})", fname, args),
      Expr::Alloc(t) => write!(f, "alloc({})", t),
      Expr::AllocArr(t, n) => write!(f, "alloc({},{})", t, n),
      Expr::Null => write!(f, "null"),
      Expr::Dot(l, r) => write!(f, "({}).({})", l, r),
      Expr::Arrow(l, r) => write!(f, "({})->({})", l, r),
      Expr::Deref(x) => write!(f, "*({})", x),
      Expr::Idx(l, n) => write!(f, "({})[{}]", l, n),
      Expr::EnumVar(name, variant, args) => {
        write!(f, "{}::{}", name, variant)?;
        lst_paren_if_nonempty(f, args, ", ")
      }
    }
  }
}

impl Display for Typ {
  fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
    match self {
      Typ::Int => write!(fmt, "int"),
      Typ::Bool => write!(fmt, "bool"),
      Typ::C0struct(s) => write!(fmt, "struct({})", s),
      Typ::C0enum(s) => write!(fmt, "enum({})", s),
      Typ::C0array(t) => write!(fmt, "[{}]", t),
      Typ::C0ptr(t) => write!(fmt, "{}*", t),
      Typ::Custom(s) => write!(fmt, "{}_t", s),
    }
  }
}

impl Display for BinOp {
  fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
    match *self {
      BinOp::Mul => write!(fmt, "*"),
      BinOp::Div => write!(fmt, "/"),
      BinOp::Mod => write!(fmt, "%"),
      BinOp::Add => write!(fmt, "+"),
      BinOp::Sub => write!(fmt, "-"),
      BinOp::Lt => write!(fmt, "<"),
      BinOp::Le => write!(fmt, "<="),
      BinOp::Gt => write!(fmt, ">"),
      BinOp::Ge => write!(fmt, ">="),
      BinOp::Eq => write!(fmt, "=="),
      BinOp::Ne => write!(fmt, "!="),
      BinOp::AAnd => write!(fmt, "&&"),
      BinOp::OOr => write!(fmt, "||"),
      BinOp::And => write!(fmt, "&"),
      BinOp::Or => write!(fmt, "|"),
      BinOp::Xor => write!(fmt, "^"),
      BinOp::Shl => write!(fmt, "<<"),
      BinOp::Shr => write!(fmt, ">>"),
    }
  }
}

impl Display for UnOp {
  fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
    match *self {
      UnOp::Neg => write!(fmt, "-"),
      UnOp::Not => write!(fmt, "!"),
      UnOp::Tild => write!(fmt, "~"),
    }
  }
}

impl Display for AsnOp {
  fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
    match *self {
      AsnOp::TimesEq => write!(fmt, "*="),
      AsnOp::DivEq => write!(fmt, "/="),
      AsnOp::ModEq => write!(fmt, "%="),
      AsnOp::PlusEq => write!(fmt, "+="),
      AsnOp::MinusEq => write!(fmt, "-="),
      AsnOp::AndEq => write!(fmt, "&="),
      AsnOp::OrEq => write!(fmt, "|="),
      AsnOp::XorEq => write!(fmt, "^="),
      AsnOp::ShlEq => write!(fmt, "<<="),
      AsnOp::ShrEq => write!(fmt, ">>="),
    }
  }
}

impl Display for FnName {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}_f", self.0)
  }
}

impl Display for RetTyp {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    match self {
      RetTyp::T(t) => write!(f, "{}", t),
      RetTyp::Void => write!(f, "void"),
    }
  }
}

impl Display for Param {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(f, "{} {}", self.0, self.1)
  }
}

impl Display for ParamList {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    for item in &self.0 {
      write!(f, "{}, ", item)?;
    }
    Ok(())
  }
}

impl Display for Field {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}: {}", self.0, self.1)
  }
}

impl Display for FieldList {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    for item in &self.0 {
      write!(f, "{}, ", item)?;
    }
    Ok(())
  }
}

impl Display for Glob {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    match self {
      Glob::FnDecl(rettyp, id, params) => {
        write!(f, "{} _f_{}({});", rettyp, id, params)?;
      }
      Glob::HeadDecl(rettyp, id, params) => {
        write!(f, "{} _h_{}({});", rettyp, id, params)?;
      }
      Glob::FnDefn(rettyp, id, params, body) => {
        write!(f, "{} {}({}) {{\n{}\n}}", rettyp, id, params, body)?;
      }
      Glob::TypDef(typ, TypName(id)) => {
        write!(f, "type {} means {}", id, typ)?;
      }
      Glob::SDecl(TypName(id)) => {
        write!(f, "struct {}", id)?;
      }
      Glob::SDefn(TypName(id), lst) => {
        write!(f, "struct {} {{ {} }}", id, lst)?;
      }
      Glob::EDefn(id, lst) => {
        write!(f, "enum {} {{ {:?} }}", id, lst)?;
      }
    }
    write!(f, "\n")
  }
}

impl Display for Variant {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.0)?;
    lst_paren_if_nonempty(f, &self.1, ", ")
  }
}

impl Display for Patt {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    match self {
      Patt::Variant(s1, s2, v) => {
        write!(f, "{}::{}", s1, s2)?;
        lst_paren_if_nonempty(f, &v, ", ")
      }
      Patt::Variable(s) => write!(f, "{}", s),
      Patt::Any => write!(f, "_"),
    }
  }
}

impl Display for Program {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    for item in &self.0 {
      write!(f, "\n{}", item)?;
    }
    Ok(())
  }
}

impl Debug for FnName {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}_f", self.0)
  }
}

impl Debug for Typ {
  fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
    write!(fmt, "{}", self)
  }
}

impl Debug for BinOp {
  fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
    write!(fmt, "{}", self)
  }
}
impl Debug for UnOp {
  fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
    write!(fmt, "{}", self)
  }
}

impl Debug for AsnOp {
  fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
    write!(fmt, "{}", self)
  }
}
