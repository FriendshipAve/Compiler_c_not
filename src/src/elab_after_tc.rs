//! Another elaboration pass after typechecking.
//!
//! (maybe make all types non-defined?)
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;

use crate::ast::Patt;
use crate::const_params::KEEP_TRIVIAL_LOOP;
use crate::tc::exhaust::PattBank;
use crate::util::prettyprint::lst_paren_if_nonempty;
use crate::{
  ast,
  elab::{ElabGlob, ElabLval, ElabProgram, ElabStmt},
  tc::tc_info::TcInfoFn,
};

use crate::asm::DestSize;

// -------------------------------- helper fn --------------------------------

/// Computes the num of bytes of needed to store extra fn arguments, if any.
pub fn bytes_needed_on_stack(arity: usize) -> usize {
  if arity <= 6 {
    0
  } else {
    8 * (arity - 6)
  }
}

// ----------------------------- end of helper fn -----------------------------

/// Whether array bounds check is enabled.
pub enum ArrBoundChk {
  Enabled,
  Disabled,
}

/// Valid C0 memory access
#[derive(Clone)]
pub enum MemAccess {
  /// Dereference of ptr with size.
  ///
  /// ## Syntax:
  /// `Deref(x, n) := Heap[*x .. *x + n)`
  Deref(Box<ExprP2>, usize),

  /// Static offset, two `usize` are offset and len.
  ///
  /// ## Syntax:
  /// `Offset(x, a, b) := Heap[x+a .. x+a+b)`
  Offset(Box<MemAccess>, usize, usize),

  /// Dynamic offset, with idx expr and arr item size. The first argument
  /// is a memory access to the first element of array.
  ///
  /// ## Syntax:
  /// `OffsetDyn(x, i, n) := Heap[x+n*i, x+n*(i+1))`
  OffsetDyn(Box<MemAccess>, Box<ExprP2>, usize),
}

impl std::fmt::Debug for MemAccess {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      MemAccess::Deref(lv, n) => {
        write!(f, "mem(*({:?}), len={:?})", lv, n)
      }
      MemAccess::Offset(lv, m, n) => {
        write!(f, "mem({:?} + {:?}, len={:?})", lv, m, n)
      }
      MemAccess::OffsetDyn(lv, idxexpr, n) => {
        write!(f, "mem({:?} + idx<{:?}>, len={:?})", lv, idxexpr, n)
      }
    }
  }
}

impl MemAccess {
  /// Coalesces consecutive struct offsets.
  fn coalesce(self) -> Self {
    let rec = |x: MemAccess| Box::new(x.coalesce());
    match self {
      MemAccess::Deref(lv, n) => match *lv {
        ExprP2::Mem(m) => {
          MemAccess::Deref(Box::new(ExprP2::Mem(m.coalesce())), n)
        }
        e => MemAccess::Deref(e.into(), n),
      },
      MemAccess::Offset(inner_struct_head, inner_offset, inner_fieldsize) => {
        match *inner_struct_head {
          // effectful case
          MemAccess::Offset(outer_struct_head, outer_offset, _) => {
            MemAccess::Offset(
              outer_struct_head,
              inner_offset + outer_offset,
              inner_fieldsize,
            )
            .coalesce()
          }
          mm => MemAccess::Offset(rec(mm), inner_offset, inner_fieldsize),
        }
      }
      MemAccess::OffsetDyn(lm, i, n) => MemAccess::OffsetDyn(rec(*lm), i, n),
    }
  }

  /// Returns the read length for such memory access.
  pub fn len(&self) -> usize {
    match self {
      MemAccess::Deref(_, n)
      | MemAccess::Offset(_, _, n)
      | MemAccess::OffsetDyn(_, _, n) => *n,
    }
  }

  /// Computes the source variable.
  pub fn source_var(&self) -> Option<String> {
    match self {
      MemAccess::Deref(e, _) => match &**e {
        ExprP2::Variable(vname, _) => Some(vname.clone()),
        ExprP2::Null | ExprP2::Alloc(..) | ExprP2::FnCall(..) => None,
        ExprP2::Mem(m) => m.source_var(),
        e => unreachable!("lhs encountered {}", e),
      },
      MemAccess::Offset(m, ..) | MemAccess::OffsetDyn(m, ..) => m.source_var(),
    }
  }
}

/// Valid C0 lval, which is either a variable or somewhere in memory.
#[derive(Clone)]
pub enum LvalP2 {
  Var(String, DestSize),
  Mem(MemAccess),
}

impl std::fmt::Debug for LvalP2 {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      LvalP2::Var(x, size) => write!(f, "${}_{:?}", x, size),
      LvalP2::Mem(m) => write!(f, "{:?}", m),
    }
  }
}

impl LvalP2 {
  /// Creates a box of self from some `MemAccess`
  pub fn box_mem(mem: MemAccess) -> Box<Self> {
    Box::new(LvalP2::Mem(mem))
  }

  pub fn from_elablval(
    el: ElabLval,
    tc_info_fn: &TcInfoFn,
    typctx: &TypCtx2,
  ) -> LvalP2 {
    let rec = |x: Box<ElabLval>, typctx: &TypCtx2| {
      Box::new(Self::from_elablval(*x, tc_info_fn, typctx))
    };

    match el {
      ElabLval::Var(s) => {
        let var_typ = typctx.get(&s).expect("var not found in typctx");
        let var_size = var_typ.get_dest_size();
        LvalP2::Var(s, var_size)
      }
      ElabLval::Deref(elv) => {
        let typ = match elv.deduce_typ(tc_info_fn, typctx) {
          ast::Typ::C0ptr(typ) => *typ,
          bad_typ => {
            panic!("TC failed to catch invalid deref of type `{:?}`", bad_typ)
          }
        };
        let processed_elv = ExprP2::from(*rec(elv, typctx));
        LvalP2::Mem(MemAccess::Deref(
          processed_elv.into(),
          typ.size(tc_info_fn),
        ))
      }
      ElabLval::Dot(elv, ref fdname) => {
        let sname = elv.deduce_struct_name(tc_info_fn, typctx);
        let offset = tc_info_fn.sf_offset(&sname, fdname);
        let len = tc_info_fn.sf_size(&sname, fdname);

        let mem_access = match *rec(elv, typctx) {
          LvalP2::Mem(m) => m,
          LvalP2::Var(x, ..) => unreachable!("TC failed to catch `{}._`", x),
        };

        LvalP2::Mem(MemAccess::Offset(Box::new(mem_access), offset, len))
      }
      ElabLval::Idx(elv, idx) => {
        let elt_typ = elv.deduce_c0array_elt_typ(tc_info_fn, typctx);
        let idx_expr =
          Box::new(ExprP2::from_elab_expr(*idx, tc_info_fn, typctx));
        let elt_size = elt_typ.size(tc_info_fn);

        let processed_elv = ExprP2::from(*rec(elv, typctx));
        let arr_head_pos =
          Box::new(MemAccess::Deref(processed_elv.into(), elt_size));

        LvalP2::Mem(MemAccess::OffsetDyn(arr_head_pos, idx_expr, elt_size))
      }
    }
  }

  /// Attempts to calculate the len of lval.
  fn len(&self) -> usize {
    use LvalP2::*;
    match self {
      Var(.., size) => size.raw(),
      Mem(m) => m.len(),
    }
  }

  /// Attempts to get a valid dest size of lval. Panics if fails.
  pub fn access_size(&self) -> DestSize {
    match self.len() {
      4 => DestSize::quad,
      8 => DestSize::oct,
      n => panic!("Invalid destsize of lval `{:?}`: size = {}", self, n),
    }
  }
}

#[derive(Debug, Clone)]
pub enum ExprP2 {
  Num(i32),
  Variable(String, DestSize),
  Unop(ast::UnOp, Box<ExprP2>),
  Binop(Box<ExprP2>, ast::BinOp, Box<ExprP2>),
  Terop(Box<ExprP2>, Box<ExprP2>, Box<ExprP2>),

  FnCall(ast::FnName, Vec<(DestSize, ExprP2)>),

  // memory
  Null,
  Mem(MemAccess),
  Alloc(usize, Option<Box<ExprP2>>),
  EnumVar(String, String, Vec<(usize, ExprP2)>),
  FetchTag(Box<ExprP2>),
  Unify(Box<ExprP2>, Box<Patt>),
}

impl ExprP2 {
  pub fn from_elab_expr(
    expr: ast::Expr,
    tc_info_fn: &TcInfoFn,
    typctx: &TypCtx2,
  ) -> Self {
    use ast::Expr;
    let rec = |x: Box<ast::Expr>, typctx: &TypCtx2| {
      Box::new(Self::from_elab_expr(*x, tc_info_fn, typctx))
    };
    match expr {
      // var
      Expr::Variable(x) => {
        let var_typ = typctx.get(&x).expect(
          format!("var not found in typctx: {}, ctx is {:?}", x, typctx)
            .as_str(),
        );
        let var_size = var_typ.get_dest_size();
        ExprP2::Variable(x, var_size)
      }
      // const
      Expr::Number(n) => ExprP2::Num(n),
      Expr::True => ExprP2::Num(1),
      Expr::False => ExprP2::Num(0),
      Expr::Null => ExprP2::Null,

      // op
      Expr::Unop(op, e) => ExprP2::Unop(op, rec(e, typctx)),
      Expr::Binop(e1, op, e2) => {
        ExprP2::Binop(rec(e1, typctx), op, rec(e2, typctx))
      }
      Expr::Terop(e1, e2, e3) => {
        ExprP2::Terop(rec(e1, typctx), rec(e2, typctx), rec(e3, typctx))
      }

      // call
      Expr::FnCall(fname, al) => {
        let v: Vec<ExprP2> = al
          .0
          .into_iter()
          .map(|x| Self::from_elab_expr(x, tc_info_fn, typctx))
          .collect();
        let sizes: Vec<DestSize> = tc_info_fn.function_param_size(&fname.0);

        ExprP2::FnCall(fname, std::iter::zip(sizes, v).collect())
      }

      Expr::Deref(e) => {
        let typ = match e.deduce_typ(tc_info_fn, typctx) {
          ast::RetTyp::T(ast::Typ::C0ptr(t)) => t,
          t => panic!("TC failed to catch dereference of {}", t),
        };
        ExprP2::Mem(MemAccess::Deref(rec(e, typctx), typ.size(tc_info_fn)))
      }

      Expr::Dot(elv, ref fdname) => {
        let sname = elv.deduce_struct_name(tc_info_fn, typctx);
        let offset = tc_info_fn.sf_offset(&sname, fdname);
        let len = tc_info_fn.sf_size(&sname, fdname);

        let mem_access = match *rec(elv, typctx) {
          ExprP2::Mem(m) => m,
          x => unreachable!("TC failed to catch `{:?}._`", x),
        };

        ExprP2::Mem(MemAccess::Offset(Box::new(mem_access), offset, len))
      }

      Expr::Idx(elv, idx) => {
        let elt_typ = elv.deduce_c0array_elt_typ(tc_info_fn, typctx);
        let idx_expr =
          Box::new(ExprP2::from_elab_expr(*idx, tc_info_fn, typctx));
        let elt_size = elt_typ.size(tc_info_fn);

        let processed_elv = ExprP2::from(*rec(elv, typctx));
        let arr_head_pos =
          Box::new(MemAccess::Deref(processed_elv.into(), elt_size));

        ExprP2::Mem(MemAccess::OffsetDyn(arr_head_pos, idx_expr, elt_size))
      }

      // alloc
      Expr::Alloc(t) => ExprP2::Alloc(t.size(tc_info_fn), None),
      Expr::AllocArr(t, e) => {
        ExprP2::Alloc(t.size(tc_info_fn), Some(rec(e, typctx)))
      }

      // enum variant construction, which is similar to alloc.
      Expr::EnumVar(eid, vid, args) => {
        let args: Vec<ExprP2> = args
          .into_iter()
          .map(|e| Self::from_elab_expr(e, tc_info_fn, typctx))
          .collect();
        let sizes: Vec<usize> = tc_info_fn.enum_variant_param_sizes(&eid, &vid);
        ExprP2::EnumVar(eid, vid, std::iter::zip(sizes, args).collect())
      }

      Expr::Arrow(..) => unreachable!(),
    }
  }

  /// Purity analysis.
  pub fn pure(&self, pure_fn: &HashSet<String>) -> bool {
    use ast::BinOp::*;
    use ExprP2::*;
    match self {
      Num(_) | Variable(..) | Null => true,
      Alloc(..) | Mem(..) | EnumVar(..) | FetchTag(_) | Unify(..) => false, // touches memory
      Unop(_, e) => e.pure(pure_fn),
      Terop(e1, e2, e3) => {
        e1.pure(pure_fn) && e2.pure(pure_fn) && e3.pure(pure_fn)
      }
      Binop(e1, Div | Mod, e2) => {
        let rhs_val = e2.eval_const_expr().unwrap_or(0);
        e1.pure(pure_fn) && rhs_val != 0 && rhs_val != -1
      }
      Binop(e1, Shl | Shr, e2) => {
        let rhs_val = e2.eval_const_expr().unwrap_or(-1);
        e1.pure(pure_fn) && rhs_val >= 0 && rhs_val < 32
      }
      Binop(e1, op, e2) => {
        if let (ExprP2::Num(1), AAnd) = (&**e1, op) {
          return true;
        }
        if let (ExprP2::Num(0), Oor) = (&**e1, op) {
          return true;
        }
        e1.pure(pure_fn) && e2.pure(pure_fn)
      }
      FnCall(fname, args) => {
        if !pure_fn.contains(&fname.0.clone()) {
          return false;
        }
        for (_, e) in args {
          if !e.pure(pure_fn) {
            return false;
          }
        }
        true
      }
    }
  }

  pub fn eval_const_expr(&self) -> Option<i32> {
    use ast::BinOp::*;
    use ExprP2::*;
    match self {
      Num(n) => Some(*n),
      Null => Some(0),
      Unop(ast::UnOp::Not, e) => Some(1 - e.eval_const_expr()?),
      Unop(ast::UnOp::Neg, e) => Some(-e.eval_const_expr()?),
      Unop(ast::UnOp::Tild, e) => None,
      Binop(e1, Add, e2) => Some(e1.eval_const_expr()? + e2.eval_const_expr()?),
      Binop(e1, Sub, e2) => Some(e1.eval_const_expr()? - e2.eval_const_expr()?),
      Binop(e1, Mul, e2) => Some(e1.eval_const_expr()? * e2.eval_const_expr()?),
      Binop(e1, Div, e2) => {
        let e2_eval = e2.eval_const_expr()?;
        if e2_eval == 0 {
          return None;
        }
        Some(e1.eval_const_expr()? / e2_eval)
      }
      Binop(e1, Mod, e2) => {
        let e2_eval = e2.eval_const_expr()?;
        if e2_eval == 0 {
          return None;
        }
        Some(e1.eval_const_expr()? % e2_eval)
      }
      Binop(e1, Lt, e2) => {
        Some(if e1.eval_const_expr()? < e2.eval_const_expr()? {
          1
        } else {
          0
        })
      }
      Binop(e1, Le, e2) => {
        Some(if e1.eval_const_expr()? <= e2.eval_const_expr()? {
          1
        } else {
          0
        })
      }
      Binop(e1, Ge, e2) => {
        Some(if e1.eval_const_expr()? >= e2.eval_const_expr()? {
          1
        } else {
          0
        })
      }
      Binop(e1, Gt, e2) => {
        Some(if e1.eval_const_expr()? > e2.eval_const_expr()? {
          1
        } else {
          0
        })
      }
      Binop(e1, Eq, e2) => {
        Some(if e1.eval_const_expr()? == e2.eval_const_expr()? {
          1
        } else {
          0
        })
      }
      Binop(e1, Ne, e2) => {
        Some(if e1.eval_const_expr()? != e2.eval_const_expr()? {
          1
        } else {
          0
        })
      }
      Binop(..) => None, // i am lazy
      Terop(..) => None,
      Alloc(..) | Mem(..) | FnCall(..) | EnumVar(..) | FetchTag(_) => None,
      Variable(..) => None,
      Unify(..) => None,
    }
  }

  pub fn is_const_expr(&self) -> bool {
    use ast::BinOp::*;
    use ExprP2::*;
    match self {
      Num(_) | Null => true,
      Unop(_, e) => e.is_const_expr(),
      Binop(e1, Div | Mod, e2) => {
        e1.is_const_expr()
          && e2.eval_const_expr().is_some()
          && e2.eval_const_expr().unwrap() != 0
      }
      Binop(e1, Shl | Shr, e2) => false,
      Binop(e1, _, e2) => e1.is_const_expr() && e2.is_const_expr(),
      FnCall(..) | Mem(..) | Alloc(..) => false,
      _ => false,
    }
  }

  /// One div zero, used for causing exceptions in codegen.
  pub fn one_div_zero() -> Self {
    ExprP2::Binop(
      Box::new(ExprP2::Num(1)),
      ast::BinOp::Div,
      Box::new(ExprP2::Num(0)),
    )
  }

  /// Attempts to deduce the size of dereferenced self.
  pub fn deref_size(&self, tc_info_fn: &TcInfoFn) -> DestSize {
    match self {
      _ => unimplemented!(),
    }
  }

  /// Attempts to calculate the size of expr.
  pub fn size(&self, tc_info_fn: &TcInfoFn) -> DestSize {
    use ast::BinOp::*;
    use DestSize::*;
    use ExprP2::*;
    match self {
      FetchTag(_) => quad, // enum tag is always some 32 bit.
      Unify(..) => quad,   // this is a bool.
      Num(_) => quad,
      Null => oct,
      Binop(_, Eq | Ne | Lt | Le | Ge | Gt, _) => quad,
      Unop(_, e) | Binop(e, ..) | Terop(.., e) => e.size(tc_info_fn),
      Alloc(..) | EnumVar(..) => oct,
      Mem(m) => match m.len() {
        4 => quad,
        8 => oct,
        n => panic!("Invalid expr mem access of size {}", n),
      },
      Variable(s, size) => *size,
      FnCall(ast::FnName(fname), ..) => {
        let rt = tc_info_fn.function_rettyp(fname);
        match rt {
          ast::RetTyp::T(t) => t.dsize(tc_info_fn),
          ast::RetTyp::Void => quad, // stores in dummy anyway
        }
      }
    }
  }
}

impl From<LvalP2> for ExprP2 {
  fn from(value: LvalP2) -> Self {
    match value {
      LvalP2::Var(x, s) => ExprP2::Variable(x, s),
      LvalP2::Mem(m) => ExprP2::Mem(m),
    }
  }
}

#[derive(Debug, Clone)]
pub struct TypCtx2 {
  pub ctx: HashMap<String, ast::Typ>,
}
impl TypCtx2 {
  pub fn new() -> Self {
    Self {
      ctx: HashMap::new(),
    }
  }

  pub fn add(&mut self, name: String, typ: ast::Typ) {
    self.ctx.insert(name, typ);
  }

  pub fn delete(&mut self, name: &str) {
    self.ctx.remove(name);
  }

  /// Gets the type of variable name.
  pub fn get(&self, name: &str) -> Option<&ast::Typ> {
    self.ctx.get(name)
  }
}

#[derive(Clone)]
pub struct PurityInfo {
  pub pure: bool,
  pub pure_fns: HashSet<String>,
  pub decl_vars: HashSet<String>,
  pub modified: HashSet<String>,
}

impl PurityInfo {
  pub fn new(pure_fns: HashSet<String>) -> Self {
    PurityInfo {
      pure: true,
      pure_fns,
      decl_vars: HashSet::<String>::new(),
      modified: HashSet::<String>::new(),
    }
  }

  /// Creates a similar instance, except clearing away `pure` and `modified`.
  pub fn dupl_new(&self) -> Self {
    PurityInfo {
      pure: true,
      pure_fns: self.pure_fns.clone(),
      decl_vars: self.decl_vars.clone(),
      modified: HashSet::<String>::new(),
    }
  }

  pub fn decl(&mut self, vname: String) {
    self.decl_vars.insert(vname);
  }

  pub fn rm_decl(&mut self, vname: &str) {
    self.decl_vars.remove(vname);
    self.modified.remove(vname);
  }

  pub fn set_dirty(&mut self) {
    self.pure = false;
  }

  pub fn modify(&mut self, vname: String) {
    self.modified.insert(vname);
  }

  pub fn chk_expr_purity(&mut self, e: &ExprP2) -> bool {
    if e.pure(&self.pure_fns) {
      true
    } else {
      self.pure = false;
      false
    }
  }

  pub fn is_pure_fn(&self, fname: &str) -> bool {
    self.pure_fns.contains(fname)
  }

  pub fn pure_and_didnt_modify(&self, set: &HashSet<String>) -> bool {
    self.pure && self.modified.is_disjoint(set)
  }
}

/// Elab pass2 statement
#[derive(Clone)]
pub enum StmtP2 {
  /// Bool is whether or not the variable initialized at assignment
  Declare(ast::Var, ast::Typ, Box<StmtP2>, bool),
  Assign(LvalP2, Option<ast::AsnOp>, ExprP2),
  If(ExprP2, Box<StmtP2>, Box<StmtP2>),
  While(ExprP2, Box<StmtP2>),
  Ret(Option<ExprP2>),
  Seq(Box<StmtP2>, Box<StmtP2>),
  Eval(ExprP2),
  Nop,
}

impl StmtP2 {
  fn from_elabstmt(
    es: ElabStmt,
    tc_info_fn: &TcInfoFn,
    typctx: &mut TypCtx2,
  ) -> Self {
    let rec = |x: Box<ElabStmt>, typctx: &mut TypCtx2| {
      Box::new(Self::from_elabstmt(*x, tc_info_fn, typctx))
    };
    match es {
      ElabStmt::Declare(v, t, e, b) => {
        // add to typctx when declare
        typctx.add(v.clone(), t.clone());
        let new_stmt = StmtP2::Declare(v.clone(), t, rec(e, typctx), b);
        typctx.delete(&v);
        new_stmt
      }
      ElabStmt::Assign(lv, e) => StmtP2::Assign(
        LvalP2::from_elablval(lv, tc_info_fn, typctx),
        None,
        ExprP2::from_elab_expr(e, tc_info_fn, typctx),
      ),
      ElabStmt::AssignEq(ElabLval::Var(x), op, e) => {
        StmtP2::Assign(
          LvalP2::from_elablval(ElabLval::Var(x.clone()), tc_info_fn, typctx),
          None,
          ExprP2::Binop(
            // for ease of deducing var size
            Box::new(ExprP2::from_elab_expr(
              ast::Expr::Variable(x),
              tc_info_fn,
              typctx,
            )),
            ast::to_op(op),
            Box::new(ExprP2::from_elab_expr(e, tc_info_fn, typctx)),
          ),
        )
      }
      ElabStmt::AssignEq(lv, op, e) => StmtP2::Assign(
        LvalP2::from_elablval(lv, tc_info_fn, typctx),
        Some(op),
        ExprP2::from_elab_expr(e, tc_info_fn, typctx),
      ),
      ElabStmt::If(e, s1, s2) => StmtP2::If(
        ExprP2::from_elab_expr(e, tc_info_fn, typctx),
        rec(s1, typctx),
        rec(s2, typctx),
      ),
      ElabStmt::While(e, s) => StmtP2::While(
        ExprP2::from_elab_expr(e, tc_info_fn, typctx),
        rec(s, typctx),
      ),
      ElabStmt::Ret(Some(e)) => {
        StmtP2::Ret(Some(ExprP2::from_elab_expr(e, tc_info_fn, typctx)))
      }
      ElabStmt::Ret(None) => StmtP2::Ret(None),
      ElabStmt::Seq(s1, s2) => StmtP2::Seq(rec(s1, typctx), rec(s2, typctx)),
      ElabStmt::Eval(e) => {
        StmtP2::Eval(ExprP2::from_elab_expr(e, tc_info_fn, typctx))
      }
      ElabStmt::Nop => StmtP2::Nop,
      ElabStmt::Match(e, v) => {

        // performs placeholder exhaustiveness chk
        // this is no longer needed
        // let patts = v.iter().map(|(p, ..)| p);
        // if ! PattBank::exhaustiveness_chk(patts, tc_info_fn) {
        //   eprintln!("Match non-exhaustive: {}", ElabStmt::Match(e, v));
        //   panic!()
        // }


        // this is used for vars_typs() fncall.
        let e_typ = e.deduce_typ(tc_info_fn, typctx);
        let e_typ = match e_typ {
          ast::RetTyp::T(t) => t,
          _ => unreachable!("cannot match on void expr"),
        };

        let new_expr = Box::new(ExprP2::from_elab_expr(e, tc_info_fn, typctx));
        let mut cases = Vec::<(ExprP2, Box<StmtP2>)>::new();

        for (p, _, s) in v {
          let vars_typs = &p.vars_typs(&e_typ, tc_info_fn);
          let cond = ExprP2::Unify(new_expr.clone(), Box::new(p.clone()));

          for (v, t) in vars_typs {
            typctx.add(v.clone(), t.clone());
          }
          let body = rec(s, typctx);
          for (v, _) in vars_typs {
            typctx.delete(v);
          }
          cases.push((cond, body));
        }

        let mut remaining_cases = StmtP2::Nop;
        while let Some((cond, body)) = cases.pop() {
          remaining_cases = StmtP2::If(cond, body, Box::new(remaining_cases));
        }

        remaining_cases
      }
    }
  }

  /// Function purity analysis
  pub fn part_of_pure_fn(
    &self,
    mut local_vars: HashSet<String>,
    pure_fn: &HashSet<String>,
  ) -> bool {
    use StmtP2::*;
    let ret = match self {
      Nop | Ret(None) => true,
      Assign(LvalP2::Mem(..), ..) => false,
      Assign(LvalP2::Var(varname, _), _, e) => e.pure(pure_fn),
      Eval(e) | Ret(Some(e)) => e.pure(pure_fn),
      Declare(varname, _, s, _) => {
        local_vars.insert(varname.clone());
        s.part_of_pure_fn(local_vars, pure_fn)
      }
      If(e, s1, s2) => {
        e.pure(pure_fn)
          && s1.part_of_pure_fn(local_vars.clone(), pure_fn)
          && s2.part_of_pure_fn(local_vars, pure_fn)
      }
      While(e, s) => e.pure(pure_fn) && s.part_of_pure_fn(local_vars, pure_fn),
      Seq(s1, s2) => {
        s1.part_of_pure_fn(local_vars.clone(), pure_fn)
          && s2.part_of_pure_fn(local_vars, pure_fn)
      }
    };
    ret
  }

  /// Uselessness purity analysis and synthesis
  pub fn magic(self, info: &mut PurityInfo) -> Self {
    use StmtP2::*;
    match self {
      Nop => Nop,
      Ret(x) => {
        info.set_dirty();
        Ret(x)
      }
      Seq(s1, s2) => Seq(Box::new(s1.magic(info)), Box::new(s2.magic(info))),
      Assign(LvalP2::Mem(ma), op, e) => {
        if let Some(vname) = ma.source_var() {
          info.modify(vname);
        }
        info.set_dirty();
        Assign(LvalP2::Mem(ma), op, e)
      }
      Assign(LvalP2::Var(vname, size), op, e) => {
        info.modify(vname.clone());
        info.chk_expr_purity(&e);
        Assign(LvalP2::Var(vname, size), op, e)
      }
      Declare(vname, t, s, b) => {
        let glob = info.decl_vars.clone();
        info.decl(vname.clone());

        // temporarily purity info
        let old_pure = info.pure;
        info.pure = true;
        let mut old_mod = HashSet::<String>::new();
        std::mem::swap(&mut info.modified, &mut old_mod);

        let s_m = s.magic(info);

        let elim = info.pure_and_didnt_modify(&glob);

        info.pure &= old_pure;
        info.modified.extend(old_mod);

        if elim {
          Nop
        } else {
          Declare(vname, t, Box::new(s_m), b)
        }
      }
      Eval(e) => {
        if info.chk_expr_purity(&e) {
          Nop
        } else {
          Eval(e)
        }
      }
      While(e, s) => {
        let glob = info.decl_vars.clone();

        // temporarily purity info
        let old_pure = info.pure;
        info.pure = true;
        let mut old_mod = HashSet::<String>::new();
        std::mem::swap(&mut info.modified, &mut old_mod);

        info.chk_expr_purity(&e);
        let s_m = s.magic(info);

        let elim = info.pure_and_didnt_modify(&glob);

        info.pure &= old_pure;
        info.modified.extend(old_mod);

        if let ExprP2::Num(1) = e {
          // while true: intention is clear.
          return While(e, Box::new(s_m));
        }

        if !KEEP_TRIVIAL_LOOP && elim {
          Nop
        } else {
          While(e, Box::new(s_m))
        }
      }
      If(e, s1, s2) => {
        let glob = info.decl_vars.clone();

        // temporarily purity info
        let old_pure = info.pure;
        info.pure = true;
        let mut old_mod = HashSet::<String>::new();
        std::mem::swap(&mut info.modified, &mut old_mod);

        info.chk_expr_purity(&e);
        let s1_m = s1.magic(info);
        let s2_m = s2.magic(info);

        let elim = info.pure_and_didnt_modify(&glob);

        info.pure &= old_pure;
        info.modified.extend(old_mod);

        if elim {
          Nop
        } else {
          If(e, Box::new(s1_m), Box::new(s2_m))
        }
      }
    }
  }
}

/// Elab pass 2 function definition
#[derive(Clone)]
pub struct FnDefnP2(
  pub ast::RetTyp,
  pub String,
  pub ast::ParamList,
  pub StmtP2,
);

impl FnDefnP2 {
  fn from_elabglob(eg: ElabGlob, tc_info_fn: &TcInfoFn) -> Option<Self> {
    if let ElabGlob::FnDefn(rt, fname, plist, body) = eg {
      let mut typctx = TypCtx2::new();
      for param in &plist.0 {
        let (v, t) = (param.0.clone(), param.1.clone());
        typctx.add(t, v);
      }
      Some(FnDefnP2(
        rt,
        fname.0,
        plist,
        StmtP2::from_elabstmt(body, tc_info_fn, &mut typctx),
      ))
    } else {
      None
    }
  }

  // Purity analysis
  fn pure(&self, pure_fn: &HashSet<String>) -> bool {
    let ret = self.3.part_of_pure_fn(HashSet::<String>::new(), pure_fn);
    // println!("[fn purity] {}: {}", self.1, ret);
    ret
  }
}

pub struct ProgramP2(pub Vec<FnDefnP2>);

impl ProgramP2 {
  pub fn from_elabpgrm(ep: ElabProgram, tc_info_fn: &TcInfoFn) -> Self {
    let mut v = Vec::<FnDefnP2>::new();
    for eg in ep.0 {
      if let Some(thing) = FnDefnP2::from_elabglob(eg, tc_info_fn) {
        v.push(thing);
      }
    }
    // println!("elab2: \n\n{}", ProgramP2(v.clone()));
    ProgramP2(v)
  }

  pub fn pure_fns(&self) -> HashSet<String> {
    let mut ret = HashSet::<String>::new();
    // run a few iterations would be fine
    for _ in 1..=5 {
      for f in &self.0 {
        if f.pure(&ret) {
          ret.insert(f.1.clone());
        }
      }
    }

    ret
  }
}

impl std::fmt::Display for MemAccess {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      MemAccess::Deref(e, len) => {
        write!(f, "{}.deref[{}]", e, len)
      }
      MemAccess::Offset(ma, fd, len) => {
        write!(f, "{}.get[{}, {})", ma, fd, fd + len)
      }
      MemAccess::OffsetDyn(ma, i, l) => write!(f, "{}.idx{{{}}}[{}]", ma, l, i),
    }
  }
}

impl std::fmt::Display for LvalP2 {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      LvalP2::Var(x, s) => write!(f, "{}{}", x, s.to_apos()),
      LvalP2::Mem(m) => write!(f, "{}", m),
    }
  }
}

impl std::fmt::Display for ExprP2 {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      ExprP2::Null => write!(f, "null"),
      ExprP2::Num(n) => write!(f, "{}", n),
      ExprP2::Variable(x, s) => write!(f, "{}{}", x, s.to_apos()),
      ExprP2::Mem(m) => write!(f, "{}", m),
      ExprP2::FnCall(fname, v) => write!(f, "{} ({:?})", fname, v),
      ExprP2::Alloc(n, None) => write!(f, "alloc({})", n),
      ExprP2::Alloc(n, Some(e)) => write!(f, "alloc({},{})", n, e),
      ExprP2::Unop(op, e) => write!(f, "op({})", e),
      ExprP2::Binop(e1, op, e2) => write!(f, "({} {} {})", e1, op, e2),
      ExprP2::Terop(e1, e2, e3) => write!(f, "({})?({}):({})", e1, e2, e3),
      ExprP2::EnumVar(e, v, args) => write!(f, "{}::{}({:?})", e, v, args),
      ExprP2::FetchTag(e) => write!(f, "tag({})", e),
      ExprP2::Unify(e, p) => write!(f, "let {} = {}", e, p),
    }
  }
}

impl std::fmt::Display for StmtP2 {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      StmtP2::Declare(x, t, body, init) => {
        let init_str = if *init { "init" } else { "un-init" };
        write!(f, "decl({} : {}, {}, \n{}\n){};", x, t, init_str, body, x)
      }
      StmtP2::Assign(lv, op, rv) => {
        let op_str = match op {
          Some(asn) => asn.to_string(),
          None => "=".to_string(),
        };
        write!(f, "{} {} {};", lv, op_str, rv)
      }
      StmtP2::If(cond, b1, b2) => {
        write!(
          f,
          "if {} {{\n{}\n}}else{{\n{}\n}}endif {};",
          cond, b1, b2, cond
        )
      }
      StmtP2::While(cond, body) => {
        write!(f, "while {} {{\n{}\n}} endwhile {};", cond, body, cond)
      }
      StmtP2::Ret(e) => {
        let e_str = match e {
          Some(e) => e.to_string(),
          None => "void".to_string(),
        };
        write!(f, "return {};", e_str)
      }
      StmtP2::Seq(s1, s2) => write!(f, "{}\n{}", s1, s2),
      StmtP2::Nop => write!(f, "nop;"),
      StmtP2::Eval(e) => write!(f, "eval({});", e),
    }
  }
}

impl std::fmt::Display for FnDefnP2 {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{} {} ({}) {{\n", self.0, self.1, self.2)?;
    write!(f, "{}", self.3)?;
    write!(f, "\n}}")
  }
}

impl std::fmt::Display for ProgramP2 {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for fndefn in &self.0 {
      write!(f, "{}\n", fndefn)?;
    }
    Ok(())
  }
}
