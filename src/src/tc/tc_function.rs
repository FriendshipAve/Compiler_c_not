#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_mut)]
#![allow(unused_assignments)]
#![allow(unused_must_use)]
#![allow(unused_parens)]
#![allow(unused_braces)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]
#![allow(non_upper_case_globals)]
//! Type Checker
// Author: Dan Cascaval <dcascava@andrew.cmu.edu>

// Simple typechecker that checks three properties:
//  (1) If a variable is initialized, it has previously been declared.
//  (2) If a variable is used, it has previously been initialized.
//  (3) Every program has a return statement.
// This is sufficient for now, since only int types are available in L1.
use super::ProgContext;
use crate::ast;
use crate::ast::RetTyp;
use crate::elab;
use crate::elab::ElabLval;
use crate::util::helper_typs::Lax;
// use crate::util::c0spec::DEBUG;
const DEBUG: bool = false;
use super::matching::Tuples;
use std::collections::HashMap;

/// L1 doesn't have all that much in the way of type information.
#[derive(Clone, Debug)]
struct Status {
  typ: ast::Typ,
  defn: bool,
}

#[derive(Debug, Clone)]
/// We use a mutable type-checking context, modified as the typechecker progresses.
/// L1 does not support nested scopes, so we keep everything at the same level.
struct Context {
  table: HashMap<ast::Var, Status>,
}

impl Context {
  fn new() -> Self {
    Context {
      table: HashMap::new(),
    }
  }
  /// Search through all of the currently available scopes for
  /// this variable, starting from the deepest and going up.
  fn get(&mut self, var: &str) -> Option<Status> {
    self.table.get(var).cloned()
  }

  fn gets(&self, var: &str) -> Option<Status> {
    self.table.get(var).cloned()
  }

  /// Declare a variable, in the current scope.
  fn declare(&mut self, s: ast::Var, t: ast::Typ) {
    let status = Status {
      typ: t,
      defn: false,
    };
    self.table.insert(s, status);
  }

  fn undeclare(&mut self, s: ast::Var) {
    self.table.remove(&s);
  }

  fn copy_back_if(&mut self, ctx1: Context, ctx2: Context) {
    let tmp_table = self.table.clone();
    for (var, _) in tmp_table.iter() {
      let var_name = var.clone();
      let status1 = ctx1.gets(&var_name).unwrap();
      let status2 = ctx2.gets(&var_name).unwrap();

      if status1.defn == true && status2.defn == true {
        self.table.insert(var_name, status1);
      }
    }
  }

  fn copy_back(&mut self, ctx1: Context) {
    let tmp_table = self.table.clone();
    for (var, _) in tmp_table.iter() {
      let var_name = var.clone();
      let status1 = ctx1.gets(&var_name).unwrap();

      if status1.defn == true {
        self.table.insert(var_name, status1);
      }
    }
  }

  /// Define a variable, in the current scope.
  fn define(&mut self, s: ast::Var, t: ast::Typ) {
    let status = Status { typ: t, defn: true };
    self.table.insert(s, status);
  }

  /// Create scope with all declared variables defined in it.
  fn define_all(&mut self) {
    for (_, status) in self.table.iter_mut() {
      status.defn = true
    }
  }

  fn is_declared(&self, var: &str) -> bool {
    self.table.get(var).is_some()
  }

  fn is_defined(&self, var: &str) -> bool {
    match self.table.get(var) {
      Some(Status { defn: true, .. }) => true,
      _ => false,
    }
  }
  fn get_type(&mut self, var: &str) -> Option<ast::Typ> {
    match self.table.get(var) {
      Some(Status { typ, .. }) => return Some((*typ).clone()),
      _ => return None,
    }
  }
}

struct TcStatus {
  pub ok: bool,
  pub ret: Option<ast::RetTyp>,
  pub should_ret: ast::RetTyp,
}
impl TcStatus {
  fn new(should_ret_typ: ast::RetTyp) -> Self {
    TcStatus {
      ok: true,
      ret: None,
      should_ret: should_ret_typ,
    }
  }
  fn set_tc(&mut self, tc: bool) {
    self.ok = self.ok && tc;
  }

  // match return statement with previous return results, false means type error, true means no error
  fn set_ret(&mut self, ret: Option<ast::RetTyp>) -> bool {
    if self.ret.is_none() {
      self.ret = ret;
      return true;
    }
    if ret.is_none() {
      return true;
    }
    if self.ret == ret {
      return true;
    }
    eprintln!(
      "Type Error: return type {} is not the same as previous return type {}",
      ret.unwrap(),
      self.ret.clone().unwrap()
    );
    self.ok = false;
    false
  }

  fn get_tc(&self) -> bool {
    self.ok
  }
  fn get_ret(&self) -> Option<ast::RetTyp> {
    self.ret.clone()
  }

  fn combine_tcStatus(&mut self, tc: &TcStatus) -> bool {
    self.ok = self.ok && tc.get_tc();
    if self.get_ret().is_some() && tc.get_ret().is_some() {
      if self.get_ret() != tc.get_ret() {
        eprintln!(
          "Type Error: return type {} is not the same as previous return type {}",
          tc.get_ret().unwrap(),
          self.get_ret().unwrap()
        );
        self.ok = false;
        return false;
      }
    }
    self.set_ret(tc.get_ret())
  }

  fn ret_status(&self) -> Option<ast::RetTyp> {
    if self.ok {
      return self.ret.clone();
    }
    None
  }
}

fn typ_to_ret(typ: ast::Typ) -> Option<ast::RetTyp> {
  match typ {
    ast::Typ::Custom(..) => {
      eprintln!(
        "Type Error: Custom type is not supported, it shall not appear in tc"
      );
      None
    }

    _ => Some(ast::RetTyp::T(typ)),
  }
}

fn ret_to_typ(ret: ast::RetTyp) -> Option<ast::Typ> {
  match ret {
    ast::RetTyp::T(a) => Some(a),
    _ => None,
  }
}

/// return the type of the expression in option format, None if type error
fn tc_expr(
  ctx: &mut Context,
  expr: &ast::Expr,
  progctx: &ProgContext,
  fnctx: &ProgContext,
) -> Option<ast::RetTyp> {
  use ast::Expr::*;

  match expr {
    EnumVar(eid, vid, exprs) => {
      let typs = progctx.ev_typs(eid, vid);
      match typs {
        Ok(typs) => {
          // checks arg-count
          let n = exprs.len();
          if n != typs.len() {
            eprintln!("Needs {} exprs in variant, found {}", typs.len(), n);
            None
          } else {
            // typechecks each argument
            for i in 0..n {
              let expr_t = tc_expr(ctx, &exprs[i], progctx, fnctx)?;
              if expr_t != ast::RetTyp::T(typs[i].clone()) {
                eprintln!("{} is not of type {}", exprs[i], typs[i]);
                return None;
              }
            }
            Some(RetTyp::T(ast::Typ::C0enum(eid.clone())))
          }
        }
        // undefined enum
        Err(e) => {
          eprintln!("tc enumvar failed: {}", e);
          None
        }
      }
    }
    Number(_) => typ_to_ret(ast::Typ::Int),
    Variable(ref var) => {
      if ctx.is_defined(var) {
        let resultType = ctx.get_type(var);
        if resultType.is_none() {
          eprintln!("Variable {} is not defined", var);
          return None;
        }
        typ_to_ret(ctx.get_type(var).unwrap())
      } else {
        eprintln!("Variable {} is not defined", var);
        None
      }
    }
    Unop(op, ref rhs) => {
      let exp_right = tc_expr(ctx, &rhs, progctx, fnctx);
      if exp_right.is_none() {
        eprintln!("Type error in expression: {:?}", rhs);
        return None;
      }
      let typ_right = ret_to_typ(exp_right.unwrap());
      match typ_right {
        Some(ast::Typ::Int) => match op {
          ast::UnOp::Not => {
            eprintln!("Type error in expression: {:?}", rhs);
            None
          }
          _ => typ_to_ret(ast::Typ::Int),
        },
        Some(ast::Typ::Bool) => match op {
          ast::UnOp::Not => typ_to_ret(ast::Typ::Bool),
          _ => {
            eprintln!("Type error in expression: {:?}", rhs);
            None
          }
        },
        _ => {
          eprintln!("Type error in expression: {:?}", rhs);
          None
        }
      }
    }
    True => typ_to_ret(ast::Typ::Bool),
    False => typ_to_ret(ast::Typ::Bool),
    Binop(ref lhs, op, ref rhs) => {
      let exp_left = tc_expr(ctx, &lhs, progctx, fnctx);
      let exp_right = tc_expr(ctx, &rhs, progctx, fnctx);
      use ast::BinOp::*;
      if exp_left.is_none() || exp_right.is_none() {
        return None;
      }
      let typ_left = ret_to_typ(exp_left.unwrap());
      let typ_right = ret_to_typ(exp_right.unwrap());

      let combined = match (typ_left, typ_right) {
        (Some(ast::Typ::Int), Some(ast::Typ::Int)) => match op {
          Add => Some(ast::Typ::Int),
          Sub => Some(ast::Typ::Int),
          Mul => Some(ast::Typ::Int),
          Div => Some(ast::Typ::Int),
          Mod => Some(ast::Typ::Int),
          And => Some(ast::Typ::Int),
          Or => Some(ast::Typ::Int),
          Xor => Some(ast::Typ::Int),
          Shl => Some(ast::Typ::Int),
          Shr => Some(ast::Typ::Int),

          Lt => Some(ast::Typ::Bool),
          Le => Some(ast::Typ::Bool),
          Gt => Some(ast::Typ::Bool),
          Ge => Some(ast::Typ::Bool),
          Eq => Some(ast::Typ::Bool),
          Ne => Some(ast::Typ::Bool),

          _ => None,
        },
        (Some(ast::Typ::Bool), Some(ast::Typ::Bool)) => match op {
          AAnd | OOr | Eq | Ne => Some(ast::Typ::Bool),
          _ => None,
        },
        (Some(ast::Typ::C0array(typL)), Some(ast::Typ::C0array(typR)))
        | (Some(ast::Typ::C0ptr(typL)), Some(ast::Typ::C0ptr(typR))) => {
          match op {
            Eq | Ne => {
              if typL == typR {
                Some(ast::Typ::Bool)
              } else {
                eprintln!("Type error in binop: {:?}", expr);
                None
              }
            }
            _ => {
              eprintln!("Type error in binop: {:?}", expr);
              None
            }
          }
        }
        (Some(ast::Typ::C0struct(nameL)), Some(ast::Typ::C0struct(nameR))) => {
          eprintln!(
            "Type error: cannot compare two structs in stmt {:?}",
            expr
          );
          None
        }
        _ => None,
      };
      if combined.is_none() {
        eprintln!("Type error in expression: {:?}", expr);
        return None;
      }
      typ_to_ret(combined.unwrap())
    }
    Terop(ref cond, ref then, ref els) => {
      let exp_cond = tc_expr(ctx, &cond, progctx, fnctx);
      let exp_then = tc_expr(ctx, &then, progctx, fnctx);
      let exp_else = tc_expr(ctx, &els, progctx, fnctx);
      if exp_cond.is_none() || exp_then.is_none() || exp_else.is_none() {
        return None;
      }
      let typ_cond = ret_to_typ(exp_cond.unwrap());
      let typ_then = ret_to_typ(exp_then.unwrap());
      let typ_else = ret_to_typ(exp_else.unwrap());
      match (typ_cond, typ_then, typ_else) {
        (Some(ast::Typ::Bool), Some(type1), Some(type2)) => {
          if type1 == type2 {
            if type1.is_null() {
              typ_to_ret(type2)
            } else if type1.is_struct() || type2.is_struct() {
              eprintln!(
                "cannot use the conditional expression 'e ? e1 : e2' on structs {:?}",
                expr
              );
              None
            } else {
              typ_to_ret(type1)
            }
          } else {
            eprintln!("Type error in expression: {:?}", expr);
            None
          }
        }
        _ => {
          eprintln!("Type error in expression: {:?}", expr);
          None
        }
      }
    }
    FnCall(name, args) => {
      // calling abort
      if name.0 == "c0_assert" {
        if args.0.len() != 1 {
          eprintln!("Abort should have 1 input, but got {:?}", args.0.len());
          return None;
        }
        let arg = args.0.get(0).unwrap();
        let arg_typ = tc_expr(ctx, &arg, progctx, fnctx);
        if arg_typ.is_none() {
          eprintln!("Abort should have bool input, but got {:?}", arg);
          return None;
        }
        if arg_typ.unwrap() != ast::RetTyp::T(ast::Typ::Bool) {
          eprintln!("Abort should have bool input, but got {:?}", arg);
          return None;
        }
        return Some(ast::RetTyp::Void);
      }
      let mut arg_types = Vec::new();
      for arg in args.0.clone() {
        match tc_expr(ctx, &arg, progctx, fnctx) {
          Some(typ) => {
            let typ = ret_to_typ(typ);
            if typ.is_none() {
              eprintln!("Type error in expression: {:?}", arg);
              return None;
            }
            arg_types.push(typ.unwrap());
          }
          None => return None,
        }
      }
      match progctx.get_fnDecl(name.clone()) {
        Some(func) => {
          let retTyp = func.retTyp.clone();
          let params = func.params.clone();
          if arg_types.len() != params.0.len() {
            eprintln!(
              "Function {} takes {} arguments, but {} are provided",
              name,
              params.0.len(),
              arg_types.len()
            );
            return None;
          }
          for (i, (arg, param)) in
            arg_types.iter().zip(params.0.iter()).enumerate()
          {
            if *arg != param.0 {
              eprintln!(
                "Argument {} of function {} has type {}, but {} is expected",
                i, name, arg, param
              );
              return None;
            }
          }
          if !fnctx.is_fnDefn(name.clone()) {
            eprintln!("Function {} is not defined", name);
            return None;
          }
          Some(retTyp.clone())
        }
        None => {
          eprintln!("Function {} is not declared", name);
          None
        }
      }
    }
    Dot(lv, field) => {
      let lv_typ = tc_expr(ctx, &lv, progctx, fnctx);
      if lv_typ.is_none() {
        return None;
      }
      let lv_typ = lv_typ.unwrap();
      let lv_typ = ret_to_typ(lv_typ);
      if lv_typ.is_none() {
        eprintln!("Type error in expression: {:?}", lv);
        return None;
      }
      let lv_typ = lv_typ.unwrap();
      match lv_typ {
        ast::Typ::C0struct(name) => {
          let struct_typ = progctx.get_structDecl(&name);
          if struct_typ.is_none() || struct_typ.unwrap().is_defined() == false {
            eprintln!(
              "Struct {} is not declared or declared not defined",
              name
            );
            return None;
          }
          let struct_typ = struct_typ.unwrap();
          let field_typ = struct_typ.get_field_typ(&field);
          if field_typ.is_none() {
            eprintln!("Struct {} does not have field {}", name, field);
            return None;
          }
          let field_typ = field_typ.unwrap();
          typ_to_ret(field_typ.clone())
        }
        _ => {
          eprintln!(
            "Dot can only be applied on a struct in expressions, error: {:?}",
            lv
          );
          None
        }
      }
    }
    Deref(lv) => {
      match **lv {
        ast::Expr::Null => {
          eprintln!("Deref cannot be applied on null");
          return None;
        }
        _ => (),
      }

      let lv_typ = tc_expr(ctx, &lv, progctx, fnctx);
      if lv_typ.is_none() {
        return None;
      }
      let lv_typ = lv_typ.unwrap();
      let lv_typ = ret_to_typ(lv_typ);
      if lv_typ.is_none() {
        eprintln!(
          "Type error in expression (void deref is not allowed): {:?}",
          lv
        );
        return None;
      }
      let lv_typ = lv_typ.unwrap();
      if lv_typ.is_null() {
        eprintln!("Deref cannot be applied on null");
        return None;
      }
      match lv_typ {
        ast::Typ::C0ptr(typ) => typ_to_ret(*typ),
        _ => {
          eprintln!(
            "Deref can only be applied on a pointer in expressions, error: {:?}",
            lv
          );
          return None;
        }
      }
    }
    Null => typ_to_ret(ast::Typ::C0ptr(Box::new(ast::Typ::C0struct(
      "NULL".to_string(),
    )))),
    Idx(arr, num) => {
      let arr_typ = tc_expr(ctx, &arr, progctx, fnctx);
      if arr_typ.is_none() {
        return None;
      }
      let arr_typ = arr_typ.unwrap();
      let arr_typ = ret_to_typ(arr_typ);
      if arr_typ.is_none() {
        eprintln!("Type error in expression: {:?}", arr);
        return None;
      }
      let arr_typ = arr_typ.unwrap();
      match arr_typ {
        ast::Typ::C0array(typ) => {
          let num_typ = tc_expr(ctx, &num, progctx, fnctx);
          if num_typ.is_none() {
            return None;
          }
          let num_typ = num_typ.unwrap();
          let num_typ = ret_to_typ(num_typ);
          if num_typ.is_none() {
            eprintln!("Type error in expression: {:?}", num);
            return None;
          }
          let num_typ = num_typ.unwrap();
          if num_typ != ast::Typ::Int {
            eprintln!("Index must be an integer, error: {:?}", num);
            return None;
          }
          return typ_to_ret(*typ);
        }
        _ => {
          eprintln!(
            "Idx can only be applied on an array in expressions, error: {:?}",
            arr
          );
          return None;
        }
      }
    }
    Alloc(typ) => match typ {
      ast::Typ::C0struct(name) => {
        let struct_typ = progctx.get_structDecl(&name);
        if struct_typ.is_none() || struct_typ.unwrap().is_defined() == false {
          eprintln!("Struct {} is not declared or declared not defined", name);
          return None;
        }
        typ_to_ret(ast::Typ::C0ptr(Box::new(typ.clone())))
      }
      _ => typ_to_ret(ast::Typ::C0ptr(Box::new(typ.clone()))),
    },
    AllocArr(typ, len) => {
      let len_typ = tc_expr(ctx, &len, progctx, fnctx);
      if len_typ.is_none() {
        return None;
      }
      let len_typ = len_typ.unwrap();
      let len_typ = ret_to_typ(len_typ);
      if len_typ.is_none() {
        eprintln!("Type error in expression: {:?}", len);
        return None;
      }
      let len_typ = len_typ.unwrap();
      if len_typ != ast::Typ::Int {
        eprintln!("Length of array must be an integer, error: {:?}", len);
        return None;
      }
      match typ {
        ast::Typ::C0struct(name) => {
          let struct_typ = progctx.get_structDecl(&name);
          if struct_typ.is_none() || struct_typ.unwrap().is_defined() == false {
            eprintln!(
              "Struct {} is not declared or declared not defined",
              name
            );
            return None;
          }
          typ_to_ret(ast::Typ::C0array(Box::new(typ.clone())))
        }
        _ => typ_to_ret(ast::Typ::C0array(Box::new(typ.clone()))),
      }
    }
    Arrow(..) => panic!("Arrow should have been desugared"),
  }
}

/// Type check a lvalue, return the type of the lvalue, or None if there is a type error
/// The lvalue is a variable, or a field of a struct
/// The lvalue is not an expression, so it cannot be a function call
/// Notice the lvalue here must to be defined, so we can have nested lvalue
fn tc_lvalue(
  ctx: &mut Context,
  lv_expr: &ElabLval,
  progctx: &ProgContext,
  fnctx: &ProgContext,
) -> Option<ast::RetTyp> {
  match *lv_expr {
    ElabLval::Var(ref var) => {
      if ctx.is_defined(var) {
        let resultType = ctx.get_type(var);
        if resultType.is_none() {
          eprintln!("Variable {} is not defined", var);
          return None;
        }
        typ_to_ret(ctx.get_type(var).unwrap())
      } else {
        eprintln!("Variable {} is not defined", var);
        None
      }
    }
    ElabLval::Dot(ref lv, ref field) => {
      let lv_typ = tc_lvalue(ctx, &lv, progctx, fnctx);
      if lv_typ.is_none() {
        return None;
      }
      let lv_typ = lv_typ.unwrap();
      let lv_typ = ret_to_typ(lv_typ);
      if lv_typ.is_none() {
        eprintln!("Type error in expression: {:?}", lv);
        return None;
      }
      let lv_typ = lv_typ.unwrap();
      match lv_typ {
        ast::Typ::C0struct(name) => {
          let struct_typ = progctx.get_structDecl(&name);
          if struct_typ.is_none() || struct_typ.unwrap().is_defined() == false {
            eprintln!(
              "Struct {} is not declared or declared not defined",
              name
            );
            return None;
          }
          let struct_typ = struct_typ.unwrap();
          let field_typ = struct_typ.get_field_typ(&field);
          if field_typ.is_none() {
            eprintln!("Struct {} does not have field {}", name, field);
            return None;
          }
          let field_typ = field_typ.unwrap();
          typ_to_ret(field_typ.clone())
        }
        _ => {
          eprintln!(
            "Dot can only be applied on a struct in expressions, error: {:?}",
            lv
          );
          None
        }
      }
    }
    ElabLval::Deref(ref lv) => {
      let lv_typ = tc_lvalue(ctx, &lv, progctx, fnctx);
      if lv_typ.is_none() {
        return None;
      }
      let lv_typ = lv_typ.unwrap();
      let lv_typ = ret_to_typ(lv_typ);
      if lv_typ.is_none() {
        eprintln!("Type error in expression: {:?}", lv);
        return None;
      }
      let lv_typ = lv_typ.unwrap();
      match lv_typ {
        ast::Typ::C0ptr(typ) => {
          if let ElabLval::Var(v) = lv.as_ref() {
            if !ctx.is_defined(&v) {
              eprintln!("Deref on undefined variable {}", v);
              return None;
            }
          }
          match *typ.clone() {
            ast::Typ::C0struct(name) => {
              if name == "NULL" {
                eprintln!("Deref on NULL pointer");
                return None;
              } else {
                typ_to_ret(*typ)
              }
            }
            _ => typ_to_ret(*typ),
          }
        }
        _ => {
          eprintln!(
            "Deref can only be applied on a pointer in expressions, error: {:?}",
            lv
          );
          return None;
        }
      }
    }
    ElabLval::Idx(ref arr, ref num) => {
      let arr_typ = tc_lvalue(ctx, &arr, progctx, fnctx);
      if arr_typ.is_none() {
        return None;
      }
      let arr_typ = arr_typ.unwrap();
      let arr_typ = ret_to_typ(arr_typ);
      if arr_typ.is_none() {
        eprintln!("Type error in expression: {:?}", arr);
        return None;
      }
      let arr_typ = arr_typ.unwrap();
      match arr_typ {
        ast::Typ::C0array(typ) => {
          let num_typ = tc_expr(ctx, &num, progctx, fnctx);
          if num_typ.is_none() {
            return None;
          }
          let num_typ = num_typ.unwrap();
          let num_typ = ret_to_typ(num_typ);
          if num_typ.is_none() {
            eprintln!("Type error in expression: {:?}", num);
            return None;
          }
          let num_typ = num_typ.unwrap();
          if num_typ != ast::Typ::Int {
            eprintln!("Index must be an integer, error: {:?}", num);
            return None;
          }
          return typ_to_ret(*typ);
        }
        _ => {
          eprintln!(
            "Idx can only be applied on an array in expressions, error: {:?}",
            arr
          );
          return None;
        }
      }
    }
  }
}

fn lvalue_get_var_name(lv_expr: &ElabLval) -> Option<String> {
  match &*lv_expr {
    ElabLval::Var(name) => Some(name.clone()),
    _ => None,
  }
}

/// Checks the validity of some pattern; declares and defines the variable
/// patterns along the way.
fn tc_patt(
  ctx: &mut Context,
  pat: &ast::Patt,
  progctx: &ProgContext,
  fnctx: &ProgContext,
) -> Result<Lax<ast::Typ>, String> {
  match pat {
    ast::Patt::Any | ast::Patt::Variable(_) => Ok(Lax::Any),
    ast::Patt::Variant(id, var, patts) => {
      match progctx.ev_typs(&id, &var) {
        Ok(assoc_typs) => {
          let mut rec_lax_typs = Vec::<Lax<ast::Typ>>::new();
          for p in patts {
            rec_lax_typs.push(tc_patt(ctx, p, progctx, fnctx)?);
          }

          // chk number of args match.
          let n = rec_lax_typs.len();
          if n != assoc_typs.len() {
            return Err(format!(
              "Failed to tc patt: {}\n  Needs {} expressions, found {}",
              pat,
              assoc_typs.len(),
              n,
            ));
          }

          for i in 0..n {
            let assoc_typ_i = assoc_typs[i].clone();

            // checks if the recursive patterns match their lax types.
            if Lax::Fixed(assoc_typ_i.clone()) != rec_lax_typs[i] {
              return Err(format!(
                "Patt `{}` needs to be of type `{}`",
                patts[i], assoc_typ_i,
              ));
            }

            // patterns of variant `variable` actually defines a variable.
            // note that reuse of variable in patterns are already checked
            // while parsing.
            if let ast::Patt::Variable(ref varname) = patts[i] {
              // such a variable must not be previously declared
              if ctx.is_declared(varname) {
                return Err(format!(
                  "Variable `{}` in pattern is already defined elsewhere",
                  varname
                ));
              }

              ctx.declare(varname.clone(), assoc_typ_i.clone());
              ctx.define(varname.clone(), assoc_typ_i.clone());
            }
          }

          Ok(Lax::Fixed(ast::Typ::C0enum(id.to_string())))
        }
        Err(s) => Err(s),
      }
    }
  }
}

/// Check the validity of a statement.
// In future labs, you will likely want to extend the context and the return
// type to contain much more useful information than this.
fn tc_stmt(
  ctx: &mut Context,
  stmt: &elab::ElabStmt,
  progctx: &ProgContext,
  fnctx: &ProgContext,
  should_ret: ast::RetTyp,
) -> TcStatus {
  let mut tc = TcStatus::new(should_ret.clone());
  match &*stmt {
    elab::ElabStmt::Match(e, v) => {
      let e_typ = match tc_expr(ctx, e, progctx, fnctx) {
        Some(RetTyp::T(t @ ast::Typ::C0enum(_))) => t,
        Some(rt) => {
          eprintln!("Expression {} of type {} cannot be matched on", e, rt);
          tc.set_tc(false);
          tc.set_ret(None);
          return tc;
        }
        None => {
          eprintln!("Cannot match on None-type {:?}", e);
          tc.set_tc(false);
          tc.set_ret(None);
          return tc;
        }
      };

      let mut match_check = Tuples::new(e_typ.clone());
      match_check.this_id = match &e_typ {
        ast::Typ::C0enum(id) => id.clone(),
        _ => unreachable!("tc_stmt: match: e_typ is not C0enum"),
      };

      for (p, s, stmt) in v {
        // obtain match expr lax typ and implicitly declares / defines vars.
        let p_lax = match tc_patt(ctx, p, progctx, fnctx) {
          Ok(p_lax) => p_lax,
          Err(e) => {
            eprintln!("{}", e);
            tc.set_tc(false);
            tc.set_ret(None);
            return tc;
          }
        };

        // verify match expr typ
        if Lax::Fixed(e_typ.clone()) != p_lax {
          eprintln!("Pattern `{}` is not of type `{}`", p, e_typ);
          tc.set_tc(false);
          tc.set_ret(None);
          return tc;
        }

        let tc_rec = tc_stmt(ctx, stmt, progctx, fnctx, should_ret.clone());
        tc.combine_tcStatus(&tc_rec);

        // remove the declared variables
        for v in s {
          ctx.undeclare(v.clone());
        }

        match_check.add(p, progctx);
      }
      if !match_check.check_matched() {
        eprintln!("Not all variants of {} are matched on", e_typ);
        tc.set_tc(false);
        tc.set_ret(None);
        return tc;
      }

      tc
    }
    elab::ElabStmt::Declare(ref var, ref typ, s, init) => {
      let declareTyp = match typ {
        ast::Typ::C0struct(_) => {
          eprintln!("Struct {} cannot declared on stack", var);
          tc.set_tc(false);
          return tc;
        }
        _ => typ_to_ret(typ.clone()).unwrap(), // TODO: handle None (typedef)
      };
      if (!ctx.is_declared(var)
        && !progctx.is_typedefed(ast::TypName(var.clone())))
      {
        // defn name valid
        if *init {
          if DEBUG {
            println!("Declare and init: {} {:?}", var, declareTyp);
          }
          // this case is int f = something;
          let init_expr = match &**s {
            elab::ElabStmt::Seq(assn, _) => match &**assn {
              elab::ElabStmt::Assign(lv, expr) => Some(expr.clone()),
              _ => None,
            },
            _ => {
              eprintln!(
                "Declare and init: {} {:?} but no assign",
                var, declareTyp
              );
              tc.set_tc(false);
              return tc;
            }
          };
          if init_expr.is_some() {
            let is_null = match init_expr.unwrap() {
              ast::Expr::Null => true,
              _ => false,
            };
            if is_null {
              // this case is int f = NULL;
              if DEBUG {
                println!(
                  "Declare and init with NULL: {} {:?}",
                  var, declareTyp
                );
              }
              // we need to check if the type is a pointer
              let typ_check = match typ {
                ast::Typ::C0ptr(_) => true,
                _ => false,
              };
              if !typ_check {
                eprintln!("Cannot assign NULL to non-pointer type");
                tc.set_tc(false);
                return tc;
              }
              // this case is **int f = NULL;
              // we need to check if the type is a pointer
              if progctx.is_fnDecl(ast::FnName(var.clone())) {
                let mut new_progctx = progctx.clone();
                new_progctx.remove_fn(ast::FnName(var.clone()));
                let mut new_ctx = ctx.clone();
                new_ctx.declare(var.clone(), typ.clone());
                let tc_s = tc_stmt(
                  &mut new_ctx,
                  &s,
                  &new_progctx,
                  fnctx,
                  should_ret.clone(),
                );
                tc.combine_tcStatus(&tc_s);

                ctx.copy_back(new_ctx);
                return tc;
              }
              let typ_check = match typ {
                ast::Typ::C0ptr(_) => true,
                _ => false,
              };
              if !typ_check {
                eprintln!("Cannot assign NULL to non-pointer type");
                tc.set_tc(false);
                return tc;
              }
              ctx.declare(var.clone(), typ.clone());
              if DEBUG {
                eprintln!("Declare: {} as {:?}", var, typ);
              }
              let tc_s = tc_stmt(ctx, &s, progctx, fnctx, should_ret.clone());
              tc.combine_tcStatus(&tc_s);
              ctx.undeclare(var.clone());
              // ctx.copy_back(new_ctx);
              return tc;
            }
          }

          let mut new_ctx = ctx.clone();

          match &**s {
            elab::ElabStmt::Seq(stmt1, stmt2) => {
              new_ctx.declare(var.clone(), typ.clone());
              if DEBUG {
                eprintln!(
                  "Declare: {} as {:?}, next stmt is {}",
                  var, typ, stmt1
                );
              }
              tc.combine_tcStatus(&tc_stmt(
                &mut new_ctx,
                &stmt1,
                progctx,
                fnctx,
                should_ret.clone(),
              ));
              // new_ctx.define(var.clone(), typ.clone());
              let mut new_progctx = progctx.clone();
              new_progctx.remove_fn(ast::FnName(var.clone()));
              tc.combine_tcStatus(&tc_stmt(
                &mut new_ctx,
                &stmt2,
                &new_progctx,
                fnctx,
                should_ret.clone(),
              ));
              ctx.copy_back(new_ctx);
              return tc;
            }
            _ => {
              eprintln!("Invalid declaration of variable {}", var);
              tc.set_tc(false);
              tc.set_ret(None);
              return tc;
            }
          }
        } else {
          if progctx.is_fnDecl(ast::FnName(var.clone())) {
            let mut new_progctx = progctx.clone();
            new_progctx.remove_fn(ast::FnName(var.clone()));
            let mut new_ctx = ctx.clone();
            new_ctx.declare(var.clone(), typ.clone());
            let tc_s = tc_stmt(
              &mut new_ctx,
              &s,
              &new_progctx,
              fnctx,
              should_ret.clone(),
            );
            tc.combine_tcStatus(&tc_s);

            ctx.copy_back(new_ctx);
            return tc;
          }

          ctx.declare(var.clone(), typ.clone());
          if DEBUG {
            eprintln!("Declare: {} as {:?}", var, typ);
          }
          let tc_s = tc_stmt(ctx, &s, progctx, fnctx, should_ret.clone());
          tc.combine_tcStatus(&tc_s);
          ctx.undeclare(var.clone());
          // ctx.copy_back(new_ctx);
          return tc;
        }
      } else {
        eprintln!("Variable {} already declared in stmt {:?}", var, stmt);
        tc.set_tc(false);
        tc.set_ret(None);
        return tc;
      }
    }

    elab::ElabStmt::Assign(ref var, expr) => {
      let var_name = lvalue_get_var_name(var);
      // the case of lvalue is a variable only
      if var_name.is_some() {
        let var_name = var_name.unwrap();
        if ctx.is_declared(&var_name) {
          let var_type = ctx.get_type(&var_name);
          let expr_type = tc_expr(ctx, &expr, progctx, fnctx);

          if expr_type.is_none() || var_type.is_none() {
            eprintln!("Type error in expression: {:?}", expr);
            tc.set_tc(false);
            tc.set_ret(None);
            return tc;
          }

          if expr_type.is_some()
            && expr_type == typ_to_ret(var_type.clone().unwrap())
          {
            if DEBUG {
              eprintln!("Assign: {} as {:?}", var_name, expr_type);
            }
            if var_type.clone().unwrap().is_struct() {
              eprintln!("Cannot assign to struct in stmt {:?}", stmt);
            }

            tc.set_tc(true);
            ctx.define(var_name.clone(), var_type.unwrap());
            return tc;
          } else {
            eprintln!("Type mismatch in stmt {:?}", stmt);
            tc.set_tc(false);
            tc.set_ret(None);
            return tc;
          }
        } else {
          eprintln!("Variable {} not defined in stmt {:?}", &var_name, stmt);
          if DEBUG {
            eprintln!("Context: {:?}", ctx);
          }
          tc.set_tc(false);
          tc.set_ret(None);
          return tc;
        }
      }

      // Otherwise, do the type checking for lvalue
      // lvalue must have all vars be defined in this case
      let var_type = tc_lvalue(ctx, var, progctx, fnctx);
      let expr_type = tc_expr(ctx, &expr, progctx, fnctx);
      if expr_type.is_none() || var_type.is_none() {
        eprintln!("Type error in stmt: {}", stmt);
        tc.set_tc(false);
        tc.set_ret(None);
        return tc;
      }
      if expr_type.is_some() && expr_type == var_type {
        let var_typ = ret_to_typ(var_type.clone().unwrap());
        if var_typ.clone().unwrap().is_struct() {
          eprintln!("Cannot assign to struct in stmt {:?}!", stmt);
          tc.set_tc(false);
          tc.set_ret(None);
          return tc;
        }
        tc.set_tc(true);
        tc.set_ret(None);
        return tc;
      } else {
        eprintln!(
          "Type mismatch in stmt {:?}, where lvalue has type {:?} and expr has type {:?}",
          stmt, var_type, expr_type
        );
        tc.set_tc(false);
        tc.set_ret(None);
        return tc;
      }
    }
    elab::ElabStmt::If(expr, s1, s2) => {
      let expr_type = tc_expr(ctx, &expr, progctx, fnctx);
      if expr_type == typ_to_ret(ast::Typ::Bool) {
        tc.set_tc(true);
      } else {
        eprintln!("Type mismatch in if stmt {:?}", stmt);
        tc.set_tc(false);
        tc.set_ret(None);
        return tc;
      }
      let mut left_ctx = ctx.clone();
      let mut right_ctx = ctx.clone();

      let tc_left =
        tc_stmt(&mut left_ctx, &s1, progctx, fnctx, should_ret.clone());

      if tc_left.get_tc() == false {
        eprintln!("Invalid statement: {:?}", stmt);
        tc.set_tc(false);
        tc.set_ret(None);
      }

      let tc_right =
        tc_stmt(&mut right_ctx, &s2, progctx, fnctx, should_ret.clone());
      if tc_right.get_tc() == false {
        eprintln!("Invalid statement: {:?}", stmt);
        tc.set_tc(false);
        tc.set_ret(None);
      }

      ctx.copy_back_if(left_ctx, right_ctx);
      let ret_left = tc_left.get_ret();
      let ret_right = tc_right.get_ret();
      if ret_left.is_some() && ret_right.is_some() {
        if ret_left == ret_right {
          tc.set_ret(ret_left);
        } else {
          eprintln!("Return Type mismatch in if stmt {:?}", stmt);
          tc.set_tc(false);
          tc.set_ret(None);
          return tc;
        }
      } else {
        tc.set_ret(None);
      }
      tc.set_tc(tc_left.get_tc() && tc_right.get_tc());
      return tc;
    }
    elab::ElabStmt::While(expr, s) => {
      let expr_type = tc_expr(ctx, &expr, progctx, fnctx);
      if expr_type == typ_to_ret(ast::Typ::Bool) {
        tc.set_tc(true);
      } else {
        eprintln!("Type mismatch in while stmt {:?}", stmt);
        tc.set_tc(false);
        tc.set_ret(None);
        return tc;
      }
      let tc_block =
        tc_stmt(&mut ctx.clone(), &s, progctx, fnctx, should_ret.clone());
      if tc_block.get_tc() == false {
        eprintln!("Invalid statement: {:?}", stmt);
        tc.set_tc(false);
        tc.set_ret(None);
        return tc;
      }
      tc.ret = None;
      tc.set_tc(tc_block.get_tc());
      return tc;
    }
    elab::ElabStmt::Ret(Some(expr)) => {
      if should_ret == ast::RetTyp::Void {
        eprintln!(
          "Type mismatch in stmt {:?}, returned Void, should be {}",
          stmt, should_ret
        );
        tc.set_tc(false);
        tc.set_ret(None);
        return tc;
      }
      let expr_type = tc_expr(ctx, &expr, progctx, fnctx);
      if DEBUG {
        eprintln!("Ret: {:?}", expr);
      }
      if expr_type.is_some() && should_ret == expr_type.clone().unwrap() {
        tc.set_tc(true);
        ctx.define_all();
      } else {
        eprintln!(
          "Type mismatch in stmt {:?}, returned {:?}, should be {}",
          stmt, expr_type, should_ret
        );
        tc.set_tc(false);
        tc.set_ret(None);
        return tc;
      }
      tc.ret = expr_type;

      return tc;
    }
    elab::ElabStmt::Ret(None) => {
      tc.set_tc(true);
      ctx.define_all();
      if should_ret != ast::RetTyp::Void {
        eprintln!("Type mismatch in stmt {:?}", stmt);
        tc.set_tc(false);
        tc.set_ret(None);
        return tc;
      }
      tc.ret = Some(ast::RetTyp::Void);
      return tc;
    }
    elab::ElabStmt::Seq(stmt1, stmt2) => {
      tc.combine_tcStatus(&tc_stmt(
        ctx,
        &stmt1,
        progctx,
        fnctx,
        should_ret.clone(),
      ));
      if tc.get_tc() == false {
        return tc;
      }
      tc.combine_tcStatus(&tc_stmt(
        ctx,
        &stmt2,
        progctx,
        fnctx,
        should_ret.clone(),
      ));

      return tc;
    }
    elab::ElabStmt::Nop => {
      tc.set_tc(true);
      return tc;
    }
    elab::ElabStmt::Eval(expr) => {
      let expr_type = tc_expr(ctx, &expr, progctx, fnctx);
      if expr_type.is_some() {
        let expr_type = expr_type.unwrap();
        let expr_type = ret_to_typ(expr_type);
        if expr_type.is_some() {
          let expr_type = expr_type.unwrap();
          if expr_type.is_struct() {
            eprintln!(
              "expression used as statements cannot have type struct: {:?}",
              stmt
            );
            tc.set_tc(false);
            tc.set_ret(None);
            return tc;
          }
          tc.set_tc(true);
          return tc;
        }
      } else {
        eprintln!("Type mismatch in stmt {:?}", stmt);
        tc.set_tc(false);
        tc.set_ret(None);
        return tc;
      }
      return tc;
    }
    elab::ElabStmt::AssignEq(ref var, op, expr) => {
      let expr_type = tc_expr(ctx, &expr, progctx, fnctx);
      let var_type = tc_lvalue(ctx, &var, progctx, fnctx);
      if expr_type.is_some() && var_type.is_some() && expr_type == var_type {
        if expr_type.unwrap() == ast::RetTyp::T(ast::Typ::Int) {
          tc.set_tc(true);
          return tc;
        } else {
          eprintln!("Type mismatch in stmt {:?}", stmt);
          tc.set_tc(false);
          tc.set_ret(None);
          return tc;
        }
      } else {
        eprintln!("Type mismatch in stmt {:?}", stmt);
        tc.set_tc(false);
        tc.set_ret(None);
        return tc;
      }
    }
  }
}

/// Typecheck some elaborated statement!
pub fn valid_function_body(
  stmt: &elab::ElabStmt,
  progctx: &ProgContext,
  fnctx: &ProgContext,
  ret: ast::RetTyp,
  params: &ast::ParamList,
) -> bool {
  let mut ctx = Context::new();
  let mut tc = TcStatus::new(ret.clone());
  if params.0.len() == 1 {
    let param = &params.0[0];
    let fn_input_name = param.1.clone();
    if !progctx.is_fnDecl(ast::FnName(fn_input_name.clone())) {
      if progctx.is_typedefed(ast::TypName(fn_input_name.clone())) {
        eprintln!("Type name {} already defined", fn_input_name);
        return false;
      }

      if ctx.is_declared(&fn_input_name) {
        eprintln!(
          "{} in function is already defined as a variable",
          fn_input_name
        );
        return false;
      }
      let param_typ_ck = match param.0 {
        ast::Typ::C0struct(_) => {
          eprintln!(
            "Invalid type struct for parameter of function {}",
            fn_input_name
          );
          return false;
        }
        _ => (),
      };

      ctx.define(param.1.clone(), param.0.clone());
      let res = tc_stmt(&mut ctx, &stmt, progctx, fnctx, ret.clone());
      if res.get_tc() == false {
        return false;
      }
      if res.get_ret().is_none() {
        return false;
      }
      return ret == res.get_ret().unwrap();
    }
  }
  let mut new_pgctx = progctx.clone();
  for param in params.0.iter() {
    let fn_input_name = param.1.clone();
    if progctx.is_fnDecl(ast::FnName(fn_input_name.clone())) {
      new_pgctx.remove_fn(ast::FnName(fn_input_name.clone()));
    }

    if progctx.is_typedefed(ast::TypName(fn_input_name.clone())) {
      eprintln!("Type name {} already defined", fn_input_name);
      return false;
    }

    if ctx.is_declared(&fn_input_name) {
      eprintln!(
        "{} in function is already defined as a variable",
        fn_input_name
      );
      return false;
    }

    let param_typ_ck = match param.0 {
      ast::Typ::C0struct(_) => {
        eprintln!(
          "Invalid type struct for parameter of function {}",
          fn_input_name
        );
        return false;
      }
      _ => (),
    };

    ctx.define(param.1.clone(), param.0.clone());
  }

  let res = tc_stmt(&mut ctx, &stmt, &new_pgctx, fnctx, ret.clone());
  if res.get_tc() == false {
    return false;
  }
  if res.get_ret().is_none() {
    eprintln!("No return statement in function");
    return false;
  }
  ret == res.get_ret().unwrap()
}
