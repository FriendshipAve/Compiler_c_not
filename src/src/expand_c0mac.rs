//! Expands the C0 macro for structs and / or enums. 
use crate::ast::{*, self};

/// Composes a function name with its specialized type. 
fn mk_fname(t : Typ, fname: &str) -> String {
  assert!(t.is_not_custom(), "Cannot make specialized function for custom typ");
  format!("_spec_{}_{}", t, fname)
}

/// Composes a clone function with its specialized type. 
fn mk_clone(t: Typ) -> String {
  mk_fname(t, &"clone")
}

/// Given an expression and a type hint, returns an expression that generates 
/// its duplicate, be it copy or clone.
fn dup_expr(e: Expr, t : Typ) -> Expr {
  match t {
    Typ::Bool | Typ::Int => e.clone(),
    Typ::C0ptr(t) => Expr::FnCall(FnName(mk_clone(*t)), ArgList(vec![e])),
    Typ::C0array(..) => todo!("Cannot clone arr yet"),
    Typ::C0struct(..) | Typ::C0enum(..) => todo!("Cannot clone large typs yet"),
    Typ::Custom(..) => unimplemented!("Shall not handle custom"),
  }
}

/// Expands a c0 struct clone function.
pub fn struct_clone(old_s: String, fields: Vec<Field>) -> Glob {
  let st = Typ::C0struct(old_s.clone());
  let st_ptr = Typ::C0ptr(Box::new(st.clone()));

  let new_s = "new_s".to_string();

  let mut fn_body = vec![
    Stmt::Simp(Simp::Defn(
      st_ptr.clone(), 
      new_s.clone(), 
      Expr::Alloc(st_ptr.clone())
    ))
  ];

  for field in fields {
    let Field(t, field_name) = field;

    let old_arrow_field = dup_expr(
      Expr::Arrow(
        Box::new(Expr::Variable(old_s.clone())), 
        field_name.clone()
      ), 
      t
    );

    let new_arrow_field = Lval::Arrow(
      Box::new(Lval::Var(new_s.clone())), 
      field_name.clone()
    );

    fn_body.push(Stmt::Simp(Simp::Asgn(
      new_arrow_field,
      None, 
      old_arrow_field,
    )))
  }

  fn_body.push(Stmt::Ret(Some(Expr::Variable(new_s))));

  Glob::FnDefn(
    RetTyp::T(st.clone()),
    FnName(mk_fname(st.clone(), &"clone")), 
    ParamList(vec![Param(st_ptr.clone(), "x".to_string())]),
    Stmt::Block(fn_body)
  )
}
