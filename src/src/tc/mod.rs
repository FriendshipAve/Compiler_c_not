pub mod matching;
pub mod tc_function;
pub mod tc_info;
pub mod exhaust;

use crate::ast;
use crate::ast::Field;
use crate::ast::Typ;
use crate::ast::Variant;
use crate::elab;

// use crate::util::c0spec::DEBUG;
const DEBUG: bool = false;
use std::collections::HashMap;
use std::collections::HashSet;
use std::option::Option;

// context of a functon: whether it is defined, its arg types and return type
#[derive(Clone, Debug)]
pub struct FnDecl {
  pub retTyp: ast::RetTyp,
  pub params: ast::ParamList,
  pub defined: bool,
}

impl FnDecl {
  pub fn new(retTyp: ast::RetTyp, params: ast::ParamList) -> Self {
    Self {
      retTyp,
      params,
      defined: false,
    }
  }

  pub fn new_defined(retTyp: ast::RetTyp, params: ast::ParamList) -> Self {
    Self {
      retTyp,
      params,
      defined: true,
    }
  }

  pub fn is_defined(&self) -> bool {
    self.defined
  }
  pub fn matchDecl(&self, other: &FnDecl) -> bool {
    self.retTyp == other.retTyp && self.params == other.params
  }
}
impl std::fmt::Display for FnDecl {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    write!(f, "({}) -> {}", self.params, self.retTyp)
  }
}
/// Maybe need to convert to a hashmap, but not sure yet
#[derive(Clone, Debug)]
pub struct StructDecl {
  pub name: ast::TypName,
  pub fields: Vec<ast::Field>,
  pub defined: bool,
}

impl StructDecl {
  pub fn new(name: ast::TypName) -> Self {
    Self {
      name,
      fields: Vec::new(),
      defined: false,
    }
  }

  pub fn new_defined(name: ast::TypName, fields: Vec<ast::Field>) -> Self {
    Self {
      name,
      fields,
      defined: true,
    }
  }

  pub fn is_defined(&self) -> bool {
    self.defined
  }

  pub fn get_field_typ(&self, field_name: &str) -> Option<&ast::Typ> {
    for field in self.fields.iter() {
      if field.1 == field_name {
        return Some(&field.0);
      }
    }
    None
  }
}

impl std::fmt::Display for StructDecl {
  fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
    if self.defined {
      write!(f, "struct {} {{", self.name.0)?;
      for field in self.fields.iter() {
        write!(f, "{}", field)?;
      }
      write!(f, "}}")
    } else {
      write!(f, "struct {} (undefined)", self.name.0)
    }
  }
}
// the program context: all the function declarations and typedefs
#[derive(Debug, Clone)]
pub struct ProgContext {
  pub fnDecls: HashMap<String, FnDecl>,
  pub typedefs: HashMap<String, ast::Typ>,
  pub structDefs: HashMap<String, StructDecl>,
  pub enumDefs: HashMap<String, HashMap<String, Vec<ast::Typ>>>,
  pub enum_tags: HashMap<String, HashMap<String, usize>>,
}
impl ProgContext {
  pub fn new() -> Self {
    Self {
      fnDecls: {
        let mut m = HashMap::new();
        m.insert(
          "main".to_string(),
          FnDecl::new(ast::RetTyp::T(ast::Typ::Int), ast::ParamList::new()),
        );
        m
      },
      typedefs: HashMap::new(),
      structDefs: HashMap::new(),
      enumDefs: HashMap::new(),
      enum_tags: HashMap::new(),
    }
  }

  /// Checks whether a (non-custom) type is already defined.
  pub fn already_defined_type(&self, t: &Typ) -> bool {
    match t {
      Typ::Bool | Typ::Int => true,
      Typ::C0array(t) | Typ::C0ptr(t) => self.already_defined_type(t),
      Typ::Custom(_) => unreachable!(),
      Typ::C0struct(name) => self.structDefs.contains_key(name),
      Typ::C0enum(name) => self.enumDefs.contains_key(name),
    }
  }

  // add a typedef to the context
  pub fn add_typedef(&mut self, id: ast::TypName, t: ast::Typ) -> bool {
    if self.typedefs.contains_key(&id.0) || self.fnDecls.contains_key(&id.0) {
      eprintln!(
        "Cannot redefine type `{}` as `{}` because it is already defined",
        id.0, t
      );
      return false;
    }
    self.typedefs.insert(id.0, t);
    true
  }

  pub fn add_typedef_unsafe(&mut self, id: ast::TypName, t: ast::Typ) {
    self.typedefs.insert(id.0, t);
  }

  pub fn add_StructDecl(&mut self, id: ast::TypName) -> bool {
    // if self.typedefs.contains_key(&id.0) || self.fnDecls.contains_key(&id.0) {
    //   eprintln!(
    //     "Cannot redefine type `{}` as `struct {}` because it is already defined",
    //     id.0, id.0
    //   );
    //   return false;
    // }
    if self.structDefs.contains_key(&id.0) {
      // already declared
      return true;
    }
    self
      .structDefs
      .insert(id.0.clone(), StructDecl::new(id.clone()));
    true
  }

  /// Given the identifier and variants of some `c0enum`, adds it to the
  /// program context.
  pub fn add_enum(&mut self, id: String, variants: Vec<Variant>) -> Option<()> {
    // chk if enum defined
    if self.enumDefs.contains_key(&id) {
      eprintln!("Enum `{}` already defined! ", id);
      return None;
    }

    // chk if variants repeat
    let mut defined_variants = HashSet::<String>::new();
    for Variant(s, _) in &variants {
      if defined_variants.contains(s) {
        eprintln!("Enum `{}` has variant `{}` defined twice! ", id, s);
        return None;
      }
      defined_variants.insert(s.clone());
    }

    let mut variant_args_map = HashMap::<String, Vec<ast::Typ>>::new();
    let mut variant_tag_map = HashMap::<String, usize>::new();
    let mut running_vartag: usize = 0;
    for Variant(vid, args) in variants {
      // enum variants only accept small type.
      for t in &args {
        if t.is_struct() {
          eprintln!("{}::{} can only contain small type! ", id, vid);
          return None;
        }
      }
      variant_args_map.insert(vid.clone(), args);

      variant_tag_map.insert(vid, running_vartag);
      running_vartag += 1;
    }
    self.enumDefs.insert(id.clone(), variant_args_map);
    self.enum_tags.insert(id, variant_tag_map);
    Some(())
  }

  /// Given some enum and variant, retrieves a slice of types.
  pub fn ev_typs(&self, id: &str, var: &str) -> Result<&[ast::Typ], String> {
    match self.enumDefs.get(id) {
      Some(mp) => match mp.get(var) {
        Some(l) => Ok(l),
        None => Err(format!("enum `{}` has no variant `{}`", id, var)),
      },
      None => Err(format!("enum `{}` undefined! ", id)),
    }
  }

  /// given enum, retrieves all types.
  pub fn ev_all_tags(&self, id: &str) -> Vec<(&String, &Vec<Typ>)> {
    match self.enumDefs.get(id) {
      Some(mp) => {
        let mut res = Vec::new();
        for i in mp {
          res.push(i);
        }
        res
      }
      None => unreachable!("enum `{:?}` undefined! ", id),
    }
  }

  pub fn struct_declared(&self, id: &String) -> bool {
    self.structDefs.contains_key(id)
  }

  pub fn struct_defined(&self, id: &String) -> bool {
    if let Some(structDecl) = self.structDefs.get(id) {
      return structDecl.defined;
    }
    false
  }

  pub fn struct_has_field(&self, id: &String, field_name: &str) -> bool {
    if let Some(structDecl) = self.structDefs.get(id) {
      for field in structDecl.fields.iter() {
        if field.1 == field_name {
          return true;
        }
      }
    }
    false
  }

  pub fn add_StructDefn(
    &mut self,
    id: ast::TypName,
    fields: Vec<ast::Field>,
  ) -> bool {
    let oldDecl = self.structDefs.get(&id.0);
    if oldDecl.is_some() && oldDecl.unwrap().is_defined() {
      eprintln!(
        "Cannot redefine struct `{}` as `{:?}` because it is already defined",
        id.0, fields
      );
      return false;
    }
    let mut field_names: HashSet<String> = HashSet::new();
    for field in fields.iter() {
      let field_typ = &field.0;
      let field_name = &field.1;
      if field_names.contains(field_name) {
        eprintln!(
          "Cannot define struct `{}` as `{:?}` because `{}` is already defined",
          id.0, fields, field_name
        );
        return false;
      }
      field_names.insert(field_name.clone());

      if field_typ.is_struct()
        && !self.struct_defined(&field_typ.get_struct_name().unwrap())
      {
        eprintln!(
          "Cannot define struct `{}` as `{:?}` because field `{}` is not defined",
          id.0,
          fields,
          &field_typ.get_struct_name().unwrap()
        );
        return false;
      }
    }
    self
      .structDefs
      .insert(id.0.clone(), StructDecl::new_defined(id.clone(), fields));
    true
  }

  pub fn get_structDecl(&self, id: &String) -> Option<&StructDecl> {
    self.structDefs.get(id)
  }

  pub fn add_fnDecl(
    &mut self,
    id: ast::FnName,
    t: ast::RetTyp,
    params: ast::ParamList,
  ) -> bool {
    let ret_struct = match &t {
      ast::RetTyp::T(typ) => typ.is_struct(),
      ast::RetTyp::Void => false,
    };
    if ret_struct {
      eprintln!(
        "Cannot declare function `{}` as `{}` because return type cannot be a struct",
        id.0, t
      );
      return false;
    }
    let newfnDecl = FnDecl::new(t, params.clone());
    if self.fnDecls.contains_key(&id.0) {
      let oldDecl = self.fnDecls.get(&id.0).unwrap();
      if !oldDecl.matchDecl(&newfnDecl) {
        eprintln!(
          "Cannot redeclare function `{}` as `{}` because it signature doesn't match with {}",
          id.0, newfnDecl, oldDecl
        );
        return false;
      }
      return true;
    }
    if self.is_typedefed(ast::TypName(id.0.clone())) {
      eprintln!(
        "Cannot redeclare type `{}` as function `{}` because it is already defined as type",
        id.0, newfnDecl
      );
      return false;
    }
    let mut paramSet = HashSet::new();
    for param in params.0.clone() {
      if paramSet.contains(&param.1) {
        eprintln!(
          "Cannot redeclare function `{}` as `{}` because it has duplicate parameter `{}`",
          id.0, newfnDecl, param.1
        );
        return false;
      }
      paramSet.insert(param.1);
    }
    for param in params.0 {
      if self.is_typedefed(ast::TypName(param.1.clone())) {
        eprintln!(
          "Cannot accept param name `{}` in function `{}` because it is already defined as type",
          param.1.clone(),
          newfnDecl
        );
        return false;
      }
    }

    self.fnDecls.insert(id.0, newfnDecl);
    true
  }

  pub fn add_fnDecl_unsafe(
    &mut self,
    id: ast::FnName,
    t: ast::RetTyp,
    params: ast::ParamList,
  ) {
    let newfn_Decl = FnDecl::new(t, params.clone());
    if !self.fnDecls.contains_key(&id.0) {
      self.fnDecls.insert(id.0, newfn_Decl);
      return;
    }
  }

  pub fn add_headDecl(
    &mut self,
    id: ast::FnName,
    t: ast::RetTyp,
    params: ast::ParamList,
  ) -> bool {
    let ret_struct = match &t {
      ast::RetTyp::T(typ) => typ.is_struct(),
      ast::RetTyp::Void => false,
    };
    if ret_struct {
      eprintln!(
        "Cannot declare function `{}` as `{}` because return type cannot be a struct",
        id.0, t
      );
      return false;
    }
    let newfnDecl = FnDecl::new_defined(t, params.clone());
    if self.fnDecls.contains_key(&id.0) {
      let oldDecl = self.fnDecls.get(&id.0).unwrap();
      if !oldDecl.matchDecl(&newfnDecl) {
        eprintln!("Cannot redeclare function in header `{}` as `{}` because it signature doesn't match with {}", id.0, newfnDecl, oldDecl);
        return false;
      }
    }
    if self.is_typedefed(ast::TypName(id.0.clone())) {
      eprintln!("Cannot redeclare type `{}` as function `{}` in header because it is already defined as type", id.0, newfnDecl);
      return false;
    }
    let mut paramSet = HashSet::new();
    for param in params.0.clone() {
      if paramSet.contains(&param.1) {
        eprintln!("Cannot redeclare function `{}` as `{}` in header because it has duplicate parameter `{}`", id.0, newfnDecl, param.1);
        return false;
      }
      paramSet.insert(param.1);
    }
    for param in params.0 {
      if self.is_typedefed(ast::TypName(param.1.clone())) {
        eprintln!("Cannot accept param name `{}` in function `{}` in header because it is already defined as type", param.1, newfnDecl);
        return false;
      }
    }

    self.fnDecls.insert(id.0, newfnDecl);
    true
  }

  pub fn add_headDecl_unsafe(
    &mut self,
    id: ast::FnName,
    t: ast::RetTyp,
    params: ast::ParamList,
  ) {
    let newfnDecl = FnDecl::new_defined(t, params.clone());
    self.fnDecls.insert(id.0, newfnDecl);
  }

  pub fn add_fnDefn(
    &mut self,
    id: ast::FnName,
    t: ast::RetTyp,
    params: ast::ParamList,
    functionCtx: &ProgContext,
    stmt: &elab::ElabStmt,
  ) -> bool {
    let newfnDecl = FnDecl::new_defined(t.clone(), params.clone());
    if self.fnDecls.contains_key(&id.0) {
      let oldDecl = self.fnDecls.get(&id.0).unwrap();
      if oldDecl.is_defined() {
        eprintln!(
          "Cannot redefine function `{}` as `{}` because it is already defined",
          id.0, newfnDecl
        );
        return false;
      }
      if !oldDecl.matchDecl(&newfnDecl) {
        eprintln!(
          "Cannot define function `{}` as `{}` because it signature doesn't match with {}",
          id.0, newfnDecl, oldDecl
        );
        return false;
      }
      self.fnDecls.remove(&id.0);
    }
    if self.is_typedefed(ast::TypName(id.0.clone())) {
      return false;
    }

    self.fnDecls.insert(id.0.clone(), newfnDecl.clone());
    if !tc_function::valid_function_body(
      stmt,
      self,
      functionCtx,
      t.clone(),
      &params,
    ) {
      return false;
    }

    self.fnDecls.insert(id.0, newfnDecl);
    true
  }

  pub fn is_typedefed(&self, id: ast::TypName) -> bool {
    self.typedefs.contains_key(&id.0)
  }

  pub fn is_fnDecl(&self, id: ast::FnName) -> bool {
    self.fnDecls.contains_key(&id.0)
  }

  pub fn is_fnDefn(&self, id: ast::FnName) -> bool {
    if self.fnDecls.contains_key(&id.0) {
      let fnDecl = self.fnDecls.get(&id.0).unwrap();
      fnDecl.is_defined()
    } else {
      false
    }
  }

  pub fn get_fnDecl(&self, id: ast::FnName) -> Option<&FnDecl> {
    self.fnDecls.get(&id.0)
  }

  pub fn remove_fn(&mut self, id: ast::FnName) {
    self.fnDecls.remove(&id.0);
  }
}

pub fn valid_functions(prgm: &elab::ElabProgram) -> Option<ProgContext> {
  let mut context = ProgContext::new();
  for elab_glob in &prgm.0 {
    match elab_glob {
      elab::ElabGlob::EDefn(id, variants) => {
        context.add_enum(id.clone(), variants.clone())?;
      }
      elab::ElabGlob::TypDef(t, id) => {
        if !context.add_typedef(id.clone(), t.clone()) {
          return None;
        }
      }
      elab::ElabGlob::FnDecl(id, t, params) => {
        if !context.add_fnDecl(t.clone(), id.clone(), params.clone()) {
          return None;
        }
      }
      elab::ElabGlob::FnDefn(t, id, params, stmts) => {
        if !context.add_headDecl(id.clone(), t.clone(), params.clone()) {
          return None;
        }
      }
      elab::ElabGlob::HeadDecl(t, id, params) => {
        if id.0 == "main" {
          if !context.add_fnDecl(id.clone(), t.clone(), params.clone()) {
            return None;
          }
        } else if !context.add_headDecl(id.clone(), t.clone(), params.clone()) {
          return None;
        }
      }
      elab::ElabGlob::SDecl(id) => {
        if !context.add_StructDecl(id.clone()) {
          return None;
        }
      }
      elab::ElabGlob::SDefn(id, fields) => {
        if !context.add_StructDefn(id.clone(), fields.0.clone()) {
          return None;
        }
      }
    }
  }
  if context.fnDecls.contains_key("main") {
    let main_decl = context.fnDecls.get("main").unwrap();
    if main_decl.is_defined() {
      let main_params = main_decl.params.0.clone();
      if main_params.len() != 0 {
        eprintln!("Main function cannot have parameters");
        return None;
      }
      if main_decl.retTyp != ast::RetTyp::T(ast::Typ::Int) {
        eprintln!("Main function must return int");
        return None;
      }
    } else {
      eprintln!("No main function defined");
      return None;
    }
  } else {
    eprintln!("No main function defined");
    return None;
  }
  if DEBUG {
    eprintln!("Valid functions");
  }
  Some(context)
}

/// Typecheck an entire program!
/// We do one pass for checking the program is well-formed, and then
/// another pass for typechecking each function.
pub fn valid_elabbed_program(
  prgm: &elab::ElabProgram,
) -> (bool, Option<ProgContext>) {
  let mut fnContext = {
    match valid_functions(prgm) {
      Some(c) => c,
      None => return (false, None),
    }
  };

  // checks if all enums and structs contains only defined types.
  for (eid, mp) in &fnContext.enumDefs {
    for (vid, typs) in mp {
      for t in typs {
        if !fnContext.already_defined_type(t) {
          eprintln!("Type `{}` in enum `{}` is undefined", t, eid);
          return (false, None);
        }
      }
    }
  }
  for (sid, mp) in &fnContext.structDefs {
    for Field(t, _) in &mp.fields {
      if !fnContext.already_defined_type(t) {
        eprintln!("Type `{}` in struct `{}` is undefined", t, sid);
        return (false, None);
      }
    }
  }

  let mut context = ProgContext::new();
  if DEBUG {
    eprintln!("doing second pass...");
  }

  for elab_glob in &prgm.0 {
    match elab_glob {
      elab::ElabGlob::EDefn(id, variants) => {
        context.add_enum(id.clone(), variants.clone());
      }
      elab::ElabGlob::TypDef(t, id) => {
        context.add_typedef(id.clone(), t.clone());
      }
      elab::ElabGlob::FnDecl(t, id, params) => {
        context.add_fnDecl_unsafe(id.clone(), t.clone(), params.clone());
      }
      elab::ElabGlob::FnDefn(t, id, params, stmts) => {
        if !context.add_fnDefn(
          id.clone(),
          t.clone(),
          params.clone(),
          &fnContext,
          stmts,
        ) {
          eprintln!("Function `{}` is not well-formed", id.0);
          return (false, None);
        }
      }
      elab::ElabGlob::HeadDecl(t, id, params) => {
        context.add_headDecl_unsafe(id.clone(), t.clone(), params.clone());
      }
      elab::ElabGlob::SDecl(id) => {
        context.add_StructDecl(id.clone());
      }
      elab::ElabGlob::SDefn(id, fields) => {
        context.add_StructDefn(id.clone(), fields.0.clone());
      }
    }
  }
  if DEBUG {
    eprintln!("Program is well-formed");
  }

  (true, Some(context))
}
