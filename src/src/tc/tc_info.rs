//! Records the informations gained during typechecking.

use core::panic;
use std::{collections::HashMap, os::fd, rc::Rc};

use super::ProgContext;
use crate::asm::DestSize;
use crate::ast;
use crate::ast::Typ;
use crate::elab;
use crate::tc;

use std::cmp::max;

pub fn get_tc_info(
  progctx: &ProgContext,
  prog: &elab::ElabProgram,
) -> TcInfoFn {
  let mut struct_sizes: HashMap<String, usize> = HashMap::new();
  let mut struct_alignments: HashMap<String, usize> = HashMap::new();
  let mut struct_field_infos: HashMap<
    String,
    HashMap<String, StructFieldInfo>,
  > = HashMap::new();

  let mut fname_var_typs: HashMap<String, Vec<ast::Typ>> = HashMap::new();
  let mut fn_ret_typs: HashMap<String, ast::RetTyp> = HashMap::new();

  /// Computes the size of some type, given the size infos of existing structs.
  fn typsize(
    t: &ast::Typ,
    existing_struct_sizes: &HashMap<String, usize>,
  ) -> usize {
    match t {
      ast::Typ::Int | ast::Typ::Bool => 4,
      ast::Typ::C0ptr(_) | ast::Typ::C0array(_) | ast::Typ::C0enum(..) => 8,
      ast::Typ::C0struct(s) => *existing_struct_sizes
        .get(s)
        .expect("trying to calc a struct size before it's defined"),
      ast::Typ::Custom(s) => {
        panic!("Custom type not supported in struct size calculation")
      }
    }
  }

  /// Computes the alignment of some struct, given the align-info of existings.
  fn typalign(
    t: &ast::Typ,
    existing_struct_alignments: &HashMap<String, usize>,
  ) -> usize {
    match t {
      ast::Typ::Int | ast::Typ::Bool => 4,
      ast::Typ::C0ptr(_) | ast::Typ::C0array(_) | ast::Typ::C0enum(..) => 8,
      ast::Typ::C0struct(s) => *existing_struct_alignments
        .get(s)
        .expect("trying to calc a struct size before it's defined"),
      ast::Typ::Custom(s) => {
        panic!("Custom type not supported in struct size calculation")
      }
    }
  }

  /// Computes the needed padding of some type, given the running struct size
  /// and a map from existing structs to their alignment sizes.
  fn padding(
    t: &ast::Typ,
    curr_struct_size: usize,
    existing_struct_alignments: &HashMap<String, usize>,
  ) -> usize {
    let align = typalign(t, existing_struct_alignments);
    if align == 0 {
      return 0;
    }
    let over_align = curr_struct_size % align;
    (align - over_align) % align
  }

  /// Computes the end padding of struct.
  fn end_padding(align: usize, curr_struct_size: usize) -> usize {
    if align == 0 {
      return 0;
    }
    let over_align = curr_struct_size % align;
    (align - over_align) % align
  }

  for elab_glob in &prog.0 {
    // do this in the order of struct defines
    match elab_glob {
      elab::ElabGlob::SDefn(id, fields) => {
        let mut struct_size: usize = 0;
        let mut struct_field_offset = HashMap::new();
        let mut alignment = 0;

        for ast::Field(field_type, field_name) in &fields.0 {
          struct_size += padding(field_type, struct_size, &struct_alignments);
          struct_field_offset.insert(
            field_name.clone(),
            StructFieldInfo {
              offset: struct_size,
              typ: field_type.clone(),
            },
          );
          struct_size += typsize(field_type, &struct_sizes);
          alignment = max(alignment, typalign(field_type, &struct_alignments));
        }

        // pad the end of struct till nearest alignment
        struct_size += end_padding(alignment, struct_size);

        struct_sizes.insert(id.0.clone(), struct_size);
        struct_alignments.insert(id.0.clone(), alignment);
        struct_field_infos.insert(id.0.clone(), struct_field_offset);
      }
      _ => {}
    }
  }

  for (fn_name, fndecl) in &progctx.fnDecls {
    let mut var_typs = Vec::new();
    for ast::Param(var_type, _) in &fndecl.params.0 {
      var_typs.push(var_type.clone());
    }
    fname_var_typs.insert(fn_name.clone(), var_typs);
    fn_ret_typs.insert(fn_name.clone(), fndecl.retTyp.clone());
  }

  return TcInfoFn::new(
    fname_var_typs,
    struct_sizes,
    struct_field_infos,
    progctx.enumDefs.clone(),
    progctx.enum_tags.clone(),
    fn_ret_typs,
  );
}

struct TypList {
  /// A vector of types paired with their sizes, for fast access.
  pub sizes_typs: Vec<(usize, Typ)>,
  /// Sum of all type sizes.
  pub sum_size: usize,
}

impl TypList {
  /// Builds a `TypList` instance from a vector of types. This builds up the
  /// cumulative offset-bytes of each type in the list, as well as the sum
  /// of type sizes.
  fn build(v: Vec<Typ>) -> Self {
    let sizes_typs: Vec<(usize, Typ)> = v
      .into_iter()
      .map(|t| (t.smalltyp_size_bytes(), t))
      .collect();
    let sum_size = sizes_typs.iter().map(|x| x.0).fold(0, |x, y| x + y);
    Self {
      sizes_typs,
      sum_size,
    }
  }

  /// Similar to `build` except paired with a string.
  pub fn build_pair(pair: (String, Vec<Typ>)) -> (String, Self) {
    (pair.0, TypList::build(pair.1))
  }
}

/// Given an enum name, stores its union-size and a map of variant info.
pub struct EnumInfo {
  /// Maps an enum name to its memsize, paired with another map from its
  /// variants to a corresponding `TypList`.
  data: HashMap<String, (usize, HashMap<String, TypList>)>,

  /// Maps an enum and a variant to its index, starting from zero.
  variant_idx: HashMap<String, HashMap<String, usize>>,
}

impl EnumInfo {
  /// Builds an `EnumInfo` instance from some program context field.
  fn build(
    mp: HashMap<String, HashMap<String, Vec<Typ>>>,
    variant_idx: HashMap<String, HashMap<String, usize>>,
  ) -> Self {
    use std::cmp::max;

    let data = mp
      .into_iter()
      .map(|(enum_id, m)| {
        let variants: HashMap<String, TypList> =
          m.into_iter().map(TypList::build_pair).collect();
        let enum_memsize = variants.iter().map(|x| x.1.sum_size).fold(0, max);

        (enum_id, (enum_memsize, variants))
      })
      .collect();
    Self { data, variant_idx }
  }

  /// Retrieves the size of some enum.
  pub fn get_size(&self, enum_name: &str) -> Option<usize> {
    Some(self.data.get(enum_name)?.0)
  }

  /// Retrieves the size of some enum-variant.
  pub fn get_ev_size(&self, eid: &str, vid: &str) -> Option<usize> {
    Some(self.data.get(eid)?.1.get(vid)?.sum_size)
  }

  /// Retrieves a slice of usizes for some variant's args.
  pub fn args_sizes(&self, eid: &str, vid: &str) -> Option<Vec<usize>> {
    Some(
      self
        .data
        .get(eid)?
        .1
        .get(vid)?
        .sizes_typs
        .iter()
        .map(|x| x.0)
        .collect(),
    )
  }

  /// Retrieves the tag of some variant in an enum.
  pub fn enum_variant_tag(&self, eid: &str, vid: &str) -> Option<usize> {
    Some(*self.variant_idx.get(eid)?.get(vid)?)
  }

  /// Counts the number of variants of some enum.
  pub fn enum_count_variant(&self, eid: &str) -> Option<usize> {
    Some(self.variant_idx.get(eid)?.len())
  }
}

/// TcInfo constrained to some function.
pub struct TcInfoFn {
  /// Given a function name and a variable name, returns its type.
  fn_var_typ: HashMap<String, Vec<ast::Typ>>,

  /// Given a struct name, returns its type.
  struct_size: HashMap<String, usize>,

  /// Given a struct name and a field, returns its type.
  struct_field_info: HashMap<String, HashMap<String, StructFieldInfo>>,

  enum_defs: HashMap<String, HashMap<String, Vec<Typ>>>,
  enum_info: EnumInfo,

  /// Given a fn name, return its return typ
  fn_ret_typ: HashMap<String, ast::RetTyp>,
}

impl TcInfoFn {
  /// Creates a new `TcInfoFn` instance.
  pub fn new(
    fn_var_typ: HashMap<String, Vec<ast::Typ>>,
    struct_size: HashMap<String, usize>,
    struct_field_info: HashMap<String, HashMap<String, StructFieldInfo>>,
    enum_info: HashMap<String, HashMap<String, Vec<Typ>>>,
    variant_idx: HashMap<String, HashMap<String, usize>>,
    fn_ret_typ: HashMap<String, ast::RetTyp>,
  ) -> Self {
    Self {
      fn_var_typ: {
        let mut fn_var_typ = fn_var_typ;
        fn_var_typ.insert("c0_assert".to_string(), vec![ast::Typ::Bool]);
        fn_var_typ
      },
      struct_size,
      struct_field_info,
      enum_defs: enum_info.clone(),
      enum_info: EnumInfo::build(enum_info, variant_idx),
      fn_ret_typ: {
        let mut fn_ret_typ = fn_ret_typ;
        fn_ret_typ.insert("c0_assert".to_string(), ast::RetTyp::Void);
        fn_ret_typ
      },
    }
  }

  pub fn struct_size(&self, sname: &str) -> usize {
    (self.struct_size)
      .get(sname)
      .expect("Struct not found in struct_sizes")
      .clone()
  }

  pub fn vartyp(&self, varname: &str) -> ast::Typ {
    panic!(
      "vartyp not implemented, you should be using elab to get typ of vars"
    )
  }

  pub fn sf_typ(&self, sname: &str, fdname: &str) -> ast::Typ {
    (self.struct_field_info)
      .get(sname)
      .expect("struct not found in struct fields")
      .get(fdname)
      .expect("field not found in struct fields")
      .typ
      .clone()
  }

  pub fn sf_size(&self, sname: &str, fdname: &str) -> usize {
    self.sf_typ(sname, fdname).size(&self)
  }

  pub fn sf_offset(&self, sname: &str, fdname: &str) -> usize {
    (self.struct_field_info)
      .get(sname)
      .expect("struct not found in struct fields")
      .get(fdname)
      .expect("field not found in struct fields")
      .offset
      .clone()
  }

  pub fn function_rettyp(&self, fname: &str) -> ast::RetTyp {
    self
      .fn_ret_typ
      .get(fname)
      .expect("function not found in fn_ret_typs")
      .clone()
  }

  /// Returns a `vec` of argtyp sizes.
  pub fn function_param_size(&self, fname: &str) -> Vec<DestSize> {
    let mut param_typs = self
      .fn_var_typ
      .get(fname)
      .expect(&format!("function not found in fn_var_typs {}", fname));
    param_typs.into_iter().map(|t| t.dsize(&self)).collect()
  }

  /// Returns a `vec` of variant typ sizes.
  pub fn enum_variant_param_sizes(&self, eid: &str, vid: &str) -> Vec<usize> {
    self
      .enum_info
      .args_sizes(eid, vid)
      .expect("tc missed invalid variant")
  }

  /// Returns the overall heap size of some enum.
  pub fn enum_heap_size(&self, eid: &str) -> usize {
    self
      .enum_info
      .get_size(eid)
      .expect("tc missed non-existend enum")
  }

  /// Returns the size of a particular variant of enum.
  pub fn ev_heap_size(&self, eid: &str, vid: &str) -> usize {
    self
      .enum_info
      .get_ev_size(eid, vid)
      .expect("tc missed bad enum")
  }

  /// Given an enum and a variant, returns the corresponding tag.
  pub fn ev_tag(&self, eid: &str, vid: &str) -> usize {
    self
      .enum_info
      .enum_variant_tag(eid, vid)
      .expect("tc missed bad enum")
  }

  /// Given an enum, returns the number of variants. 
  pub fn num_variants(&self, eid: &str) -> usize {
    self.enum_info.enum_count_variant(eid).expect("tc missed bad")
  }

  /// Given an enum and a variant, returns the corresponding types. 
  pub fn ev_typs(&self, eid: &str, vid: &str) -> Vec<Typ> {
    self
      .enum_defs
      .get(eid)
      .expect("no enum")
      .get(vid)
      .expect("no v")
      .clone()
  }
}

/// Information regarding a specific field of a struct.
pub struct StructFieldInfo {
  typ: ast::Typ,
  offset: usize,
}
impl StructFieldInfo {
  pub fn new(typ: ast::Typ, offset: usize) -> Self {
    Self { typ, offset }
  }
}
