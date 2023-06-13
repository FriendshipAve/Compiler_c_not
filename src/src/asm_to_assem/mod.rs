#![allow(dead_code)]
#![allow(unused_imports)]
mod asm_reg_to_assem;
mod binop_convert;
mod function_body_to_assem;
mod temp_to_reg;
use core::panic;
use std::{collections::HashMap, hash::Hash};

use crate::codegen::Context;

use self::function_body_to_assem::Assemb;
use crate::assembly::AssemblyLine;
use crate::util::c0spec::MAC;
use std::vec::Vec;

pub fn asm_to_assem(
  asm: &HashMap<String, Context>,
  optimize_level: usize,
) -> HashMap<String, Assemb> {
  let mut ref_assembs = HashMap::new();
  for (name, ctx) in asm {
    ref_assembs.insert(
      name.clone(),
      function_body_to_assem::ctx_preprocess(ctx, optimize_level),
    );
  }
  let mut assembs = HashMap::new();
  for (name, ctx) in asm {
    let working = ref_assembs.get(name).unwrap();
    assembs.insert(
      name.clone(),
      function_body_to_assem::parse_asm(ctx, working.clone(), &ref_assembs),
    );
  }

  let mut panic_block = assembs.get_mut("main").expect("main not found");
  panic_block.add_instr(AssemblyLine::Block("system_panic".to_string()));
  if MAC {
    panic_block.add_instr(AssemblyLine::Call("_raise".to_string()));
  } else {
    panic_block.add_instr(AssemblyLine::Call("raise".to_string()));
  }

  assembs
}
