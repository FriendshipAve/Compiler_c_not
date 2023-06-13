use crate::codegen::Context;
// use std::collections::HashMap;
use crate::asm::{self, Dest, HeapLocation, Instr, Operand};
use crate::assembly::{
  AssemblyLine, ImmNumber, MemRefReg, Memdef, RegX86, SignExtend, VarSize,
  X86Operand,
};

use super::asm_reg_to_assem::{
  asm_reg_to_assem, asm_reg_to_assem64, reg_size_convert,
};
use super::temp_to_reg;
use crate::args::Config;
use crate::asm_to_assem::asm_reg_to_assem::sign_extension_convert;
use crate::asm_to_assem::function_body_to_assem;
use crate::asm_to_assem::temp_to_reg::{reg_conversion, temp_to_node};
use crate::asm_to_assem::Assemb;
use crate::ast;
use crate::ast::{BinOp, PostOp, UnOp};
use crate::reg_alloc::x86_register::NamedReg;
use crate::reg_alloc::{
  ast_graph_node::Node, context_to_assignment, x86_register::RegAbs86,
};
use crate::util::c0spec::{DEBUG, MAC};
use std::cmp;
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;
const R11_64: X86Operand = X86Operand::Reg(RegX86::R11(VarSize::V64));
const R11_32: X86Operand = X86Operand::Reg(RegX86::R11(VarSize::V32));

pub fn add_v32(
  ass_line: &mut Assemb,
  assSource1: &X86Operand,
  assSource2: &X86Operand,
  assDest: &X86Operand,
) {
  /// adding a binop where there is one source is spilled (mem_s)
  fn add_mem_source_ref_source(
    ass_line: &mut Assemb,
    s1: &X86Operand,
    mem_s: &X86Operand,
    d: &X86Operand,
  ) {
    if *s1 != *d {
      ass_line.push_Operand_to_Operand(mem_s, d);
      ass_line.add_instr(AssemblyLine::Add(
        s1.clone(),
        d.clone(),
        VarSize::V32,
      ));
    } else {
      ass_line.push_Operand_to_Operand(mem_s, &R11_32);
      // add s1 to r11
      ass_line.add_instr(AssemblyLine::Add(
        s1.clone(),
        R11_32.clone(),
        VarSize::V32,
      ));
      ass_line.push_Operand_to_Operand(&R11_32, d);
    }
  }

  /// adding a binop where there is one source is const (const_s)
  fn add_const_src_ref_source(
    ass_line: &mut Assemb,
    s1: &X86Operand,
    const_s: i128,
    d: &X86Operand,
  ) {
    match (s1, d) {
      (X86Operand::Reg(s), X86Operand::Reg(..)) => {
        let sum = Memdef {
          imm: const_s,
          reg1: MemRefReg {
            reg: Some(s.clone()),
          },
          reg2: MemRefReg { reg: None },
          scale: 1,
        };
        ass_line.add_instr(AssemblyLine::Lea(
          X86Operand::Mem(sum, VarSize::V32),
          d.clone(),
          VarSize::V32,
        ));
      }
      (X86Operand::Mem(..), _) => {
        let imm = function_body_to_assem::add_new_imm32(const_s as i32);
        add_mem_source_ref_source(ass_line, &X86Operand::Imm(imm), s1, d);
      }
      _ => unreachable!("s1 and d shall not be consts"),
    }
  }
  match (assSource1, assSource2) {
    (X86Operand::Reg(s1), X86Operand::Reg(s2)) => {
      let sum = Memdef::new_one(
        0,
        Some(s1.to_size(VarSize::V32)),
        Some(s2.to_size(VarSize::V32)),
        1,
      );
      match assDest {
        X86Operand::Reg(d) => ass_line.add_instr(AssemblyLine::Lea(
          X86Operand::Mem(sum, VarSize::V32),
          assDest.clone(),
          VarSize::V32,
        )),
        X86Operand::Mem(..) => {
          ass_line.add_instr(AssemblyLine::Lea(
            X86Operand::Mem(sum, VarSize::V32),
            R11_32.clone(),
            VarSize::V32,
          ));
          ass_line.push_Operand_to_Operand(&R11_32, assDest);
        }
        _ => unreachable!("add's dest shall not be imm"),
      }
    }
    (X86Operand::Mem(..), X86Operand::Reg(..)) => {
      add_mem_source_ref_source(ass_line, assSource2, assSource1, assDest)
    }
    (X86Operand::Reg(..), X86Operand::Mem(..)) => {
      add_mem_source_ref_source(ass_line, assSource1, assSource2, assDest)
    }
    (X86Operand::Mem(..), X86Operand::Mem(..)) => {
      match assDest {
        X86Operand::Reg(..) => {
          ass_line.push_Operand_to_Operand(assSource2, assDest);
          // add s1 to r11
          ass_line.add_instr(AssemblyLine::Add(
            assSource1.clone(),
            assDest.clone(),
            VarSize::V32,
          ));
        }
        X86Operand::Mem(..) => {
          ass_line.push_Operand_to_Operand(assSource2, &R11_32);
          // add s1 to r11
          ass_line.add_instr(AssemblyLine::Add(
            assSource1.clone(),
            R11_32.clone(),
            VarSize::V32,
          ));
          ass_line.push_Operand_to_Operand(&R11_32, assDest);
        }
        _ => unreachable!("add's dest shall not be imm"),
      }
    }
    (X86Operand::Imm(c1), X86Operand::Imm(c2)) => {
      let num1 = c1.get_number() as i32;
      let num2 = c2.get_number() as i32;
      ass_line.push_int_to_Operand(num1 + num2, assDest);
    }
    (X86Operand::Imm(c1), _) => {
      let num = c1.get_number();
      add_const_src_ref_source(ass_line, assSource2, num, assDest);
    }
    (_, X86Operand::Imm(c2)) => {
      let num = c2.get_number();
      add_const_src_ref_source(ass_line, assSource1, num, assDest);
    }
  }
}

pub fn add_v64(
  ass_line: &mut Assemb,
  assSource1: &X86Operand,
  assSource2: &X86Operand,
  assDest: &X86Operand,
) {
  /// adding a binop where there is one source is spilled (mem_s)
  fn add_mem_source_ref_source(
    ass_line: &mut Assemb,
    s1: &X86Operand,
    mem_s: &X86Operand,
    d: &X86Operand,
  ) {
    if *s1 != *d {
      ass_line.push_Operand_to_Operand(mem_s, d);
      ass_line.add_instr(AssemblyLine::Add(
        s1.clone(),
        d.clone(),
        VarSize::V64,
      ));
    } else {
      ass_line.push_Operand_to_Operand(mem_s, &R11_64);
      // add s1 to r11
      ass_line.add_instr(AssemblyLine::Add(
        s1.clone(),
        R11_64.clone(),
        VarSize::V64,
      ));
      ass_line.push_Operand_to_Operand(&R11_64, d);
    }
  }

  /// adding a binop where there is one source is const (const_s)
  fn add_const_src_ref_source(
    ass_line: &mut Assemb,
    s1: &X86Operand,
    const_s: i128,
    d: &X86Operand,
  ) {
    match (s1, d) {
      (X86Operand::Reg(s), X86Operand::Reg(..)) => {
        let sum = Memdef {
          imm: const_s,
          reg1: MemRefReg {
            reg: Some(s.clone()),
          },
          reg2: MemRefReg { reg: None },
          scale: 1,
        };
        ass_line.add_instr(AssemblyLine::Lea(
          X86Operand::Mem(sum, VarSize::V64),
          d.clone(),
          VarSize::V64,
        ));
      }
      (X86Operand::Mem(..), _) => {
        let imm = function_body_to_assem::add_new_imm64(const_s as i64);
        let new_s1 = &X86Operand::Imm(imm);
        ass_line.push_Operand_to_Operand(new_s1, &R11_64);
        add_mem_source_ref_source(ass_line, &R11_64, s1, d);
      }
      _ => unreachable!("s1 and d shall not be consts"),
    }
  }
  match (assSource1, assSource2) {
    (X86Operand::Reg(s1), X86Operand::Reg(s2)) => {
      let sum = Memdef::new_one(
        0,
        Some(s1.to_size(VarSize::V64)),
        Some(s2.to_size(VarSize::V64)),
        1,
      );
      match assDest {
        X86Operand::Reg(d) => ass_line.add_instr(AssemblyLine::Lea(
          X86Operand::Mem(sum, VarSize::V64),
          assDest.clone(),
          VarSize::V64,
        )),
        X86Operand::Mem(..) => {
          ass_line.add_instr(AssemblyLine::Lea(
            X86Operand::Mem(sum, VarSize::V64),
            R11_64.clone(),
            VarSize::V64,
          ));
          ass_line.push_Operand_to_Operand(&R11_64, assDest);
        }
        _ => unreachable!("add's dest shall not be imm"),
      }
    }
    (X86Operand::Mem(..), X86Operand::Reg(..)) => {
      add_mem_source_ref_source(ass_line, assSource2, assSource1, assDest)
    }
    (X86Operand::Reg(..), X86Operand::Mem(..)) => {
      add_mem_source_ref_source(ass_line, assSource1, assSource2, assDest)
    }
    (X86Operand::Mem(..), X86Operand::Mem(..)) => {
      match assDest {
        X86Operand::Reg(..) => {
          ass_line.push_Operand_to_Operand(assSource2, assDest);
          // add s1 to r11
          ass_line.add_instr(AssemblyLine::Add(
            assSource1.clone(),
            assDest.clone(),
            VarSize::V64,
          ));
        }
        X86Operand::Mem(..) => {
          ass_line.push_Operand_to_Operand(assSource2, &R11_64);
          // add s1 to r11
          ass_line.add_instr(AssemblyLine::Add(
            assSource1.clone(),
            R11_64.clone(),
            VarSize::V32,
          ));
          ass_line.push_Operand_to_Operand(&R11_64, assDest);
        }
        _ => unreachable!("add's dest shall not be imm"),
      }
    }
    (X86Operand::Imm(c1), X86Operand::Imm(c2)) => {
      let num1 = c1.get_number() as i32;
      let num2 = c2.get_number() as i32;
      ass_line.push_int_to_Operand(num1 + num2, assDest);
    }
    (X86Operand::Imm(c1), _) => {
      let num = c1.get_number();
      add_const_src_ref_source(ass_line, assSource2, num, assDest);
    }
    (_, X86Operand::Imm(c2)) => {
      let num = c2.get_number();
      add_const_src_ref_source(ass_line, assSource1, num, assDest);
    }
  }
}

pub fn sub_v22(
  ass_line: &mut Assemb,
  assSource1: &X86Operand,
  assSource2: &X86Operand,
  assDest: &X86Operand,
) {
  if *assSource2 != *assDest && (assSource2.is_reg() && assDest.is_reg()) {
    ass_line.push_Operand_to_Operand(assSource1, &assDest);

    ass_line.add_instr(AssemblyLine::Sub(
      assSource2.clone(),
      assDest.clone(),
      VarSize::V32,
    ));
  } else {
    ass_line.push_Operand_to_Operand(assSource1, &R11_32);
    // sub s2 to r11
    ass_line.instrs.push(AssemblyLine::Sub(
      assSource2.clone(),
      R11_32.clone(),
      VarSize::V32,
    ));
    ass_line.push_Operand_to_Operand(&R11_32, assDest);
  }
}

pub fn r11v8_to_dest(ass_line: &mut Assemb, assDest: &X86Operand) {
  let r11_8 = RegX86::R11(VarSize::V8);
  let size = assDest.get_size();
  let r11_size = RegX86::R11(size);
  if assDest.is_reg() {
    ass_line.mov_ze(r11_8.xop(), assDest.clone(), VarSize::V8)
  } else {
    ass_line.mov_ze(r11_8.xop(), r11_size.xop(), VarSize::V8);
    ass_line.mov_ne(r11_size.xop(), assDest.clone(), size);
  }
}

pub fn cmp_sources_v32(
  ass_line: &mut Assemb,
  assSource1: &X86Operand,
  assSource2: &X86Operand,
) {
  let size = assSource1.get_size();
  assert_eq!(size, assSource2.get_size());

  let r11_size = RegX86::R11(size).xop();

  let arg1 = *assSource2;

  let arg2 = if Assemb::X86Operand_conflict(*assSource1, *assSource2) {
    ass_line.mov_ne(*assSource1, r11_size, size);
    r11_size
  } else {
    *assSource1
  };

  ass_line.add_instr(AssemblyLine::Cmp(arg1, arg2, size));
}
