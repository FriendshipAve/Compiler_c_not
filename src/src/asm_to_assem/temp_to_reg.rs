#![allow(dead_code)]
#![allow(unused_imports)]
// use crate::asm::Dest;
use crate::assembly::RegX86;
use crate::assembly::{VarSize, X86Operand};
use crate::reg_alloc::{
  ast_graph_node::Node, x86_register::NamedReg, x86_register::RegAbs86::*,
};

pub fn temp_to_node(tmp: u32) -> Node {
  Node::Temporary(tmp)
}

pub fn reg_conversion(r: NamedReg, varsize: VarSize) -> RegX86 {
  match r {
    NamedReg::Rax => RegX86::Rax(varsize),
    NamedReg::Rbx => RegX86::Rbx(varsize),
    NamedReg::Rcx => RegX86::Rcx(varsize),
    NamedReg::Rdx => RegX86::Rdx(varsize),
    NamedReg::Rsi => RegX86::Rsi(varsize),
    NamedReg::Rdi => RegX86::Rdi(varsize),
    NamedReg::Rbp => RegX86::Rbp(varsize),
    NamedReg::Rsp => RegX86::Rsp(varsize),
    NamedReg::R8 => RegX86::R8(varsize),
    NamedReg::R9 => RegX86::R9(varsize),
    NamedReg::R10 => RegX86::R10(varsize),
    // NamedReg::R11 => RegX86::R11(varsize),
    NamedReg::R12 => RegX86::R12(varsize),
    NamedReg::R13 => RegX86::R13(varsize),
    NamedReg::R14 => RegX86::R14(varsize),
    NamedReg::R15 => RegX86::R15(varsize),
  }
}

pub fn reg_conversion_64(r: NamedReg) -> X86Operand {
  match r {
    NamedReg::Rax => X86Operand::Reg(RegX86::Rax(VarSize::V64)),
    NamedReg::Rbx => X86Operand::Reg(RegX86::Rbx(VarSize::V64)),
    NamedReg::Rcx => X86Operand::Reg(RegX86::Rcx(VarSize::V64)),
    NamedReg::Rdx => X86Operand::Reg(RegX86::Rdx(VarSize::V64)),
    NamedReg::Rsi => X86Operand::Reg(RegX86::Rsi(VarSize::V64)),
    NamedReg::Rdi => X86Operand::Reg(RegX86::Rdi(VarSize::V64)),
    NamedReg::Rbp => X86Operand::Reg(RegX86::Rbp(VarSize::V64)),
    NamedReg::Rsp => X86Operand::Reg(RegX86::Rsp(VarSize::V64)),
    NamedReg::R8 => X86Operand::Reg(RegX86::R8(VarSize::V64)),
    NamedReg::R9 => X86Operand::Reg(RegX86::R9(VarSize::V64)),
    NamedReg::R10 => X86Operand::Reg(RegX86::R10(VarSize::V64)),
    NamedReg::R12 => X86Operand::Reg(RegX86::R12(VarSize::V64)),
    NamedReg::R13 => X86Operand::Reg(RegX86::R13(VarSize::V64)),
    NamedReg::R14 => X86Operand::Reg(RegX86::R14(VarSize::V64)),
    NamedReg::R15 => X86Operand::Reg(RegX86::R15(VarSize::V64)),
  }
}
