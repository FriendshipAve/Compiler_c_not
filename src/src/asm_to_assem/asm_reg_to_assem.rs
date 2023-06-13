#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_mut)]
#![allow(unused_assignments)]
use crate::asm::Dest;
use crate::assembly::{RegX86, SignExtend, VarSize, X86Operand};
use crate::ast::Var;
use crate::reg_alloc::x86_register::NamedReg;

pub fn asm_reg_to_assem(reg: NamedReg, varsize: VarSize) -> X86Operand {
  match reg {
    NamedReg::Rax => X86Operand::Reg(RegX86::Rax(varsize)),
    NamedReg::Rbx => X86Operand::Reg(RegX86::Rbx(varsize)),
    NamedReg::Rcx => X86Operand::Reg(RegX86::Rcx(varsize)),
    NamedReg::Rdx => X86Operand::Reg(RegX86::Rdx(varsize)),
    NamedReg::Rsi => X86Operand::Reg(RegX86::Rsi(varsize)),
    NamedReg::Rdi => X86Operand::Reg(RegX86::Rdi(varsize)),
    NamedReg::Rbp => X86Operand::Reg(RegX86::Rbp(varsize)),
    NamedReg::Rsp => X86Operand::Reg(RegX86::Rsp(varsize)),
    NamedReg::R8 => X86Operand::Reg(RegX86::R8(varsize)),
    NamedReg::R9 => X86Operand::Reg(RegX86::R9(varsize)),
    NamedReg::R10 => X86Operand::Reg(RegX86::R10(varsize)),
    NamedReg::R12 => X86Operand::Reg(RegX86::R12(varsize)),
    NamedReg::R13 => X86Operand::Reg(RegX86::R13(varsize)),
    NamedReg::R14 => X86Operand::Reg(RegX86::R14(varsize)),
    NamedReg::R15 => X86Operand::Reg(RegX86::R15(varsize)),
  }
}

pub fn asm_reg_to_assem64(reg: NamedReg) -> X86Operand {
  match reg {
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

pub fn reg_size_convert(source: X86Operand, destSize: VarSize) -> X86Operand {
  match source {
    X86Operand::Reg(x) => match x {
      RegX86::Rax(_) => return X86Operand::Reg(RegX86::Rax(destSize)),
      RegX86::Rbx(_) => return X86Operand::Reg(RegX86::Rbx(destSize)),
      RegX86::Rcx(_) => return X86Operand::Reg(RegX86::Rcx(destSize)),
      RegX86::Rdx(_) => return X86Operand::Reg(RegX86::Rdx(destSize)),
      RegX86::Rsi(_) => return X86Operand::Reg(RegX86::Rsi(destSize)),
      RegX86::Rdi(_) => return X86Operand::Reg(RegX86::Rdi(destSize)),
      RegX86::Rbp(_) => return X86Operand::Reg(RegX86::Rbp(destSize)),
      RegX86::Rsp(_) => return X86Operand::Reg(RegX86::Rsp(destSize)),
      RegX86::R8(_) => return X86Operand::Reg(RegX86::R8(destSize)),
      RegX86::R9(_) => return X86Operand::Reg(RegX86::R9(destSize)),
      RegX86::R10(_) => return X86Operand::Reg(RegX86::R10(destSize)),
      RegX86::R12(_) => return X86Operand::Reg(RegX86::R12(destSize)),
      RegX86::R13(_) => return X86Operand::Reg(RegX86::R13(destSize)),
      RegX86::R14(_) => return X86Operand::Reg(RegX86::R14(destSize)),
      RegX86::R15(_) => return X86Operand::Reg(RegX86::R15(destSize)),
      RegX86::R11(_) => return X86Operand::Reg(RegX86::R11(destSize)),
    },
    _ => return source,
  }
}
pub fn sign_extension_convert(
  src: &X86Operand,
  dest: &X86Operand,
) -> SignExtend {
  let size1 = src.get_size();
  let size2 = dest.get_size();

  if size1 >= size2 {
    return SignExtend::No;
  } else {
    return SignExtend::Zero(size1, size2);
  }
}
