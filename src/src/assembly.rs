// use core::error::Source;
use crate::asm::Instr;
use crate::util::c0spec::MAC;
use std::env;
#[allow(dead_code)]
use std::fmt::{Display, Error, Formatter};

#[allow(dead_code)]
fn get_main() -> &'static str {
  if env::var("UNAME") == Ok(String::from("Darwin")) {
    "__c0_main"
  } else {
    "_c0_main"
  }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
#[allow(dead_code, non_snake_case, unused_variables)]
pub enum VarSize {
  V64,
  V32,
  V16,
  V8,
}
#[allow(dead_code, non_snake_case, unused_variables)]
impl Display for VarSize {
  fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
    match self {
      VarSize::V8 => write!(fmt, "b"),
      VarSize::V16 => write!(fmt, "w"),
      VarSize::V32 => write!(fmt, "l"),
      VarSize::V64 => write!(fmt, "q"),
    }
  }
}

impl PartialOrd for VarSize {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    match (self, other) {
      (VarSize::V8, VarSize::V8) => Some(std::cmp::Ordering::Equal),
      (VarSize::V8, _) => Some(std::cmp::Ordering::Less),
      (VarSize::V16, VarSize::V16) => Some(std::cmp::Ordering::Equal),
      (VarSize::V16, VarSize::V8) => Some(std::cmp::Ordering::Greater),
      (VarSize::V16, _) => Some(std::cmp::Ordering::Less),
      (VarSize::V32, VarSize::V32) => Some(std::cmp::Ordering::Equal),
      (VarSize::V32, VarSize::V8) => Some(std::cmp::Ordering::Greater),
      (VarSize::V32, VarSize::V16) => Some(std::cmp::Ordering::Greater),
      (VarSize::V32, _) => Some(std::cmp::Ordering::Less),
      (VarSize::V64, VarSize::V64) => Some(std::cmp::Ordering::Equal),
      (VarSize::V64, VarSize::V8) => Some(std::cmp::Ordering::Greater),
      (VarSize::V64, VarSize::V16) => Some(std::cmp::Ordering::Greater),
      (VarSize::V64, VarSize::V32) => Some(std::cmp::Ordering::Greater),
    }
  }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
#[allow(dead_code)]
pub enum RegX86 {
  Rsp(VarSize), // stack pointer
  Rax(VarSize), // return register
  Rdi(VarSize),
  Rsi(VarSize),
  Rdx(VarSize),
  Rcx(VarSize),
  R8(VarSize),
  R9(VarSize), // first 6 fn args
  R10(VarSize),
  R11(VarSize), // caller-saved
  Rbx(VarSize),
  Rbp(VarSize),
  R12(VarSize),
  R13(VarSize),
  R14(VarSize),
  R15(VarSize), // callee-saved
}

#[allow(dead_code, non_snake_case, unused_variables)]
impl RegX86 {
  /// Checks whether a register is callee-saved. See CSAPP section 3.7.5.
  // pub fn callee_saved(&self) -> bool {
  //   use RegX86::*;
  //   [Rbx, Rbp, R12, R13, R14, R15].contains(self)
  // }

  /// Get register size
  pub fn get_size(&self) -> VarSize {
    match *self {
      RegX86::Rsp(s) => s,
      RegX86::Rax(s) => s,
      RegX86::Rdi(s) => s,
      RegX86::Rsi(s) => s,
      RegX86::Rdx(s) => s,
      RegX86::Rcx(s) => s,
      RegX86::R8(s) => s,
      RegX86::R9(s) => s,
      RegX86::R10(s) => s,
      RegX86::R11(s) => s,
      RegX86::Rbx(s) => s,
      RegX86::Rbp(s) => s,
      RegX86::R12(s) => s,
      RegX86::R13(s) => s,
      RegX86::R14(s) => s,
      RegX86::R15(s) => s,
    }
  }

  pub fn to_size(&self, varsize: VarSize) -> RegX86 {
    match self {
      RegX86::Rsp(_) => RegX86::Rsp(varsize),
      RegX86::Rax(_) => RegX86::Rax(varsize),
      RegX86::Rdi(_) => RegX86::Rdi(varsize),
      RegX86::Rsi(_) => RegX86::Rsi(varsize),
      RegX86::Rdx(_) => RegX86::Rdx(varsize),
      RegX86::Rcx(_) => RegX86::Rcx(varsize),
      RegX86::R8(_) => RegX86::R8(varsize),
      RegX86::R9(_) => RegX86::R9(varsize),
      RegX86::R10(_) => RegX86::R10(varsize),
      RegX86::R11(_) => RegX86::R11(varsize),
      RegX86::Rbx(_) => RegX86::Rbx(varsize),
      RegX86::Rbp(_) => RegX86::Rbp(varsize),
      RegX86::R12(_) => RegX86::R12(varsize),
      RegX86::R13(_) => RegX86::R13(varsize),
      RegX86::R14(_) => RegX86::R14(varsize),
      RegX86::R15(_) => RegX86::R15(varsize),
    }
  }

  /// Converts self to x86 operand.
  pub fn xop(self) -> X86Operand {
    X86Operand::Reg(self)
  }
}

impl Into<X86Operand> for RegX86 {
  fn into(self) -> X86Operand {
    self.xop()
  }
}

#[allow(dead_code, non_snake_case, unused_variables)]
impl Display for RegX86 {
  fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
    use RegX86::*;
    match *self {
      Rsp(size) => match size {
        VarSize::V64 => write!(fmt, "%rsp"),
        VarSize::V32 => write!(fmt, "%esp"),
        VarSize::V16 => write!(fmt, "%sp"),
        VarSize::V8 => write!(fmt, "%spl"),
      },
      Rax(size) => match size {
        VarSize::V64 => write!(fmt, "%rax"),
        VarSize::V32 => write!(fmt, "%eax"),
        VarSize::V16 => write!(fmt, "%ax"),
        VarSize::V8 => write!(fmt, "%al"),
      },
      Rdi(size) => match size {
        VarSize::V64 => write!(fmt, "%rdi"),
        VarSize::V32 => write!(fmt, "%edi"),
        VarSize::V16 => write!(fmt, "%di"),
        VarSize::V8 => write!(fmt, "%dil"),
      },
      Rsi(size) => match size {
        VarSize::V64 => write!(fmt, "%rsi"),
        VarSize::V32 => write!(fmt, "%esi"),
        VarSize::V16 => write!(fmt, "%si"),
        VarSize::V8 => write!(fmt, "%sil"),
      },
      Rdx(size) => match size {
        VarSize::V64 => write!(fmt, "%rdx"),
        VarSize::V32 => write!(fmt, "%edx"),
        VarSize::V16 => write!(fmt, "%dx"),
        VarSize::V8 => write!(fmt, "%dl"),
      },
      Rcx(size) => match size {
        VarSize::V64 => write!(fmt, "%rcx"),
        VarSize::V32 => write!(fmt, "%ecx"),
        VarSize::V16 => write!(fmt, "%cx"),
        VarSize::V8 => write!(fmt, "%cl"),
      },
      R8(size) => match size {
        VarSize::V64 => write!(fmt, "%r8"),
        VarSize::V32 => write!(fmt, "%r8d"),
        VarSize::V16 => write!(fmt, "%r8w"),
        VarSize::V8 => write!(fmt, "%r8b"),
      },
      R9(size) => match size {
        VarSize::V64 => write!(fmt, "%r9"),
        VarSize::V32 => write!(fmt, "%r9d"),
        VarSize::V16 => write!(fmt, "%r9w"),
        VarSize::V8 => write!(fmt, "%r9b"),
      },
      R10(size) => match size {
        VarSize::V64 => write!(fmt, "%r10"),
        VarSize::V32 => write!(fmt, "%r10d"),
        VarSize::V16 => write!(fmt, "%r10w"),
        VarSize::V8 => write!(fmt, "%r10b"),
      },
      R11(size) => match size {
        VarSize::V64 => write!(fmt, "%r11"),
        VarSize::V32 => write!(fmt, "%r11d"),
        VarSize::V16 => write!(fmt, "%r11w"),
        VarSize::V8 => write!(fmt, "%r11b"),
      },
      Rbx(size) => match size {
        VarSize::V64 => write!(fmt, "%rbx"),
        VarSize::V32 => write!(fmt, "%ebx"),
        VarSize::V16 => write!(fmt, "%bx"),
        VarSize::V8 => write!(fmt, "%bl"),
      },
      Rbp(size) => match size {
        VarSize::V64 => write!(fmt, "%rbp"),
        VarSize::V32 => write!(fmt, "%ebp"),
        VarSize::V16 => write!(fmt, "%bp"),
        VarSize::V8 => write!(fmt, "%bpl"),
      },
      R12(size) => match size {
        VarSize::V64 => write!(fmt, "%r12"),
        VarSize::V32 => write!(fmt, "%r12d"),
        VarSize::V16 => write!(fmt, "%r12w"),
        VarSize::V8 => write!(fmt, "%r12b"),
      },
      R13(size) => match size {
        VarSize::V64 => write!(fmt, "%r13"),
        VarSize::V32 => write!(fmt, "%r13d"),
        VarSize::V16 => write!(fmt, "%r13w"),
        VarSize::V8 => write!(fmt, "%r13b"),
      },
      R14(size) => match size {
        VarSize::V64 => write!(fmt, "%r14"),
        VarSize::V32 => write!(fmt, "%r14d"),
        VarSize::V16 => write!(fmt, "%r14w"),
        VarSize::V8 => write!(fmt, "%r14b"),
      },
      R15(size) => match size {
        VarSize::V64 => write!(fmt, "%r15"),
        VarSize::V32 => write!(fmt, "%r15d"),
        VarSize::V16 => write!(fmt, "%r15w"),
        VarSize::V8 => write!(fmt, "%r15b"),
      },
    }
  }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
#[allow(dead_code)]
pub struct MemRefReg {
  pub reg: Option<RegX86>,
}

impl Display for MemRefReg {
  fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
    match &self.reg {
      None => write!(fmt, ""),
      Some(reg) => write!(fmt, "{}", reg),
    }
  }
}
/// Memory deref math, using int 64.
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
#[allow(dead_code)]
pub struct Memdef {
  pub imm: i128,
  pub reg1: MemRefReg,
  pub reg2: MemRefReg,
  pub scale: i128,
}
#[allow(dead_code, non_snake_case, unused_variables)]
impl Memdef {
  fn new() -> Self {
    Memdef {
      imm: 0,
      reg1: MemRefReg { reg: None },
      reg2: MemRefReg { reg: None },
      scale: 1,
    }
  }

  pub fn new_one(
    imm: usize,
    r1: Option<RegX86>,
    r2: Option<RegX86>,
    scale: i128,
  ) -> Self {
    Memdef {
      imm: imm as i128,
      reg1: MemRefReg { reg: r1 },
      reg2: MemRefReg { reg: r2 },
      scale: scale,
    }
  }

  pub fn build(
    imm: usize,
    r1: Option<RegX86>,
    r2: Option<RegX86>,
    scale: i128,
  ) -> Self {
    Memdef {
      imm: imm as i128,
      reg1: MemRefReg { reg: r1 },
      reg2: MemRefReg { reg: r2 },
      scale,
    }
  }

  /// Converts self to 32bit x86 operand
  pub fn xop_32(self) -> X86Operand {
    X86Operand::Mem(self, VarSize::V32)
  }

  /// Converts self to 64bit x86 operand
  pub fn xop_64(self) -> X86Operand {
    X86Operand::Mem(self, VarSize::V64)
  }

  /// Converts self to x86 operand of given size.
  pub fn xop(self, vsize: VarSize) -> X86Operand {
    X86Operand::Mem(self, vsize)
  }
}

impl Display for Memdef {
  fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
    // matching is not exaustive here
    match &self.reg2.reg {
      None => match self.reg1.reg {
        None => write!(fmt, "{}", self.imm),
        Some(_) => write!(fmt, "{}({})", self.imm, self.reg1),
      },
      Some(_) => write!(
        fmt,
        "{}({}, {}, {})",
        self.imm, self.reg1, self.reg2, self.scale
      ),
    }
  }
}
/// Immediate number representation
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
#[allow(dead_code)]
pub struct ImmNumber {
  pub number: i128,
  pub size: VarSize,
}

impl ImmNumber {
  /// return the size of the immediate
  pub fn get_size(&self) -> VarSize {
    return self.size;
  }

  /// return the number of the immediate
  pub fn get_number(&self) -> i128 {
    return self.number;
  }
}

/// print the immnumber
impl Display for ImmNumber {
  fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
    write!(fmt, "${}", self.number)
  }
}

#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
#[allow(dead_code)]
/// The assembly opererations
pub enum X86Operand {
  Imm(ImmNumber),
  Reg(RegX86),
  Mem(Memdef, VarSize),
}
#[allow(dead_code)]
impl X86Operand {
  /// Geg size of this operand
  pub fn get_size(&self) -> VarSize {
    match *self {
      X86Operand::Imm(imm) => imm.get_size(),
      X86Operand::Reg(r) => r.get_size(),
      X86Operand::Mem(_, s) => s,
    }
  }

  pub fn to_size(&self, size: VarSize) -> X86Operand {
    match *self {
      X86Operand::Imm(imm) => X86Operand::Imm(ImmNumber {
        number: imm.number,
        size: size,
      }),
      X86Operand::Reg(r) => match r {
        RegX86::Rax(_) => X86Operand::Reg(RegX86::Rax(size)),
        RegX86::Rbx(_) => X86Operand::Reg(RegX86::Rbx(size)),
        RegX86::Rcx(_) => X86Operand::Reg(RegX86::Rcx(size)),
        RegX86::Rdx(_) => X86Operand::Reg(RegX86::Rdx(size)),
        RegX86::Rsi(_) => X86Operand::Reg(RegX86::Rsi(size)),
        RegX86::Rdi(_) => X86Operand::Reg(RegX86::Rdi(size)),
        RegX86::Rsp(_) => X86Operand::Reg(RegX86::Rsp(size)),
        RegX86::Rbp(_) => X86Operand::Reg(RegX86::Rbp(size)),
        RegX86::R8(_) => X86Operand::Reg(RegX86::R8(size)),
        RegX86::R9(_) => X86Operand::Reg(RegX86::R9(size)),
        RegX86::R10(_) => X86Operand::Reg(RegX86::R10(size)),
        RegX86::R11(_) => X86Operand::Reg(RegX86::R11(size)),
        RegX86::R12(_) => X86Operand::Reg(RegX86::R12(size)),
        RegX86::R13(_) => X86Operand::Reg(RegX86::R13(size)),
        RegX86::R14(_) => X86Operand::Reg(RegX86::R14(size)),
        RegX86::R15(_) => X86Operand::Reg(RegX86::R15(size)),
      },
      X86Operand::Mem(m, _) => X86Operand::Mem(m, size),
    }
  }

  /// return the register if it is a register
  pub fn is_reg(&self) -> bool {
    match *self {
      X86Operand::Reg(r) => true,
      _ => false,
    }
  }
}

/// print out the operand
impl Display for X86Operand {
  fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
    match &*self {
      X86Operand::Imm(imm) => write!(fmt, "{}", imm),
      X86Operand::Reg(reg) => write!(fmt, "{}", reg),
      X86Operand::Mem(memdef, _) => write!(fmt, "{}", memdef),
    }
  }
}

/// define the sign extend for mov instruction
#[derive(PartialEq, Eq, Hash, Clone, Copy, Debug)]
#[allow(dead_code)]
pub enum SignExtend {
  Sign(VarSize, VarSize), // sign extend
  Zero(VarSize, VarSize), // zero extend
  No,                     // no extend
}

#[derive(PartialEq, Eq, Hash, Clone, Debug)]
#[allow(dead_code, unused_variables)]
pub enum AssemblyLine {
  Mov(X86Operand, X86Operand, VarSize, SignExtend),
  Lea(X86Operand, X86Operand, VarSize),
  Add(X86Operand, X86Operand, VarSize),
  Sub(X86Operand, X86Operand, VarSize),
  Idiv(X86Operand, VarSize),
  Imul(X86Operand, X86Operand, VarSize),
  Xor(X86Operand, X86Operand, VarSize),
  Or(X86Operand, X86Operand, VarSize),
  And(X86Operand, X86Operand, VarSize),
  Push(X86Operand, VarSize),
  Pop(X86Operand, VarSize),
  Cgo,
  Shl(X86Operand, X86Operand, VarSize), // first argument for shifting must be immediate
  Shr(X86Operand, X86Operand, VarSize),
  Cmp(X86Operand, X86Operand, VarSize),
  Test(X86Operand, X86Operand, VarSize),
  Jmp(String),
  Jl(String),
  Jle(String),
  Jge(String),
  Jg(String),
  Je(String),
  Jne(String),
  Ret,
  Cltd,
  Cqto,
  Cltq,
  Sete(X86Operand),
  Setne(X86Operand),
  Setl(X86Operand),
  Setle(X86Operand),
  Sets(X86Operand),
  Setns(X86Operand),
  Setg(X86Operand),
  Setge(X86Operand),
  Not(X86Operand, VarSize),
  Neg(X86Operand, VarSize),
  Block(String),
  DebugBinOp(Instr),
  Debug(String),
  FnDefn(String),
  Call(String),
}

#[allow(dead_code, unused_variables)]
impl Display for AssemblyLine {
  fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
    use AssemblyLine::*;
    match &*self {
      Mov(s, d, size, sign) => match (*size, *sign) {
        (VarSize::V64, SignExtend::No) => write!(fmt, "  movq {}, {}", s, d),
        (VarSize::V32, SignExtend::No) => write!(fmt, "  movl {}, {}", s, d),
        (VarSize::V16, SignExtend::No) => write!(fmt, "  movw {}, {}", s, d),
        (VarSize::V8, SignExtend::No) => write!(fmt, " movb {}, {}", s, d),

        (_, SignExtend::Sign(VarSize::V8, VarSize::V16)) => {
          write!(fmt, "  movsbw {}, {}", s, d)
        }
        (_, SignExtend::Sign(VarSize::V8, VarSize::V32)) => {
          write!(fmt, "  movsbl {}, {}", s, d)
        }
        (_, SignExtend::Sign(VarSize::V16, VarSize::V32)) => {
          write!(fmt, " movswl {}, {}", s, d)
        }
        (_, SignExtend::Sign(VarSize::V8, VarSize::V64)) => {
          write!(fmt, "  movsbq {}, {}", s, d)
        }
        (_, SignExtend::Sign(VarSize::V16, VarSize::V64)) => {
          write!(fmt, " movswq {}, {}", s, d)
        }
        (_, SignExtend::Sign(VarSize::V32, VarSize::V64)) => {
          write!(fmt, " movslq {}, {}", s, d)
        }

        (_, SignExtend::Zero(VarSize::V8, VarSize::V16)) => {
          write!(fmt, "  movzbw {}, {}", s, d)
        }
        (_, SignExtend::Zero(VarSize::V8, VarSize::V32)) => {
          write!(fmt, "  movzbl {}, {}", s, d)
        }
        (_, SignExtend::Zero(VarSize::V16, VarSize::V32)) => {
          write!(fmt, " mozswl {}, {}", s, d)
        }
        (_, SignExtend::Zero(VarSize::V8, VarSize::V64)) => {
          write!(fmt, "  movzbq {}, {}", s, d)
        }
        (_, SignExtend::Zero(VarSize::V16, VarSize::V64)) => {
          write!(fmt, " movzwq {}, {}", s, d)
        }
        (_, SignExtend::Zero(VarSize::V32, VarSize::V64)) => {
          write!(fmt, " movslq {}, {}", s, d)
        }
        (..) => panic!("Mov match error!"),
      },
      Lea(s, d, size) => write!(fmt, "  lea{} {}, {}", size, s, d),
      Add(s, d, size) => write!(fmt, "  add{} {}, {}", size, s, d),
      Sub(s, d, size) => write!(fmt, "  sub{} {}, {}", size, s, d),
      Idiv(s, size) => write!(fmt, "  idiv{} {}", size, s),
      Imul(s, d, size) => write!(fmt, "  imul{} {}, {}", size, s, d),
      Push(s, size) => write!(fmt, "  push{} {}", size, s),
      Pop(d, size) => write!(fmt, "  pop{} {}", size, d),
      Xor(s, d, size) => write!(fmt, "  xor{} {}, {}", size, s, d),
      Or(s, d, size) => write!(fmt, "  or{} {}, {}", size, s, d),
      And(s, d, size) => write!(fmt, "  and{} {}, {}", size, s, d),
      Cgo => write!(fmt, "cgo"),
      Shl(k, d, size) => write!(fmt, "  sal{} {}, {}", size, k, d),
      Shr(k, d, size) => write!(fmt, "  sar{} {}, {}", size, k, d),
      Cmp(k, d, size) => write!(fmt, "  cmp{} {}, {}", size, k, d),
      Test(k, d, size) => write!(fmt, "  test{} {}, {}", size, k, d),
      Jmp(block) => write!(fmt, "  jmp LABEL_{}", block),
      Jl(block) => write!(fmt, "  jl LABEL_{}", block),
      Jle(block) => write!(fmt, "  jle LABEL_{}", block),
      Jge(block) => write!(fmt, "  jge LABEL_{}", block),
      Jg(block) => write!(fmt, "  jg LABEL_{}", block),
      Je(block) => write!(fmt, "  je LABEL_{}", block),
      Jne(block) => write!(fmt, "  jne LABEL_{}", block),
      Block(block) => write!(fmt, "LABEL_{}:", block),
      Sete(d) => write!(fmt, "  sete {}", d),
      Setne(d) => write!(fmt, "  setne {}", d),
      Sets(d) => write!(fmt, "  sets {}", d),
      Setns(d) => write!(fmt, "  setns {}", d),
      Setl(d) => write!(fmt, "  setl {}", d),
      Setle(d) => write!(fmt, "  setle {}", d),
      Setg(d) => write!(fmt, "  setg {}", d),
      Setge(d) => write!(fmt, "  setge {}", d),
      Not(d, size) => write!(fmt, "  not{} {}", size, d),
      Neg(d, size) => write!(fmt, "  neg{} {}", size, d),
      Ret => write!(fmt, "  retq"),
      Cqto => write!(fmt, "  cqto"),
      Cltq => write!(fmt, "  cltq"),
      Cltd => write!(fmt, "  cltd"),
      FnDefn(name) => {
        if name == "main" {
          if MAC {
            let new_name = "__c0_main".clone();
            return write!(fmt, ".globl {}\n {}:", new_name, new_name);
          }
          let new_name = "_c0_main".clone();
          return write!(fmt, ".globl {}\n {}:", new_name, new_name);
        }
        if name == "checksum"
          || name == "init"
          || name == "prepare"
          || name == "run"
        {
          if MAC {
            let new_name = format!("{}{}", "__c0_".to_owned(), name.to_owned());
            return write!(fmt, ".globl {}\n {}:", new_name, new_name);
          }
          let new_name = format!("{}{}", "_c0_".to_owned(), name.to_owned());
          return write!(fmt, ".globl {}\n {}:", new_name, new_name);
        }
        let new_name = format!("{}{}", "_c0_".to_owned(), name.to_owned());
        write!(fmt, "{}:", new_name)
      }
      DebugBinOp(instr) => {
        let new_instr = instr.clone();
        match new_instr {
          Instr::JmpCondition {
            condition,
            tgt_true,
            tgt_false,
          } => write!(
            fmt,
            "# ifCondition {} true goto {} otherwise goto {}",
            condition, tgt_true, tgt_false
          ),
          _ => write!(fmt, "# {}", new_instr),
        }
      }
      Debug(s) => write!(fmt, "# {}", s),
      Call(name) => {
        write!(fmt, "  callq {}", name)
      }
    }
  }
}
