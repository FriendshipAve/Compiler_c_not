// L1 Compiler
//! Abstract Assembly Type (Triples)
// Author: Dan Cascaval <dcascava@andrew.cmu.edu>

use crate::{
  assembly::AssemblyLine,
  ast,
  codegen_elab2::FlagTyp,
  const_params::{
    EXPLICIT_PUSH_POP_CALLER_SAVED_REGS, FNCALL_STORE_ALL_SIX_REGS,
    NAIVE_FNCALL_DURING_CODEGEN, REGALLOC_IGNORE_RSP,
  },
  reg_alloc::{
    self,
    x86_register::{NamedReg, RegAbs86},
  },
};
use std::fmt::{Display, Error, Formatter};

use crate::assembly::VarSize;

use crate::reg_alloc::lifetime::UsesDefine;

use std::collections::HashSet;

use crate::const_params::CALLER_SHOULD_SAVE;

/// Variants of C0 runtime errors.
///
/// [todo] Optimize codegen err chk ctrl flow
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum C0RuntimeError {
  ArrayIndexOutOfBound,
  DerefNullPtr,
}

/// Operand. Can be either a temp, a constant, a named registers, or a
/// function argument.
/// __DO NOT put spill registers in!__
#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum Operand {
  Const(i128, DestSize),
  Var(Dest),
}

impl Operand {
  /// get size
  pub fn get_size(&self) -> DestSize {
    match self {
      Operand::Const(_, s) => *s,
      Operand::Var(d) => d.get_size(),
    }
  }

  pub fn incr_id(&self, id: u32) -> Operand {
    match self {
      Operand::Const(c, s) => Operand::Const(*c, *s),
      Operand::Var(d) => Operand::Var(d.incr_id(id)),
    }
  }
}

/// Operand designated to heap memory.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum HeapLocation {
  ConstAddr(usize),                            // _ <- src
  VarAddr(Dest),                               // _ <- (src)
  ScaleShort(usize, Dest),                     // _ <- Imm(Eb)
  ScaleFull(usize, Option<Dest>, Dest, usize), // _ <- Imm(Eb, Ei, s)
}

impl HeapLocation {
  /// Computes the uses of self.
  fn uses(&self) -> Vec<&Dest> {
    use HeapLocation::*;
    match self {
      ConstAddr(_) => vec![],
      VarAddr(d) | ScaleShort(_, d) | ScaleFull(_, None, d, _) => vec![d],
      ScaleFull(_, Some(d1), d2, _) => vec![d1, d2],
    }
  }

  pub fn incr_id(&self, id: u32) -> HeapLocation {
    use HeapLocation::*;
    match self {
      ConstAddr(c) => ConstAddr(*c),
      VarAddr(d) => VarAddr(d.incr_id(id)),
      ScaleShort(s, d) => ScaleShort(*s, d.incr_id(id)),
      ScaleFull(s1, d1, d2, s2) => {
        ScaleFull(*s1, d1.map(|d| d.incr_id(id)), d2.incr_id(id), *s2)
      }
    }
  }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum DestSize {
  quad,
  oct,
}

impl DestSize {
  /// Returns the raw `usize` representation of the size in question.
  pub fn raw(&self) -> usize {
    match self {
      DestSize::quad => 32,
      DestSize::oct => 64,
    }
  }

  pub fn to_var_size(&self) -> VarSize {
    match self {
      DestSize::quad => VarSize::V32,
      DestSize::oct => VarSize::V64,
    }
  }

  /// Converts destsize to apostrophie.
  pub fn to_apos(&self) -> &'static str {
    match self {
      DestSize::quad => "",
      DestSize::oct => "'",
    }
  }
}

/// Destination, which can be either a temp var, a named register, or
/// a function argument on stack.
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Dest {
  FnArgOnStack(usize, DestSize),
  R(NamedReg, DestSize),
  T(u32, DestSize),
}

/// Given the arity of a function, returns the list of uses, which shall be
/// either named registers or fn args on stack.
pub fn compute_uses_from_arity(arity: usize, size: DestSize) -> Vec<Dest> {
  let mut ret = Vec::<Dest>::new();
  for argpos in 0..arity {
    ret.push(Dest::from_nth_function_arg(argpos, size));
  }
  ret
}

impl Dest {
  /// Converts the `nth` (starting from `0`) fn arg to its corresponding dest.
  pub fn from_nth_function_arg(argpos: usize, size: DestSize) -> Self {
    match RegAbs86::from_nth_function_arg(argpos) {
      RegAbs86::FnArgOnStack(n) => Dest::FnArgOnStack(n, size),
      RegAbs86::Named(reg) => Dest::R(reg, size),
      RegAbs86::Spill(_) => unreachable!(),
    }
  }
  /// get a size from a dest.
  pub fn get_size(&self) -> DestSize {
    match self {
      Dest::FnArgOnStack(_, size) | Dest::R(_, size) | Dest::T(_, size) => {
        size.clone()
      }
    }
  }

  pub fn incr_id(&self, incr: u32) -> Self {
    match self {
      Dest::FnArgOnStack(..) => self.clone(),
      Dest::R(reg, size) => Dest::R(reg.clone(), size.clone()),
      Dest::T(id, size) => Dest::T(*id + incr, size.clone()),
    }
  }
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd)]
pub struct AsmLabel(pub u32);

impl AsmLabel {
  pub fn incr_id(&self, incr: u32) -> Self {
    AsmLabel(self.0 + incr)
  }
}
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
/// Abstract Assembly Instruction
pub enum Instr {
  BinOp {
    op: ast::BinOp,
    dest: Dest,
    src1: Operand,
    src2: Operand,
  },
  UnOp {
    op: ast::UnOp,
    dest: Dest,
    src: Operand,
  },
  Mov {
    dest: Dest,
    src: Operand,
  },
  /// Writes the content of the heap location to dest.
  MovFromHeap {
    dest: Dest,
    src: HeapLocation,
  },
  /// Loads effective address.
  LoadAddr {
    dest: Dest,
    src: HeapLocation,
  },
  /// Given the ptr to arr head, loads its length to dest.
  LoadArrLen {
    dest: Dest,
    arr_head_addr: Dest,
  },
  /// Writes source to the heap location as pointed to by dest.
  WriteToHeap {
    dest: Dest,
    src: Operand,
  },
  JmpCondition {
    condition: Dest,
    tgt_true: AsmLabel,
    tgt_false: AsmLabel,
  },
  Jmp(AsmLabel),
  Lbl(AsmLabel),
  FnLbl(String),
  FnCallSpillSize(usize, String),
  Push(Operand),
  Call(String, usize),

  // handles storing and restoring fn arg regs b4 fn calls.
  /// Store caller-saved registers, given function arity
  Store(usize),

  /// Restore caller-saved registers, given function arity
  Restore(usize),

  #[allow(dead_code)]
  NaiveCall(String, Vec<Dest>),

  IncrRsp(usize),
  Return(Operand),
  ReturnVoid,

  /// Chks nullptr, jmps to `panic branch` if null, to `end branch` otherwise.
  NullPtrChk {
    ptr: Dest,
    panic: AsmLabel,
    end: AsmLabel,
  },

  Panic(C0RuntimeError),
  Comment(String),

  /// Optimization instrs for ctrl flow
  Test(Dest),
  Cmp(Dest, Operand),
  JmpFlag(FlagTyp, AsmLabel, AsmLabel),
}

// Pretty Printing.

impl std::fmt::Debug for Dest {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.to_string())
  }
}

impl std::fmt::Display for AsmLabel {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(f, "L{}", self.0)
  }
}

impl std::fmt::Debug for AsmLabel {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(f, "L{}", self.0)
  }
}

impl Display for Operand {
  fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
    use Operand::*;
    match *self {
      Const(n, size) => write!(fmt, "${}{}", n, size.to_apos()),
      Var(d) => write!(fmt, "{}", d),
    }
  }
}

impl Display for HeapLocation {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    match self {
      HeapLocation::ConstAddr(addr) => write!(f, "{:16x}", addr),
      HeapLocation::VarAddr(x) => write!(f, "[{}]", x),
      HeapLocation::ScaleShort(offset, x) => write!(f, "{}[{}]", offset, x),
      HeapLocation::ScaleFull(offset, None, ei, x) => {
        write!(f, "{}[,{},{}]", offset, ei, x)
      }
      HeapLocation::ScaleFull(offset, Some(eb), ei, x) => {
        write!(f, "{}[{},{},{}]", offset, eb, ei, x)
      }
    }
  }
}

impl Display for Instr {
  fn fmt(&self, fmt: &mut Formatter) -> Result<(), Error> {
    match &*self {
      Instr::BinOp {
        op,
        dest,
        src1,
        src2,
      } => write!(fmt, "  {} <- {} {} {}", dest, src1, op, src2),
      Instr::UnOp { op, dest, src } => {
        write!(fmt, "  {} <- {}{}", dest, op, src)
      }
      Instr::Mov { dest, src } => write!(fmt, "  {} <- {}", dest, src),
      Instr::Return(dest) => write!(fmt, "  RET {}", dest),
      Instr::ReturnVoid => write!(fmt, "  RET void"),
      Instr::Jmp(lbl) => write!(fmt, "  goto {}", lbl),
      Instr::JmpCondition {
        condition,
        tgt_true,
        tgt_false,
      } => {
        write!(
          fmt,
          "  if {} then goto {} else goto {}",
          condition, tgt_true, tgt_false
        )
      }
      Instr::Lbl(n) => write!(fmt, "{}:", n),
      Instr::FnLbl(ref s) => write!(fmt, "<.{}>:", s),
      Instr::Call(ref s, _) => write!(fmt, "  call <.{}>", s),
      Instr::NaiveCall(ref s, ref args) => {
        write!(fmt, "  ncall {}({:?})", s, args)
      }
      Instr::Push(src) => write!(fmt, "  push {}", src),
      Instr::IncrRsp(n) => write!(fmt, "  %rsp += {}", n),
      Instr::FnCallSpillSize(n, fname) => {
        write!(fmt, "  fn call {} args spill size = {}", fname, n)
      }
      Instr::Store(arity) => write!(fmt, "  store {}", arity),
      Instr::Restore(arity) => write!(fmt, "  restore {}", arity),
      Instr::MovFromHeap { dest, src } => write!(fmt, "  {} <- {}", dest, src),
      Instr::LoadAddr { dest, src } => write!(fmt, "  {} <-lea- {}", dest, src),
      Instr::LoadArrLen {
        dest,
        arr_head_addr,
      } => write!(fmt, "  {} <- {}.len", dest, arr_head_addr),
      Instr::WriteToHeap { dest, src } => {
        write!(fmt, "  ({}) <- {}", dest, src)
      }
      Instr::Panic(p) => write!(fmt, "  panic({:?})", p),
      Instr::Comment(s) => write!(fmt, "  // {}", s),
      Instr::NullPtrChk { ptr, panic, end } => {
        write!(fmt, "  not_null({})? {} : {}", ptr, panic, end)
      }
      Instr::Test(x) => write!(fmt, "  test {}", x),
      Instr::Cmp(l, r) => write!(fmt, "  cmp {} vs {}", l, r),
      Instr::JmpFlag(fg, t, f) => write!(fmt, "  {} {}, {}", fg, t, f),
    }
  }
}

impl Instr {
  /// Computes the used and defined variables of instruction
  ///
  /// [warning] Division seems to overwrite %rsp according to Bob. Be aware!
  /// Add %rsp to 'define' if necessary.
  pub fn use_define(&self, optimize_level: usize) -> UsesDefine {
    let (mut uses_v, mut define_v) =
      (HashSet::<Dest>::new(), HashSet::<Dest>::new());

    match self {
      // binary op
      Instr::BinOp {
        op,
        dest,
        src1,
        src2,
      } => {
        define_v.insert(*dest);

        if let Operand::Var(d1) = src1 {
          uses_v.insert(*d1);
        }

        if let Operand::Var(d2) = src2 {
          uses_v.insert(*d2);
        }

        // division and mod via idivq
        if let ast::BinOp::Div | ast::BinOp::Mod = op {
          assert!(
            *src1 == Operand::Var(Dest::R(NamedReg::Rax, DestSize::quad))
          );
          uses_v.insert(Dest::R(NamedReg::Rdx, DestSize::quad)); // since rax is already used
          define_v.insert(Dest::R(NamedReg::Rdx, DestSize::quad));
          define_v.insert(Dest::R(NamedReg::Rax, DestSize::quad));
        }
      }

      // unary op
      Instr::UnOp { op: _, dest, src } => {
        define_v.insert(*dest);

        if let Operand::Var(d) = src {
          uses_v.insert(*d);
        }
      }

      // move
      // [TODO] Implement reg coalescing
      Instr::Mov { dest, src } => {
        define_v.insert(*dest);

        if let Operand::Var(d) = src {
          uses_v.insert(*d);
        }
      }
      Instr::WriteToHeap { dest, src } => {
        if let Operand::Var(d) = src {
          uses_v.insert(*d);
        }
        uses_v.insert(*dest);
      }

      Instr::Return(oprnd) => {
        if let Operand::Var(d) = oprnd {
          uses_v.insert(*d);
        }
      }

      // return void
      Instr::ReturnVoid => {
        // nothing is used nor defined
      }

      Instr::JmpCondition { condition, .. } => {
        uses_v.insert(*condition);
      }

      Instr::FnCallSpillSize(..) =>
        // nothing is used nor defined
        {}
      Instr::Push(oprnd) => {
        if let Operand::Var(d) = oprnd {
          uses_v.insert(*d);
        }
        if !REGALLOC_IGNORE_RSP {
          define_v.insert(Dest::R(NamedReg::Rsp, DestSize::oct));
        }
      }

      Instr::NaiveCall(..) => {
        if !NAIVE_FNCALL_DURING_CODEGEN {
          unreachable!()
        }
        unimplemented!()
      }

      Instr::Call(_, arity) => {
        if NAIVE_FNCALL_DURING_CODEGEN {
          unreachable!()
        }

        // the sizes don't matter here: they won't influence vargraph coloring.
        uses_v.extend(compute_uses_from_arity(*arity, DestSize::oct));
        define_v.insert(Dest::R(NamedReg::Rax, DestSize::oct));

        if !EXPLICIT_PUSH_POP_CALLER_SAVED_REGS {
          // in case of implicitly preserving caller-saved registers, we
          // might instead assume that all caller-saved registers are defined
          // across fncall.
          define_v.extend(
            CALLER_SHOULD_SAVE
              .iter()
              .map(|r| Dest::R(*r, DestSize::oct)),
          );
        }

        if !REGALLOC_IGNORE_RSP {
          define_v.insert(Dest::R(NamedReg::Rsp, DestSize::oct));
        }
      }

      Instr::IncrRsp(_) => {
        if !REGALLOC_IGNORE_RSP {
          uses_v.insert(Dest::R(NamedReg::Rsp, DestSize::oct));
          define_v.insert(Dest::R(NamedReg::Rsp, DestSize::oct));
        }
      }

      Instr::Store(_arity) => {
        if !EXPLICIT_PUSH_POP_CALLER_SAVED_REGS {
          unreachable!(
            "`Store` shall not exist without explicitly \
            saving caller-saved registers"
          )
        }

        if FNCALL_STORE_ALL_SIX_REGS {
          let more_uses = CALLER_SHOULD_SAVE
            .iter()
            .map(|r| Dest::R(*r, DestSize::oct));
          uses_v.extend(more_uses);
        } else {
          unimplemented!()
        }
      }

      Instr::Restore(_arity) => {
        if !EXPLICIT_PUSH_POP_CALLER_SAVED_REGS {
          unreachable!(
            "`Restore` shall not exist without explicitly \
            saving caller-saved registers"
          )
        }

        if FNCALL_STORE_ALL_SIX_REGS {
          let more_defines = CALLER_SHOULD_SAVE
            .iter()
            .map(|r| Dest::R(*r, DestSize::oct));
          define_v.extend(more_defines);
        } else {
          unimplemented!()
        }
      }

      Instr::LoadArrLen {
        dest,
        arr_head_addr,
      } => {
        define_v.insert(*dest);
        uses_v.insert(*arr_head_addr);
      }

      Instr::MovFromHeap { dest, src } | Instr::LoadAddr { dest, src } => {
        define_v.insert(*dest);
        uses_v.extend(src.uses());
      }

      Instr::NullPtrChk { ptr, .. } => {
        uses_v.insert(*ptr);
      }

      Instr::Test(d) => {
        uses_v.insert(*d);
      }

      Instr::Cmp(op1, op2) => {
        uses_v.insert(*op1);
        if let Operand::Var(d2) = op2 {
          uses_v.insert(*d2);
        }
      }

      Instr::Lbl(_)
      | Instr::Jmp(_)
      | Instr::FnLbl(_)
      | Instr::Panic(_)
      | Instr::Comment(_)
      | Instr::JmpFlag(..) => (),
    };

    return UsesDefine::new(uses_v, define_v, optimize_level);
  }

  #[allow(dead_code)]
  pub fn is_start_of_basic_block(&self) -> bool {
    match self {
      Self::FnLbl(_) | Self::Lbl(_) => true,
      _ => false,
    }
  }

  pub fn is_start_of_function(&self) -> bool {
    if let Self::FnLbl(_) = self {
      true
    } else {
      false
    }
  }
}

impl std::fmt::Display for Dest {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::T(n, s) => write!(f, "T{}{}", n, s.to_apos()),
      Self::R(r, s) => write!(f, "{}{}", r, s.to_apos()),
      Self::FnArgOnStack(n, s) => write!(f, "#{}{}", n, s.to_apos()),
    }
  }
}
