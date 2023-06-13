use crate::asm::{self, Dest, DestSize, HeapLocation, Instr, Operand};
use crate::assembly::{
  AssemblyLine, ImmNumber, MemRefReg, Memdef, RegX86, SignExtend, VarSize,
  X86Operand,
};
use crate::codegen::Context;

use super::asm_reg_to_assem::{
  asm_reg_to_assem, asm_reg_to_assem64, reg_size_convert,
};
use super::binop_convert;
use super::temp_to_reg;
use crate::args::Config;
use crate::asm_to_assem::asm_reg_to_assem::sign_extension_convert;
use crate::asm_to_assem::temp_to_reg::{reg_conversion, temp_to_node};
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

const LongSize: usize = 8;
const INT_MAX: i128 = 2147483647;
const DIRTY_HANDLE_OVERSIZE: bool = false;
const SIGUSR2: i32 = 12;
const SIGSEGV: i32 = 11;
const ALIGNMENT_DEBUG: bool = false;
const FNARGS: [X86Operand; 6] = [
  X86Operand::Reg(RegX86::Rdi(VarSize::V64)),
  X86Operand::Reg(RegX86::Rsi(VarSize::V64)),
  X86Operand::Reg(RegX86::Rdx(VarSize::V64)),
  X86Operand::Reg(RegX86::Rcx(VarSize::V64)),
  X86Operand::Reg(RegX86::R8(VarSize::V64)),
  X86Operand::Reg(RegX86::R9(VarSize::V64)),
];

#[allow(dead_code, non_snake_case)]
#[derive(Debug, Clone)]
pub struct Assemb {
  pub name: String,
  pub instrs: Vec<AssemblyLine>,
  pub done_function: bool,
  pub var_temp_map: HashMap<Node, RegAbs86>,
  pub used_caller_saved: Vec<X86Operand>, // caller saved registers is counted after reg_alloc
  pub used_callee_saved: Vec<X86Operand>, // callee saved registers is counted as using them
  pub spill_size: usize,
  pub fn_call_time_tmp_frame_size_including_fn_call_addr: usize,
  pub frame_size: usize,
  pub pushed_caller_saved_from_codegen: usize,
  pub pushed_arg_size: usize,
  pub codegen_caller_saved: Vec<X86Operand>,
  pub spilled_var_size: usize,
}

/// create a new imm of size 32 from i32
pub fn add_new_imm32(c: i32) -> ImmNumber {
  return ImmNumber {
    number: i128::try_from(c).unwrap(),
    size: VarSize::V32,
  };
}

pub fn add_new_imm64(c: i64) -> ImmNumber {
  return ImmNumber {
    number: i128::try_from(c).unwrap(),
    size: VarSize::V64,
  };
}

fn add_new_imm(c: i128, varsize: VarSize) -> ImmNumber {
  return ImmNumber {
    number: c,
    size: varsize,
  };
}

#[allow(dead_code, non_snake_case)]
impl Assemb {
  pub fn new(ctx: &Context) -> Self {
    Assemb {
      name: ctx.get_name().clone(),
      instrs: Vec::new(),
      done_function: false,
      var_temp_map: HashMap::new(),
      used_callee_saved: Vec::new(),
      used_caller_saved: Vec::new(),
      spill_size: 0,
      frame_size: 0,
      fn_call_time_tmp_frame_size_including_fn_call_addr: 0,
      pushed_caller_saved_from_codegen: 0,
      codegen_caller_saved: Vec::new(),
      pushed_arg_size: 0,
      spilled_var_size: 8,
    }
  }

  pub fn empty_assemb() -> Self {
    Assemb {
      name: String::new(),
      instrs: Vec::new(),
      done_function: false,
      var_temp_map: HashMap::new(),
      used_callee_saved: Vec::new(),
      used_caller_saved: Vec::new(),
      spill_size: 0,
      frame_size: 0,
      fn_call_time_tmp_frame_size_including_fn_call_addr: 0,
      pushed_caller_saved_from_codegen: 0,
      codegen_caller_saved: Vec::new(),
      pushed_arg_size: 0,
      spilled_var_size: 8,
    }
  }

  /// Adds a generic instruction.
  pub fn add_instr(&mut self, instr: AssemblyLine) {
    self.instrs.push(instr);
  }

  /// Adds sign-extended `mov` instruction.
  pub fn mov_se(&mut self, src: X86Operand, tgt: X86Operand, vsize: VarSize) {
    self.instrs.push(AssemblyLine::Mov(
      src,
      tgt,
      vsize,
      SignExtend::Sign(src.get_size(), tgt.get_size()),
    ));
  }

  /// Adds zero-extended `mov` instruction.
  pub fn mov_ze(&mut self, src: X86Operand, tgt: X86Operand, vsize: VarSize) {
    self.instrs.push(AssemblyLine::Mov(
      src,
      tgt,
      vsize,
      SignExtend::Zero(src.get_size(), tgt.get_size()),
    ));
  }

  /// Adds no-extended `mov` instruction. Elims self-moves.
  pub fn mov_ne(&mut self, src: X86Operand, tgt: X86Operand, vsize: VarSize) {
    if src != tgt {
      self
        .instrs
        .push(AssemblyLine::Mov(src, tgt, vsize, SignExtend::No));
    }
  }

  /// Similar to mov_ne, but possibly uses `r11`. Elims self-moves.
  pub fn mov_ne_r11(
    &mut self,
    src: X86Operand,
    tgt: X86Operand,
    vsize: VarSize,
  ) {
    if src != tgt {
      let src = if let X86Operand::Mem(..) = tgt {
        self.into_reg(&src, RegX86::R11(vsize))
      } else {
        src
      };
      self.mov_ne(src, tgt, vsize);
    }
  }

  /// convert return instruction
  fn return_instr(&mut self, dest: Option<&Operand>) -> () {
    if dest.is_some() {
      match *dest.unwrap() {
        Operand::Const(a, size) => {
          let varsize = size.to_var_size();
          self.instrs.push(AssemblyLine::Mov(
            X86Operand::Imm(add_new_imm(a, varsize)),
            RegX86::Rax(VarSize::V64).xop(),
            VarSize::V64,
            SignExtend::No,
          ));
        }
        Operand::Var(Dest::T(d, size)) => {
          let mov_line = AssemblyLine::Mov(
            self.memLocation(d, size.to_var_size()),
            X86Operand::Reg(RegX86::Rax(size.to_var_size())),
            size.to_var_size(),
            SignExtend::No,
          );
          self.instrs.push(mov_line);
          if (size.to_var_size() == VarSize::V32) {
            self.add_instr(AssemblyLine::Cltq);
          }
        }
        Operand::Var(Dest::R(d, size)) => {
          if d != NamedReg::Rax {
            if ALIGNMENT_DEBUG {
              println!(
                "returning register {:?}, size is not considered! should fix here? unsafe!",
                d
              );
            }
            self.instrs.push(AssemblyLine::Mov(
              asm_reg_to_assem(d, size.to_var_size()),
              X86Operand::Reg(RegX86::Rax(VarSize::V64)),
              VarSize::V64,
              SignExtend::No,
            ));
          }
        }
        Operand::Var(Dest::FnArgOnStack(..)) => {
          unreachable!("returning function argument")
        }
      }
    }
    let rsp_dec_amt = self.spill_size as i32;
    if rsp_dec_amt != 0 {
      self.add_instr(AssemblyLine::Add(
        X86Operand::Imm(add_new_imm32(rsp_dec_amt)),
        X86Operand::Reg(RegX86::Rsp(VarSize::V64)),
        VarSize::V64,
      ));
    }
    for reg in self.used_callee_saved.clone().into_iter().rev() {
      self.add_instr(AssemblyLine::Pop(reg, VarSize::V64));
    }
    self.add_instr(AssemblyLine::Ret);
  }

  fn function_started(&mut self) {
    // callee saving
    for reg in self.used_callee_saved.clone() {
      self.add_instr(AssemblyLine::Push(reg, VarSize::V64));
    }
    self.frame_size += self.used_callee_saved.len() * LongSize;
    if ALIGNMENT_DEBUG {
      eprintln!("dec rsp by {} due to frame size", self.spill_size);
    }
    self.frame_size += self.spill_size;
    let rsp_dec_amt = 0 - self.spill_size as i32;
    if rsp_dec_amt != 0 {
      self.add_instr(AssemblyLine::Add(
        X86Operand::Imm(add_new_imm32(rsp_dec_amt)),
        X86Operand::Reg(RegX86::Rsp(VarSize::V64)),
        VarSize::V64,
      ));
    }
  }

  fn function_call_ended(&mut self, spill_amt: usize) {
    // spill_amt is the amount of bytes that the function
    // call has spilled for its arguments
    let mut rsp_inc_amt = spill_amt as i32;
    let frame_size = self.fn_call_time_tmp_frame_size_including_fn_call_addr;
    let mut bias = 16 - ((frame_size % 16) as i32);
    if bias == 16 {
      bias = 0;
    }
    bias = -bias;
    rsp_inc_amt -= bias;
    if rsp_inc_amt > 0 {
      self.add_instr(AssemblyLine::Add(
        X86Operand::Imm(add_new_imm32(rsp_inc_amt)),
        X86Operand::Reg(RegX86::Rsp(VarSize::V64)),
        VarSize::V64,
      ));
    }
    if ALIGNMENT_DEBUG {
      eprintln!(
        "inc rsp by {} due to frame size, bias is {}",
        self.spill_size, bias
      );
    }
    self.pushed_caller_saved_from_codegen -= (0 - bias) as usize;
    self.pushed_arg_size = 0;
  }

  fn function_call_prepare_alignment(
    &mut self,
    spill_amt: usize,
    assembs: &HashMap<String, Assemb>,
    fname: &String,
  ) {
    // spilled_reg + spill_amt + spill size + pushed caller saved + fn_call_space
    self.fn_call_time_tmp_frame_size_including_fn_call_addr =
      spill_amt + self.frame_size + LongSize;
    let frame_size = self.fn_call_time_tmp_frame_size_including_fn_call_addr;
    let mut bias = 16 - ((frame_size % 16) as i32);
    if bias == 16 {
      bias = 0;
    }
    bias = -bias;
    // add bias into the frame size for function call
    // self.fn_call_time_tmp_frame_size_including_fn_call_addr += (0 - bias) as usize;

    if ALIGNMENT_DEBUG {
      eprintln!("fn call: {}", fname);
      eprintln!("spill_amt: {}", spill_amt);
      eprintln!("old frame_size: {}", self.frame_size);
      eprintln!(
        "frame size (should be a multiple of 16 when \'adding\' bias): {}",
        frame_size
      );
      eprintln!("bias: {}\n", bias);
    }
    if bias != 0 {
      self.add_instr(AssemblyLine::Add(
        X86Operand::Imm(add_new_imm32(bias)),
        X86Operand::Reg(RegX86::Rsp(VarSize::V64)),
        VarSize::V64,
      ));
      if ALIGNMENT_DEBUG {
        eprintln!("added bias");
      }
    }
    self.pushed_caller_saved_from_codegen += (0 - bias) as usize;
  }

  fn block_name_convert(&mut self, block_name: &String) -> String {
    format!("{}_label_{}", self.name.clone(), block_name.clone())
  }
  #[allow(dead_code, non_snake_case, unused_variables)]
  fn convert(&mut self, ins: &Instr, assembs: &HashMap<String, Assemb>) -> () {
    if DEBUG {
      self.instrs.push(AssemblyLine::DebugBinOp(ins.clone()));
    }
    match ins {
      Instr::Comment(_) => (),
      Instr::BinOp {
        op,
        dest,
        src1,
        src2,
      } => self.convert_binOp(&op, &dest, &src1, &src2),

      Instr::UnOp { op, dest, src } => self.convert_UnOp(op, &dest, &src),
      Instr::Mov { dest, src } => self.convert_move(&dest, &src),
      Instr::Return(dest) => self.return_instr(Some(dest)),
      Instr::ReturnVoid => self.return_instr(None),
      Instr::NullPtrChk { ptr, panic, end } => {
        use crate::const_params::FAST_NULLPTR_CHK;

        if !FAST_NULLPTR_CHK {
          unreachable!()
        }

        // [todo for bob] In case of T() and FnArgOnStack(),
        // writes it to %r11 before testing.
        let ptr_xop: X86Operand = match ptr {
          Dest::R(r, size) => asm_reg_to_assem(*r, size.to_var_size()),
          Dest::T(idx, size) => self.memLocation(*idx, size.to_var_size()),
          Dest::FnArgOnStack(pos, size) => {
            self.fnargsStackLocation(*pos, *size)
          }
        };

        let ptr_xop = match ptr_xop {
          X86Operand::Reg(r) => X86Operand::Reg(r),
          X86Operand::Mem(m, _) => {
            let r11 = X86Operand::Reg(RegX86::R11(VarSize::V64));
            self.add_instr(AssemblyLine::Mov(
              X86Operand::Mem(m, VarSize::V64),
              r11,
              VarSize::V64,
              SignExtend::No,
            ));
            r11
          }
          _ => unreachable!(),
        };

        // testq ptr, ptr
        self.add_instr(AssemblyLine::Test(ptr_xop, ptr_xop, VarSize::V64));

        // jne end_branch
        let end_branch = self.block_name_convert(&end.0.to_string());
        self.add_instr(AssemblyLine::Jne(end_branch));
      }
      Instr::JmpFlag(fg, _, tgt_false) => {
        use crate::codegen_elab2::FlagTyp::*;
        use AssemblyLine::*;

        let tgt = self.block_name_convert(&tgt_false.0.to_string());

        let line = match fg {
          Lt => Jl(tgt),
          Le => Jle(tgt),
          Ge => Jge(tgt),
          Gt => Jg(tgt),
          Eq => Je(tgt),
          Ne => Jne(tgt),
        };

        self.add_instr(line);
      }
      Instr::JmpCondition {
        condition,
        tgt_true,
        tgt_false,
      } => match condition {
        Dest::T(d, size) => {
          let cmp_line = AssemblyLine::Cmp(
            X86Operand::Imm(add_new_imm32(1)),
            self.memLocation(*d, size.to_var_size()),
            VarSize::V32,
          );
          self.add_instr(cmp_line);

          // let new_block_t = self.block_name_convert(&tgt_true.0.to_string());
          // self.add_instr(AssemblyLine::Je(new_block_t));

          let new_block_f = self.block_name_convert(&tgt_false.0.to_string());
          self.add_instr(AssemblyLine::Jne(new_block_f));
        }
        Dest::R(d, size) => {
          self.add_instr(AssemblyLine::Cmp(
            X86Operand::Imm(add_new_imm64(1)),
            asm_reg_to_assem(*d, size.to_var_size()),
            size.to_var_size(),
          ));
          // let new_block_t = self.block_name_convert(&tgt_true.0.to_string());
          // self.add_instr(AssemblyLine::Je(new_block_t));

          let new_block_f = self.block_name_convert(&tgt_false.0.to_string());
          self.add_instr(AssemblyLine::Jne(new_block_f));
        }
        Dest::FnArgOnStack(..) => unreachable!("JmpCondition on FnArgOnStack"),
      },
      Instr::Lbl(lbl) => {
        let new_block = self.block_name_convert(&lbl.0.to_string());
        self.add_instr(AssemblyLine::Block(new_block));
      }

      Instr::Jmp(lbl) => {
        let new_block = self.block_name_convert(&lbl.0.to_string());
        self.add_instr(AssemblyLine::Jmp(new_block))
      }
      Instr::Test(op) => match op {
        Dest::T(idx, size) => {
          let size = size.to_var_size();
          let x = self.memLocation(*idx, size);
          let x = self.into_reg(&x, RegX86::R11(size));
          self.add_instr(AssemblyLine::Test(x, x, size));
        }
        Dest::R(d, size) => {
          let size = size.to_var_size();
          let x = asm_reg_to_assem(*d, size);
          self.add_instr(AssemblyLine::Test(x, x, size));
        }
        Dest::FnArgOnStack(..) => unreachable!(),
      },
      Instr::Cmp(l, r) => {
        self.cmp(l, r);
      }
      Instr::Call(fn_name, fn_arg_count) => {
        if MAC {
          if fn_name == "main" {
            self.add_instr(AssemblyLine::Call("__c0_main".to_string()));
            return;
          }
          if fn_name == "c0_assert" {
            self.add_instr(AssemblyLine::Call("__c0_assert".to_string()));
            return;
          }
          if fn_name == "calloc" {
            self.add_instr(AssemblyLine::Call("_calloc".to_string()));
            return;
          }
          if fn_name == "checksum"
            || fn_name == "init"
            || fn_name == "prepare"
            || fn_name == "run"
          {
            let new_name =
              format!("{}{}", "__c0_".to_owned(), fn_name.to_owned());
            self.add_instr(AssemblyLine::Call(new_name));
            return;
          }
          if assembs.get(fn_name).is_some() {
            let new_name =
              format!("{}{}", "_c0_".to_owned(), fn_name.to_owned());
            self.add_instr(AssemblyLine::Call(new_name.clone()));
            return;
          } else {
            let new_name = format!("{}{}", "_".to_owned(), fn_name.to_owned());
            self.add_instr(AssemblyLine::Call(new_name.clone()));
            return;
          }
        }

        if fn_name == "main" {
          self.add_instr(AssemblyLine::Call("_c0_main".to_string()));
          return;
        }
        if fn_name == "c0_assert" {
          self.add_instr(AssemblyLine::Call("_c0_assert".to_string()));
          return;
        }
        if fn_name == "calloc" {
          self.add_instr(AssemblyLine::Call("calloc".to_string()));
          return;
        }
        if fn_name == "checksum"
          || fn_name == "init"
          || fn_name == "prepare"
          || fn_name == "run"
        {
          let new_name = format!("{}{}", "_c0_".to_owned(), fn_name.to_owned());
          self.add_instr(AssemblyLine::Call(new_name));
          return;
        }
        if assembs.get(fn_name).is_some() {
          let new_name = format!("{}{}", "_c0_".to_owned(), fn_name.to_owned());
          self.add_instr(AssemblyLine::Call(new_name.clone()));
          return;
        } else {
          let new_name = format!("{}{}", "".to_owned(), fn_name.to_owned());
          self.add_instr(AssemblyLine::Call(new_name.clone()));
        }
      }

      Instr::Push(src) => match src {
        Operand::Const(a, size) => {
          let varsize = size.to_var_size();
          self.add_instr(AssemblyLine::Push(
            X86Operand::Imm(add_new_imm(*a, varsize)),
            varsize,
          ));
        }
        Operand::Var(Dest::T(d, size)) => {
          let being_pushed = self.memLocation(*d, size.to_var_size());
          match being_pushed {
            X86Operand::Mem(_, VarSize::V32) => {
              self.add_instr(AssemblyLine::Mov(
                being_pushed.clone(),
                X86Operand::Reg(RegX86::R11(VarSize::V64)),
                VarSize::V64,
                SignExtend::Sign(VarSize::V32, VarSize::V64),
              ));
              self.add_instr(AssemblyLine::Push(
                X86Operand::Reg(RegX86::R11(VarSize::V64)),
                VarSize::V64,
              ));
            }
            X86Operand::Mem(_, VarSize::V64) => {
              self.add_instr(AssemblyLine::Push(
                being_pushed.clone(),
                VarSize::V64,
              ));
            }
            X86Operand::Mem(_, _) => {
              unreachable!("Shall not have mem with size other than 32 or 64")
            }
            X86Operand::Reg(_) => {
              let converted_being_pushed =
                reg_size_convert(being_pushed, VarSize::V64);
              let push_line =
                AssemblyLine::Push(converted_being_pushed, VarSize::V64);
              self.add_instr(push_line);
            }
            _ => unreachable!(
              "Pushing something that is not a register or memory location"
            ),
          }
          self.pushed_arg_size += LongSize;
        }
        Operand::Var(Dest::R(d, size)) => {
          self.add_instr(AssemblyLine::Push(
            asm_reg_to_assem64(*d),
            size.to_var_size(),
          ));
        }
        Operand::Var(Dest::FnArgOnStack(..)) => {
          unreachable!("Push FnArgOnStack")
        }
      },
      Instr::FnLbl(name) => {
        self.add_instr(AssemblyLine::FnDefn(name.clone()));
        if ALIGNMENT_DEBUG {
          println!("Working on Function name: {}", name);
        }
        self.function_started()
      }
      Instr::NaiveCall(..) => {
        unreachable!("NaiveCall should not be in the codegen")
      }
      Instr::IncrRsp(amt) => self.function_call_ended(*amt),
      Instr::FnCallSpillSize(amt, fname) => {
        self.function_call_prepare_alignment(*amt, assembs, fname)
      }
      Instr::Store(arity) => {
        unreachable!("Store should not be in the codegen");
        let mut unsaved_caller_saved = self.used_caller_saved.clone();
        let index = cmp::min(6, *arity);
        for i in 0..index {
          let arg = FNARGS[i].clone();
          self.add_instr(AssemblyLine::Push(arg.clone(), VarSize::V64));
          self.frame_size += LongSize;
          self.pushed_caller_saved_from_codegen += LongSize;
          if let Some(index) =
            unsaved_caller_saved.iter().position(|x| *x == arg)
          {
            unsaved_caller_saved.remove(index);
          }
        }
        for reg in unsaved_caller_saved {
          self.add_instr(AssemblyLine::Push(reg.clone(), VarSize::V64));
          self.frame_size += LongSize;
          self.pushed_caller_saved_from_codegen += LongSize;
        }
      }

      Instr::Restore(arity) => {
        unreachable!("Restore should not be in the codegen");
        let mut unrestored_caller_saved = self.used_caller_saved.clone();
        let index = cmp::min(6, *arity);
        for i in 0..index {
          let arg = FNARGS[i].clone();
          if let Some(index) =
            unrestored_caller_saved.iter().position(|x| *x == arg)
          {
            unrestored_caller_saved.remove(index);
          }
        }
        for reg in unrestored_caller_saved.into_iter().rev() {
          self.add_instr(AssemblyLine::Pop(reg.clone(), VarSize::V64));
          self.frame_size -= LongSize;
          self.pushed_caller_saved_from_codegen -= LongSize;
        }

        for i in (0..index).rev() {
          let arg = FNARGS[i].clone();
          self.add_instr(AssemblyLine::Pop(arg.clone(), VarSize::V64));
          self.frame_size -= LongSize;
          self.pushed_caller_saved_from_codegen -= LongSize;
        }
      }
      Instr::MovFromHeap { dest, src } => {
        let mut r10_inuse = false;
        let mut r11_inuse = false;
        let assSource: X86Operand = match src {
          HeapLocation::ConstAddr(size) => {
            unreachable!(
              "C0 should not have a constant address moving from heap"
            );
          }
          HeapLocation::VarAddr(d) => match d {
            Dest::FnArgOnStack(..) => {
              unreachable!("MovFromHeap to FnArgOnStack")
            }
            Dest::R(d, size) => X86Operand::Mem(
              Memdef {
                imm: 0,
                reg1: MemRefReg {
                  reg: Some(reg_conversion(*d, VarSize::V64)),
                },
                reg2: MemRefReg { reg: None },
                scale: 1,
              },
              size.to_var_size(),
            ),
            Dest::T(i, size) => {
              let addr = self.memLocation(*i, size.to_var_size());
              match addr {
                X86Operand::Mem(memdef, varsize) => {
                  self.add_instr(AssemblyLine::Mov(
                    X86Operand::Mem(memdef, varsize),
                    X86Operand::Reg(RegX86::R10(VarSize::V64)),
                    varsize,
                    SignExtend::No,
                  ));
                  r10_inuse = true;
                  X86Operand::Mem(
                    Memdef {
                      imm: 0,
                      reg1: MemRefReg {
                        reg: Some(RegX86::R10(VarSize::V64)),
                      },
                      reg2: MemRefReg { reg: None },
                      scale: 1,
                    },
                    size.to_var_size(),
                  )
                }
                X86Operand::Reg(reg) => X86Operand::Mem(
                  Memdef {
                    imm: 0,
                    reg1: MemRefReg { reg: Some(reg) },
                    reg2: MemRefReg { reg: None },
                    scale: 1,
                  },
                  size.to_var_size(),
                ),
                _ => {
                  unreachable!("Shall not have a constant address as a temp")
                }
              }
            }
          },
          HeapLocation::ScaleShort(offset, dest1) => {
            let (tmpidx, size) = match dest1 {
              Dest::FnArgOnStack(..) => {
                unreachable!("MovFromHeap to FnArgOnStack")
              }
              Dest::R(d, size) => {
                unreachable!(
                  "C0 scaleshort should not have a register as a dest"
                )
              }
              Dest::T(i, size) => (i, size),
            };
            let tmp_operand =
              match self.memLocation(*tmpidx, size.to_var_size()) {
                X86Operand::Mem(memdef, varsize) => {
                  self.add_instr(AssemblyLine::Mov(
                    X86Operand::Mem(memdef, size.to_var_size()),
                    X86Operand::Reg(RegX86::R10(VarSize::V64)),
                    varsize,
                    SignExtend::No,
                  ));
                  r10_inuse = true;
                  RegX86::R10(VarSize::V64)
                }
                X86Operand::Reg(reg) => reg.to_size(VarSize::V64),
                X86Operand::Imm(..) => {
                  unreachable!("C0 scaleshort should not have a imm as a dest")
                }
              };
            X86Operand::Mem(
              Memdef {
                imm: *offset as i128,
                reg1: MemRefReg { reg: None },
                reg2: MemRefReg {
                  reg: Some(tmp_operand),
                },
                scale: 1,
              },
              VarSize::V64,
            )
            // The varsize here is inaccurate,it need to be updated later
          }
          HeapLocation::ScaleFull(imm, reg1, reg2, scale) => {
            let reg1 = match reg1 {
              None => None,
              Some(Dest::FnArgOnStack(..)) => {
                unreachable!("MovFromHeap to FnArgOnStack for ScaleFull")
              }
              Some(Dest::R(d, size)) => {
                Some(reg_conversion(*d, size.to_var_size()))
              }
              Some(Dest::T(i, size)) => {
                match self.memLocation(*i, size.to_var_size()) {
                  X86Operand::Mem(memdef, varsize) => {
                    self.add_instr(AssemblyLine::Mov(
                      X86Operand::Mem(memdef, size.to_var_size()),
                      X86Operand::Reg(RegX86::R10(VarSize::V64)),
                      varsize,
                      SignExtend::No,
                    ));
                    r10_inuse = true;
                    Some(RegX86::R10(VarSize::V64))
                  }
                  X86Operand::Reg(reg) => Some(reg.to_size(VarSize::V64)),
                  X86Operand::Imm(..) => {
                    unreachable!(
                      "C0 ScaleFull reg1 should not have a imm as a dest"
                    )
                  }
                }
              }
            };
            let r11d = X86Operand::Reg(RegX86::R11(VarSize::V32));
            let reg2 = match reg2 {
              Dest::FnArgOnStack(..) => {
                unreachable!(
                  "MovFromHeap to FnArgOnStack for ScaleFull for reg2"
                )
              }
              Dest::R(d, size) => {
                let reg = reg_conversion(*d, size.to_var_size());
                self.add_instr(AssemblyLine::Mov(
                  X86Operand::Reg(reg),
                  X86Operand::Reg(RegX86::R11(VarSize::V64)),
                  VarSize::V64,
                  SignExtend::Sign(VarSize::V32, VarSize::V64),
                ));

                self.add_instr(AssemblyLine::Imul(
                  X86Operand::Imm(add_new_imm64(*scale as i64)),
                  X86Operand::Reg(RegX86::R11(VarSize::V64)),
                  VarSize::V64,
                ));
                RegX86::R11(VarSize::V64)
              }
              Dest::T(i, size) => {
                match self.memLocation(*i, size.to_var_size()) {
                  X86Operand::Mem(memdef, varsize) => {
                    self.add_instr(AssemblyLine::Mov(
                      X86Operand::Mem(memdef, VarSize::V32),
                      r11d,
                      VarSize::V32,
                      SignExtend::No,
                    ));
                    r11_inuse = true;
                    self.add_instr(AssemblyLine::Imul(
                      X86Operand::Imm(add_new_imm64(*scale as i64)),
                      X86Operand::Reg(RegX86::R11(VarSize::V64)),
                      VarSize::V64,
                    ));
                    RegX86::R11(VarSize::V64)
                  }
                  X86Operand::Reg(reg) => {
                    self.add_instr(AssemblyLine::Mov(
                      X86Operand::Reg(reg),
                      X86Operand::Reg(RegX86::R11(VarSize::V64)),
                      VarSize::V64,
                      SignExtend::Sign(VarSize::V32, VarSize::V64),
                    ));

                    self.add_instr(AssemblyLine::Imul(
                      X86Operand::Imm(add_new_imm64(*scale as i64)),
                      X86Operand::Reg(RegX86::R11(VarSize::V64)),
                      VarSize::V64,
                    ));
                    RegX86::R11(VarSize::V64)
                  }
                  X86Operand::Imm(..) => {
                    unreachable!(
                      "C0 ScaleFull reg2 should not have a imm as a dest"
                    )
                  }
                }
              }
            };

            X86Operand::Mem(
              Memdef {
                imm: *imm as i128,
                reg1: MemRefReg { reg: reg1 },
                reg2: MemRefReg { reg: Some(reg2) },
                scale: 1,
              },
              VarSize::V64,
            )
            // varsize unspecified, but since we are doing a move, we know what we want
          }
        };
        assert!(
          match assSource {
            X86Operand::Mem(..) => true,
            _ => false,
          },
          "move from fake heap"
        );
        match dest {
          Dest::T(d, size) => {
            let assDest: X86Operand = self.memLocation(*d, size.to_var_size());
            match assDest {
              X86Operand::Reg(reg) => {
                self.add_instr(AssemblyLine::Mov(
                  assSource,
                  X86Operand::Reg(reg),
                  reg.get_size(),
                  SignExtend::No,
                ));
              }
              X86Operand::Mem(memdef, varsize) => {
                self.add_instr(AssemblyLine::Mov(
                  assSource,
                  X86Operand::Reg(RegX86::R10(varsize)),
                  varsize,
                  SignExtend::No,
                ));
                self.add_instr(AssemblyLine::Mov(
                  X86Operand::Reg(RegX86::R10(varsize)),
                  X86Operand::Mem(memdef, varsize),
                  varsize,
                  SignExtend::No,
                ));
              }
              X86Operand::Imm(..) => {
                unreachable!("C0 MoveFromHeap should not have a imm as a dest")
              }
            }
          }
          Dest::R(d, size) => {
            let dest = asm_reg_to_assem(*d, size.to_var_size());
            self.add_instr(AssemblyLine::Mov(
              assSource,
              dest,
              size.to_var_size(),
              SignExtend::No,
            ));
          }
          Dest::FnArgOnStack(..) => unreachable!("MovFromHeap to FnArgOnStack"),
        }
      }
      Instr::Panic(_) => {
        self.add_instr(AssemblyLine::Mov(
          X86Operand::Imm(add_new_imm32(SIGUSR2)),
          X86Operand::Reg(RegX86::Rdi(VarSize::V64)),
          VarSize::V64,
          SignExtend::No,
        ));

        self.add_instr(AssemblyLine::Jmp("system_panic".to_string()));
      }

      Instr::LoadArrLen {
        dest,
        arr_head_addr,
      } => {
        let mut r11_inuse = false;
        let assSource: X86Operand = match arr_head_addr {
          Dest::T(i, size) => {
            assert!(
              size.to_var_size() == VarSize::V64,
              "LoadArrLen from T with size != 64!"
            );
            let head = self.memLocation(*i, size.to_var_size());
            let head = match head {
              X86Operand::Mem(memdef, varsize) => {
                assert!(
                  varsize == VarSize::V64,
                  "LoadArrLen from Mem with size != 64"
                );
                self.add_instr(AssemblyLine::Mov(
                  X86Operand::Mem(memdef, size.to_var_size()),
                  X86Operand::Reg(RegX86::R11(varsize)),
                  varsize,
                  SignExtend::No,
                ));
                r11_inuse = true;

                RegX86::R11(varsize)
              }
              X86Operand::Reg(reg) => reg,
              X86Operand::Imm(..) => {
                unreachable!(
                  "C0 LoadArrLen should not have a imm as a arr head"
                )
              }
            };
            X86Operand::Mem(
              Memdef {
                imm: -8,
                reg1: MemRefReg { reg: Some(head) },
                reg2: MemRefReg { reg: None },
                scale: 0,
              },
              VarSize::V64,
            )
          }
          Dest::R(r, size) => unreachable!(
            "LoadArrLen from R ({}), and you should not load from named reg",
            r
          ),
          Dest::FnArgOnStack(..) => {
            unreachable!("LoadArrLen from FnArgOnStack")
          }
        };
        match dest {
          Dest::T(d, size) => {
            assert!(
              size.to_var_size() == VarSize::V32,
              "LoadArrLen to T with size != 32!"
            );
            let assDest: X86Operand = self.memLocation(*d, size.to_var_size());
            match assDest {
              X86Operand::Reg(reg) => {
                self.add_instr(AssemblyLine::Mov(
                  assSource,
                  X86Operand::Reg(reg),
                  reg.get_size(),
                  SignExtend::No,
                ));
              }
              X86Operand::Mem(memdef, varsize) => {
                if r11_inuse {
                  self.add_instr(AssemblyLine::Mov(
                    assSource,
                    X86Operand::Reg(RegX86::R10(varsize)),
                    varsize,
                    SignExtend::No,
                  ));
                  self.add_instr(AssemblyLine::Mov(
                    X86Operand::Reg(RegX86::R10(varsize)),
                    X86Operand::Mem(memdef, varsize),
                    varsize,
                    SignExtend::No,
                  ));
                } else {
                  self.add_instr(AssemblyLine::Mov(
                    assSource,
                    X86Operand::Reg(RegX86::R11(varsize)),
                    varsize,
                    SignExtend::No,
                  ));
                  self.add_instr(AssemblyLine::Mov(
                    X86Operand::Reg(RegX86::R11(varsize)),
                    X86Operand::Mem(memdef, varsize),
                    varsize,
                    SignExtend::No,
                  ));
                }
              }
              X86Operand::Imm(..) => {
                unreachable!("C0 LoadArrLen should not have a imm as a dest")
              }
            }
          }
          Dest::R(d, size) => {
            let dest = asm_reg_to_assem(*d, size.to_var_size());
            self.add_instr(AssemblyLine::Mov(
              assSource,
              dest,
              size.to_var_size(),
              SignExtend::No,
            ));
          }
          Dest::FnArgOnStack(..) => unreachable!("LoadArrLen to FnArgOnStack"),
        }
      }
      Instr::WriteToHeap { dest, src } => {
        let mut r10_inuse = false;
        let mut r11_inuse = false;
        let mut varsize = VarSize::V64;
        let assSource = match src {
          Operand::Var(d) => {
            match d {
              Dest::T(i, size) => {
                let assSource: X86Operand =
                  self.memLocation(*i, size.to_var_size());
                varsize = size.to_var_size();
                match assSource {
                  X86Operand::Reg(reg) => X86Operand::Reg(reg),
                  X86Operand::Mem(memdef, varsize) => {
                    self.add_instr(AssemblyLine::Mov(
                      assSource,
                      X86Operand::Reg(RegX86::R10(varsize)),
                      varsize,
                      SignExtend::No,
                    ));
                    r10_inuse = true;
                    X86Operand::Reg(RegX86::R10(varsize))
                  }
                  X86Operand::Imm(..) => {
                    let varsize = VarSize::V64; // not clearified number here
                    self.add_instr(AssemblyLine::Mov(
                      assSource,
                      X86Operand::Reg(RegX86::R10(varsize)),
                      varsize,
                      SignExtend::No,
                    ));
                    r10_inuse = true;
                    X86Operand::Reg(RegX86::R10(varsize))
                  }
                }
              }
              Dest::R(d, size) => {
                varsize = size.to_var_size();
                asm_reg_to_assem(*d, size.to_var_size())
              }
              Dest::FnArgOnStack(..) => {
                unreachable!("WriteToHeap from FnArgOnStack")
              }
            }
          }
          Operand::Const(c, size) => {
            let varsize = size.to_var_size();
            X86Operand::Imm(add_new_imm(*c, varsize.clone()))
          }
        };
        let mut assDest_register_conflict = false;
        let assDest = match dest {
          Dest::T(i, size) => {
            let assDest: X86Operand = self.memLocation(*i, size.to_var_size());
            match assDest {
              X86Operand::Reg(reg) => X86Operand::Mem(
                Memdef {
                  imm: 0,
                  reg1: MemRefReg { reg: Some(reg) },
                  reg2: MemRefReg { reg: None },
                  scale: 1,
                },
                varsize.clone(),
              ),
              X86Operand::Mem(memdef, varsize) => {
                assDest_register_conflict = true;
                assDest.clone()
              }
              X86Operand::Imm(..) => {
                let varsize = VarSize::V64; // not clearified number here
                self.add_instr(AssemblyLine::Mov(
                  assDest,
                  X86Operand::Reg(RegX86::R11(varsize)),
                  varsize,
                  SignExtend::No,
                ));
                r11_inuse = true;
                X86Operand::Reg(RegX86::R11(varsize))
              }
            }
          }
          Dest::R(d, size) => {
            let reg = reg_conversion(*d, size.to_var_size());
            X86Operand::Mem(
              Memdef {
                imm: 0,
                reg1: MemRefReg { reg: Some(reg) },
                reg2: MemRefReg { reg: None },
                scale: 1,
              },
              size.to_var_size(),
            )
          }
          Dest::FnArgOnStack(..) => unreachable!("WriteToHeap to FnArgOnStack"),
        };
        if assDest_register_conflict {
          self.add_instr(AssemblyLine::Mov(
            assDest,
            X86Operand::Reg(RegX86::R11(VarSize::V64)),
            VarSize::V64,
            SignExtend::No,
          ));
          let new_assDest = X86Operand::Mem(
            Memdef {
              imm: 0,
              reg1: MemRefReg {
                reg: Some(RegX86::R11(VarSize::V64)),
              },
              reg2: MemRefReg { reg: None },
              scale: 1,
            },
            VarSize::V32,
          );
          self.add_instr(AssemblyLine::Mov(
            assSource,
            new_assDest,
            varsize,
            SignExtend::No,
          ));
        } else {
          self.add_instr(AssemblyLine::Mov(
            assSource,
            assDest,
            varsize,
            SignExtend::No,
          ));
        }
      }
      Instr::LoadAddr { dest, src } => {
        let mut r10_inuse = false;
        let mut r11_inuse = false;
        // assSource should be mem
        let assSource: X86Operand = match src {
          HeapLocation::ConstAddr(size) => {
            self.add_instr(AssemblyLine::Mov(
              X86Operand::Imm(add_new_imm(*size as i128, VarSize::V64)),
              X86Operand::Reg(RegX86::R10(VarSize::V64)),
              VarSize::V64,
              SignExtend::No,
            ));
            r10_inuse = true;
            X86Operand::Mem(
              Memdef {
                imm: *size as i128,
                reg1: MemRefReg {
                  reg: Some(RegX86::R10(VarSize::V64)),
                },
                reg2: MemRefReg { reg: None },
                scale: 1,
              },
              VarSize::V64,
            )
          }
          HeapLocation::VarAddr(d) => match d {
            Dest::FnArgOnStack(..) => {
              unreachable!("MovFromHeap to FnArgOnStack")
            }
            Dest::R(d, size) => X86Operand::Mem(
              Memdef {
                imm: 0,
                reg1: MemRefReg {
                  reg: Some(reg_conversion(*d, VarSize::V64)),
                },
                reg2: MemRefReg { reg: None },
                scale: 1,
              },
              size.to_var_size(),
            ),
            Dest::T(i, size) => {
              let addr = self.memLocation(*i, size.to_var_size());
              match addr {
                X86Operand::Mem(memdef, varsize) => {
                  self.add_instr(AssemblyLine::Mov(
                    X86Operand::Mem(memdef, varsize),
                    X86Operand::Reg(RegX86::R10(VarSize::V64)),
                    varsize,
                    SignExtend::No,
                  ));
                  r10_inuse = true;
                  X86Operand::Mem(
                    Memdef {
                      imm: 0,
                      reg1: MemRefReg {
                        reg: Some(RegX86::R10(VarSize::V64)),
                      },
                      reg2: MemRefReg { reg: None },
                      scale: 1,
                    },
                    VarSize::V64,
                  )
                }
                X86Operand::Reg(reg) => X86Operand::Mem(
                  Memdef {
                    imm: 0,
                    reg1: MemRefReg {
                      reg: Some(reg.to_size(VarSize::V64)),
                    },
                    reg2: MemRefReg { reg: None },
                    scale: 1,
                  },
                  size.to_var_size(),
                ),
                _ => {
                  unreachable!("Shall not have a constant address as a temp")
                }
              }
            }
          },
          HeapLocation::ScaleShort(offset, dest1) => {
            let offset_operand = match dest1 {
              Dest::R(r, size) => reg_conversion(*r, size.to_var_size()),
              Dest::T(tmpidx, size) => match self
                .memLocation(*tmpidx, size.to_var_size())
              {
                X86Operand::Mem(memdef, varsize) => {
                  let r10 = RegX86::R10(varsize);

                  self.mov_ne(
                    memdef.xop(size.to_var_size()),
                    r10.xop(),
                    varsize,
                  );
                  r10_inuse = true;

                  r10
                }
                X86Operand::Reg(reg) => reg,
                X86Operand::Imm(..) => {
                  unreachable!("C0 scaleshort should not have a imm as a dest")
                }
              },
              Dest::FnArgOnStack(stack_arg_num, size) => {
                let stack_arg_xop =
                  self.fnargsStackLocation(*stack_arg_num, *size);
                let op_size = stack_arg_xop.get_size();
                let r10 = RegX86::R10(op_size);

                self.mov_ne(stack_arg_xop, r10.xop(), op_size);
                r10_inuse = true;

                r10
              }
            };

            // offset(, E_i, 1)
            Memdef::build(*offset, None, Some(offset_operand), 1).xop_64()
            // The varsize here is inaccurate,it need to be updated later
          }
          HeapLocation::ScaleFull(imm, reg1, reg2, scale) => {
            let r11_32 = RegX86::R11(VarSize::V32);
            let r11_64 = RegX86::R11(VarSize::V64);
            let r10_64 = RegX86::R10(VarSize::V64);

            let reg1 = match reg1 {
              None => None,
              Some(Dest::FnArgOnStack(..)) => {
                unreachable!("MovFromHeap to FnArgOnStack for ScaleFull")
              }
              Some(Dest::R(d, size)) => {
                Some(reg_conversion(*d, size.to_var_size()))
              }
              Some(Dest::T(i, size)) => {
                match self.memLocation(*i, size.to_var_size()) {
                  X86Operand::Mem(memdef, varsize) => {
                    self.mov_ne(
                      memdef.xop(size.to_var_size()),
                      r10_64.xop(),
                      varsize,
                    );
                    r10_inuse = true;
                    Some(r10_64)
                  }
                  X86Operand::Reg(reg) => Some(reg.to_size(VarSize::V64)),
                  X86Operand::Imm(..) => {
                    unreachable!(
                      "C0 ScaleFull reg1 should not have a imm as a dest"
                    )
                  }
                }
              }
            };

            // fetch reg2 of ScaleFull to r11.
            let reg2 = match reg2 {
              Dest::FnArgOnStack(..) => {
                unreachable!(
                  "MovFromHeap to FnArgOnStack for ScaleFull for reg2"
                )
              }
              Dest::R(d, size) => {
                let reg = reg_conversion(*d, VarSize::V64);
                if let 1 | 2 | 4 | 8 = scale {
                  reg // register will not be modified, can directly use.
                } else {
                  self.mov_ne(reg.xop(), r11_64.xop(), VarSize::V64);
                  r11_64
                }
              }
              Dest::T(i, size) => {
                match self.memLocation(*i, size.to_var_size()) {
                  X86Operand::Mem(memdef, varsize) => {
                    // [owen] Index is always 32bit in c0.
                    self.mov_ne(memdef.xop_32(), r11_32.xop(), VarSize::V32);
                    self.mov_se(r11_32.xop(), r11_64.xop(), VarSize::V64);

                    r11_inuse = true;
                    r11_64
                  }
                  X86Operand::Reg(reg) => {
                    if let 1 | 2 | 4 | 8 = scale {
                      reg.to_size(VarSize::V64) // similarly, can directly use.
                    } else {
                      self.mov_se(reg.xop(), r11_64.xop(), VarSize::V64);
                      r11_64
                    }
                  }
                  X86Operand::Imm(..) => {
                    unreachable!(
                      "C0 ScaleFull reg2 should not have a imm as a dest"
                    )
                  }
                }
              }
            };

            let imm_ub = (u32::MAX as usize);

            let new_scale = if let 1 | 2 | 4 | 8 = scale {
              *scale as i128
            } else if *scale > imm_ub {
              let (div, remainder) = (*scale / imm_ub, *scale % imm_ub);
              let div_op = X86Operand::Imm(add_new_imm64(div as i64));
              let mod_op = X86Operand::Imm(add_new_imm64(remainder as i64));
              let imm_ub_op = X86Operand::Imm(add_new_imm64(imm_ub as i64));

              self.mov_ne(imm_ub_op, r11_64.xop(), VarSize::V64);
              self.add_instr(AssemblyLine::Imul(
                div_op,
                r11_64.xop(),
                VarSize::V64,
              ));
              self.add_instr(AssemblyLine::Add(
                mod_op,
                r11_64.xop(),
                VarSize::V64,
              ));
              1
            } else {
              let scale_op = X86Operand::Imm(add_new_imm64(*scale as i64));
              self.add_instr(AssemblyLine::Imul(
                scale_op,
                r11_64.xop(),
                VarSize::V64,
              ));
              1
            };

            Memdef::build(*imm, reg1, Some(reg2), new_scale).xop_64()
          }
        };
        assert!(
          match assSource {
            X86Operand::Mem(..) => true,
            _ => false,
          },
          "move from fake heap"
        );
        match dest {
          Dest::T(d, size) => {
            let assDest: X86Operand = self.memLocation(*d, size.to_var_size());
            match assDest {
              X86Operand::Reg(reg) => {
                self.add_instr(AssemblyLine::Lea(
                  assSource,
                  reg.xop(),
                  reg.get_size(),
                ));
              }
              X86Operand::Mem(memdef, varsize) => {
                let r10_vs = RegX86::R10(varsize);
                self.add_instr(AssemblyLine::Lea(
                  assSource,
                  r10_vs.xop(),
                  varsize,
                ));
                self.mov_ne(r10_vs.xop(), memdef.xop(varsize), varsize);
              }
              X86Operand::Imm(..) => unreachable!(),
            }
          }
          Dest::R(d, size) => {
            let dest = asm_reg_to_assem(*d, size.to_var_size());
            self.mov_ne(assSource, dest, size.to_var_size());
          }
          Dest::FnArgOnStack(..) => unreachable!("MovFromHeap to FnArgOnStack"),
        }
      }
    }
  }

  /// Makes comparison.
  pub fn cmp(&mut self, lhs: &Dest, rhs: &Operand) {
    let lhs_op = match lhs {
      Dest::T(idx, size) => self.memLocation(*idx, size.to_var_size()),
      Dest::R(r, size) => asm_reg_to_assem(*r, size.to_var_size()),
      _ => unreachable!(),
    };

    let rhs_op = match rhs {
      Operand::Var(Dest::T(idx, size)) => {
        self.memLocation(*idx, size.to_var_size())
      }
      Operand::Var(Dest::R(r, size)) => {
        asm_reg_to_assem(*r, size.to_var_size())
      }
      Operand::Const(c, size) => {
        X86Operand::Imm(add_new_imm(*c, size.to_var_size()))
      }
      Operand::Var(_) => unreachable!(),
    };

    binop_convert::cmp_sources_v32(self, &lhs_op, &rhs_op);
  }

  /// get location of memory
  pub fn locationCalc(&mut self, pos: u32) -> i32 {
    if ALIGNMENT_DEBUG {
      println!("locationCalc: {} -> pushed_arg_size {} pushed_caller_saved_from_codegen {} spilled_var_size {} ",
       pos, self.pushed_arg_size, self.pushed_caller_saved_from_codegen, self.spilled_var_size);
    }
    (self.pushed_arg_size as i32
      + self.pushed_caller_saved_from_codegen as i32
      + (pos as i32) * (self.spilled_var_size as i32)) as i32
  }

  /// Given some `n`, calculates the stack location of the `n`th function
  /// argument on stack (ie. the `n+6`th argument, if counting begins with 0.)
  pub fn fnargsStackLocation(
    &mut self,
    pos: usize,
    size: DestSize,
  ) -> X86Operand {
    // frame size + return location + 8 * (pos + 1)
    let bias = self.frame_size + LongSize + (pos) * LongSize;
    if ALIGNMENT_DEBUG {
      println!("fnargsStackLocation: {} -> {}", pos, bias);
    }

    let rsp_64 = RegX86::Rsp(VarSize::V64);

    Memdef::build(bias, Some(rsp_64), None, 1).xop_32()
  }

  /// Get memory location of temp
  pub fn memLocation(&mut self, tmpNumber: u32, size: VarSize) -> X86Operand {
    let n: Node = temp_to_node(tmpNumber.clone());
    let assign = self.var_temp_map.get(&n);
    match assign {
      Some(RegAbs86::Named(r)) => {
        let reg = asm_reg_to_assem(*r, size.clone());
        reg
      }
      // Spill size should be handled
      Some(RegAbs86::Spill(m)) => {
        let bias = self.locationCalc(*m as u32);
        X86Operand::Mem(
          Memdef {
            imm: bias as i128,
            reg1: MemRefReg {
              reg: Some(RegX86::Rsp(VarSize::V64)),
            },
            reg2: MemRefReg { reg: None },
            scale: 1,
          },
          size.clone(),
        )
      }
      Some(RegAbs86::FnArgOnStack(_)) => {
        panic!("FnArgOnStack should not be on this function stack")
      }
      None => {
        while (true) {
          let i = 2;
        }
        panic!("No assign for temp {}", tmpNumber);
      }
    }
  }

  /// Converts some `Dest` instance to `X86Operand`.
  fn dest_to_x86op(&mut self, dest: Dest) -> X86Operand {
    match dest {
      Dest::T(d, size) => self.memLocation(d, size.to_var_size()),
      Dest::R(d, size) => asm_reg_to_assem(d, size.to_var_size()),
      Dest::FnArgOnStack(pos, size) => self.fnargsStackLocation(pos, size),
    }
  }

  fn move_x86_reg_to_dest(&mut self, &dest: &Dest, assSource: &X86Operand) {
    let assSource = assSource.clone();
    let dest_size = dest.get_size();
    let src_size = assSource.get_size();
    match dest {
      Dest::T(d, size) => {
        let dest_size = size.to_var_size();
        let assDest = self.memLocation(d, size.to_var_size());
        if assDest == assSource {
          return;
        }
        match assDest {
          X86Operand::Reg(_) => {
            if dest_size > src_size {
              self.add_instr(AssemblyLine::Mov(
                assSource,
                assDest,
                dest_size,
                SignExtend::Zero(src_size.clone(), dest_size.clone()),
              ))
            } else if src_size > dest_size {
              self.add_instr(AssemblyLine::Mov(
                assSource.to_size(dest_size.clone()),
                assDest,
                dest_size,
                SignExtend::No,
              ))
            } else {
              self.add_instr(AssemblyLine::Mov(
                assSource,
                assDest,
                dest_size,
                SignExtend::No,
              ))
            }
          }
          _ => {
            if dest_size > src_size {
              self.add_instr(AssemblyLine::Mov(
                assSource,
                X86Operand::Reg(RegX86::R11(dest_size.clone())),
                dest_size,
                SignExtend::Zero(src_size.clone(), dest_size.clone()),
              ))
            } else if src_size > dest_size {
              self.add_instr(AssemblyLine::Mov(
                assSource.to_size(dest_size.clone()),
                X86Operand::Reg(RegX86::R11(dest_size.clone())),
                dest_size,
                SignExtend::No,
              ))
            } else {
              self.add_instr(AssemblyLine::Mov(
                assSource,
                X86Operand::Reg(RegX86::R11(dest_size.clone())),
                dest_size,
                SignExtend::No,
              ));
            }
            self.instrs.push(AssemblyLine::Mov(
              X86Operand::Reg(RegX86::R11(dest_size)),
              assDest,
              dest_size,
              SignExtend::No,
            ))
          }
        }
      }
      Dest::R(d, size) => {
        let assDest = asm_reg_to_assem(d, size.to_var_size());
        let dest_size = size.to_var_size();
        if dest_size > src_size {
          self.add_instr(AssemblyLine::Mov(
            assSource,
            assDest,
            dest_size,
            SignExtend::Zero(src_size.clone(), dest_size.clone()),
          ))
        } else if src_size > dest_size {
          self.add_instr(AssemblyLine::Mov(
            assSource.to_size(dest_size.clone()),
            assDest,
            dest_size,
            SignExtend::No,
          ))
        } else {
          self.add_instr(AssemblyLine::Mov(
            assSource,
            assDest,
            dest_size,
            SignExtend::No,
          ))
        }
      }
      Dest::FnArgOnStack(i, size) => {
        let assDest = self.fnargsStackLocation(i, size);
        match (assSource, assDest) {
          (X86Operand::Mem(..), X86Operand::Mem(..)) => {
            self.instrs.push(AssemblyLine::Mov(
              assSource,
              X86Operand::Reg(RegX86::R11(VarSize::V32)),
              VarSize::V32,
              SignExtend::No,
            ));
            self.instrs.push(AssemblyLine::Mov(
              X86Operand::Reg(RegX86::R11(VarSize::V32)),
              assDest,
              VarSize::V32,
              SignExtend::No,
            ));
          }
          _ => {
            self.instrs.push(AssemblyLine::Mov(
              assSource,
              assDest,
              VarSize::V32,
              SignExtend::No,
            ));
          }
        }
      }
    }
  }

  fn convert_move(&mut self, &dest: &Dest, &src: &Operand) {
    match src {
      Operand::Const(c, size) => {
        let varsize = dest.get_size().to_var_size();
        let mov_line = AssemblyLine::Mov(
          X86Operand::Imm(add_new_imm(c, varsize)),
          self.dest_to_x86op(dest),
          varsize,
          SignExtend::No,
        );
        self.instrs.push(mov_line)
      }
      Operand::Var(Dest::T(d, size)) => {
        let assSource = self.memLocation(d, size.to_var_size());
        let src_size = size.to_var_size();
        self.move_x86_reg_to_dest(&dest, &assSource);
      }
      Operand::Var(Dest::R(d, size)) => {
        let assSource = asm_reg_to_assem(d, size.to_var_size());
        let src_size = size.to_var_size();
        if src_size == VarSize::V32 {
          self.move_x86_reg_to_dest(&dest, &assSource);
        } else {
          let assDest = self.dest_to_x86op(dest);
          self.push_Operand_to_Operand(
            &assSource,
            &assDest.to_size(VarSize::V64),
          );
        }
      }
      Operand::Var(Dest::FnArgOnStack(i, size)) => {
        let assSource = self.fnargsStackLocation(i, size);
        let assDest = self.dest_to_x86op(dest);
        let dest_size = dest.get_size().to_var_size();
        match (assSource, assDest) {
          (X86Operand::Mem(..), X86Operand::Mem(..)) => {
            self.instrs.push(AssemblyLine::Mov(
              assSource,
              X86Operand::Reg(RegX86::R11(dest_size)),
              dest_size,
              SignExtend::No,
            ));
            self.instrs.push(AssemblyLine::Mov(
              X86Operand::Reg(RegX86::R11(dest_size)),
              assDest,
              dest_size,
              SignExtend::No,
            ));
          }
          _ => {
            self.instrs.push(AssemblyLine::Mov(
              assSource,
              assDest,
              dest_size,
              SignExtend::No,
            ));
          }
        }
      }
    };
  }

  /// check if both are mem
  pub fn X86Operand_conflict(s1: X86Operand, s2: X86Operand) -> bool {
    match (s1, s2) {
      (X86Operand::Mem(..), X86Operand::Mem(..)) => true,
      (X86Operand::Mem(..), X86Operand::Imm(..)) => true,
      _ => false,
    }
  }

  /// if x is `X86Operand::Reg` variant, then returns x as-is; else,
  /// move the value to the specified register `backup_reg` and returns it.
  fn into_reg(&mut self, x: &X86Operand, backup_reg: RegX86) -> X86Operand {
    if x.is_reg() {
      x.clone()
    } else {
      let x_size = x.get_size();
      let backup_reg = backup_reg.xop();

      self.mov_ne(x.clone(), backup_reg, x_size);
      backup_reg
    }
  }

  /// If the given `X86Operand::Reg` is over multiplication-limit, truncate;
  /// else, return as-is.
  fn truncate_large_const_for_mul(x: X86Operand) -> X86Operand {
    match x {
      X86Operand::Imm(c) => {
        let num = c.get_number();
        if num > 4611686018427387900 {
          X86Operand::Imm(ImmNumber {
            number: 0,
            size: VarSize::V64,
          })
        } else {
          x
        }
      }
      _ => x,
    }
  }

  fn convert_binOp_const_and_temp(
    &mut self,
    assSource1: &X86Operand,
    assSource2: &X86Operand,
    assDest: &X86Operand,
    op: &BinOp,
  ) {
    let r11_8 = RegX86::R11(VarSize::V8);
    let size = assSource2.get_size();
    assert_eq!(size, assSource1.get_size());
    let r11_size = RegX86::R11(size);

    match *op {
      // comparison case
      BinOp::Lt | BinOp::Le | BinOp::Ge | BinOp::Gt | BinOp::Eq | BinOp::Ne => {
        let assSource1 = if assSource2.is_reg() {
          *assSource1
        } else {
          self.into_reg(assSource1, r11_size)
        };

        // x86 does not allow second arg to be const, so we need to swap the
        // ordering here...
        self.add_instr(AssemblyLine::Cmp(assSource1, assSource2.clone(), size));

        // ... and flip the flags back. this is ugly...
        match op {
          BinOp::Gt => self.add_instr(AssemblyLine::Setl(r11_8.xop())),
          BinOp::Ge => self.add_instr(AssemblyLine::Setle(r11_8.xop())),
          BinOp::Le => self.add_instr(AssemblyLine::Setge(r11_8.xop())),
          BinOp::Lt => self.add_instr(AssemblyLine::Setg(r11_8.xop())),
          BinOp::Eq => self.add_instr(AssemblyLine::Sete(r11_8.xop())),
          BinOp::Ne => self.add_instr(AssemblyLine::Setne(r11_8.xop())),
          _ => unreachable!(),
        }

        binop_convert::r11v8_to_dest(self, assDest);
      }

      // num op
      BinOp::Add | BinOp::Sub => {
        todo!()
      }

      BinOp::Mul => {
        let dest_size = assDest.get_size();

        let assSource1 = Self::truncate_large_const_for_mul(*assSource1);

        let assSource1 = if assSource2.is_reg() {
          assSource1
        } else {
          self.into_reg(&assSource1, r11_size)
        };

        unimplemented!()

        // if assDest.is_reg() {
        //   if assSource2 != assDest {
        //     // d <- s1
        //     self.push_Operand_to_Operand(assSource1, assDest);
        //     // mult d by s2
        //     self.instrs.push(AssemblyLine::Imul(
        //       assSource2.clone(),
        //       assDest.clone(),
        //       assDest.get_size(),
        //     ));
        //   } else {
        //     // d <- s2
        //     self.push_Operand_to_Operand(assSource2, assDest);
        //     // mult d by s1
        //     self.instrs.push(AssemblyLine::Imul(
        //       assSource1.clone(),
        //       assDest.clone(),
        //       assDest.get_size(),
        //     ));
        //   }
        // } else {
        //   let r11 = X86Operand::Reg(RegX86::R11(VarSize::V32));
        //   // d <- s1 * s2
        //   // s1 -> r11
        //   self.push_Operand_to_Operand(assSource1, &r11);
        //   // mult r11 by s2
        //   self.instrs.push(AssemblyLine::Imul(
        //     assSource2.clone(),
        //     r11.clone(),
        //     VarSize::V32,
        //   ));
        //   // move rax to d
        //   self.push_Operand_to_Operand(&r11, assDest);
        // }
      }

      // bool op
      BinOp::And | BinOp::Or | BinOp::Xor => {
        todo!()
      }

      // shift case
      BinOp::Shl | BinOp::Shr => {
        unreachable!("shift with const should not have made it here")
      }

      // divmod case
      BinOp::Div | BinOp::Mod => {
        unreachable!("divmod with const should not have made it here")
      }

      // impossible case
      BinOp::AAnd | BinOp::OOr => {
        unreachable!("Shortcut binop shouldn't be here")
      }
    }
  }

  fn convert_binOp_temp_and_const(
    &mut self,
    assSource1: &X86Operand,
    assSource2: &X86Operand,
    assDest: &X86Operand,
    op: &BinOp,
  ) {
    let r11_8 = RegX86::R11(VarSize::V8);
    let size = assSource2.get_size();

    // mult with const on rhs can have some lhs: 32 and rhs: 64 due to
    // arr idx arithmetic.
    assert!(
      (size == assSource1.get_size()) | (*op == BinOp::Mul),
      "{}",
      op
    );
    let r11_size = RegX86::R11(size);

    match *op {
      // comparison case
      BinOp::Lt | BinOp::Le | BinOp::Ge | BinOp::Gt | BinOp::Eq | BinOp::Ne => {
        let assSource2 = if assSource1.is_reg() {
          *assSource2
        } else {
          self.into_reg(assSource2, r11_size)
        };

        self.add_instr(AssemblyLine::Cmp(assSource2, assSource1.clone(), size));

        match op {
          BinOp::Lt => self.add_instr(AssemblyLine::Setl(r11_8.xop())),
          BinOp::Le => self.add_instr(AssemblyLine::Setle(r11_8.xop())),
          BinOp::Ge => self.add_instr(AssemblyLine::Setge(r11_8.xop())),
          BinOp::Gt => self.add_instr(AssemblyLine::Setg(r11_8.xop())),
          BinOp::Eq => self.add_instr(AssemblyLine::Sete(r11_8.xop())),
          BinOp::Ne => self.add_instr(AssemblyLine::Setne(r11_8.xop())),
          _ => unreachable!(),
        }

        binop_convert::r11v8_to_dest(self, assDest);
      }

      BinOp::Mul => {
        let dest_size = assDest.get_size();
        let assSource2 = match assSource2 {
          X86Operand::Imm(c) => {
            let num = c.get_number();
            if num > 4611686018427387900 {
              &X86Operand::Imm(ImmNumber {
                number: 0,
                size: VarSize::V64,
              })
            } else {
              assSource2
            }
          }
          _ => assSource2,
        };
        if assDest.is_reg() {
          if assSource2 != assDest {
            self.push_Operand_to_Operand(assSource1, assDest);
            self.instrs.push(AssemblyLine::Imul(
              assSource2.clone(),
              assDest.clone(),
              assDest.get_size(),
            ));
          } else {
            self.push_Operand_to_Operand(assSource2, assDest);
            self.instrs.push(AssemblyLine::Imul(
              assSource1.clone(),
              assDest.clone(),
              assDest.get_size(),
            ));
          }
        } else {
          let r11 = X86Operand::Reg(RegX86::R11(VarSize::V32));
          // d <- s1 * s2
          // s1 -> rax
          self.push_Operand_to_Operand(assSource1, &r11);
          // mult rax by s2
          self.instrs.push(AssemblyLine::Imul(
            assSource2.clone(),
            r11.clone(),
            VarSize::V32,
          ));
          // move rax to d
          self.push_Operand_to_Operand(&r11, assDest);
        }
      }

      BinOp::Add => {
        let size = assSource1.get_size();
        assert!(size == assDest.get_size());

        let num = match assSource2 {
          X86Operand::Imm(c1) => c1.get_number(),
          _ => panic!("convert_binOp_temp_and_const's dest should be a constant"),
        };

        if num > INT_MAX {
          let assSource2_new = &X86Operand::Reg(RegX86::R11(size));
          self.push_Operand_to_Operand(assSource2, assSource2_new);
          let assSource2 = assSource2_new;
          binop_convert::add_v64(self, assSource1, assSource2, assDest)
        } else {
          self.mov_ne_r11(*assSource1, *assDest, size);
          self.add_instr(AssemblyLine::Add(*assSource2, *assDest, size));
          // binop_convert::add_v64(self, assSource1, assSource2, assDest)
        }
      }

      BinOp::Sub => {
        let size = assSource1.get_size();
        assert!(size == assDest.get_size());

        let num = match assSource2 {
          X86Operand::Imm(c1) => c1.get_number(),
          _ => unreachable!("assSource2 is not a const"),
        };

        self.mov_ne_r11(*assSource1, *assDest, size);
        self.add_instr(AssemblyLine::Sub(*assSource2, *assDest, size));
      }

      _ => panic!(
        "{}",
        format!(
          "convert_binOp_temp_and_const does not support op other than Lt and Ge 
      which appeared in Shl and Shr, got {}",
          op
        )
        .to_string()
      ),
    }
  }

  fn convert_binOp_const_and_const(
    &mut self,
    &a: &i128,
    &b: &i128,
    assDest: X86Operand,
    op: &BinOp,
  ) {
    let c: i128 = match op {
      // num arithmetic
      ast::BinOp::Add => a + b,
      ast::BinOp::Sub => a - b,
      ast::BinOp::Mul => a * b,
      ast::BinOp::Div => a / b,
      ast::BinOp::Mod => a % b,

      // comparison
      ast::BinOp::Eq => (a == b).into(),
      ast::BinOp::Ne => (a != b).into(),
      ast::BinOp::Lt => (a < b).into(),
      ast::BinOp::Le => (a <= b).into(),
      ast::BinOp::Ge => (a >= b).into(),
      ast::BinOp::Gt => (a > b).into(),

      // bitwise arithmetic
      ast::BinOp::And => a & b,
      ast::BinOp::Or => a | b,
      ast::BinOp::Xor => a ^ b,

      ast::BinOp::AAnd | ast::BinOp::OOr => {
        unreachable!("shall gone after codegen")
      }

      shift => todo!("shift must go through safemode check!"),
    };
    self.instrs.push(AssemblyLine::Mov(
      X86Operand::Imm(add_new_imm(c, VarSize::V32)),
      assDest,
      VarSize::V32,
      SignExtend::No,
    ))
  }

  fn push_int_to_register(&mut self, i: i128, reg: RegX86) {
    self.instrs.push(AssemblyLine::Mov(
      X86Operand::Imm(add_new_imm(i, VarSize::V32)),
      X86Operand::Reg(reg),
      VarSize::V64,
      SignExtend::No,
    ))
  }

  pub fn push_int_to_Operand(&mut self, i: i32, operand: &X86Operand) {
    self.instrs.push(AssemblyLine::Mov(
      X86Operand::Imm(add_new_imm32(i)),
      operand.clone(),
      VarSize::V64,
      SignExtend::No,
    ))
  }

  /// not well formed
  fn push_mem_to_register(&mut self, mem: &Memdef, reg: RegX86) {
    self.instrs.push(AssemblyLine::Mov(
      X86Operand::Mem(mem.clone(), VarSize::V32),
      X86Operand::Reg(reg),
      VarSize::V64,
      SignExtend::No,
    ))
  }

  fn push_Operand_to_register_v64(
    &mut self,
    operand: &X86Operand,
    reg: RegX86,
  ) {
    self.instrs.push(AssemblyLine::Mov(
      operand.clone(),
      X86Operand::Reg(reg),
      VarSize::V64,
      SignExtend::No,
    ))
  }

  fn push_Operand_to_register(&mut self, operand: &X86Operand, reg: RegX86) {
    self.instrs.push(AssemblyLine::Mov(
      operand.clone(),
      X86Operand::Reg(reg),
      reg.get_size(),
      sign_extension_convert(operand, &X86Operand::Reg(reg)),
    ))
  }

  ///warning: operand should not be im,
  fn push_register_to_operand(&mut self, reg: RegX86, dest: &X86Operand) {
    self.instrs.push(AssemblyLine::Mov(
      X86Operand::Reg(reg),
      dest.clone(),
      VarSize::V64,
      SignExtend::No,
    ))
  }

  fn push_register_to_mem(&mut self, reg: RegX86, mem: &Memdef) {
    self.instrs.push(AssemblyLine::Mov(
      X86Operand::Reg(reg),
      X86Operand::Mem(mem.clone(), reg.get_size()),
      reg.get_size(),
      SignExtend::No,
    ))
  }

  pub fn push_Operand_to_Operand(
    &mut self,
    source: &X86Operand,
    dest: &X86Operand,
  ) {
    if *source == *dest {
      return;
    }

    match (*source, *dest) {
      (X86Operand::Mem(..), X86Operand::Mem(destMem, size)) => {
        self.push_Operand_to_register(source, RegX86::R11(size));
        self.push_register_to_mem(RegX86::R11(size), &destMem)
      }
      (_, _) => self.instrs.push(AssemblyLine::Mov(
        source.clone(),
        dest.clone(),
        dest.get_size(),
        sign_extension_convert(source, dest),
      )),
    }
  }

  /// Convert a binOp where one is a temp the other is temp memory
  /// Should be updated later
  fn convert_binOp_temp_and_temp(
    &mut self,
    assSource1: &X86Operand,
    assSource2: &X86Operand,
    assDest: &X86Operand,
    op: &BinOp,
  ) {
    let assDest = &assDest.to_size(VarSize::V32);
    let r11 = X86Operand::Reg(RegX86::R11(VarSize::V32));
    match op {
      // d <- s1 + s2
      ast::BinOp::Add => {
        binop_convert::add_v32(self, assSource1, assSource2, assDest)
      }
      ast::BinOp::Sub => {
        binop_convert::sub_v22(self, assSource1, assSource2, assDest);
      }
      ast::BinOp::Mul => {
        if assDest.is_reg() {
          if assSource2 != assDest {
            self.push_Operand_to_Operand(assSource1, assDest);
            self.instrs.push(AssemblyLine::Imul(
              assSource2.clone(),
              assDest.clone(),
              VarSize::V32,
            ));
          } else {
            self.push_Operand_to_Operand(assSource2, assDest);
            self.instrs.push(AssemblyLine::Imul(
              assSource1.clone(),
              assDest.clone(),
              VarSize::V32,
            ));
          }
        } else {
          let r11 = X86Operand::Reg(RegX86::R11(VarSize::V32));
          // d <- s1 * s2
          // s1 -> rax
          self.push_Operand_to_Operand(assSource1, &r11);
          // mult rax by s2
          self.instrs.push(AssemblyLine::Imul(
            assSource2.clone(),
            r11.clone(),
            VarSize::V32,
          ));
          // move rax to d
          self.push_Operand_to_Operand(&r11, assDest);
        }
      }
      ast::BinOp::Div => {
        // rdx <- 0
        //s1 to rax
        self.push_Operand_to_Operand(
          assSource1,
          &X86Operand::Reg(RegX86::Rax(VarSize::V32)),
        );
        //sign extend
        self.instrs.push(AssemblyLine::Cltd);
        if assSource2.is_reg() {
          self
            .instrs
            .push(AssemblyLine::Idiv(assSource2.clone(), VarSize::V32));
        } else {
          self.push_Operand_to_register(assSource2, RegX86::R11(VarSize::V32));
          self
            .instrs
            .push(AssemblyLine::Idiv(r11.clone(), VarSize::V32));
        }
        //move from rax
        self.push_Operand_to_Operand(
          &X86Operand::Reg(RegX86::Rax(VarSize::V32)),
          assDest,
        );
      }
      ast::BinOp::Mod => {
        // d <- s1 % s2

        // rdx <- 0
        //s1 to rax
        self.push_Operand_to_Operand(
          assSource1,
          &X86Operand::Reg(RegX86::Rax(VarSize::V32)),
        );
        //sign extend
        self.instrs.push(AssemblyLine::Cltd);
        if assSource2.is_reg() {
          self
            .instrs
            .push(AssemblyLine::Idiv(assSource2.clone(), VarSize::V32));
        } else {
          self.push_Operand_to_register(assSource2, RegX86::R11(VarSize::V32));
          self
            .instrs
            .push(AssemblyLine::Idiv(r11.clone(), VarSize::V32));
        }
        // move rdx to d
        self.instrs.push(AssemblyLine::Mov(
          X86Operand::Reg(RegX86::Rdx(VarSize::V32)),
          assDest.clone(),
          VarSize::V32,
          SignExtend::No,
        ))
      }
      // d <- a < b
      ast::BinOp::Lt => {
        binop_convert::cmp_sources_v32(self, assSource1, assSource2);
        self.add_instr(AssemblyLine::Setl(X86Operand::Reg(RegX86::R11(
          VarSize::V8,
        ))));
        binop_convert::r11v8_to_dest(self, assDest);
      }
      // d <- a <= b
      BinOp::Le => {
        binop_convert::cmp_sources_v32(self, assSource1, assSource2);
        self.add_instr(AssemblyLine::Setle(X86Operand::Reg(RegX86::R11(
          VarSize::V8,
        ))));
        binop_convert::r11v8_to_dest(self, assDest);
      }
      // d <- a > b
      BinOp::Gt => {
        binop_convert::cmp_sources_v32(self, assSource1, assSource2);
        self.add_instr(AssemblyLine::Setg(X86Operand::Reg(RegX86::R11(
          VarSize::V8,
        ))));
        binop_convert::r11v8_to_dest(self, assDest);
      }
      // d <- a >= b
      BinOp::Ge => {
        binop_convert::cmp_sources_v32(self, assSource1, assSource2);
        self.add_instr(AssemblyLine::Setge(X86Operand::Reg(RegX86::R11(
          VarSize::V8,
        ))));
        binop_convert::r11v8_to_dest(self, assDest);
      }
      // d <- a == b
      BinOp::Eq => {
        let size = assSource1.get_size();
        assert!(
          assSource1.get_size() == assSource2.get_size(),
          "size mismatch for eq!"
        );
        if Self::X86Operand_conflict(*assSource1, *assSource2) {
          self.add_instr(AssemblyLine::Mov(
            assSource1.clone(),
            X86Operand::Reg(RegX86::R11(size)),
            size,
            SignExtend::No,
          ));
          self.add_instr(AssemblyLine::Cmp(
            assSource2.clone(),
            X86Operand::Reg(RegX86::R11(size)),
            size,
          ));
          self.add_instr(AssemblyLine::Sete(X86Operand::Reg(RegX86::R11(
            VarSize::V8,
          ))));
        } else {
          self.add_instr(AssemblyLine::Cmp(
            assSource2.clone(),
            assSource1.clone(),
            size,
          ));
          self.add_instr(AssemblyLine::Sete(X86Operand::Reg(RegX86::R11(
            VarSize::V8,
          ))));
        }
        binop_convert::r11v8_to_dest(self, assDest);
      }
      // d <- a != b
      BinOp::Ne => {
        let size = assSource1.get_size();
        assert!(
          assSource1.get_size() == assSource2.get_size(),
          "size mismatch for eq!"
        );
        if Self::X86Operand_conflict(*assSource1, *assSource2) {
          self.add_instr(AssemblyLine::Mov(
            assSource1.clone(),
            X86Operand::Reg(RegX86::R11(size)),
            size,
            SignExtend::No,
          ));
          self.add_instr(AssemblyLine::Cmp(
            assSource2.clone(),
            X86Operand::Reg(RegX86::R11(size)),
            size,
          ));
          self.add_instr(AssemblyLine::Setne(X86Operand::Reg(RegX86::R11(
            VarSize::V8,
          ))));
        } else {
          self.add_instr(AssemblyLine::Cmp(
            assSource2.clone(),
            assSource1.clone(),
            size,
          ));
          self.add_instr(AssemblyLine::Setne(X86Operand::Reg(RegX86::R11(
            VarSize::V8,
          ))));
        }
        binop_convert::r11v8_to_dest(self, assDest);
      }
      // d <- a && b
      BinOp::AAnd => {
        if assDest.is_reg() {
          if assSource1 != assDest {
            self.push_Operand_to_Operand(assSource2, assDest);
            self.add_instr(AssemblyLine::And(
              assSource1.clone(),
              assDest.clone(),
              VarSize::V32,
            ));
          } else {
            self.push_Operand_to_Operand(assSource1, assDest);
            self.add_instr(AssemblyLine::And(
              assSource2.clone(),
              assDest.clone(),
              VarSize::V32,
            ));
          }
          self.add_instr(AssemblyLine::Mov(
            assDest.to_size(VarSize::V8),
            assDest.to_size(VarSize::V32),
            VarSize::V32,
            SignExtend::Zero(VarSize::V8, VarSize::V32),
          ));
        } else {
          let r11 = X86Operand::Reg(RegX86::R11(VarSize::V32));
          self.push_Operand_to_Operand(assSource2, &r11);
          self.add_instr(AssemblyLine::And(
            assSource1.clone(),
            r11.clone(),
            VarSize::V32,
          ));
          binop_convert::r11v8_to_dest(self, assDest);
        }
      }

      // d <- a || b
      BinOp::OOr => {
        if assDest.is_reg() {
          if assSource1 != assDest {
            self.push_Operand_to_Operand(assSource2, assDest);
            self.add_instr(AssemblyLine::Or(
              assSource1.clone(),
              assDest.clone(),
              VarSize::V32,
            ));
          } else {
            self.push_Operand_to_Operand(assSource1, assDest);
            self.add_instr(AssemblyLine::Or(
              assSource2.clone(),
              assDest.clone(),
              VarSize::V32,
            ));
          }
          self.add_instr(AssemblyLine::Mov(
            assDest.to_size(VarSize::V8),
            assDest.to_size(VarSize::V32),
            VarSize::V32,
            SignExtend::Zero(VarSize::V8, VarSize::V32),
          ));
        } else {
          let r11 = X86Operand::Reg(RegX86::R11(VarSize::V32));
          self.push_Operand_to_Operand(assSource2, &r11);
          self.add_instr(AssemblyLine::Or(
            assSource1.clone(),
            r11.clone(),
            VarSize::V32,
          ));
          binop_convert::r11v8_to_dest(self, assDest)
        }
      }
      BinOp::And => {
        if assDest.is_reg() {
          if assSource1 != assDest {
            self.push_Operand_to_Operand(assSource2, assDest);
            self.add_instr(AssemblyLine::And(
              assSource1.clone(),
              assDest.clone(),
              VarSize::V32,
            ));
          } else {
            self.push_Operand_to_Operand(assSource1, assDest);
            self.add_instr(AssemblyLine::And(
              assSource2.clone(),
              assDest.clone(),
              VarSize::V32,
            ));
          }
        } else {
          let r11 = X86Operand::Reg(RegX86::R11(VarSize::V32));
          self.push_Operand_to_Operand(assSource2, &r11);
          self.add_instr(AssemblyLine::And(
            assSource1.clone(),
            r11.clone(),
            VarSize::V32,
          ));
          self.add_instr(AssemblyLine::Mov(
            r11,
            assDest.to_size(VarSize::V32),
            VarSize::V32,
            SignExtend::No,
          ));
        }
      }
      // d <- a | b
      BinOp::Or => {
        if assDest.is_reg() {
          if assSource1 != assDest {
            self.push_Operand_to_Operand(assSource2, assDest);
            self.add_instr(AssemblyLine::Or(
              assSource1.clone(),
              assDest.clone(),
              VarSize::V32,
            ));
          } else {
            self.push_Operand_to_Operand(assSource1, assDest);
            self.add_instr(AssemblyLine::Or(
              assSource2.clone(),
              assDest.clone(),
              VarSize::V32,
            ));
          }
        } else {
          self.add_instr(AssemblyLine::Mov(
            assSource1.clone(),
            X86Operand::Reg(RegX86::R11(VarSize::V32)),
            VarSize::V32,
            SignExtend::No,
          ));
          self.add_instr(AssemblyLine::Or(
            assSource2.clone(),
            X86Operand::Reg(RegX86::R11(VarSize::V32)),
            VarSize::V32,
          ));
          self.add_instr(AssemblyLine::Mov(
            X86Operand::Reg(RegX86::R11(VarSize::V32)),
            assDest.clone(),
            VarSize::V32,
            SignExtend::No,
          ));
        }
      }
      // d <- a ^ b
      BinOp::Xor => {
        if assDest.is_reg() {
          if assSource1 != assDest {
            self.push_Operand_to_Operand(assSource2, assDest);
            self.add_instr(AssemblyLine::Xor(
              assSource1.clone(),
              assDest.clone(),
              VarSize::V32,
            ));
          } else {
            self.push_Operand_to_Operand(assSource1, assDest);
            self.add_instr(AssemblyLine::Xor(
              assSource2.clone(),
              assDest.clone(),
              VarSize::V32,
            ));
          }
        } else {
          self.add_instr(AssemblyLine::Mov(
            assSource1.clone(),
            X86Operand::Reg(RegX86::R11(VarSize::V32)),
            VarSize::V32,
            SignExtend::No,
          ));
          self.add_instr(AssemblyLine::Xor(
            assSource2.clone(),
            X86Operand::Reg(RegX86::R11(VarSize::V32)),
            VarSize::V32,
          ));
          self.add_instr(AssemblyLine::Mov(
            X86Operand::Reg(RegX86::R11(VarSize::V32)),
            assDest.clone(),
            VarSize::V32,
            SignExtend::No,
          ));
        }
      }
      // d <- a << b
      BinOp::Shl => {
        if assDest.is_reg() && assSource2 != assDest {
          self.push_Operand_to_Operand(assSource1, assDest);
          self.add_instr(AssemblyLine::Shl(
            X86Operand::Reg(RegX86::Rcx(VarSize::V8)),
            assDest.clone(),
            VarSize::V32,
          ));
        } else {
          self.push_Operand_to_Operand(
            assSource1,
            &X86Operand::Reg(RegX86::R11(VarSize::V32)),
          );
          self.add_instr(AssemblyLine::Shl(
            X86Operand::Reg(RegX86::Rcx(VarSize::V8)),
            X86Operand::Reg(RegX86::R11(VarSize::V32)),
            VarSize::V32,
          ));

          self.add_instr(AssemblyLine::Mov(
            X86Operand::Reg(RegX86::R11(VarSize::V32)),
            assDest.clone(),
            VarSize::V32,
            SignExtend::No,
          ));
        }
      }
      // d <- a >> b
      BinOp::Shr => {
        if assDest.is_reg() && assSource2 != assDest {
          self.push_Operand_to_Operand(assSource1, assDest);
          self.add_instr(AssemblyLine::Shr(
            X86Operand::Reg(RegX86::Rcx(VarSize::V8)),
            assDest.clone(),
            VarSize::V32,
          ));
        } else {
          self.push_Operand_to_Operand(
            assSource1,
            &X86Operand::Reg(RegX86::R11(VarSize::V32)),
          );
          self.add_instr(AssemblyLine::Shr(
            X86Operand::Reg(RegX86::Rcx(VarSize::V8)),
            X86Operand::Reg(RegX86::R11(VarSize::V32)),
            VarSize::V32,
          ));

          self.add_instr(AssemblyLine::Mov(
            X86Operand::Reg(RegX86::R11(VarSize::V32)),
            assDest.clone(),
            VarSize::V32,
            SignExtend::No,
          ));
        }
      }
    }
  }

  /// Adds segfault operations.
  fn add_sigsegv(&mut self) {
    self.add_instr(AssemblyLine::Mov(
      X86Operand::Imm(add_new_imm32(SIGSEGV)),
      X86Operand::Reg(RegX86::Rdi(VarSize::V64)),
      VarSize::V64,
      SignExtend::No,
    ));
    self.add_instr(AssemblyLine::Jmp("system_panic".to_string()));
  }

  fn convert_binOp(
    &mut self,
    op: &BinOp,
    dest: &Dest,
    src1: &Operand,
    src2: &Operand,
  ) {
    let assDest = self.dest_to_x86op(dest.clone());
    match (&src1, &src2) {
      (Operand::Const(a, size_a), Operand::Const(b, size_b)) => {
        self.convert_binOp_const_and_const(&a, &b, assDest, &op)
      }
      (Operand::Var(a), Operand::Var(b)) => {
        let assSource1: X86Operand = self.dest_to_x86op(*a);
        let assSource2: X86Operand = self.dest_to_x86op(*b);
        self.convert_binOp_temp_and_temp(
          &assSource1,
          &assSource2,
          &assDest,
          op,
        );
      }
      (Operand::Const(a, size_a), Operand::Var(b)) => {
        let assSource1: X86Operand =
          X86Operand::Imm(add_new_imm(*a, size_a.to_var_size()));
        let assSource2: X86Operand = self.dest_to_x86op(*b);
        // if the const is too big, we need call the system panic since this bias is too big
        if DIRTY_HANDLE_OVERSIZE && *a > 2147483647 {
          unreachable!("oversize const passed tc");
          // self.add_sigsegv();
          // return;
        }
        self.convert_binOp_const_and_temp(
          &assSource1,
          &assSource2,
          &assDest,
          op,
        );
      }
      (Operand::Var(a), Operand::Const(b, size_b)) => {
        let assSource1: X86Operand = self.dest_to_x86op(*a);
        let assSource2: X86Operand =
          X86Operand::Imm(add_new_imm(*b, size_b.to_var_size()));
        // if the const is too big, we need call the system panic since this bias is too big
        if DIRTY_HANDLE_OVERSIZE && *b > 2147483647 {
          unreachable!("oversize const passed tc");
          // self.add_sigsegv();
          // return;
        }
        self.convert_binOp_temp_and_const(
          &assSource1,
          &assSource2,
          &assDest,
          op,
        );
      } // _ => todo!("Const64 unimplemented"),
    }
  }

  fn convert_UnOp(&mut self, op: &UnOp, dest: &Dest, src: &Operand) {
    let destsize = dest.get_size().to_var_size();
    assert_eq!(destsize, VarSize::V32, "UnOp dest size not 32 bit!");
    let assDest = self.dest_to_x86op(dest.clone());
    match *op {
      UnOp::Neg => match &src {
        Operand::Const(a, size) => self.instrs.push(AssemblyLine::Mov(
          X86Operand::Imm(add_new_imm(-(*a), size.to_var_size())),
          assDest,
          VarSize::V32,
          SignExtend::No,
        )),
        Operand::Var(s) => {
          let assSource = self.dest_to_x86op(*s);
          if assDest.is_reg() {
            self.push_Operand_to_Operand(&assSource, &assDest);
            self.add_instr(AssemblyLine::Neg(assDest.clone(), VarSize::V32));
          } else {
            self.push_Operand_to_Operand(
              &assSource,
              &X86Operand::Reg(RegX86::R11(VarSize::V32)),
            );
            self.add_instr(AssemblyLine::Neg(
              X86Operand::Reg(RegX86::R11(VarSize::V32)),
              VarSize::V32,
            ));
            self.add_instr(AssemblyLine::Mov(
              X86Operand::Reg(RegX86::R11(VarSize::V32)),
              assDest.clone(),
              VarSize::V32,
              SignExtend::No,
            ));
          }
        }
      },
      UnOp::Not => match src {
        Operand::Const(a, size) => {
          assert_eq!(
            size.to_var_size(),
            VarSize::V32,
            "UnOp Not size not 32 bit!"
          );
          self.instrs.push(AssemblyLine::Mov(
            X86Operand::Imm(add_new_imm32(if *a == 0 { 1 } else { 0 })),
            assDest,
            VarSize::V32,
            SignExtend::No,
          ));
        }
        Operand::Var(s) => {
          let assSource = self.dest_to_x86op(*s);
          if assDest.is_reg() {
            self.push_Operand_to_Operand(&assSource, &assDest);
            self.add_instr(AssemblyLine::Xor(
              X86Operand::Imm(add_new_imm32(1)),
              assDest.clone(),
              VarSize::V32,
            ));
            self.add_instr(AssemblyLine::Mov(
              assDest.to_size(VarSize::V8),
              assDest.clone(),
              VarSize::V32,
              SignExtend::Zero(VarSize::V8, VarSize::V32),
            ));
          } else {
            self.push_Operand_to_Operand(
              &assSource,
              &X86Operand::Reg(RegX86::R11(VarSize::V32)),
            );
            self.add_instr(AssemblyLine::Xor(
              X86Operand::Imm(add_new_imm32(1)),
              X86Operand::Reg(RegX86::R11(VarSize::V32)),
              VarSize::V32,
            ));
            self.add_instr(AssemblyLine::Mov(
              X86Operand::Reg(RegX86::R11(VarSize::V8)),
              X86Operand::Reg(RegX86::R11(VarSize::V32)),
              VarSize::V32,
              SignExtend::Zero(VarSize::V8, VarSize::V32),
            ));
            self.add_instr(AssemblyLine::Mov(
              X86Operand::Reg(RegX86::R11(VarSize::V32)),
              assDest.clone(),
              VarSize::V32,
              SignExtend::No,
            ));
          }
        }
      },
      UnOp::Tild => match src {
        Operand::Const(a, size) => {
          assert_eq!(
            size.to_var_size(),
            VarSize::V32,
            "UnOp Tild size not 32 bit!"
          );
          self.instrs.push(AssemblyLine::Mov(
            X86Operand::Imm(add_new_imm32(!(*a as i32))),
            assDest,
            VarSize::V32,
            SignExtend::No,
          ));
        }
        Operand::Var(s) => {
          let assSource = self.dest_to_x86op(*s);
          if assSource.is_reg() {
            self.push_Operand_to_Operand(&assSource, &assDest);
            self
              .instrs
              .push(AssemblyLine::Not(assDest.clone(), VarSize::V32));
          } else {
            self.add_instr(AssemblyLine::Mov(
              assSource,
              X86Operand::Reg(RegX86::R11(VarSize::V32)),
              VarSize::V32,
              SignExtend::No,
            ));
            self.instrs.push(AssemblyLine::Not(
              X86Operand::Reg(RegX86::R11(VarSize::V32)),
              VarSize::V32,
            ));
            self.add_instr(AssemblyLine::Mov(
              X86Operand::Reg(RegX86::R11(VarSize::V32)),
              assDest,
              VarSize::V32,
              SignExtend::No,
            ));
          }
        }
      },
    }
  }
}

/// preprocess the context to get the assignment
/// and the spill count
/// the assignment is a map from a set of variables to a register or spills
/// the spill count is the space of spills
pub fn ctx_preprocess(ctx: &Context, optimize_level: usize) -> Assemb {
  let mut ass: Assemb = Assemb::new(ctx);
  let consumed_ctx = ctx.clone();
  let regs2: HashSet<NamedReg>;
  let spill_count: usize;
  (ass.var_temp_map, regs2, spill_count) =
    context_to_assignment(consumed_ctx, optimize_level);
  let mut regs = HashSet::new();
  for (vars, reg) in &ass.var_temp_map {
    match *vars {
      Node::Temporary(_) => regs.insert(reg),
      _ => false,
    };
  }
  ass.spill_size = spill_count * ass.spilled_var_size;
  let caller_saved_regs: HashSet<X86Operand> = HashSet::new();
  for reg in regs.clone() {
    match *reg {
      RegAbs86::Named(NamedReg::Rax) => continue,
      RegAbs86::Named(r) => {
        if !reg.callee_saved() {
          ass
            .used_caller_saved
            .push(temp_to_reg::reg_conversion_64(r));
        } else {
          ass
            .used_callee_saved
            .push(temp_to_reg::reg_conversion_64(r));
        }
      }
      _ => {}
    }
  }

  ass
}
/// Parses a piece of abstract assembly, as represented in a `Context`, into
/// `x86` assembly.
pub fn parse_asm(
  ctx: &Context,
  mut ass: Assemb,
  assembs: &HashMap<String, Assemb>,
) -> Assemb {
  for ins in &ctx.instrs {
    ass.convert(ins, assembs);
    if ass.done_function {
      break;
    }
  }

  return ass;
}
