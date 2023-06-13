use std::collections::HashMap;

use crate::asm::{Dest, Instr, Operand};
use crate::codegen::Context;
use crate::reg_alloc::ast_graph_node::Node;
use crate::reg_alloc::x86_register::RegAbs86;

fn assign_reg_to_dest(d: &mut Dest, assignment: &HashMap<Node, RegAbs86>) {
  if let Dest::T(n, size) = d {
    match assignment
      .get(&Node::Temporary(*n))
      .expect("regassignment failed")
    {
      RegAbs86::Named(r) => {
        *d = Dest::R(*r, *size);
      }
      RegAbs86::FnArgOnStack(n) => {
        *d = Dest::FnArgOnStack(*n, *size);
      }
      RegAbs86::Spill(n) => {
        *d = Dest::T(*n as u32, *size);
      }
    }
  }
}

fn assign_reg_to_operand(
  op: &mut Operand,
  assignment: &HashMap<Node, RegAbs86>,
) {
  if let Operand::Var(d) = op {
    assign_reg_to_dest(d, assignment);
  }
}

fn substitute_register(
  ctx: &mut Context,
  regalloc_result: &HashMap<Node, RegAbs86>,
) {
  for instr in &mut ctx.instrs {
    match instr {
      Instr::BinOp {
        op: _,
        dest,
        src1,
        src2,
      } => {
        assign_reg_to_dest(dest, &regalloc_result);
        assign_reg_to_operand(src1, &regalloc_result);
        assign_reg_to_operand(src2, &regalloc_result);
      }
      Instr::UnOp { op: _, dest, src } => {
        assign_reg_to_dest(dest, &regalloc_result);
        assign_reg_to_operand(src, &regalloc_result);
      }
      Instr::Mov { dest, src } => {
        assign_reg_to_dest(dest, &regalloc_result);
        assign_reg_to_operand(src, &regalloc_result);
      }
      Instr::Push(op) => {
        assign_reg_to_operand(op, &regalloc_result);
      }
      Instr::NaiveCall(_, _) => unimplemented!(),
      Instr::Return(op) => {
        assign_reg_to_operand(op, &regalloc_result);
      }
      Instr::JmpCondition {
        condition,
        tgt_true: _,
        tgt_false: _,
      } => {
        assign_reg_to_dest(condition, &regalloc_result);
      }
      Instr::Call(..)
      | Instr::FnLbl(..)
      | Instr::Lbl(..)
      | Instr::IncrRsp(..)
      | Instr::ReturnVoid
      | Instr::Jmp(..)
      | Instr::FnCallSpillSize(..)
      | Instr::Store(..)
      | Instr::Restore(..) => {}
      x => todo!("`{}` unmatched", x),
    }
  }
}

fn remove_useless_mov(ctx: &mut Context) {
  ctx.instrs = ctx
    .instrs
    .iter()
    .cloned()
    .filter(|instr| {
      if let Instr::Mov {
        dest,
        src: Operand::Var(d),
      } = instr
      {
        d != dest
      } else {
        true
      }
    })
    .collect();
}

pub fn optimize(ctx: &mut Context, regalloc_result: &HashMap<Node, RegAbs86>) {
  substitute_register(ctx, regalloc_result);
  remove_useless_mov(ctx);
}
