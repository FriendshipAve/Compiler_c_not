//! function inline pass after codegen

use crate::asm::AsmLabel;
use crate::asm::Instr;
use crate::elab_after_tc::{self, LvalP2, MemAccess, StmtP2};
use crate::tc::tc_info::TcInfoFn;
use crate::{asm, ast};
/// Global context across functions, ie. struct definition, etc.

/// Code generation context that contains a counter for creating new temps,
/// the list of currently-generated instructions, and the mapping from variable
/// names to temps. In a valid L1 program, it's OK to reuse the temp.
///
/// [L3] Context now represents whatever is going on in a function.
use crate::{asm::Dest, asm::Operand, codegen::Context, elab_after_tc::ExprP2};

use crate::reg_alloc::x86_register::NamedReg;

use crate::const_params::*;

use crate::util::datastructure::split_vec;

use crate::asm::DestSize;

use crate::ast::Typ;
use std::collections::{HashMap, HashSet};
use std::convert::TryFrom;
use std::sync::Arc;

pub struct InlineCtx {
  pub available: HashSet<String>,
  pub fn_ctx_index: HashMap<String, usize>,
  pub tail_recursive: HashSet<String>,
}

pub const DEBUG_INLINE: bool = false;
impl InlineCtx {
  pub fn new() -> InlineCtx {
    InlineCtx {
      available: HashSet::new(),
      fn_ctx_index: HashMap::new(),
      tail_recursive: HashSet::new(),
    }
  }
}

pub fn identify_calls(
  ctx: &Context,
  inline_ctx: &mut InlineCtx,
) -> (bool, bool) {
  let fn_name = ctx.get_name();
  // if this function is external funtion, we do not inline it
  if fn_name == "main"
    || fn_name == "init"
    || fn_name == "prepare"
    || fn_name == "run"
    || fn_name == "checksum"
  {
    return (false, false);
  }
  if ctx.get_arity() > 6 {
    return (false, false);
  }
  let mut is_recursive = false;
  for (i, instr) in ctx.instrs.iter().enumerate() {
    match instr {
      asm::Instr::Call(name, _) => {
        if *name == fn_name {
          is_recursive = true;
        }
      }
      _ => {}
    }
  }
  if !is_recursive {
    inline_ctx.available.insert(fn_name.clone());
    return (true, true);
  }
  (true, false)
}

pub fn identify_tail_recursive(
  ctx: &Context,
  inline_ctx: &mut InlineCtx,
) -> bool {
  let abs_len = ctx.instrs.len();
  if abs_len < 3 {
    return false;
  }
  let last_instr = &ctx.instrs[abs_len - 1];
  let second_last_instr = &ctx.instrs[abs_len - 2];
  let third_last_instr = &ctx.instrs[abs_len - 3];

  match last_instr {
    asm::Instr::Return(dest) => match (second_last_instr, third_last_instr) {
      (Instr::Comment(c), Instr::Mov { dest: dest2, src }) => {
        let names = c.split_whitespace().collect::<Vec<&str>>();
        if names.len() != 2 {
          return false;
        }
        if names[0] != "endfncall" || names[1] != ctx.get_name() {
          return false;
        }
        if let asm::Operand::Var(d) = dest {
          return d == dest2;
        } else {
          return false;
        }
      }
      _ => return false,
    },
    _ => return false,
  }
}

pub fn build_available_calls(ctx_v: &Vec<Context>) -> InlineCtx {
  let mut inline_ctx = InlineCtx::new();
  for (i, ctx) in ctx_v.iter().enumerate() {
    if let (valid_name, recursive) = identify_calls(ctx, &mut inline_ctx) {
      if valid_name && recursive {
        inline_ctx.fn_ctx_index.insert(ctx.get_name(), i);
      } else if valid_name && !recursive {
        inline_ctx.fn_ctx_index.insert(ctx.get_name(), i);
        inline_ctx.tail_recursive.insert(ctx.get_name());
      }
    }
  }
  inline_ctx
}
/// return label is not implemented
pub fn incr_instr_id(
  instr: &Instr,
  tmp_id: u32,
  lbl_id: u32,
  ret_dest: &Dest,
) -> Option<Instr> {
  match instr {
    Instr::Lbl(lbl) => Some(Instr::Lbl(lbl.incr_id(lbl_id))),
    Instr::FnLbl(..)
    | Instr::Store(..)
    | Instr::Restore(..)
    | Instr::NaiveCall(..) => None,
    Instr::Mov { dest, src } => Some(Instr::Mov {
      dest: dest.incr_id(tmp_id),
      src: src.incr_id(tmp_id),
    }),
    Instr::WriteToHeap { dest, src } => Some(Instr::WriteToHeap {
      dest: dest.incr_id(tmp_id),
      src: src.incr_id(tmp_id),
    }),
    Instr::Return(oprnd) => Some(Instr::Mov {
      dest: ret_dest.clone(),
      src: oprnd.incr_id(tmp_id),
    }),
    Instr::ReturnVoid => None,
    Instr::Call(name, count) => Some(Instr::Call(name.clone(), *count)),
    Instr::Push(oprnd) => Some(Instr::Push(oprnd.incr_id(tmp_id))),
    Instr::BinOp {
      dest,
      op,
      src1,
      src2,
    } => Some(Instr::BinOp {
      dest: dest.incr_id(tmp_id),
      op: op.clone(),
      src1: src1.incr_id(tmp_id),
      src2: src2.incr_id(tmp_id),
    }),
    Instr::UnOp { op, dest, src } => Some(Instr::UnOp {
      op: op.clone(),
      dest: dest.incr_id(tmp_id),
      src: src.incr_id(tmp_id),
    }),
    Instr::MovFromHeap { dest, src } => Some(Instr::MovFromHeap {
      dest: dest.incr_id(tmp_id),
      src: src.incr_id(tmp_id),
    }),
    Instr::LoadAddr { dest, src } => Some(Instr::LoadAddr {
      dest: dest.incr_id(tmp_id),
      src: src.incr_id(tmp_id),
    }),
    Instr::LoadArrLen {
      dest,
      arr_head_addr,
    } => Some(Instr::LoadArrLen {
      dest: dest.incr_id(tmp_id),
      arr_head_addr: arr_head_addr.incr_id(tmp_id),
    }),
    Instr::JmpCondition {
      condition,
      tgt_true,
      tgt_false,
    } => Some(Instr::JmpCondition {
      condition: condition.incr_id(tmp_id),
      tgt_true: tgt_true.incr_id(lbl_id),
      tgt_false: tgt_false.incr_id(lbl_id),
    }),
    Instr::Jmp(lbl) => Some(Instr::Jmp(lbl.incr_id(lbl_id))),
    Instr::FnCallSpillSize(..)
    | Instr::IncrRsp(..)
    | Instr::Panic(..)
    | Instr::Comment(..) => Some(instr.clone()),
    Instr::NullPtrChk { ptr, panic, end } => Some(Instr::NullPtrChk {
      ptr: ptr.incr_id(tmp_id),
      panic: panic.incr_id(lbl_id),
      end: end.incr_id(lbl_id),
    }),
    Instr::Test(d) => Some(Instr::Test(d.incr_id(tmp_id))),
    Instr::Cmp(dest, op) => {
      Some(Instr::Cmp(dest.incr_id(tmp_id), op.incr_id(tmp_id)))
    }
    Instr::JmpFlag(flg, lbl1, lbl2) => Some(Instr::JmpFlag(
      flg.clone(),
      lbl1.incr_id(lbl_id),
      lbl2.incr_id(lbl_id),
    )),
  }
}

pub fn convert_inline_locally(
  old_ctx: &Context,
  new_ctx: &mut Context,
  called_fn_ctx: &Context,
  line_num: usize,
  end_line_num: usize,
  return_dest: &Dest,
  return_lbl: &AsmLabel,
  fn_name: &str,
) {
  // match rdi,... and fnargspill to their old temps before move
  let mut fn_args_temp: HashMap<Dest, asm::Operand> = HashMap::new();
  let called_fn_arity = called_fn_ctx.arity;
  let spilled_args = if called_fn_arity > 6 {
    called_fn_arity - 6
  } else {
    0
  };

  let mut pushed = spilled_args;
  let old_tmp_count = new_ctx.temp_index;
  let old_lbl_count = new_ctx.lbl_index;
  if DEBUG_INLINE {
    eprintln!("old tmp count {}", old_tmp_count);
    eprintln!("old lbl count {}", old_lbl_count);
  }
  // copy called depth to new ctx
  for (i, dep) in called_fn_ctx.temp_depth_map.0.iter() {
    new_ctx
      .temp_depth_map
      .0
      .insert(i + old_tmp_count, dep + new_ctx.loop_depth);
  }
  for index in line_num..end_line_num {
    let instr = &old_ctx.instrs[index];
    match instr {
      asm::Instr::Mov { dest, src } => match src {
        asm::Operand::Var(Dest::R(NamedReg::Rax, DestSize::oct)) => {}
        _ => {
          fn_args_temp.insert(dest.clone(), src.clone());
        }
      },
      asm::Instr::Push(src) => {
        unreachable!("pushing args shall not be allowed for inline fn");
      }
      asm::Instr::Call(fname, fn_count) => {
        assert_eq!(fname, fn_name);
        assert_eq!(fn_count, &called_fn_arity);
        let mut moving_args_to_tmp = true;
        for (i, new_instr) in called_fn_ctx.instrs.iter().enumerate() {
          if moving_args_to_tmp {
            match new_instr {
              asm::Instr::Mov { dest, src } => {
                let new_dest = dest.incr_id(old_tmp_count);
                let new_src = match src {
                  asm::Operand::Var(d) => {
                    fn_args_temp.get(d).expect("fn args not found").clone()
                  }
                  _ => panic!("not name reg for inital args passing"),
                };
                new_ctx.add_instr(asm::Instr::Mov {
                  dest: new_dest,
                  src: new_src,
                });
              }
              asm::Instr::Comment(s) => {
                if s == "endMoveArgs" {
                  moving_args_to_tmp = false;
                }
              }
              _ => {}
            }
          } else {
            let added_instr = incr_instr_id(
              new_instr,
              old_tmp_count,
              old_lbl_count,
              return_dest,
            );
            match added_instr {
              Some(instr) => new_ctx.add_instr(instr),
              None => {}
            };
            match new_instr {
              Instr::Return(..) | Instr::ReturnVoid => {
                new_ctx.add_instr(asm::Instr::Jmp(return_lbl.clone()));
              }
              _ => {}
            }
          }
        }
      }
      _ => {}
    }
  }
  new_ctx.temp_index += called_fn_ctx.temp_index;
  new_ctx.lbl_index += called_fn_ctx.lbl_index;
  let new_ctx_length = new_ctx.instrs.len();
  let last_instr = &new_ctx.instrs[new_ctx_length - 1];
  if DEBUG_INLINE {
    eprintln!("last instr {:?}", last_instr);
  }
  match last_instr {
    Instr::Jmp(..) => {}
    _ => new_ctx.add_instr(Instr::Jmp(return_lbl.clone())),
  };
  new_ctx.add_instr(asm::Instr::Lbl(return_lbl.clone()));
}

pub fn convert_inline_fn(
  ctx: &Context,
  inline_ctx: &mut InlineCtx,
  ctx_v: &Vec<Context>,
) -> Context {
  if DEBUG_INLINE {
    eprintln!("converting inline fn for {}\n", ctx.name);
  }
  let mut new_ctx = Context {
    temp_index: ctx.temp_index,
    lbl_index: ctx.lbl_index,
    fn_name: ctx.fn_name.clone(),
    instrs: Vec::new(),
    var_temp_map: ctx.var_temp_map.clone(),
    varname_argpos_map: ctx.varname_argpos_map.clone(),
    // var_typesize_map: HashMap<String, usize>,
    arity: ctx.arity,
    name: ctx.name.clone(),
    loop_depth: ctx.loop_depth,
    temp_depth_map: ctx.temp_depth_map.clone(),
  };
  let mut fn_call_start_index: usize = 0;
  let mut fn_call_end_index: usize = 0;
  let mut doing_inline = false;
  let mut call_loop_depth: usize = 0;
  let mut fn_call_depth: usize = 0;
  for (i, instr) in ctx.instrs.iter().enumerate() {
    match instr {
      asm::Instr::Comment(name) => {
        let names = name.split_whitespace().collect::<Vec<&str>>();
        if names.len() >= 2 && names[0] == "fncall" {
          let fn_name = names[1];
          fn_call_depth = names[3]
            .parse::<usize>()
            .expect("fn call depth 4th comment not usize");
          if inline_ctx.available.contains(fn_name) {
            doing_inline = true;
            fn_call_start_index = i;
            new_ctx.loop_depth += fn_call_depth;
            if DEBUG_INLINE {
              eprintln!("\nfound fncall {}", fn_name);
            }
          } else {
            new_ctx.add_instr(instr.clone());
          }
        } else if names.len() == 2 && names[0] == "endfncall" {
          if doing_inline {
            new_ctx.loop_depth -= fn_call_depth;
            let fn_name = names[1];
            if DEBUG_INLINE {
              eprintln!("endfncall {}\n", fn_name);
            }
            let mut called_fn_ctx = &ctx_v[inline_ctx.fn_ctx_index[fn_name]];
            fn_call_end_index = i;
            doing_inline = false;
            let ret_arg = &ctx.instrs[i - 1];
            let return_dest = match ret_arg {
              asm::Instr::Mov { dest, src } => dest,
              _ => panic!("next arg is not mov"),
            };
            let ret_lbl = new_ctx.create_lbl();
            convert_inline_locally(
              ctx,
              &mut new_ctx,
              called_fn_ctx,
              fn_call_start_index,
              fn_call_end_index,
              &return_dest,
              &ret_lbl,
              fn_name,
            );
          } else {
            new_ctx.add_instr(instr.clone());
          }
        } else {
          new_ctx.add_instr(instr.clone())
        }
      }
      _ => {
        if !doing_inline {
          new_ctx.add_instr(instr.clone())
        }
      }
    }
  }
  new_ctx
}

pub fn convert_tail_fn(
  ctx: &Context,
  inline_ctx: &InlineCtx,
) -> Option<Context> {
  return None;
  if !inline_ctx.tail_recursive.contains(&ctx.name) {
    return None;
  }
  if DEBUG_INLINE {
    eprintln!("converting tail fn for {}\n", ctx.name);
  }
  let mut recurse_idx = vec![];
  let len = ctx.instrs.len();
  for (i, instr) in ctx.instrs.iter().enumerate() {
    match instr {
      asm::Instr::Comment(name) => {
        let names = name.split_whitespace().collect::<Vec<&str>>();
        if names.len() == 2 && names[0] == "endfncall" {
          let fn_name = names[1];
          if fn_name == ctx.name && i + 1 < len {
            if let asm::Instr::Return(name) = &ctx.instrs[i + 1] {
              let prev_instr = &ctx.instrs[i - 1];
              match prev_instr {
                asm::Instr::Mov { dest, src } => {
                  if let Operand::Var(Dest::R(NamedReg::Rax, _)) = src {
                    if Operand::Var(dest.clone()) == *name {
                      recurse_idx.push(i);
                    }
                  }
                }
                _ => {}
              }
            }
          }
        }
      }
      _ => {}
    }
  }
  if recurse_idx.len() == 0 {
    return None;
  }

  /*let mut namedreg_tmp_map: HashMap<Operand, Dest> = HashMap::new();
  for idx in 1..=ctx.arity {
    let instr = &ctx.instrs[idx];
    match instr {
      Instr::Mov { dest, src } => match src {
        Operand::Var(Dest::R(..)) => {
          namedreg_tmp_map.insert(src.clone(), dest.clone());
        }
        _ => {}
      },
      Instr::Comment(c) => {
        if c == "endMoveArgs" {
          break;
        }
      }
      _ => {}
    }
  }
  assert_eq!(
    namedreg_tmp_map.len(),
    ctx.arity,
    "arity mismatch, args have {:?} namedregs",
    namedreg_tmp_map
  );*/
  let mut new_ctx = ctx.clone();
  let lbl_index = new_ctx.lbl_index;
  let mut added_lbl = new_ctx.create_lbl();
  new_ctx.instrs.insert(1, Instr::Lbl(added_lbl.clone()));
  new_ctx.instrs.insert(1, Instr::Jmp(added_lbl.clone()));
  for idx in recurse_idx {
    let idx = idx + 2;
    new_ctx.instrs[idx - 4] =
      Instr::Comment(format!("tailcall replaced {}", new_ctx.instrs[idx - 2]));
    new_ctx.instrs[idx - 3] = Instr::Jmp(added_lbl.clone());
    new_ctx.instrs[idx - 2] =
      Instr::Comment(format!("tailcall replaced {}", new_ctx.instrs[idx - 2]));
    new_ctx.instrs[idx - 1] =
      Instr::Comment(format!("tailcall replaced {}", new_ctx.instrs[idx - 1]));
    new_ctx.instrs[idx] =
      Instr::Comment("tailcall replaced return".to_string());
    let mut new_lbl = new_ctx.create_lbl();
    new_ctx.instrs[idx + 1] = Instr::Jmp(new_lbl.clone())
  }

  Some(new_ctx)
}

pub fn convert_inline_v(ctx_v: &Vec<Context>) -> Vec<Context> {
  let mut inline_ctx = build_available_calls(ctx_v);
  let mut new_ctx_v = Vec::new();
  for ctx in ctx_v {
    let new_ctx = convert_inline_fn(ctx, &mut inline_ctx, ctx_v);
    new_ctx_v.push(new_ctx);
  }
  let tail_rec = inline_ctx.tail_recursive.iter();
  for ctx in tail_rec {
    let new_ctx =
      convert_tail_fn(&new_ctx_v[inline_ctx.fn_ctx_index[ctx]], &inline_ctx);
    let idx = inline_ctx.fn_ctx_index[ctx];
    match new_ctx {
      Some(ctx) => new_ctx_v[idx] = ctx,
      None => {}
    }
  }
  new_ctx_v
}
