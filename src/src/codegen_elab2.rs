//! Code generation from second elab pass

use crate::asm::{AsmLabel, HeapLocation};
use crate::ast::Patt;
use crate::elab_after_tc::{self, LvalP2, MemAccess, StmtP2};
use crate::tc::tc_info::TcInfoFn;
use crate::{asm, ast};
/// Global context across functions, ie. struct definition, etc.

/// Code generation context that contains a counter for creating new temps,
/// the list of currently-generated instructions, and the mapping from variable
/// names to temps. In a valid L1 program, it's OK to reuse the temp.
///
/// [L3] Context now represents whatever is going on in a function.
use crate::{asm::Dest, codegen::Context, elab_after_tc::ExprP2};

use crate::reg_alloc::x86_register::NamedReg;

use crate::const_params::*;

use crate::util::datastructure::split_vec;

use crate::asm::DestSize;

use std::collections::HashSet;
use std::convert::TryFrom;

// ------------------------------ begin helpers ------------------------------

/// Evaluates an iterator of expressions, returns the results as a vector
/// of temps.
fn munch_exprs<'a, T>(
  ctx: &mut Context,
  exprs: T,
  tc_info_fn: &TcInfoFn,
  safemode: bool,
  purity: &HashSet<String>,
) -> Vec<Dest>
where
  T: Iterator<Item = &'a (DestSize, ExprP2)>,
{
  let mut ret = Vec::<Dest>::new();
  for (_, expr) in exprs {
    ret.push(expr_to_dest(ctx, expr, tc_info_fn, safemode, purity));
  }
  ret
}

/// Helper function to `alloc()` and `alloc_arr()`. DO NOT USE unless you know
/// what you are doing.
fn call_calloc(ctx: &mut Context, safemode: bool) {
  use asm::Instr::*;
  // make call
  ctx.add_instr(FnCallSpillSize(0, "calloc".to_string()));
  ctx.add_instr(Call("calloc".to_string(), 2));
  ctx.add_instr(IncrRsp(0));

  // if safety mode, check non-null
  if safemode {
    assert_not_null(ctx, Dest::R(NamedReg::Rax, DestSize::oct));
  }
}

/// Increments `dest` by this much.
fn incr(ctx: &mut Context, dest: Dest, offset: i128) {
  ctx.add_instr(asm::Instr::BinOp {
    op: ast::BinOp::Add,
    dest,
    src1: asm::Operand::Var(dest),
    src2: asm::Operand::Const(offset, DestSize::oct),
  })
}

/// Handles div / mod op and its uses of registers.
fn divmod(
  ctx: &mut Context,
  op: ast::BinOp,
  dest: Dest,
  src1: Dest,
  src2: Dest,
) {
  // div and mod are always working on int
  // reg are all 32 bit here

  use asm::DestSize::quad;
  use asm::Instr::BinOp;
  use asm::Instr::Mov;
  use asm::Operand;

  assert!(op == ast::BinOp::Div || op == ast::BinOp::Mod);

  // rdx <- $0
  ctx.add_instr(Mov {
    dest: Dest::R(NamedReg::Rdx, DestSize::quad),
    src: Operand::Const(0, quad),
  });

  // rax <- src1
  ctx.add_instr(Mov {
    dest: Dest::R(NamedReg::Rax, DestSize::quad),
    src: Operand::Var(src1),
  });

  // dest <- rax / src2
  ctx.add_instr(BinOp {
    op,
    dest,
    src1: Operand::Var(Dest::R(NamedReg::Rax, DestSize::quad)),
    src2: Operand::Var(src2),
  })
}

/// Handles shift and its boundchecks.
fn shift(
  ctx: &mut Context,
  op: ast::BinOp,
  dest: Dest,
  lhs: Dest,
  rhs: Dest,
  tc_info_fn: &TcInfoFn,
  safemode: bool,
  purity: &HashSet<String>,
) {
  use asm::DestSize::quad;
  use asm::Instr::BinOp;
  use asm::Instr::Mov;
  use asm::Operand;

  assert!(op == ast::BinOp::Shl || op == ast::BinOp::Shr);

  if safemode {
    let (underflow_chk, overflow_chk) = (ctx.temp(quad), ctx.temp(quad));

    // underflow_chk <- (rhs_eval < 0)
    ctx.add_instr(BinOp {
      op: ast::BinOp::Lt,
      dest: underflow_chk,
      src1: Operand::Var(rhs),
      src2: Operand::Const(0, quad),
    });

    // overflow_chk <- (rhs_eval >= 32)
    ctx.add_instr(BinOp {
      op: ast::BinOp::Ge,
      dest: overflow_chk,
      src1: Operand::Var(rhs),
      src2: Operand::Const(32, quad),
    });

    // invalid_shift_range <- (underflow_chk | overflow_chk)
    let invalid_shift = ctx.temp(quad);
    ctx.add_instr(BinOp {
      op: ast::BinOp::Or,
      dest: invalid_shift,
      src1: Operand::Var(underflow_chk),
      src2: Operand::Var(overflow_chk),
    });

    let (panic_branch, shift_branch, end) = ctx.create_three_lbls();

    ctx.add_jmp_condition(invalid_shift, panic_branch, shift_branch);

    // panic branch
    add_eval_bb(
      ctx,
      panic_branch,
      &ExprP2::one_div_zero(),
      dest,
      end,
      tc_info_fn,
      safemode,
      purity,
    );

    // shift branch
    ctx.label(shift_branch);
    {
      // shifting always is operated on 32-bit values
      // rcx is quad
      // %rcx <- b
      ctx.add_instr(Mov {
        dest: Dest::R(NamedReg::Rcx, DestSize::quad),
        src: Operand::Var(rhs),
      });
      // d <- a << %rcx
      ctx.add_instr(BinOp {
        op,
        dest,
        src1: Operand::Var(lhs),
        src2: Operand::Var(Dest::R(NamedReg::Rcx, DestSize::quad)),
      });
    }
    ctx.goto(end);

    // end
    ctx.label(end);
  } else {
    // shifting always is operated on 32-bit values
    // rcx is quad
    // %rcx <- b
    ctx.add_instr(Mov {
      dest: Dest::R(NamedReg::Rcx, DestSize::quad),
      src: Operand::Var(rhs),
    });
    // d <- a << %rcx
    ctx.add_instr(BinOp {
      op,
      dest,
      src1: Operand::Var(lhs),
      src2: Operand::Var(Dest::R(NamedReg::Rcx, DestSize::quad)),
    });
  }
}

// ------------------------------- end helpers -------------------------------

/// Checkes if an expression is some variable. If yes, returns its fetch;
/// if not, creates a new `Temp` and munch the expression into
/// such a temp.
fn expr_to_dest(
  ctx: &mut Context,
  expr: &ExprP2,
  tc_info_fn: &TcInfoFn,
  safemode: bool,
  purity: &HashSet<String>,
) -> Dest {
  use asm::Dest;
  use ExprP2::*;

  // good case
  if let (Variable(x, size), true) = (expr, DEST_OP_PROP) {
    if let ret @ Dest::T(..) | ret @ Dest::R(..) =
      ctx.var(x, Some(*size)).expect("Failed to fetch")
    {
      return ret;
    }
  }

  // slow case
  let dest = ctx.temp(expr.size(tc_info_fn));
  munch_expr(ctx, dest, expr, tc_info_fn, safemode, purity);
  dest
}

/// Checks if an expression is some constant. If yet, returns its corresponding
/// operand; if not, calls `expr_to_dest` and converts the result to operand.
fn expr_to_operand(
  ctx: &mut Context,
  expr: &ExprP2,
  tc_info_fn: &TcInfoFn,
  safemode: bool,
  purity: &HashSet<String>,
) -> asm::Operand {
  use asm::Operand;
  use DestSize::*;
  use ExprP2::*;

  match (expr, DEST_OP_PROP) {
    (Num(n), true) => Operand::Const(i128::from(*n), quad),
    (Null, true) => Operand::Const(0, oct),
    (e, _) => Operand::Var(expr_to_dest(ctx, e, tc_info_fn, safemode, purity)),
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FlagTyp {
  Lt,
  Le,
  Ge,
  Gt,
  Eq,
  Ne,
}

impl std::fmt::Display for FlagTyp {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use FlagTyp::*;
    let s = match self {
      Lt => "jl",
      Le => "jle",
      Ge => "jge",
      Gt => "jg",
      Eq => "je",
      Ne => "jne",
    };
    write!(f, "{}", s)
  }
}

/// Given some boolean expression `expr`. sets the flag corresponding to
/// testing `expr`. Returns a `FlagTyp` corresponding to the false flag.
fn test(
  ctx: &mut Context,
  expr: &ExprP2,
  tc_info_fn: &TcInfoFn,
  safemode: bool,
  purity: &HashSet<String>,
) -> FlagTyp {
  let eval_expr = expr_to_dest(ctx, expr, tc_info_fn, safemode, purity);
  ctx.add_instr(asm::Instr::Test(eval_expr));
  FlagTyp::Eq // je jumps to branch when expr is false
}

/// Given some boolean expression `expr`, sets the flag corresponding to
/// `expr`.  Returns a `FlagTyp` corresponding to the false flag.
fn false_flag(
  ctx: &mut Context,
  expr: &ExprP2,
  tc_info_fn: &TcInfoFn,
  safemode: bool,
  purity: &HashSet<String>,
) -> FlagTyp {
  use asm::Instr::*;
  use asm::Operand;
  use ast::BinOp::*;
  use DestSize::*;
  use ExprP2::*;

  match expr {
    expr @ Binop(e1, op, e2) => match op {
      Lt | Le | Ge | Gt | Eq | Ne => {
        let e1_eval = expr_to_dest(ctx, e1, tc_info_fn, safemode, purity);
        let e2_eval = expr_to_operand(ctx, e2, tc_info_fn, safemode, purity);
        ctx.add_instr(Cmp(e1_eval, e2_eval));
        match op {
          Lt => FlagTyp::Ge,
          Le => FlagTyp::Gt,
          Ge => FlagTyp::Lt,
          Gt => FlagTyp::Le,
          Eq => FlagTyp::Ne,
          Ne => FlagTyp::Eq,
          _ => unreachable!(),
        }
      }
      op => test(ctx, expr, tc_info_fn, safemode, purity),
    },
    expr => test(ctx, expr, tc_info_fn, safemode, purity),
  }
}

/// Transform an expression into a series of instructions in a context.
///
/// [todo] consider 32 vs 64 bit.
fn munch_expr(
  ctx: &mut Context,
  dest: Dest,
  expr: &ExprP2,
  tc_info_fn: &TcInfoFn,
  safemode: bool,
  purity: &HashSet<String>,
) {
  use asm::Instr::*;
  use asm::Operand;
  use DestSize::*;
  use ExprP2::*;

  let edi = Dest::R(NamedReg::Rdi, DestSize::quad);
  let rdi = Dest::R(NamedReg::Rdi, DestSize::oct);
  let rsi = Dest::R(NamedReg::Rsi, DestSize::oct);
  let rax = Dest::R(NamedReg::Rax, DestSize::oct);

  match expr {
    Num(n) => ctx.add_instr(Mov {
      dest,
      src: Operand::Const(i128::from(*n), quad),
    }),
    Null => ctx.add_instr(Mov {
      dest,
      src: Operand::Const(0, oct),
    }),
    Variable(v, size) => {
      let src = ctx
        .var(v, Some(*size))
        .expect("Failed at Variable(v, size)");
      if dest != src {
        let src = Operand::Var(src);
        ctx.add_instr(Mov { dest, src })
      }
    }
    FnCall(ast::FnName(fname), args) => {
      if NAIVE_FNCALL_DURING_CODEGEN {
        unimplemented!()
      }

      let arity = args.len();
      let (reg_args, stack_args) = split_vec(&args, NUM_ARGS_PASSED_BY_REGS);

      let reg_args_evals =
        munch_exprs(ctx, reg_args.into_iter(), tc_info_fn, safemode, purity);
      let stack_args_evals =
        munch_exprs(ctx, stack_args.into_iter(), tc_info_fn, safemode, purity);

      if EXPLICIT_PUSH_POP_CALLER_SAVED_REGS {
        // Stores a copy of caller-preserved registers.
        ctx.add_instr(Store(arity));
      }
      let depth = ctx.loop_depth;
      ctx.add_instr(Comment(format!("fncall {} depth {}", fname, depth)));
      // Moves the values of register-based args to corresponding registers.
      for (argpos, t) in reg_args_evals.iter().enumerate() {
        ctx.add_instr(Mov {
          dest: Dest::R(
            NamedReg::from_first_six_function_arg(argpos),
            t.get_size().clone(),
          ),
          src: Operand::Var(*t),
        });
      }

      // Properly name fn alignment before fn call
      let spill_size = elab_after_tc::bytes_needed_on_stack(arity);
      ctx.add_instr(FnCallSpillSize(spill_size, fname.clone()));

      // Reverse the vec of temp and push them on stack.
      for t in stack_args_evals.into_iter().rev() {
        ctx.add_instr(Push(Operand::Var(t)));
      }

      // Make function call.
      ctx.add_instr(Call(fname.clone(), arity));

      // Increment %rsp. This is to undo the effect of the `push` instructions.
      // Also this is reverting by the `FnCallSpillSize` instruction.
      let delta_rsp = spill_size;
      ctx.add_instr(IncrRsp(delta_rsp));

      if EXPLICIT_PUSH_POP_CALLER_SAVED_REGS {
        // Restores a copy of the caller-preserved registers.
        ctx.add_instr(Restore(arity));
      }

      // Writes result from %rax back to dest
      // the size of rax doesn't matter, since we are moving it to dest
      ctx.add_instr(Mov {
        dest,
        src: Operand::Var(Dest::R(NamedReg::Rax, DestSize::oct)),
      });
      ctx.add_instr(Comment(format!("endfncall {}", fname)));
    }
    Binop(lhs, op, rhs) => {
      match op {
        // a << b or a >> b
        ast::BinOp::Shl | ast::BinOp::Shr => {
          let lhs_eval = expr_to_dest(ctx, lhs, tc_info_fn, safemode, purity);
          let rhs_eval = expr_to_dest(ctx, rhs, tc_info_fn, safemode, purity);
          shift(
            ctx, *op, dest, lhs_eval, rhs_eval, tc_info_fn, safemode, purity,
          );
        }
        ast::BinOp::OOr => {
          let (lhs_true, lhs_false, end) = ctx.create_three_lbls();

          // head
          let lhs_eval = expr_to_dest(ctx, lhs, tc_info_fn, safemode, purity);
          ctx.add_jmp_condition(lhs_eval, lhs_true, lhs_false);

          // branches
          add_eval_bb(
            ctx,
            lhs_true,
            &ExprP2::Num(1),
            dest,
            end,
            tc_info_fn,
            safemode,
            purity,
          ); // true
          add_eval_bb(
            ctx, lhs_false, &*rhs, dest, end, tc_info_fn, safemode, purity,
          );

          // end
          ctx.label(end);
        }
        ast::BinOp::AAnd => {
          let (lhs_true, lhs_false, end) = ctx.create_three_lbls();

          // head
          let lhs_eval = expr_to_dest(ctx, lhs, tc_info_fn, safemode, purity);
          ctx.add_jmp_condition(lhs_eval, lhs_true, lhs_false);

          // branches
          add_eval_bb(
            ctx, lhs_true, &*rhs, dest, end, tc_info_fn, safemode, purity,
          );
          add_eval_bb(
            ctx,
            lhs_false,
            &ExprP2::Num(0),
            dest,
            end,
            tc_info_fn,
            safemode,
            purity,
          ); // false

          // end
          ctx.label(end);
        }
        ast::BinOp::Div | ast::BinOp::Mod => {
          // div and mod are always working on int reg and are all 32 bit
          let src1 = expr_to_dest(ctx, &*lhs, tc_info_fn, safemode, purity);
          let src2 = expr_to_dest(ctx, &*rhs, tc_info_fn, safemode, purity);
          divmod(ctx, *op, dest, src1, src2);
        }
        ast::BinOp::Le
        | ast::BinOp::Ge
        | ast::BinOp::Lt
        | ast::BinOp::Gt
        | ast::BinOp::Eq
        | ast::BinOp::Ne => {
          // experimental mode
          let lhs_eval =
            expr_to_operand(ctx, &lhs, tc_info_fn, safemode, purity);
          let rhs_eval =
            expr_to_operand(ctx, &rhs, tc_info_fn, safemode, purity);
          ctx.add_instr(BinOp {
            op: *op,
            dest,
            src1: lhs_eval,
            src2: rhs_eval,
          });
        }
        ast::BinOp::Add | ast::BinOp::Sub => {
          let src1 = expr_to_dest(ctx, &*lhs, tc_info_fn, safemode, purity);
          let src2 = expr_to_operand(ctx, &*rhs, tc_info_fn, safemode, purity);
          ctx.add_instr(BinOp {
            op: *op,
            dest,
            src1: Operand::Var(src1),
            src2: src2,
          });
        }
        _ => {
          let src1 = expr_to_dest(ctx, &*lhs, tc_info_fn, safemode, purity);
          let src2 = expr_to_dest(ctx, &*rhs, tc_info_fn, safemode, purity);
          ctx.add_instr(BinOp {
            op: *op,
            dest,
            src1: Operand::Var(src1),
            src2: Operand::Var(src2),
          });
        }
      }
    }
    Unop(op, rhs) => {
      let src = expr_to_dest(ctx, rhs, tc_info_fn, safemode, purity);
      ctx.add_instr(UnOp {
        op: *op,
        dest,
        src: Operand::Var(src),
      });
    }
    Terop(cond, lhs, rhs) => {
      let (cond_true, cond_false, end) = ctx.create_three_lbls();

      // head
      let cond_eval = expr_to_dest(ctx, cond, tc_info_fn, safemode, purity);
      ctx.add_jmp_condition(cond_eval, cond_true, cond_false);

      // branches
      add_eval_bb(
        ctx, cond_true, &*lhs, dest, end, tc_info_fn, safemode, purity,
      );
      add_eval_bb(
        ctx, cond_false, &*rhs, dest, end, tc_info_fn, safemode, purity,
      );

      // end
      ctx.label(end);
    }
    Mem(mem) => {
      let ptr_to_mem = mem_ptr_to_dest(ctx, mem, tc_info_fn, safemode, purity);
      if safemode {
        assert_not_null(ctx, ptr_to_mem);
      }
      ctx.add_instr(MovFromHeap {
        dest,
        src: asm::HeapLocation::VarAddr(ptr_to_mem),
      });
    }
    Alloc(typsize, e_opt) => {
      // for alloc, all registers are 64 bit
      let typsize_i128 = *typsize as i128;
      assert_eq!(format!("{}", typsize_i128), format!("{}", typsize));
      let typsize_const = Operand::Const(typsize_i128, oct);

      let one_oct = Operand::Const(1, oct);
      let eight_oct = Operand::Const(8, oct);

      // prep for fn arg
      match (e_opt, safemode) {
        (Some(idx_expr), true) => {
          let idx_eval =
            expr_to_dest(ctx, &idx_expr, tc_info_fn, safemode, purity);
          if safemode {
            assert_nonneg(ctx, idx_eval);
          }

          // rdi = idx * typsize + 8
          ctx.add_instr(BinOp {
            op: ast::BinOp::Mul,
            dest: rdi,
            src1: Operand::Var(idx_eval),
            src2: typsize_const,
          });
          ctx.add_instr(BinOp {
            op: ast::BinOp::Add,
            dest: rdi,
            src1: Operand::Var(rdi),
            src2: eight_oct,
          });

          // rsi = 1
          ctx.add_instr(Mov {
            dest: rsi,
            src: one_oct,
          });

          // make call
          call_calloc(ctx, safemode);

          // writes arr length to ptr
          ctx.add_instr(WriteToHeap {
            dest: rax,
            src: Operand::Var(idx_eval),
          });

          // ptr + 8 is the start of safemode array
          ctx.add_instr(BinOp {
            op: ast::BinOp::Add,
            dest: rax,
            src1: Operand::Var(rax),
            src2: Operand::Const(8, oct),
          })
        }
        (Some(idx_expr), false) => {
          // rdi = idx
          munch_expr(ctx, edi, idx_expr, tc_info_fn, safemode, purity);
          if safemode {
            assert_nonneg(ctx, edi)
          }

          // rsi = typsize
          ctx.add_instr(Mov {
            dest: rsi,
            src: typsize_const,
          });

          // make call
          call_calloc(ctx, safemode);
        }
        // alloc(), (rdi, rsi) = (typsize, 1)
        (None, _) => {
          //rdi = typsize
          ctx.add_instr(Mov {
            dest: rdi,
            src: typsize_const,
          });

          // rsi = 1
          ctx.add_instr(Mov {
            dest: rsi,
            src: one_oct,
          });

          // make call
          call_calloc(ctx, safemode);
        }
      }

      // Writes result from %rax back to dest
      ctx.add_instr(Mov {
        dest,
        src: Operand::Var(rax),
      });
    }
    EnumVar(eid, vid, args) => {
      // size in bytes of the entire enum.
      let enum_memsize = tc_info_fn.enum_heap_size(eid);
      let memsize_i128 = enum_memsize as i128;

      // alloc size is 8 larger, to make space for tag.
      let allocsize_i128 = memsize_i128 + 8;
      let allocsize_op = Operand::Const(allocsize_i128, oct);

      // size in bytes of a certain variant.
      let variant_memsize = tc_info_fn.ev_heap_size(eid, vid);
      let variantsize_op = Operand::Const(variant_memsize as i128, oct);

      // rdi <- enum_memsize; rsi <- 1;
      ctx.add_instr(Mov {
        dest: rdi,
        src: allocsize_op,
      });
      ctx.add_instr(Mov {
        dest: rsi,
        src: Operand::Const(1, oct),
      });

      // make call
      call_calloc(ctx, safemode);

      // writes tag to rax
      ctx.add_instr(WriteToHeap {
        dest: rax,
        src: Operand::Const(tc_info_fn.ev_tag(eid, vid) as i128, quad),
      });

      // dest <- rax + 8 (which points to the start of enum memory)
      ctx.add_instr(LoadAddr {
        dest,
        src: HeapLocation::ScaleShort(8, rax),
      });

      // writes eval'd expressions to locations
      let mut running_offset: usize = 0;
      for (e_size, e) in args {
        // evaluation of e
        let e_eval = expr_to_dest(ctx, e, tc_info_fn, safemode, purity);

        // destination of e
        let e_dest = ctx.temp(oct);
        ctx.add_instr(LoadAddr {
          dest: e_dest,
          src: HeapLocation::ScaleShort(running_offset, dest),
        });

        // writes evaluation of e to its destination
        ctx.add_instr(WriteToHeap {
          dest: e_dest,
          src: Operand::Var(e_eval),
        });

        running_offset += e_size;
      }
    }
    FetchTag(e) => {
      let e_dest = expr_to_dest(ctx, e, tc_info_fn, safemode, purity);
      ctx.add_instr(LoadArrLen {
        dest,
        arr_head_addr: e_dest,
      });
    }
    Unify(expr, p) => {
      let e_dest = expr_to_dest(ctx, expr, tc_info_fn, safemode, purity);
      unify(ctx, e_dest, p, dest, tc_info_fn, safemode, purity);
    }
  }
}

/// Given a success and a failure label, performs pattern unification on
/// some dest, and jumps accordingly.
pub fn unify(
  ctx: &mut Context,
  to_be_matched: Dest,
  p: &Patt,
  result: Dest,
  tc_info_fn: &TcInfoFn,
  safemode: bool,
  purity: &HashSet<String>,
) {
  use asm::Instr::*;
  use asm::Operand;
  use DestSize::*;

  // initializes result as true; will become false if fails to unify.
  ctx.add_instr(Comment(format!("initializes unf-var: {}", result)));
  ctx.add_instr(Mov {
    dest: result,
    src: Operand::Const(1, quad),
  });

  match p {
    Patt::Variant(eid, vid, patts) => {
      // in this case, we must be matching some enum.
      let ptr_to_enum_start = to_be_matched;

      // fetch tag of expr
      let expr_tag = ctx.temp(quad);
      ctx.add_instr(LoadArrLen {
        dest: expr_tag,
        arr_head_addr: ptr_to_enum_start,
      });

      // fetch tag of pattern
      let patt_tag = tc_info_fn.ev_tag(eid, vid);
      let patt_tag_op = Operand::Const(patt_tag as i128, quad);

      // compares tag
      ctx.add_instr(Comment(format!("tries to unify {}::{}", eid, vid)));
      let (matches, fails, end) = ctx.create_three_lbls();
      ctx.add_instr(Cmp(expr_tag, patt_tag_op));
      ctx.add_instr(JmpFlag(FlagTyp::Ne, matches, fails));

      // initial match succeed, performs recursive matches.
      ctx.add_instr(Comment(format!("unified {}::{}", eid, vid)));
      ctx.label(matches);
      for i in 0..patts.len() {
        // tries to unify the ith arg with the ith rec pattern
        let ith_arg = destructure(
          ctx,
          ptr_to_enum_start,
          eid,
          vid,
          i,
          tc_info_fn,
          safemode,
          purity,
        );
        unify(
          ctx, ith_arg, &patts[i], result, tc_info_fn, safemode, purity,
        );

        // if the recursive match fails, we shortcut.
        let match_next_patt = ctx.create_lbl();
        ctx.add_instr(Test(result));
        ctx.add_instr(JmpFlag(FlagTyp::Eq, match_next_patt, end));

        ctx.label(match_next_patt);
      }
      ctx.goto(end);

      // match fails somewhere, write `false` to result and end.
      ctx.add_instr(Comment(format!("failed to unify {}::{}", eid, vid)));
      ctx.label(fails);
      ctx.add_instr(Mov {
        dest: result,
        src: Operand::Const(0, quad),
      });
      ctx.goto(end);

      ctx.label(end);
    }
    Patt::Variable(x) => {
      // this is basically creating a new variable.
      let x_var = ctx.eqsize_var(x, to_be_matched.get_size());
      ctx.add_instr(Mov {
        dest: x_var,
        src: Operand::Var(to_be_matched),
      });
    }
    Patt::Any => {}
  }
}

/// Given some ptr to enum start, the eid / vid, and argpos, fetches
/// the expr to some dest.
pub fn destructure(
  ctx: &mut Context,
  ptr_to_enum_start: Dest,
  eid: &str,
  vid: &str,
  argpos: usize,
  tc_info_fn: &TcInfoFn,
  safemode: bool,
  purity: &HashSet<String>,
) -> Dest {
  use asm::Instr::*;
  use DestSize::*;

  let arg_size_lst = tc_info_fn.enum_variant_param_sizes(eid, vid);
  // println!("arg_size_lst: {:?}", arg_size_lst);
  let arg_offset: usize = arg_size_lst[0..argpos].iter().fold(0, |x, y| x + y);
  let arg_size = match arg_size_lst[argpos] {
    4 => quad,
    8 => oct,
    k => unreachable!("Bad size of {}", k),
  };
  let dest = ctx.temp(arg_size);
  let ptr_to_arg = HeapLocation::ScaleShort(arg_offset, ptr_to_enum_start);

  ctx.add_instr(MovFromHeap {
    dest,
    src: ptr_to_arg,
  });

  dest
}

/// Checks to make sure that some `ptr` is not null.
pub fn assert_not_null(ctx: &mut Context, ptr: Dest) {
  use asm::DestSize::*;
  use asm::Instr::*;
  use asm::Operand;

  let (panic, end) = (ctx.create_lbl(), ctx.create_lbl());

  if FAST_NULLPTR_CHK {
    ctx.add_instr(NullPtrChk { ptr, panic, end });
  } else {
    // check null.
    ctx.add_instr(Comment(format!("chk {} is not NULL", ptr)));
    let is_null = ctx.temp(quad);
    ctx.add_instr(BinOp {
      op: ast::BinOp::Eq,
      dest: is_null,
      src1: Operand::Var(ptr),
      src2: Operand::Const(0, oct),
    });

    ctx.add_jmp_condition(is_null, panic, end);
  }

  ctx.label(panic);
  ctx.add_instr(FnCallSpillSize(0, "DerefNullPtr error".to_string()));
  ctx.add_instr(Panic(asm::C0RuntimeError::DerefNullPtr));
  ctx.add_instr(IncrRsp(0));
  ctx.goto(end);

  ctx.label(end);
}

/// Checks to make sure that some 32 bit `Dest` is non-negative.
pub fn assert_nonneg(ctx: &mut Context, ptr: Dest) {
  use asm::DestSize::*;
  use asm::Instr::*;
  use asm::Operand;

  // check null.
  ctx.add_instr(Comment(format!("chk {} is not negative", ptr)));
  let is_null = ctx.temp(quad);
  ctx.add_instr(BinOp {
    op: ast::BinOp::Lt,
    dest: is_null,
    src1: Operand::Var(ptr),
    src2: Operand::Const(0, quad),
  });

  let (panic_branch, end_branch) = (ctx.create_lbl(), ctx.create_lbl());

  ctx.add_jmp_condition(is_null, panic_branch, end_branch);

  ctx.label(panic_branch);
  ctx.add_instr(FnCallSpillSize(0, "DerefNullPtr error".to_string()));
  ctx.add_instr(Panic(asm::C0RuntimeError::DerefNullPtr));
  ctx.add_instr(IncrRsp(0));
  ctx.goto(end_branch);

  ctx.label(end_branch);
}

/// Similar to expr_to_dest(), except that it applies to memptr.
pub fn mem_ptr_to_dest(
  ctx: &mut Context,
  mem: &MemAccess,
  tc_info_fn: &TcInfoFn,
  safemode: bool,
  purity: &HashSet<String>,
) -> Dest {
  if MEMPTR_PROP {
    if let MemAccess::Deref(lv, n) = mem {
      if let ExprP2::Variable(x, size) = &**lv {
        if let ret @ Dest::T(..) | ret @ Dest::R(..) =
          ctx.var(x, Some(*size)).expect("failed to fetch")
        {
          return ret;
        }
      }
    }
  }

  let ret = ctx.temp(DestSize::oct);
  mem_ptr(ctx, ret, mem, tc_info_fn, safemode, purity);
  ret
}

/// Given some `MemAccess`, stores in `ptr_to_mem`
/// a pointer to `mem`.
///
/// [todo] Optimize by merging deref and offset in one go
///
/// [todo] Null checks optimization
pub fn mem_ptr(
  ctx: &mut Context,
  ptr_to_mem: Dest,
  mem: &MemAccess,
  tc_info_fn: &TcInfoFn,
  safemode: bool,
  purity: &HashSet<String>,
) {
  use asm::DestSize::*;
  use asm::HeapLocation::*;
  use asm::Instr::*;
  use asm::Operand;

  match mem {
    MemAccess::Deref(lv, n) => {
      match &**lv {
        // *x
        ExprP2::Variable(x, size) => {
          // x -> *x
          let x_dest = ctx
            .var(x, Some(*size))
            .expect("Failed at fetching var to be deref'd");
          ctx.add_instr(Mov {
            dest: ptr_to_mem,
            src: Operand::Var(x_dest),
          })
        }

        // *<mem>
        ExprP2::Mem(ref m) => {
          let ptr_to_m = mem_ptr_to_dest(ctx, m, tc_info_fn, safemode, purity);

          // (ptr_to_m) -> m
          if safemode {
            assert_not_null(ctx, ptr_to_m);
          }
          ctx.add_instr(MovFromHeap {
            dest: ptr_to_mem,
            src: VarAddr(ptr_to_m),
          })
        }

        // *alloc
        expr => {
          let ret_size = expr.size(tc_info_fn);
          let expr_eval = expr_to_dest(ctx, expr, tc_info_fn, safemode, purity);
          ctx.add_instr(Mov {
            dest: ptr_to_mem,
            src: Operand::Var(expr_eval),
          })
        }
      }
    }
    MemAccess::Offset(struct_head, offset, fieldsize) => {
      let ptr_to_struct_head = if let MemAccess::Deref(blv, _) = &**struct_head
      {
        // if struct head is represented by *v, use v instead of eval it.
        let ptr_to_struct_head = if let ExprP2::Variable(v, size_v) = &**blv {
          ctx.var(v, Some(*size_v)).expect("Failed to fetch ptr2head")
        } else {
          mem_ptr_to_dest(ctx, struct_head, tc_info_fn, safemode, purity)
        };

        // dereferencing some expression can result in null., purity
        if safemode {
          assert_not_null(ctx, ptr_to_struct_head);
        }

        ptr_to_struct_head
      } else {
        // no need to check this (offset-static) case, because the former
        // offset is recursively checked.
        mem_ptr_to_dest(ctx, struct_head, tc_info_fn, safemode, purity)
      };

      // if offset is out of range of i32::max, then add it to ptr.
      let new_offset = if *offset
        > usize::try_from(i32::MAX).expect("i32 to usize shall not fail")
      {
        let offset_128 = *offset as i128;
        assert_eq!(format!("{}", offset_128), format!("{}", *offset));
        let typsize_const = Operand::Const(offset_128, oct);

        // ptr += offset
        ctx.add_instr(BinOp {
          op: ast::BinOp::Add,
          dest: ptr_to_struct_head,
          src1: Operand::Var(ptr_to_struct_head),
          src2: Operand::Const(offset_128, oct),
        });

        0
      } else {
        *offset
      };

      ctx.add_instr(LoadAddr {
        dest: ptr_to_mem,
        src: ScaleShort(new_offset, ptr_to_struct_head),
      })
    }
    MemAccess::OffsetDyn(arr_head, idx, elt_size) => {
      let ptr_to_arr_head =
        mem_ptr_to_dest(ctx, arr_head, tc_info_fn, safemode, purity);
      let idx_eval = expr_to_dest(ctx, idx, tc_info_fn, safemode, purity);

      if safemode {
        assert_not_null(ctx, ptr_to_arr_head);
      }

      // bounds checking
      if safemode {
        // eval arr length
        let arr_len = ctx.temp(quad);
        ctx.add_instr(LoadArrLen {
          dest: arr_len,
          arr_head_addr: ptr_to_arr_head,
        });

        // create labels
        let (panic_branch, access_branch, end) = ctx.create_three_lbls();

        // overflow  <-  idx_eval >= arr_len
        let overflow = ctx.temp(quad);
        ctx.add_instr(BinOp {
          op: ast::BinOp::Ge,
          dest: overflow,
          src1: Operand::Var(idx_eval),
          src2: Operand::Var(arr_len),
        });

        // underflow  <- idx_eval < 0
        let underflow = ctx.temp(quad);
        ctx.add_instr(BinOp {
          op: ast::BinOp::Lt,
          dest: underflow,
          src1: Operand::Var(idx_eval),
          src2: Operand::Const(0, quad),
        });

        // overflow  <- overflow || underflow
        ctx.add_instr(BinOp {
          op: ast::BinOp::OOr,
          dest: overflow,
          src1: Operand::Var(overflow),
          src2: Operand::Var(underflow),
        });

        // if overflow then panic else chk_underflow
        ctx.add_jmp_condition(overflow, panic_branch, access_branch);

        ctx.label(panic_branch);
        ctx.add_instr(FnCallSpillSize(0, "exn".to_string())); // align
        ctx.add_instr(Panic(asm::C0RuntimeError::ArrayIndexOutOfBound));
        ctx.add_instr(IncrRsp(0));
        ctx.goto(end);

        ctx.label(access_branch);
        ctx.add_instr(LoadAddr {
          dest: ptr_to_mem,
          src: ScaleFull(0, Some(ptr_to_arr_head), idx_eval, *elt_size),
        });
        ctx.goto(end);

        ctx.label(end);
      } else {
        ctx.add_instr(LoadAddr {
          dest: ptr_to_mem,
          src: ScaleFull(0, Some(ptr_to_arr_head), idx_eval, *elt_size),
        });
      }
    }
  }
}

/// Adds basic block.
pub fn add_bb(
  ctx: &mut Context,
  hd: AsmLabel,
  body: &StmtP2,
  jmptgt: AsmLabel,
  tc_info_fn: &TcInfoFn,
  safemode: bool,
  purity: &HashSet<String>,
) {
  ctx.label(hd);
  munch_elabtree(ctx, body, tc_info_fn, safemode, purity);
  ctx.goto(jmptgt);
}

/// Adds expression evaluation basic block, which starts with label `hd`,
/// evaluates `expr` and assigns it to `expr_eval`, before jumping to `jmptgt`.
pub fn add_eval_bb(
  ctx: &mut Context,
  hd: AsmLabel,
  expr: &ExprP2,
  expr_eval: Dest,
  jmptgt: AsmLabel,
  tc_info_fn: &TcInfoFn,
  safemode: bool,
  purity: &HashSet<String>,
) {
  ctx.label(hd);
  munch_expr(ctx, expr_eval, expr, tc_info_fn, safemode, purity);
  ctx.goto(jmptgt);
}

/// a helper function for assign statement, which performs `rhs <= lhs op rhs`.
fn rhs_lhs_op_rhs(
  ctx: &mut Context,
  lhs: Dest,
  asnop: ast::AsnOp,
  rhs: Dest,
  tc_info_fn: &TcInfoFn,
  safemode: bool,
  purity: &HashSet<String>,
) {
  use asm::Operand;
  use ast::BinOp::*;

  match ast::to_op(asnop) {
    op @ Div | op @ Mod => {
      divmod(ctx, op, rhs, lhs, rhs);
    }
    op @ Shl | op @ Shr => {
      shift(ctx, op, rhs, lhs, rhs, tc_info_fn, safemode, purity);
    }
    op => {
      ctx.add_instr(asm::Instr::BinOp {
        op: ast::to_op(asnop),
        dest: rhs,
        src1: Operand::Var(lhs),
        src2: Operand::Var(rhs),
      });
    }
  }
}

/// Transform an `StmtP2` into a series of instructions in a context.
///
/// [todo] Assignment mem to mem direct move.
pub fn munch_elabtree(
  ctx: &mut Context,
  p2tree: &StmtP2,
  tc_info_fn: &TcInfoFn,
  safemode: bool,
  purity: &HashSet<String>,
) {
  use asm::DestSize::*;
  use asm::HeapLocation::*;
  use asm::Instr::*;
  use asm::Operand;
  use StmtP2::*;

  match p2tree {
    Declare(x, t, scope_of_x, _) => {
      ctx.eqsize_var(x, t.dsize(tc_info_fn));
      munch_elabtree(ctx, scope_of_x, tc_info_fn, safemode, purity);
    }
    Assign(LvalP2::Var(..), Some(_), _) => unreachable!("var asnop is elab'd"),
    Assign(LvalP2::Var(x, size), None, rhs) => {
      let dest = ctx.var(x, Some(*size)).expect("Failed to fetch lval var");
      munch_expr(ctx, dest, rhs, tc_info_fn, safemode, purity);
    }
    Assign(lhs @ LvalP2::Mem(lhs_mem), op, rhs_expr) => {
      ctx.add_instr(Comment(format!("{} asnop {}", lhs, rhs_expr)));
      if safemode {
        let ptr_to_lhs =
          mem_ptr_to_dest(ctx, lhs_mem, tc_info_fn, safemode, purity);

        // optionally modify rhs
        let rhs_eval = if let Some(asnop) = op {
          let rhs_eval = ctx.temp(rhs_expr.size(tc_info_fn));
          munch_expr(ctx, rhs_eval, rhs_expr, tc_info_fn, safemode, purity);

          assert_not_null(ctx, ptr_to_lhs);

          // eval lhs
          let lhs_eval = ctx.temp(lhs.access_size());
          ctx.add_instr(MovFromHeap {
            dest: lhs_eval,
            src: VarAddr(ptr_to_lhs),
          });

          rhs_lhs_op_rhs(
            ctx, lhs_eval, *asnop, rhs_eval, tc_info_fn, safemode, purity,
          );

          rhs_eval
        } else {
          expr_to_dest(ctx, rhs_expr, tc_info_fn, safemode, purity)
        };

        // only needs to chk ptr if not yet checked
        if op.is_none() {
          assert_not_null(ctx, ptr_to_lhs);
        }

        // write rhs_eval to lhs
        ctx.add_instr(WriteToHeap {
          dest: ptr_to_lhs,
          src: Operand::Var(rhs_eval),
        })
      } else {
        let ptr_to_lhs =
          mem_ptr_to_dest(ctx, lhs_mem, tc_info_fn, safemode, purity);

        // optionally modify rhs
        let rhs_eval = if let Some(asnop) = op {
          let rhs_eval = ctx.temp(rhs_expr.size(tc_info_fn));
          munch_expr(ctx, rhs_eval, rhs_expr, tc_info_fn, safemode, purity);

          // eval lhs
          let lhs_eval = ctx.temp(lhs.access_size());
          ctx.add_instr(MovFromHeap {
            dest: lhs_eval,
            src: VarAddr(ptr_to_lhs),
          });

          rhs_lhs_op_rhs(
            ctx, lhs_eval, *asnop, rhs_eval, tc_info_fn, safemode, purity,
          );

          rhs_eval
        } else {
          expr_to_dest(ctx, rhs_expr, tc_info_fn, safemode, purity)
        };

        // write rhs_eval to lhs
        ctx.add_instr(WriteToHeap {
          dest: ptr_to_lhs,
          src: Operand::Var(rhs_eval),
        })
      }
    }
    If(cond, s1, s2) => {
      let (cond_true, cond_false, end) = ctx.create_three_lbls();
      if FAST_FLAG {
        let flag = false_flag(ctx, cond, tc_info_fn, safemode, purity);
        ctx.add_instr(JmpFlag(flag, cond_true, cond_false));
      } else {
        let cond_eval = expr_to_dest(ctx, cond, tc_info_fn, safemode, purity);
        ctx.add_jmp_condition(cond_eval, cond_true, cond_false);
      }

      // if branches
      add_bb(ctx, cond_true, s1, end, tc_info_fn, safemode, purity);
      add_bb(ctx, cond_false, s2, end, tc_info_fn, safemode, purity);

      // if end
      ctx.label(end);
    }
    While(cond, s) => {
      ctx.increment_loop_depth();

      let (head, body, end) = ctx.create_three_lbls();

      // add a jmp here to ensure that all basic blocks end with jmp.
      ctx.goto(head);
      ctx.label(head);

      // expr shall be re-computed per iteration.
      if FAST_FLAG {
        let flag = false_flag(ctx, cond, tc_info_fn, safemode, purity);
        ctx.add_instr(JmpFlag(flag, body, end));
      } else {
        let cond_eval = expr_to_dest(ctx, cond, tc_info_fn, safemode, purity);
        ctx.add_jmp_condition(cond_eval, body, end);
      }
      add_bb(ctx, body, s, head, tc_info_fn, safemode, purity);
      ctx.label(end);

      ctx.decrement_loop_depth();
    }
    Ret(Some(expr)) => {
      let dest = ctx.temp(expr.size(tc_info_fn));
      munch_expr(ctx, dest, expr, tc_info_fn, safemode, purity);
      ctx.add_instr(Return(Operand::Var(dest)));
    }
    Ret(None) => ctx.add_instr(ReturnVoid),
    Seq(s1, s2) => {
      munch_elabtree(ctx, s1, tc_info_fn, safemode, purity);
      munch_elabtree(ctx, s2, tc_info_fn, safemode, purity);
    }
    Eval(expr) => {
      if !expr.pure(purity) {
        let dest = ctx.temp(expr.size(tc_info_fn));
        munch_expr(ctx, dest, expr, tc_info_fn, safemode, purity);
      }
    }
    Nop => (),
  }
}

/// Converts an entire program into a vector of contexts, each representing
/// a standalone function.
pub fn mk_asm_l4(
  ep: &elab_after_tc::ProgramP2,
  tc_info_fn: &TcInfoFn,
  safemode: bool,
) -> Vec<Context> {
  let purity = ep.pure_fns();
  println!("Pure fns: \n{:?}", purity);
  let mut ret = Vec::<Context>::new();
  for fdef in &ep.0 {
    ret.push(Context::from_glob_l4(fdef, tc_info_fn, safemode, &purity));
  }
  ret
}
