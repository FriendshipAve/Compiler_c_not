//! Dedicated to record constant parameters that
//! influence the Compiler's design choice.

use crate::reg_alloc::x86_register::NamedReg::{self, *};

/// Ignores all instructions after RET in each basic block.
pub const IGNORE_UNREACHABLE_INSTRS: bool = false;

/// Ignores all jump relations after RET in each basic block.
pub const IGNORE_UNREACHABLE_JMPS: bool = false;

/// Prints dbg log for control flow liveness.
pub const DBG_INTRAFUNCTION_LIVENESS: bool = false;

/// Handles non-straightline code liveness analysis.
pub const CONSIDER_CTRLFLOW_LIVENESS: bool = true;

/// Register allocation temp size threshold for l4 and before
pub const LARGE_TEMP_SIZE: usize = 2600;

/// Register allocation max number of living temp threshold for l4 and before
pub const LARGE_LIVEIO_THRESHOLD: usize = 105;

/// Register allocation temp size threshold for l4 and before
pub const O1_TEMP_SIZE: usize = 2600;

/// Register allocation max number of living temp threshold for l4 and before
pub const O1_LIVEIO_THRESHOLD: usize = 105;

/// Debugs max cardinality search
pub const DBG_MCS: bool = false;

/// Uses naive fncall expression during codegen
pub const NAIVE_FNCALL_DURING_CODEGEN: bool = false;

/// Forcibly disable typechecker regardless of CLI flag.
/// shall not skip typechecking since we need the info for codegen and elab pass 2.
pub const NO_TYPECHECK: bool = false;

/// Treats register %rsp as nonexistent during reg_alloc
pub const REGALLOC_IGNORE_RSP: bool = true;

/// Stores and restores all 6 registers (6 fn args, BUT NOT %r10) before
/// and after fncall, regardless of their uses later in program
pub const FNCALL_STORE_ALL_SIX_REGS: bool = true;

/// Move first six function arguments to temps,
/// and address them as such.
pub const MOVE_FNARG_FROM_REGS_TO_TEMPS: bool = true;

/// Explicitly push to save caller-saved registers before function call,
/// and restore after function call.
pub const EXPLICIT_PUSH_POP_CALLER_SAVED_REGS: bool = false;

/// Number of fnargs passed by register during call.
pub const NUM_ARGS_PASSED_BY_REGS: usize = 6;

/// Registers that caller should save. Does not incl R10 and R11 since
/// they are for scratch works.
pub const CALLER_SHOULD_SAVE: [NamedReg; 6] = [
  NamedReg::Rdi,
  NamedReg::Rsi,
  NamedReg::Rdx,
  NamedReg::Rcx,
  NamedReg::R8,
  NamedReg::R9,
];

/// Regalloc register pool
pub const REGALLOC_POOL: [NamedReg; 12] =
  [Rax, Rdi, Rdx, Rcx, R8, R9, Rbx, R12, R13, R14, R15, Rbp];

/// Max degree of inference for reg-coalescing.
pub const REG_COALESCE_THRESHOLD: usize = 12;

/// Enables Dest / Operand prop.
pub const DEST_OP_PROP: bool = true;

/// Enables memptr prop.
pub const MEMPTR_PROP: bool = true;

/// Enables fast nullptr check in safe mode.
pub const FAST_NULLPTR_CHK: bool = true;

/// Enables register coalescing.
pub const REG_COALESCE: bool = true;

/// Enables max-cardinality search heuristics.
pub const ENABLE_MCS_HEURISTICS: bool = true;

/// Simplifies CFG flag generation
pub const FAST_FLAG: bool = true;

/// Enables useless analysis.
pub const SKIP_USELESS_CODE: bool = true;

/// Preserves trivial infinite loop
pub const KEEP_TRIVIAL_LOOP: bool = false;

/// Performs function inlining
pub const FN_INLINE: bool = false;
