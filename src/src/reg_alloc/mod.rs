// Register Allocation
// Author: Owen Li <tianwei2@andrew.cmu.edu>

use std::collections::{HashMap, HashSet};

use crate::{
  asm_processing::intrafunction_structure::BBGraph, codegen::Context,
};
pub mod ast_graph_node;
use ast_graph_node::*;
pub mod x86_register;

pub mod lifetime;

pub mod var_graph;
use var_graph::*;

pub mod reg_alloc_err;

use self::{
  reg_alloc_err::RegAllocErr,
  x86_register::{NamedReg, RegAbs86},
};
use crate::const_params::*;

/// Consumes a codegen::Context instance, converts it into a register
/// assignment in the form of a hashmap, paired with some set of used named
/// registers, as well the number of spill registers used.
///
/// [returns] Some tuple of `(m, s, n)`, where `m` is a hashmap that converts
/// any temporary address to its assigned register (named or spilled), `s` is
/// a set of registers that is used, and
/// `n` is the number of spilled register used.
#[allow(dead_code)]
pub fn context_to_assignment(
  ctx: Context,
  optimize_level: usize,
) -> (HashMap<Node, RegAbs86>, HashSet<NamedReg>, usize) {
  // eprintln!("[{}] Regalloc begin", ctx.get_name());
  if (optimize_level == 0 && ctx.temp_index as usize > LARGE_TEMP_SIZE)
    || (optimize_level == 1 && ctx.temp_index as usize > O1_TEMP_SIZE)
  {
    eprintln!(
      "Warning: large number of temporaries: {} > {}",
      ctx.temp_index, LARGE_TEMP_SIZE
    );
    return spill_everything(ctx);
  }

  let mut bbg = BBGraph::from_codegen_ctx(ctx.clone(), optimize_level);

  let mut vg = if CONSIDER_CTRLFLOW_LIVENESS {
    let maybe_err = bbg.propagate_liveio_till_saturation();
    if let Err(RegAllocErr::LiveioExceedsThreshold) = maybe_err {
      eprintln!("Warning: liveio exceeds threshold, spilling everything");
      return spill_everything(ctx);
    }
    NodeGraphHs::from_bbgraph(&bbg)
  } else {
    unimplemented!("Regalloc without control flow is deprecated")
  };

  let mut result = if REG_COALESCE {
    let coal_map =
      vg.greedy_coalesce(vg.maybe_coalesces(&bbg), REG_COALESCE_THRESHOLD);
    let (mp, regs, numspill) = vg.assign_register();
    let ret = (coal_map.expand_node_col_map(mp), regs, numspill);
    // eprintln!("[{}] Regalloc done\n", ctx.geet_name());
    ret
  } else {
    vg.assign_register()
  };

  // remove rsp from used named registers, because for it is neither caller or callee saved register
  // remove all 6 input registers, since they are handled by codegen
  result.1.remove(&NamedReg::Rsp);
  result
}

/// Does not perform register allocation and treats everything as temp.
fn spill_everything(
  ctx: Context,
) -> (HashMap<Node, RegAbs86>, HashSet<NamedReg>, usize) {
  let mut res = HashMap::new();
  for i in 0..ctx.temp_index {
    res.insert(Node::Temporary(i), RegAbs86::Spill(i as usize));
  }

  // In theory can be optimized via tracing the instrs, but counting the
  // potentially used named registers via function arity is a simple and
  // safe method.
  let used_named_regs = NamedReg::used_namedregs_from_arity(ctx.get_arity());
  return (res, used_named_regs, ctx.temp_index as usize);
}
