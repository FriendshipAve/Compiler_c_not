use std::collections::HashMap;

use crate::{
  asm::{AsmLabel, Instr},
  codegen::Context,
};

pub mod intrafunction_structure;
pub mod regalloc_assign_pass;

/// Coalesce consecutive (and therefore equivalent) blocks of labels.
///
/// [warning] This works for only one function at a time.
pub fn truncate_empty_basic_block(ctx: &mut Context) {
  // maps each label to its replacement.
  let mut equiv_lbls = HashMap::<AsmLabel, AsmLabel>::new();

  // when a seq of labels present, we keep the first one and rm the rest.
  let mut fst_lbl_opt: Option<AsmLabel> = None;

  for ins in &ctx.instrs {
    // skip the label that represents top of function.
    if ins.is_start_of_function() {
      continue;
    }

    if let Instr::Lbl(curr_lbl) = ins {
      // entered consecutive labels
      match fst_lbl_opt {
        // curr_lbl is not the first in the consecutive label block, therefore
        // must be replaced by the first label of its block.
        Some(fst_lbl) => {
          equiv_lbls.insert(*curr_lbl, fst_lbl);
        }

        // curr_lbl is the first in the consecutive label block.
        None => {
          fst_lbl_opt = Some(*curr_lbl);
        }
      }
    } else {
      fst_lbl_opt = None; // leaved consecurive labels
    }
  }

  // replace labels within goto comands
  for ins in &mut ctx.instrs {
    match ins {
      Instr::Jmp(ref mut lbl) => {
        *lbl = *equiv_lbls.get_mut(&lbl).unwrap_or(lbl);
      }
      Instr::JmpCondition {
        condition: _,
        ref mut tgt_true,
        ref mut tgt_false,
      } => {
        *tgt_true = *equiv_lbls.get_mut(&tgt_true).unwrap_or(tgt_true);
        *tgt_false = *equiv_lbls.get_mut(&tgt_false).unwrap_or(tgt_false);
      }
      _ => (),
    }
  }

  // remove redundant labels
  ctx.instrs = ctx
    .instrs
    .clone()
    .into_iter()
    .filter(|ins| {
      if let Instr::Lbl(lbl) = ins {
        !equiv_lbls.contains_key(lbl)
      } else {
        true
      }
    })
    .collect();
}
