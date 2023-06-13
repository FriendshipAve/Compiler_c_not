//! Graphs of basic blocks + extended basic blocks within the same function.
//!
//! Author: Owen Li <tianwei2@andrew.cmu.edu>

use crate::{
  asm::{AsmLabel, Dest, Instr},
  codegen::{self, TmpDepthMap},
  reg_alloc::lifetime::{AnnotatedInstrBlock, LivenessInfo},
  util::datastructure::Counter,
};
use std::collections::{HashMap, HashSet};

use crate::const_params::*;

use crate::reg_alloc::reg_alloc_err::RegAllocErr;

#[derive(Debug)]
#[allow(dead_code)]
pub enum Error {
  NotBasicBlk,
  NotExtendedBasicBlk,
}

/// Munch the first basic block of a some function in asm.
fn munch_fnhead_bb<T>(instrs_stream: &mut T, optimize_level: usize) -> FnHead
where
  T: Iterator<Item = Instr>,
{
  match instrs_stream.next() {
    Some(Instr::FnLbl(name)) => {
      let mut instrs = Vec::<Instr>::new();

      instrs.push(Instr::FnLbl(name.clone()));

      let nexts = munch_remaining_blk(instrs_stream, &mut instrs);

      FnHead {
        name,
        instrs: AnnotatedInstrBlock::from_instrs(instrs, optimize_level),
        nexts,
      }
    }
    x => panic!("Expected to munch `FnLbl`, found `{:?}`", x),
  }
}

/// Munch a `BodyBlock` from asm instruction.
/// If given an empty instruction stream, returns `None`.
///
/// [warning] This does __NOT__ initialize the `prevs` field.
fn munch_fnbody_bb<T>(
  instrs_stream: &mut T,
  optimize_level: usize,
) -> Option<BodyBlock>
where
  T: Iterator<Item = Instr>,
{
  // we skip irrelevant stuff until a new label is encountered.
  'skip_things_b4_lbl: loop {
    match instrs_stream.next() {
      Some(Instr::Lbl(label)) => {
        let mut bb_instrs = Vec::<Instr>::new();

        bb_instrs.push(Instr::Lbl(label));

        let nexts = munch_remaining_blk(instrs_stream, &mut bb_instrs);

        break 'skip_things_b4_lbl Some(BodyBlock {
          label,
          prevs: None,
          bb_instrs: AnnotatedInstrBlock::from_instrs(
            bb_instrs,
            optimize_level,
          ),
          nexts,
        });
      }
      Some(x) => continue 'skip_things_b4_lbl,
      // panic!("Expected to munch `Lbl`, found `{:?}`", x), // legacy code
      None => break 'skip_things_b4_lbl None,
    }
  }
}

/// Munch the remaining of the basic block and push everything onto `bb_instrs`,
/// until there is either some `Jmp`,
/// `JmpCondition`, or we run out of instructions. On success, returns a vector
/// representing the potential jmp targets of such a basic block; If
/// encounters a label, return a `NotBasicBlock` error.
fn munch_remaining_blk<T>(
  instrs_stream: &mut T,
  bb_instrs: &mut Vec<Instr>,
) -> Vec<AsmLabel>
where
  T: Iterator<Item = Instr>,
{
  let mut encountered_return: bool = false;
  while let Some(ins) = instrs_stream.next() {
    use Instr::*;
    if !(encountered_return && IGNORE_UNREACHABLE_INSTRS) {
      bb_instrs.push(ins.clone())
    };
    match ins {
      Jmp(tgt) => {
        // if encountered RET, there's no `next block`.
        return if encountered_return && IGNORE_UNREACHABLE_JMPS {
          vec![]
        } else {
          vec![tgt]
        };
      }
      JmpCondition {
        condition: _,
        tgt_true,
        tgt_false,
      } => {
        return if encountered_return && IGNORE_UNREACHABLE_JMPS {
          vec![]
        } else {
          vec![tgt_true, tgt_false]
        };
      }
      NullPtrChk { ptr: _, panic, end } => {
        return if encountered_return && IGNORE_UNREACHABLE_JMPS {
          vec![]
        } else {
          vec![panic, end]
        };
      }
      JmpFlag(_, tgt_true, tgt_false) => {
        return if encountered_return && IGNORE_UNREACHABLE_JMPS {
          vec![]
        } else {
          vec![tgt_true, tgt_false]
        };
      }
      Lbl(_) => {
        panic!("Lbl can't appear in middle of basic block in {}", ins)
      }
      FnLbl(_) => {
        panic!("FnLbl can't appear in middle of basic block")
      }
      Return(_) => {
        // read and ignore instructions after return
        encountered_return = true;
      }
      _ => {} // UnOp / BinOp / Mov, no special treatment.
    }
  }
  vec![] // run out of instructions, no 'goto', thus no jmp target.
}

/// An enum type that encodes the set of possible basic block, which
/// can be either a `FnHead` or a `BodyBlock`.
#[derive(PartialEq, Eq, Hash, Clone)]
pub enum BasicBlock {
  Body(AsmLabel),
  Head(String),
}

impl std::fmt::Debug for BasicBlock {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      BasicBlock::Body(lbl) => write!(f, "{}", lbl),
      BasicBlock::Head(s) => write!(f, "<.{}>", s),
    }
  }
}

/// A basic block as an element of the control flow graph. Must contain a
/// specific label in the beginning and some form of jump in the end, with no
/// labels / jumps anywhere else.
pub struct BodyBlock {
  pub label: AsmLabel,
  pub prevs: Option<HashSet<BasicBlock>>,
  pub bb_instrs: AnnotatedInstrBlock,
  pub nexts: Vec<AsmLabel>,
}

impl BodyBlock {
  /// Initialize `self.prevs` (optional) and insert `bb`.
  fn init_or_insert_prev(&mut self, bb: BasicBlock) {
    match &mut self.prevs {
      Some(ref mut s) => {
        s.insert(bb);
      }
      None => {
        let mut s = HashSet::<BasicBlock>::new();
        s.insert(bb);
        self.prevs = Some(s);
      }
    }
  }

  /// for dbg purposes
  pub fn print_current_liveness(&self) {
    println!("{}", self.to_string())
  }
}

impl std::fmt::Display for BodyBlock {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}\n", self.bb_instrs)
  }
}

/// Special basic block that represents the head of the function.
/// Can only be reached by function calls, but not by jumps.
pub struct FnHead {
  pub name: String,
  pub instrs: AnnotatedInstrBlock,
  pub nexts: Vec<AsmLabel>,
}

impl FnHead {
  /// for dbg purposes
  fn print_current_liveness(&self) {
    println!("{}", self.to_string())
  }
}

impl std::fmt::Display for FnHead {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}\n", self.instrs)
  }
}

/// A graph of basic blocks within a single function.
pub struct BBGraph {
  head: FnHead,
  body: HashMap<AsmLabel, BodyBlock>,
  prevs_initialized: bool,
  pub tmp_depth: TmpDepthMap,
}

impl BBGraph {
  /// Gets the name of function as represented by this BBG.
  pub fn get_fn_name(&self) -> &str {
    &self.head.name
  }

  /// Given a vector of instructions that represents a single function,
  /// creates a corresponding instance of `BBGraph`, and initializes the prevs.
  ///
  /// This function automatically init's all `uses` and `defines`.
  pub fn from_codegen_ctx(
    ctx: codegen::Context,
    optimize_level: usize,
  ) -> Self {
    let mut instrs_stream = ctx.instrs.into_iter();
    let head = munch_fnhead_bb(&mut instrs_stream, optimize_level);
    let mut body = HashMap::<AsmLabel, BodyBlock>::new();
    while let Some(bb) = munch_fnbody_bb(&mut instrs_stream, optimize_level) {
      body.insert(bb.label, bb);
    }
    let mut ret = BBGraph {
      head,
      body,
      prevs_initialized: false,
      tmp_depth: ctx.temp_depth_map,
    };
    ret.init_prevs();
    ret
  }

  /// Returns an optional mutable reference to the corresponding block of
  /// `lbl`, if it exist.
  fn get_mut_body_block(&mut self, lbl: &AsmLabel) -> Option<&mut BodyBlock> {
    self.body.get_mut(lbl)
  }

  /// Returns an optional immutable reference to the corresponding block of
  /// `lbl`, if it exist.
  fn get_body_block(&self, lbl: &AsmLabel) -> Option<&BodyBlock> {
    self.body.get(lbl)
  }

  /// Initializes the `prevs` field of basic blocks in graph.
  fn init_prevs(&mut self) {
    // process function head basic block

    let head_lbl = self.head.name.clone();
    let head_nexts = self.head.nexts.clone();

    for child_lbl in &head_nexts {
      let child_blk = self
        .get_mut_body_block(child_lbl)
        .expect("Head cannot jmp out of fn body");

      child_blk.init_or_insert_prev(BasicBlock::Head(head_lbl.clone()));
    }

    // process other basic blocks

    let bodyblk_lbls: Vec<AsmLabel> = self.body.keys().cloned().collect();

    for parent_lbl in bodyblk_lbls {
      let parent_nexts = self
        .get_body_block(&parent_lbl)
        .expect("parent_lbl should be a valid label of body block")
        .nexts
        .clone();

      for child_lbl in parent_nexts {
        let child_blk = self
          .get_mut_body_block(&child_lbl)
          .expect("Body cannot jmp out of fn body");
        child_blk.init_or_insert_prev(BasicBlock::Body(parent_lbl));
      }
    }

    // Mark unreachable basic blocks' prevs as initialized.
    // [todo] should be turned off once dead-code-removal is impl'd.
    for mut item in self.body.values_mut() {
      if item.prevs.is_none() {
        item.prevs = Some(HashSet::<BasicBlock>::new());
      }
    }

    self.prevs_initialized = true;
  }

  /// Returns an immutable reference to the collection of previous
  /// basic blocks of `lbl`.
  fn get_prevs_cpy(&self, lbl: &AsmLabel) -> HashSet<BasicBlock> {
    self
      .get_body_block(lbl)
      .expect("cannot get_prevs of nonexistent block")
      .prevs
      .as_ref()
      .expect("cannot get_prevs if prevs are uninitialized")
      .clone()
  }

  // ---------------------- Lifetime propagation module ----------------------

  /// Union the given `LivenessInfo` into the last liveout of the basic block
  /// specified in args.
  fn update_basicblock_last_liveout(
    &mut self,
    bb: BasicBlock,
    extra_liveout: &LivenessInfo,
  ) -> Result<(), RegAllocErr> {
    let annot_instr_blk_to_update = match bb {
      BasicBlock::Head(s) => {
        assert_eq!(s, self.head.name);
        &mut self.head.instrs
      }
      BasicBlock::Body(lbl) => {
        &mut self
          .get_mut_body_block(&lbl)
          .expect("cannot update last liveout of nonexistent block")
          .bb_instrs
      }
    };

    annot_instr_blk_to_update.add_to_last_liveout(extra_liveout)
  }

  /// Re-propagates the liveins and liveouts independently within each basic
  /// block, in response to their potentially changed liveouts of last lines.
  /// Does not consider the interferences between basic blocks.
  ///
  /// [returns] a boolean indicating if everything within such a
  /// propagation is saturated.
  fn propagate_liveio_foreach(&mut self) -> Result<bool, RegAllocErr> {
    let mut saturated: bool = true;
    for blk in self.body.values_mut() {
      let blk_saturated = blk.bb_instrs.propagate_liveio()?;
      saturated = saturated && blk_saturated;
    }
    let head_saturated = self.head.instrs.propagate_liveio()?;
    saturated = saturated && head_saturated;
    Ok(saturated)
  }

  /// Propagates the liveins of first instructions in each basic block to its
  /// set of `prevs`'s liveouts.
  fn propagate_liveio_across(&mut self) -> Result<(), RegAllocErr> {
    assert!(self.prevs_initialized);

    let bodyblk_lbls: Vec<AsmLabel> = self.body.keys().cloned().collect();

    for child_lbl in bodyblk_lbls {
      let child_fst_livein = self
        .get_body_block(&child_lbl)
        .expect("cannot get fst_livein of nonexistent child")
        .bb_instrs
        .get_fst_livein()
        .clone();

      for parent in self.get_prevs_cpy(&child_lbl) {
        self.update_basicblock_last_liveout(parent, &child_fst_livein)?;
      }
    }
    Ok(())
  }

  /// Initializes each basic block's liveio, then alternates between
  /// `propagate_liveio_foreach()` and `propagate_liveio_across()` until
  /// everything saturates.
  pub fn propagate_liveio_till_saturation(
    &mut self,
  ) -> Result<(), RegAllocErr> {
    while !self.propagate_liveio_foreach()? {
      if DBG_INTRAFUNCTION_LIVENESS {
        print!("\n<< foreach >>\n");
        self.print_current_liveness();
      }

      self.propagate_liveio_across()?;

      if DBG_INTRAFUNCTION_LIVENESS {
        print!("\n<< across >>\n");
        self.print_current_liveness();
      }
    }

    if DBG_INTRAFUNCTION_LIVENESS {
      print!("\n<<< saturated: >>>\n");
      self.print_current_liveness();
    }

    Ok(())
  }

  /// Computes the set of variables across all basic blocks.
  pub fn variable_set(&self) -> HashSet<Dest> {
    let mut ret: HashSet<Dest> = HashSet::new();

    for item in self.body.values() {
      ret.extend(item.bb_instrs.variable_set());
    }

    ret.extend(self.head.instrs.variable_set());

    ret
  }

  /// Counts the occurrences of temps.
  pub fn count_temp(&self) -> Counter<u32> {
    let mut counter = Counter::<u32>::mk_empty();

    for item in self.body.values() {
      item.bb_instrs.count_temp(&mut counter);
    }

    self.head.instrs.count_temp(&mut counter);

    counter
  }

  /// Computes the set of variable interference across all basic blocks.
  pub fn get_interference_set(&self) -> HashSet<(Dest, Dest)> {
    let mut interference_set: HashSet<(Dest, Dest)> = HashSet::new();

    for item in self.body.values() {
      interference_set.extend(item.bb_instrs.get_interference_set());
    }

    interference_set.extend(self.head.instrs.get_interference_set());

    interference_set
  }

  /// Computes a vector of `(source, dest)` pairs of `mov` instructions.
  /// Only considers sources and destinations that are of type `asm::Dest`.
  pub fn mov_instrs(&self) -> Vec<(Dest, Dest)> {
    let mut ret = Vec::<(Dest, Dest)>::new();

    for item in self.body.values() {
      ret.extend(item.bb_instrs.mov_instrs());
    }

    ret.extend(self.head.instrs.mov_instrs());

    ret
  }

  /// For debug purposes
  pub fn print_current_liveness(&self) {
    self.head.print_current_liveness();
    for item in self.body.values() {
      item.print_current_liveness();
    }
    println!("\n<-->\n");
  }

  pub fn to_bbg_print(self) -> BBGraphPrint {
    BBGraphPrint(self)
  }
}

impl std::fmt::Display for BBGraph {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "<{}>:  {:?}\n", self.head.name, self.head.nexts)?;
    for (_, v) in &self.body {
      write!(
        f,
        "{:<5}:  {:?}; {:?}\n",
        v.label,
        v.prevs
          .as_ref()
          .expect("cannot print prevs unless init'd {}"),
        v.nexts
      )?;
    }
    write!(f, "\n")
  }
}

// A type for pretty-printing.
pub struct BBGraphPrint(BBGraph);

impl std::fmt::Display for BBGraphPrint {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.0.head)?;
    for item in self.0.body.values() {
      write!(f, "{}", item)?;
    }
    write!(f, "\n<-->")
  }
}
