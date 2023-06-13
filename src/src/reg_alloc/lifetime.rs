use crate::{
  asm::{Dest, Instr, Operand},
  const_params::{LARGE_LIVEIO_THRESHOLD, O1_LIVEIO_THRESHOLD},
  util::datastructure::Counter,
};

use std::{
  collections::HashSet,
  fmt::{Display, Error},
};

use super::reg_alloc_err::RegAllocErr;

/// A vector consists of the label (ie. asm::Dest) of temp variables,
/// used for encoding the liveness (ie. livein / liveout) information of
/// each instruction.
///
/// usize is the optimize level
///
/// Note that this type is wrapped around an Option<> to make sure it is not
/// used before initialized. Rust will perform null-optimization.
#[derive(Clone)]
pub struct LivenessInfo(HashSet<Dest>, usize);

/// A struct for passing around a pair of use and define info.
pub struct UsesDefine {
  uses: LivenessInfo,
  define: LivenessInfo,
}

/// Instruction with livein & liveout annotations.
///
/// [TODO] optimize-out either livein or liveout.
pub struct AnnotatedInstr {
  livein: LivenessInfo,
  liveout: LivenessInfo,
  uses: LivenessInfo,
  define: LivenessInfo,
  instr: Instr,
}

/// A straight-line block (ie. basic block) of instructions, available
/// for liveness annotation.
///
/// [warning] cannot yet handle control flows.
///
/// [todo] in future labs, handle inter-block control flow.
pub struct AnnotatedInstrBlock {
  ops: Vec<AnnotatedInstr>,
  liveio_up_to_date: bool,
}

impl LivenessInfo {
  /// Creates a new empty `LivenessInfo`.
  pub fn empty(optimize_level: usize) -> Self {
    Self(HashSet::<Dest>::new(), optimize_level)
  }

  /// Gets the encapsulated set.
  pub fn get_set(&self) -> &HashSet<Dest> {
    &self.0
  }

  /// Inserts the content of Self into the given HashSet<Dest>.
  /// Returns error if self is not initialized.
  pub fn insert_into_hashset(&self, varset: &mut HashSet<Dest>) {
    varset.extend(self.get_set());
  }

  /// Adds the occurrences of temps towards a counter.
  pub fn count_temp(&self, counter: &mut Counter<u32>) {
    for item in &self.0 {
      if let Dest::T(n, _) = item {
        counter.insert(n);
      }
    }
  }

  /// Performs checked-extend; returns error if size exceeds threshold.
  pub fn checked_extend(
    &mut self,
    rhs: LivenessInfo,
  ) -> Result<(), RegAllocErr> {
    self.0.extend(rhs.0);
    if (self.1 == 0 && self.0.len() > LARGE_LIVEIO_THRESHOLD)
      || (self.1 == 1 && self.0.len() > O1_LIVEIO_THRESHOLD)
    {
      eprintln!("Liveio exceeds threshold: {}", self.0.len());
      Err(RegAllocErr::LiveioExceedsThreshold)
    } else {
      Ok(())
    }
  }
}

impl UsesDefine {
  pub fn new(
    uses: HashSet<Dest>,
    define: HashSet<Dest>,
    optimize_level: usize,
  ) -> Self {
    Self {
      uses: LivenessInfo(uses, optimize_level),
      define: LivenessInfo(define, optimize_level),
    }
  }
}

impl std::ops::Add for LivenessInfo {
  type Output = Result<Self, RegAllocErr>;
  fn add(mut self, rhs: Self) -> Self::Output {
    self.checked_extend(rhs)?;
    Ok(self)
  }
}

impl std::ops::Sub for LivenessInfo {
  type Output = Self;
  fn sub(self, rhs: Self) -> Self::Output {
    assert_eq!(self.1, rhs.1, "LivenessInfo::Sub: optimize level mismatch");
    LivenessInfo(&self.0 - &rhs.0, self.1)
  }
}

impl PartialEq for LivenessInfo {
  fn eq(&self, other: &Self) -> bool {
    let mut l1: Vec<Dest> = self.0.iter().cloned().collect();
    let mut l2: Vec<Dest> = other.0.iter().cloned().collect();
    l1.sort();
    l2.sort();
    l1 == l2
  }
}

impl Display for LivenessInfo {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{:?}", self.0)
  }
}

impl AnnotatedInstr {
  /// Consumes an asm::Instr argument, creates an empty instance of
  /// AnnotatedInstr,
  pub fn from_instr(instr: Instr, optimize_level: usize) -> Self {
    AnnotatedInstr {
      livein: LivenessInfo::empty(optimize_level),
      liveout: LivenessInfo::empty(optimize_level),
      uses: LivenessInfo::empty(optimize_level),
      define: LivenessInfo::empty(optimize_level),
      instr,
    }
  }

  /// Recomputes livein using formula "livein = uses + (liveout - defines)"
  pub fn init_livein(&mut self) -> Result<(), RegAllocErr> {
    self.livein =
      (self.uses.clone() + (self.liveout.clone() - self.define.clone()))?;
    Ok(())
  }

  /// Given a hashset of interferences, appends the variable interferences
  /// from self. Specifically, variable interference is a symmetric relation
  /// where (u, v) interferes with each other iff one is the destination
  /// of Self.instr, and another is within Self.liveout.
  pub fn add_interference_to(&self, db: &mut HashSet<(Dest, Dest)>) {
    for u in &self.define.0 {
      for v in &self.liveout.0 {
        // Only adds interferences in (small, large) order to save space.
        // Interference graph creation process will automatically insert both
        // edges, as it is designed to produce only undirected graphs.
        if u < v {
          db.insert((*u, *v));
        } else if v < u {
          db.insert((*v, *u));
        } else {
          // do nothing because self-interference is auto-handled
          // in graph coloring.
        }
      }
    }
  }
}

impl AnnotatedInstrBlock {
  /// Consumes a vector of asm::Instr, creates an instance of Self, with uses
  /// and defines initialized but liveins and liveouts empty.
  ///
  /// [requires] `opvec` does not contain any `label` or `goto` besides
  /// possibly at head / tail.
  pub fn from_instrs(opvec: Vec<Instr>, optimize_level: usize) -> Self {
    let mut ret = AnnotatedInstrBlock {
      ops: opvec
        .into_iter()
        .map(|x| AnnotatedInstr::from_instr(x, optimize_level))
        .collect(),
      liveio_up_to_date: false,
    };
    ret.init_ud(optimize_level);
    ret
  }

  /// Consumes oneself and returns its ops.
  pub fn to_ops(self) -> Vec<AnnotatedInstr> {
    self.ops
  }

  /// Initializes the 'use' and 'define' field of each annotated instruction.
  ///
  /// [warning] iter_mut() is used
  fn init_ud(&mut self, optimize_level: usize) {
    let mut item = self.ops.iter_mut();

    while let Some(annot_instr) = item.next() {
      let ud = annot_instr.instr.use_define(optimize_level);
      annot_instr.uses = ud.uses;
      annot_instr.define = ud.define;
    }
  }

  /// Propagate livein's and liveout's in a back-and-forth manner, similar
  /// to dynamic programming. Returns an error if some liveness lines' size
  /// exceeds the limiting threshold.
  ///
  /// [note] This function returns `Ok(true)` immediately if there is nothing
  /// to update.
  ///
  /// [returns] A `Result<bool>` indicating if such a propagation is saturated.
  /// This is tested via checking if the first livein changes, and the reason
  /// is as follows: if none of the basic blocks have their first livein
  /// modified after running
  /// `intrafunction_structure::propagate_liveio_foreach`, then
  /// `intrafunction_structure::propagate_liveio_across` will have no effect,
  /// and the same argument applies to all subsequent propagations, which
  /// overall implies saturation.
  ///
  /// [sanity] Is my above statement correct?
  pub fn propagate_liveio(&mut self) -> Result<bool, RegAllocErr> {
    // if everything is up to date, this annot_instr_blk is trivially saturated.
    if self.liveio_up_to_date {
      return Ok(true);
    }

    let fst_livein_before_propagation = self.get_fst_livein().clone();

    let mut item = self.ops.iter_mut().rev();
    let optim_lvl = fst_livein_before_propagation.1;
    let mut child_livein = LivenessInfo::empty(optim_lvl);

    while let Some(parent) = item.next() {
      parent.liveout.checked_extend(child_livein)?;
      parent.init_livein()?;
      child_livein = parent.livein.clone(); // parent becomes child in next iter
    }

    self.liveio_up_to_date = true;
    Ok(fst_livein_before_propagation == *self.get_fst_livein())
  }

  /// Gets the `Livein` of the very first instruction.
  pub fn get_fst_livein(&self) -> &LivenessInfo {
    &self
      .ops
      .first()
      .expect("AnnotInstrBlk must be init'd b4 get_first_livein")
      .livein
  }

  /// Union the given `LivenessInfo` into the last liveout of this basic block.
  /// and then re-run `propagate liveio`.
  pub fn add_to_last_liveout(
    &mut self,
    extra_liveout: &LivenessInfo,
  ) -> Result<(), RegAllocErr> {
    let last_liveout = &mut self
      .ops
      .last_mut()
      .expect("AnnotInstrBlk must be init'd b4 update_liveio")
      .liveout;

    let last_liveout_old_size = last_liveout.0.len();

    last_liveout.checked_extend(extra_liveout.clone())?;

    if last_liveout.0.len() > last_liveout_old_size {
      // last liveout changed, needs to repropagate liveio.
      self.liveio_up_to_date = false;
    }

    Ok(())
  }

  /// Returns a vector of liveness info in this basic block, starting from the
  /// livein of the first instruction, all the way up to the liveout of the
  /// last instruction.
  ///
  /// [optimize] Clone optimization
  ///
  /// [waring] This only works for BASIC BLOCKS! DO Not attempt to copy this
  /// function and use it to deal with entire control flows, unless you know
  /// what is happening
  fn liveness_lines(&self) -> Vec<LivenessInfo> {
    let mut ret: Vec<LivenessInfo> = Vec::new();

    // insert variables from all of the liveins
    for annot_instr in &self.ops {
      ret.push(annot_instr.livein.clone());
    }

    // insert variables from the last liveout
    if let Some(annot_instr) = self.ops.last() {
      ret.push(annot_instr.liveout.clone());
    }

    ret
  }

  /// Returns the set of variables appeared in this basic block
  ///
  /// [optimize] Clone optimization
  pub fn variable_set(&self) -> HashSet<Dest> {
    let mut ret: HashSet<Dest> = HashSet::new();

    for item in self.liveness_lines() {
      item.insert_into_hashset(&mut ret);
    }

    for item in &self.ops {
      item.uses.insert_into_hashset(&mut ret);
      item.define.insert_into_hashset(&mut ret);
    }

    ret
  }

  /// Adds the occurrences of temps towards a counter.
  pub fn count_temp(&self, counter: &mut Counter<u32>) {
    for op in &self.ops {
      op.uses.count_temp(counter);
      op.define.count_temp(counter);
    }
  }

  /// Creates a hashset of temp variable interference.
  pub fn get_interference_set(&self) -> HashSet<(Dest, Dest)> {
    let mut interference_set: HashSet<(Dest, Dest)> = HashSet::new();

    for annot_instr in &self.ops {
      annot_instr.add_interference_to(&mut interference_set);
    }

    interference_set
  }

  /// Computes a vector of `(source, dest)` pairs of `mov` instructions.
  /// Only considers sources and destinations that are of type `asm::Dest`.
  pub fn mov_instrs(&self) -> Vec<(Dest, Dest)> {
    let mut ret = Vec::<(Dest, Dest)>::new();

    for op in &self.ops {
      if let Instr::Mov {
        dest,
        src: Operand::Var(s),
      } = op.instr
      {
        ret.push((s, dest));
      }
    }

    ret
  }
}

impl Display for AnnotatedInstr {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), Error> {
    write!(
      f,
      "\
  \t\t\t\t\tliveio:  {}
  {}",
      self.livein, self.instr
    )
  }
}

impl Display for AnnotatedInstrBlock {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    for item in &self.ops {
      writeln!(f, "{}", item)?;
    }
    let back_liveout = &self
      .ops
      .last()
      .expect("cannot display empty annotated instr block")
      .liveout;
    writeln!(f, "\t\t\t\t\tliveio:  {}", back_liveout)
  }
}

#[allow(dead_code, unused_imports)]
mod test {
  use super::*;
  use crate::ast::BinOp;

  #[test]
  fn lifetime_trivial() {}

  #[test]
  fn lifetime_recitation_code() {}
}
