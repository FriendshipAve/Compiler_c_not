use std::collections::HashSet;
use std::hash::Hash;
use std::vec::IntoIter;

use crate::const_params::REGALLOC_POOL;

/// Named x86-64 registers, ie. the ones without spill.
#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash, PartialOrd, Ord)]
pub enum NamedReg {
  Rsp,
  Rax,
  Rdi,
  Rsi,
  Rdx,
  Rcx,
  R8,
  R9,
  R10,
  Rbx,
  Rbp,
  R12,
  R13,
  R14,
  R15,
}

impl NamedReg {
  pub fn from_first_six_function_arg(argpos: usize) -> Self {
    match argpos {
      0 => NamedReg::Rdi,
      1 => NamedReg::Rsi,
      2 => NamedReg::Rdx,
      3 => NamedReg::Rcx,
      4 => NamedReg::R8,
      5 => NamedReg::R9,
      n => panic!(
        "Only arguments 0 through 5 makes use of named registers, \
      not argument `{}`.",
        n
      ),
    }
  }

  /// Computes the set of named registers used as function argument, given the
  /// arity of the function.
  pub fn used_namedregs_from_arity(arity: usize) -> HashSet<Self> {
    use NamedReg::*;
    match arity {
      0 => HashSet::<Self>::new(),
      1 => HashSet::<Self>::from([Rdi]),
      2 => HashSet::<Self>::from([Rdi, Rsi]),
      3 => HashSet::<Self>::from([Rdi, Rsi, Rdx]),
      4 => HashSet::<Self>::from([Rdi, Rsi, Rdx, Rcx]),
      5 => HashSet::<Self>::from([Rdi, Rsi, Rdx, Rcx, R8]),
      _ => HashSet::<Self>::from([Rdi, Rsi, Rdx, Rcx, R8, R9]),
    }
  }

  /// Given the arity of a function, compute an ordered-list
  /// of registers to store.
  #[allow(dead_code)]
  pub fn store_regs_from_arity(arity: usize) -> Vec<Self> {
    use NamedReg::*;
    match arity {
      0 => vec![R10],
      1 => vec![R10, Rdi],
      2 => vec![R10, Rdi, Rsi],
      3 => vec![R10, Rdi, Rsi, Rdx],
      4 => vec![R10, Rdi, Rsi, Rdx, Rcx],
      5 => vec![R10, Rdi, Rsi, Rdx, Rcx, R8],
      _ => vec![R10, Rdi, Rsi, Rdx, Rcx, R8, R9],
    }
  }

  /// Given the arity of a function, compute an ordered-list
  /// of registers to restore.
  #[allow(dead_code)]
  pub fn restore_regs_from_arity(arity: usize) -> Vec<Self> {
    let mut ret = Self::store_regs_from_arity(arity);
    ret.reverse();
    ret
  }
}

/// abstract x86-64 registers (ie. does not consider size)
#[derive(Debug, PartialEq, Eq, Hash, Clone, Copy)]
#[allow(dead_code)]
pub enum RegAbs86 {
  // Rsp,                            // stack pointer
  // Rax,                            // return register
  // Rdi, Rsi, Rdx, Rcx, R8, R9,     // first 6 fn args
  // R10, R11,                       // caller-saved
  // Rbx, Rbp, R12, R13, R14, R15,   // callee-saved
  Named(NamedReg),
  Spill(usize),

  /// Function argument beyond the first six (and therefore must be put onto
  /// the stack). For example, `FnArgOnStack(0)` is the `6th` function
  /// argument, if we count them starting from 0.
  FnArgOnStack(usize),
}

/// Palette for x86-64 registers, for iterating over a given set of allowed
/// x86-64 registers. Specifically, this implementation shall iterate over all
/// regsiters within the `real_regs` field, before proceeding to spill over.
pub struct Palette86 {
  real_regs: IntoIter<NamedReg>,
  spill_idx: usize,
}

impl RegAbs86 {
  /// Converts the `nth` (start counting from `0`) function argument to its
  /// corresponding abstract register.
  pub fn from_nth_function_arg(argpos: usize) -> Self {
    match argpos {
      0 => RegAbs86::Named(NamedReg::Rdi),
      1 => RegAbs86::Named(NamedReg::Rsi),
      2 => RegAbs86::Named(NamedReg::Rdx),
      3 => RegAbs86::Named(NamedReg::Rcx),
      4 => RegAbs86::Named(NamedReg::R8),
      5 => RegAbs86::Named(NamedReg::R9),
      n => RegAbs86::FnArgOnStack(n - 6),
    }
  }

  /// Fuzzily convert a String object to some RegAbs86. Panics if conversion
  /// fails. Only parses non-spills.
  ///
  /// [warning] Only 32-bit and 64-bit registers are implemented.
  ///
  /// # Examples
  ///
  /// basic usage:
  /// ```
  /// let s = String::from("\ni am register %rdx ");
  /// assert_eq!(RegAbs86::Rdx, fuzzy_from_str(s));
  /// ```
  pub fn fuzzy_from_str(fuzzy_name: String) -> Self {
    let simplified_str = fuzzy_name.trim().to_lowercase();

    if simplified_str.contains("rsp") {
      Self::Named(NamedReg::Rsp)
    } else if simplified_str.contains("rax") {
      Self::Named(NamedReg::Rax)
    } else if simplified_str.contains("rdi") {
      Self::Named(NamedReg::Rdi)
    } else if simplified_str.contains("rsi") {
      Self::Named(NamedReg::Rsi)
    } else if simplified_str.contains("rdx") {
      Self::Named(NamedReg::Rdx)
    } else if simplified_str.contains("rcx") {
      Self::Named(NamedReg::Rcx)
    } else if simplified_str.contains("r8") {
      Self::Named(NamedReg::R8)
    } else if simplified_str.contains("r9") {
      Self::Named(NamedReg::R9)
    } else if simplified_str.contains("r10") {
      Self::Named(NamedReg::R10)
    } else if simplified_str.contains("rbx") {
      Self::Named(NamedReg::Rbx)
    } else if simplified_str.contains("rbp") {
      Self::Named(NamedReg::Rbp)
    } else if simplified_str.contains("r12") {
      Self::Named(NamedReg::R12)
    } else if simplified_str.contains("r13") {
      Self::Named(NamedReg::R13)
    } else if simplified_str.contains("r14") {
      Self::Named(NamedReg::R14)
    } else if simplified_str.contains("r15") {
      Self::Named(NamedReg::R15)
    } else if simplified_str.contains("esp") {
      Self::Named(NamedReg::Rsp)
    } else if simplified_str.contains("eax") {
      Self::Named(NamedReg::Rax)
    } else if simplified_str.contains("edi") {
      Self::Named(NamedReg::Rdi)
    } else if simplified_str.contains("esi") {
      Self::Named(NamedReg::Rsi)
    } else if simplified_str.contains("edx") {
      Self::Named(NamedReg::Rdx)
    } else if simplified_str.contains("ecx") {
      Self::Named(NamedReg::Rcx)
    } else if simplified_str.contains("r8d") {
      Self::Named(NamedReg::R8)
    } else if simplified_str.contains("r9d") {
      Self::Named(NamedReg::R9)
    } else if simplified_str.contains("r10d") {
      Self::Named(NamedReg::R10)
    } else if simplified_str.contains("ebx") {
      Self::Named(NamedReg::Rbx)
    } else if simplified_str.contains("ebp") {
      Self::Named(NamedReg::Rbp)
    } else if simplified_str.contains("r12d") {
      Self::Named(NamedReg::R12)
    } else if simplified_str.contains("r13d") {
      Self::Named(NamedReg::R13)
    } else if simplified_str.contains("r14d") {
      Self::Named(NamedReg::R14)
    } else if simplified_str.contains("r15d") {
      Self::Named(NamedReg::R15)
    } else {
      panic!("Failed to parse x86 register from {}", fuzzy_name)
    }
  }

  pub fn to_named(&self) -> NamedReg {
    match self {
      RegAbs86::Named(nr) => *nr,
      x => panic!("Cannot convert spilled register `{}` to named! ", x),
    }
  }
}

impl Palette86 {
  /// Creates a new x86 abstract register palette according to specs.
  ///
  /// [args] `existing` A collection consisting of existing colors, ie. when `%rdi`
  /// is used for passing data as the first argument of a called function.
  /// This shall be prioritized to reduce the total number of colors used.
  pub fn new(existing: &Vec<NamedReg>) -> Self {
    use NamedReg::*;
    let all_real_regs: Vec<NamedReg> = REGALLOC_POOL.into();

    let mut ordered_real_regs: Vec<NamedReg> = existing.clone();

    assert!(
      !(ordered_real_regs.contains(&NamedReg::Rsp)),
      "cannot use register %rsp during regalloc"
    );

    for item in all_real_regs {
      if !existing.contains(&item) {
        ordered_real_regs.push(item);
      }
    }

    Self {
      real_regs: ordered_real_regs.into_iter(),
      spill_idx: 0,
    }
  }

  /// Similar to self.next, except always in spill mode. Specifically, returns
  /// current spill register, and increment `spill_idx` by one.
  fn spill_next(&mut self) -> RegAbs86 {
    let ret = RegAbs86::Spill(self.spill_idx);
    self.spill_idx += 1;
    ret
  }

  /// Returns the next available register to use, including spill.
  pub fn next(&mut self) -> RegAbs86 {
    if self.spill_idx > 0 {
      // spill has already started, thus keep spilling.
      self.spill_next()
    } else {
      // spill has not started yet
      match self.real_regs.next() {
        Some(nr) => RegAbs86::Named(nr), // can still use real registers
        _ => self.spill_next(),          // real regs used up, start spilling
      }
    }
  }
}

#[allow(dead_code)]
impl RegAbs86 {
  /// Checks whether a register is callee-saved. See CSAPP section 3.7.5.
  pub fn callee_saved(&self) -> bool {
    if let Self::Named(r) = self {
      use NamedReg::*;
      [Rbx, Rbp, R12, R13, R14, R15].contains(r)
    } else {
      false
    }
  }

  /// Checks whether a register is spilled.
  pub fn is_spill(&self) -> bool {
    match self {
      RegAbs86::Spill(_) => true,
      _ => false,
    }
  }
}

impl std::fmt::Display for RegAbs86 {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let s = format!("%{:?}", self).to_lowercase();
    write!(f, "{}", s)
  }
}

impl std::fmt::Display for NamedReg {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let s = format!("%{:?}", self).to_lowercase();
    write!(f, "{}", s)
  }
}
