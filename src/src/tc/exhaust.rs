//! placeholder exhaustiveness checking. 

use std::collections::HashSet;

use crate::{ast::Patt, util::prettyprint::lst_paren_if_nonempty};

use super::tc_info::TcInfoFn;

// --- Helper fn ---

/// Converts a vector of set into a set of vector via product.
fn set_prod<T: Clone + Eq + core::hash::Hash>(v: &[HashSet<T>]) 
-> HashSet<Vec<T>> {
  match &v[..] {
    [] => HashSet::new(),
    [head, tail @ ..] => {
      let s = set_prod(tail);
      let mut ret = HashSet::<Vec<T>>::new();
      for head_elt in head {
        for tail_elt in s.clone() {
          let mut tmp_v = Vec::<T>::new();
          tmp_v.push(head_elt.clone());
          tmp_v.extend(tail_elt);
          ret.insert(tmp_v);
        }
      }
      ret
    }
  }
}

#[derive(Hash, PartialEq, Eq, Clone)]
pub struct BoundedNat{
  pub ub: usize,
  pub val: usize,
}

/// Note that for exhaustiveness chk, `variable` is the same as 
/// a wildcard, therefore we simplify `Patt`.
#[derive(Hash, PartialEq, Eq, Clone)]
pub enum SimpPatt {
  Any,
  Variant(BoundedNat, Vec<SimpPatt>)
}

impl std::fmt::Display for SimpPatt {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Any => write!(f, "_"),
      Self::Variant(bn, v) => {
        write!(f, "({}/{}, ", bn.val, bn.ub)?;
        lst_paren_if_nonempty(f, v, ",")?;
        write!(f, ")")
      }
    }
  }
}

impl SimpPatt {

  /// Conversion from some pattern.
  fn from(value: &Patt, tc_info_fn: &TcInfoFn) -> Self {
    match value {
      Patt::Any | Patt::Variable(_) => SimpPatt::Any,
      Patt::Variant(eid, vid, v) => {
        let ub = tc_info_fn.num_variants(&eid);
        let val = tc_info_fn.ev_tag(&eid, &vid);
        Self::Variant(
          BoundedNat { ub, val }, 
          v.into_iter().map(|x| Self::from(x, tc_info_fn)).collect()
        )
      }
    }
  }

  /// Checks if this pattern completely covers that of another pattern.
  fn covers(&self, other: &Self) -> bool {
    match (self, other) {
      (Self::Any, _) => true,
      (Self::Variant(..), Self::Any) => false,
      (Self::Variant(bn1, v1), Self::Variant(bn2, v2)) => {
        assert_eq!(bn1.ub, bn2.ub); // since same type
        if bn1.val != bn2.val { return false; } // self and other has diff var.

        // recursively check coverage of all subpatterns. 
        assert_eq!(v1.len(), v2.len()); // same num of args
        std::iter::zip(v1.iter(), v2.iter())
          .map(|(l, r)| l.covers(r))
          .fold(true, |x,y| x && y)
      }
    }
  }

  /// Expands self into a set of potentially unmatched simple patts.
  fn expand(self) -> HashSet<SimpPatt> {
    match self {
      Self::Any => HashSet::<SimpPatt>::new(),
      Self::Variant(bn, v) => {
        let rec: Vec<HashSet<SimpPatt>> = v.into_iter()
          .map(|x| x.expand())
          .collect();
        let all_rec = set_prod(&rec);

        let mut ret = HashSet::<SimpPatt>::new();

        if all_rec.is_empty() {
          for i in 0..bn.ub {
            ret.insert(Self::Variant(
              BoundedNat { ub: bn.ub, val: i }, 
              vec![]
            ));
          }
        } else {

          todo!()

          // same variant, different args
          // for v in &all_vec {
          //   ret.insert(Self::Variant(
          //     bn, 
          //     v.clone()
          //   ));
          // }

          // different variant
          
        }

        for i in 0..bn.ub {
          if all_rec.is_empty() {
            ret.insert(Self::Variant(
              BoundedNat { ub: bn.ub, val: i }, 
              vec![]
            ));
          } else {
            for v in &all_rec {
              ret.insert(Self::Variant(
                BoundedNat { ub: bn.ub, val: i }, 
                v.clone()
              ));
            }
          }
        }

        ret
      }
    }
  }
}

/// A bank that holds all potential simple patterns to chk.
pub struct PattBank {
  data: HashSet<SimpPatt>
}

impl std::fmt::Display for PattBank {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{{\n")?;
    for item in &self.data {
      write!(f, "  {}", item)?;
    }
    write!(f, "}}\n")
  }
}

impl PattBank {

  pub fn new() -> Self {
    Self { data: HashSet::new() }
  }

  pub fn is_empty(&self) -> bool {
    self.data.is_empty()
  }

  /// Given a simple pattern, expands it and inserts everything.
  fn expand(&mut self, sp: &SimpPatt) {
    self.data.extend(sp.clone().expand());
  }

  /// Given a simple pattern, uses it to kill-off anything covered.
  fn kill(&mut self, sp: &SimpPatt) {
    let empty = HashSet::<SimpPatt>::new();
    let old_data = std::mem::replace(&mut self.data, empty);
    self.data = old_data.into_iter().filter(|x| ! sp.covers(x)).collect();
  }

  /// Performs expansion and kill.
  pub fn update(&mut self, sp: &SimpPatt) {
    println!("b4 update, bank = {}", self);
    println!("sp = {}", sp);
    self.expand(sp);
    println!("expanded, bank = {}", self);
    self.kill(sp);
    println!("killed, bank = {}", self);
  }

  /// Exhaustiveness Checking, yay! 
  pub fn exhaustiveness_chk<'a, T>(patts: T, tc_info_fn: &TcInfoFn) -> bool 
  where
    T: Iterator<Item = &'a Patt>
  {
    println!("Testing exhaustiveness:");
    let simp_patts: Vec<SimpPatt> = patts
      .map(|p| SimpPatt::from(p, tc_info_fn))
      .collect();

    let mut bank = Self::new();

    for sp in simp_patts {
      bank.update(&sp);
    }

    bank.is_empty()
  }
}
