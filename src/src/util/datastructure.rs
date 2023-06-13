use crate::error::{Error, Result};
use crate::lex::{Lexer, Token};
use std::collections::{HashMap, HashSet, VecDeque};
use std::fmt::Display;
use std::hash::Hash;
use std::io::Read;

/// A buffer wrapped on top of a lexer that allows arbitrary-depth `peek()`.
pub struct PeekBuffer<R: Read> {
  buf: VecDeque<Result<Token>>,
  lex: Lexer<R>,
}

impl<R: Read> PeekBuffer<R> {
  /// Creates a new `PeekBuffer` instance from a `crate::lex::Lexer`.
  pub fn from_lexer(lexer: Lexer<R>) -> Self {
    Self {
      buf: VecDeque::<Result<Token>>::new(),
      lex: lexer,
    }
  }

  /// Peeks the `k`th item, where `k=0` peeks the immediate next item. This
  /// function never advances the lexer. Multiple calls return the same result.
  ///
  /// [args] `k` the index of desired item, where `0` stands for the immediate
  /// next item.
  pub fn peek(&mut self, n: usize) -> std::result::Result<&Token, &Error> {
    while self.buf.len() <= n {
      // so that get() will return Some(_).
      self.buf.push_back(self.lex.token());
    }
    self
      .buf
      .get(n)
      .expect("peekable should have kth element")
      .as_ref()
  }

  /// Gets the next token. This function always advances the lexer by one token.
  pub fn token(&mut self) -> Result<Token> {
    let ret = self.buf.pop_front();

    // !!! This is NOT the same as unwrap_or(). This short-circuits !!!
    let ret = match ret {
      Some(r) => r,
      None => self.lex.token(),
    };

    ret
  }

  /// When parsing failed, outputs a helper message indicating what went wrong.
  /// The helper message marks the line num and the specific token in question.
  pub fn get_helpmsg(&mut self) -> String {
    self.lex.fail_msg()
  }
}

/// Splits a given slice `v` into two slices, where the first one has
/// a length of at most `fst_len`.
pub fn split_vec<'a, T>(v: &'a [T], fst_len: usize) -> (&'a [T], &'a [T]) {
  let split_idx = std::cmp::min(v.len(), fst_len);
  (&v[..split_idx], &v[split_idx..])
}

/// A tally counter.
#[derive(Debug, Clone)]
pub struct Counter<T>
where
  T: Hash + PartialEq + Eq + PartialOrd + Ord + Clone + Display,
{
  map: HashMap<T, usize>,
}

impl<T> Counter<T>
where
  T: Hash + PartialEq + Eq + PartialOrd + Ord + Clone + Display,
{
  /// Makes an empty counter
  pub fn mk_empty() -> Self {
    Counter {
      map: HashMap::<T, usize>::new(),
    }
  }

  /// Inserts an element into the counter.
  pub fn insert(&mut self, elt: &T) {
    match self.map.get_mut(elt) {
      Some(n) => {
        *n += 1;
      }
      None => {
        self.map.insert(elt.clone(), 1);
      }
    }
  }

  /// Returns the count of some element.
  pub fn count(&self, elt: &T) -> usize {
    *self.map.get(elt).unwrap_or(&0)
  }

  /// Contracts `src` to `dest`: adds the counts of `src` to `dest`, and
  /// removes `src`.
  pub fn coalesce(&mut self, src: &T, tgt: &T) {
    let src_count = *self.map.get(src).expect("src does not exist");
    let tgt_count = self.map.get_mut(tgt).expect("tgt does not exist");

    *tgt_count += src_count;

    self.map.remove(src);
  }

  /// Removes some item from counter.
  pub fn remove(&mut self, item: &T) {
    self.map.remove(item);
  }
}

impl<T> Display for Counter<T>
where
  T: Hash + PartialEq + Eq + PartialOrd + Ord + Clone + Display,
{
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    use std::cmp::Ordering::*;
    let mut v: Vec<(&T, &usize)> = self.map.iter().collect();
    v.sort_by(|(x1, c1), (x2, c2)| c1.cmp(c2).then(x2.cmp(x1)));
    v.reverse();
    write!(f, "{{")?;
    for (x, c) in v {
      write!(f, "T{}={}, ", x, c)?;
    }
    write!(f, "}}")
  }
}

mod test {
  use super::Counter;

  #[test]
  fn counter_effect() {
    let mut ct = Counter::<i32>::mk_empty();
    ct.insert(&233);
    ct.insert(&666);
    ct.insert(&233);

    assert!((0, 1, 2) == (ct.count(&251), ct.count(&666), ct.count(&233)));
  }
}
