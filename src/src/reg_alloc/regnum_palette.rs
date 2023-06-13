
/// A register consisting of only a number. Used for register allocation 
/// tasks. This is a more abstract representation than RegAbs86.
#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct RegNum(usize);


/// Holds a number indicating the current register. This is primarily used 
/// to greedily color a chordal graph.
/// 
/// # Examples
/// ```
/// let plt = RegNumPalette::new();
/// assert!(plt.is_brand_new());
/// 
/// assert_eq!(plt.get_reg(), RegNum(0));
/// assert_eq!(plt.next(), RegNum(0));
/// assert_eq!(plt.get_reg(), RegNum(1));
/// 
/// assert!(!plt.is_brand_new());
/// ```
pub struct RegNumPalette {
  index: usize
}

impl RegNumPalette {

  /// Creates a new RegNumPalette, starting at the zeroth RegNum.
  pub fn new() -> Self {
    RegNumPalette { index: 0 }
  }


  /// Shows if self is an unused RegNumPalette.
  pub fn is_brand_new(&self) -> bool {
    0 == self.index
  }


  /// Returns current register, then increments the register index.
  pub fn next(&mut self) -> RegNum {
    let ret = RegNum(self.index);
    self.index += 1;
    ret
  }


  /// Rrturns current register.
  pub fn get_reg(&self) -> RegNum {
    RegNum(self.index)
  }

}


impl std::fmt::Display for RegNum {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "%rn{}", self.0)
  }
}


impl std::fmt::Debug for RegNum {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
      write!(f, "%rn{}", self.0)
  }
}


#[allow(unused_imports)]
mod test {

  use super::*;

  #[test]
  fn test_ops() {
    let mut plt = RegNumPalette::new();
    assert!(plt.is_brand_new());

    assert_eq!(plt.get_reg(), RegNum(0));
    assert_eq!(plt.next(), RegNum(0));
    assert_eq!(plt.get_reg(), RegNum(1));

    assert!(!plt.is_brand_new());
  }
}
