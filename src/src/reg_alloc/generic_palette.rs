
/// A trait designed for colors that are used in graph coloring.
pub trait Color: Clone + Copy + PartialEq + Eq + Hash {}

/// A trait for an iterable color palette, which iterates over a set of usable 
/// colors one by one.
pub trait Palette<C> 
where
  C: Color
{

  /// Creates a new color palette instance, where preset becomes the first 
  /// few return values of `next()`.
  /// 
  /// [todo] Think about what to pass in as argument! Different `C` type needs 
  /// different arguments for proper instantiation.
  fn new(preset: Vec<C>) -> Self;

  /// Tests if the palette is brand new, ie. unused.
  fn is_brand_new(&self) -> bool;

  /// Returns the next available color.
  fn next(&mut self) -> C;
}
