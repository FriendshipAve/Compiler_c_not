//! Helper types for organizing other types.

/// A wrapper around some type `T` such that comparisons between expressions of
/// type `Lax<T>` always returns true, except when both expressions are of
/// variant `Fixed()`.
///
/// ## Examples
/// ```
/// let (e1, e2, e3) = (Lax::Fixed(1), Lax::Fixed(2), Lax::Any);
/// assert_eq!(e1, e3);
/// assert_ne!(e1, e2);
/// ```
pub enum Lax<T: Eq> {
  Fixed(T),
  Any,
}

impl<T: Eq> PartialEq for Lax<T> {
  fn eq(&self, other: &Self) -> bool {
    match (&self, other) {
      (Lax::Fixed(t1), Lax::Fixed(t2)) => t1.eq(t2),
      _ => true,
    }
  }
}

impl<T: Eq> Eq for Lax<T> {}
