//! Register allocation errors.
#[derive(Debug)]
pub enum RegAllocErr {
  LiveioExceedsThreshold,
  GraphColorConflict,
}
