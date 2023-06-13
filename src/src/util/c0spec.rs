//! This file is deditated towards defining how users want the c0 program to be
//! compiled. Contains items such as header vs c0 file, compiler flag, etc.

/// Describes whether the source file is a `Header` (`.h`) file
/// or an `Impl` (`.c0`) file.
#[derive(Clone, Copy)]
pub enum SourceFileType {
  Header,
  Impl,
}

/// Compiler optimization flag, where `-O0` stands for unoptimized, and `-O1`
/// stands for optimized.
pub enum OptimFlag {
  O0,
  O1,
}

/// Allows a new typedef to overwrite an old one.
pub const ALLOW_TYPEDEF_SHADOWING: bool = false;
pub const DEBUG: bool = false;

pub const MAC: bool = false;
pub const UNSAFE: bool = false;

pub const DEFAULT_OPTIMIZATION: usize = 0;
