// L1 Compiler
//! Compiler Errors
// Author: Dan Cascaval <dcascava@andrew.cmu.edu>

use std::fmt::{Debug, Display, Formatter};
use std::io;
use std::result;

pub type Result<T> = result::Result<T, Error>;

/// In L1, we only have two types of errors. We distinguish
/// EOF specifically in order to handle it accordingly. You
/// may want to extend this struct with more errors (for say, types.)
pub enum Error {
  Message(String),
  EOF,
}

/// Shorthand to make an `std::result::Error` with a message
pub fn err<T>(s: &str) -> Result<T> {
  Err(Error::Message(s.to_string()))
}

/// Shorthand to use an owned string, such as the result of a formatter.
pub fn errs<T>(s: String) -> Result<T> {
  Err(Error::Message(s))
}

// Implement the traits we need to use this in the lexer & parser.

impl From<io::Error> for Error {
  fn from(error: io::Error) -> Self {
    Self::Message(error.to_string())
  }
}

impl<'a> From<&'a Error> for Error {
  fn from(error: &'a Error) -> Self {
    match error {
      Error::Message(s) => Error::Message(s.clone()),
      Error::EOF => Error::EOF,
    }
  }
}

impl Display for Error {
  fn fmt(&self, fmt: &mut Formatter) -> result::Result<(), std::fmt::Error> {
    match *self {
      Error::Message(ref msg) => write!(fmt, "{}", &msg),
      Error::EOF => write!(fmt, "end of file"),
    }
  }
}

impl Debug for Error {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(f, "{}", self.to_string())
  }
}
