// Author: Stephen McIntosh <semcinto@andrew.cmu.edu>

use serde::Deserialize;
use std::collections::HashMap;
use std::fs::File;
use std::io::prelude::*;
use std::io::{BufReader, BufWriter};
use std::path::{Path, PathBuf};

// custom uses
use crate::reg_alloc::var_graph::NodeGraphHs;
use crate::reg_alloc::x86_register::{NamedReg, RegAbs86};

/// A node in interference graph, which is basically Dest.
#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub enum Node {
  Register(NamedReg),
  Temporary(u32),
  FnArgOnStack(usize),
}

impl From<String> for Node {
  fn from(s: String) -> Self {
    let mut chars = s.chars().skip(1);
    if let Some(marker) = chars.next() {
      match marker {
        't' => Self::Temporary(chars.collect::<String>().parse().unwrap()),
        m => {
          let s: String = std::iter::once(m).chain(chars).collect();
          Self::Register(RegAbs86::fuzzy_from_str(s).to_named())
        }
      }
    } else {
      panic!("Invalid node");
    }
  }
}

impl Into<String> for Node {
  fn into(self) -> String {
    match self {
      Self::Register(s) => format!("%{:?}", s),
      Self::Temporary(n) => format!("%t{:?}", n),
      Self::FnArgOnStack(n) => format!("%#{:?}", n),
    }
  }
}

type OutputLine = HashMap<String, String>;

impl std::fmt::Display for Node {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Register(s) => write!(f, "%{}", s),
      Self::Temporary(n) => write!(f, "%t{}", n),
      Self::FnArgOnStack(n) => write!(f, "#{}", n),
    }
  }
}

impl std::fmt::Debug for Node {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    match self {
      Self::Register(s) => write!(f, "%{}", s),
      Self::Temporary(n) => write!(f, "%t{}", n),
      Self::FnArgOnStack(n) => write!(f, "#{}", n),
    }
  }
}
