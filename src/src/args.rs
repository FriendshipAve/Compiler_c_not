// L3 Compiler
//! Parse command line arguments
//! We expect this to be good enough for this course.
//! You could also use something like clap at the expense of bad compile times.
// Author: Dan Cascaval <dcascava@andrew.cmu.edu>

use crate::util::c0spec::{DEFAULT_OPTIMIZATION, UNSAFE};
use std::env;
pub enum EmitTarget {
  TokenStream,
  AstV0,
  AstElab,
  ElabP2,
  Abstract,
  BasicBlockGraph,
  AbstractLiveness,
  VarGraph,
  RegAlloc,
  RegAllocSubstitute,
  X86,
  Inline,
}

/// Configuration options for this compiler run.
pub struct Config {
  pub verbose: bool,
  pub regalloc_only: bool,
  pub tc_only: bool,
  pub dump_ast: bool,
  pub dump_assem: bool,

  pub emit: EmitTarget,
  pub file: Option<String>,
  pub headerfile: Option<String>,
  pub has_headerfile: bool,
  pub unsafe_mode: bool,
  pub lab_number: u32,
  pub optimize: usize,
}

impl Config {
  /// Set your defaults here!
  fn default() -> Self {
    Config {
      verbose: false,       // Get extra output from the compiler
      regalloc_only: false, // Register allocate for checkpoint
      tc_only: false,       // Stop after parsing & checking types.
      dump_ast: false,      // Print the AST
      dump_assem: false,    // Print the generated abstract assembly.

      emit: EmitTarget::Abstract, // Type of file to output
      file: None,                 // Source file to compile.
      headerfile: None,
      has_headerfile: false,
      unsafe_mode: UNSAFE, // Allow unsafe mode (ignore array boundary checks)
      lab_number: 4,       // Lab number to compile for
      optimize: 0,         // Optimization level
    }
  }
}

/// Parses command line input into a configuration. Panics on invalid args.
pub fn parse_args() -> Config {
  let args: Vec<String> = env::args().collect();
  let mut config = Config::default();
  let mut index = 1;
  while index < args.len() {
    match args[index].as_str() {
      "-v" | "--verbose" => config.verbose = true,
      "--dump-ast" => config.dump_ast = true,
      "--dump-assem" => config.dump_assem = true,
      "-t" | "--typecheck-only" => config.tc_only = true,
      "-r" | "--regalloc-only" => config.regalloc_only = true,
      "-e" | "--emit" => {
        // Allow for the emit type to be the next space-delimited token.
        if index + 1 < args.len() {
          match args[index + 1].as_str() {
            "abs" => config.emit = EmitTarget::Abstract,
            "x86-64" => config.emit = EmitTarget::X86,
            other => {
              panic!("Unkown emit type : {}", other.to_string());
            }
          };
          index += 1;
        } else {
          panic!("Expected emit type");
        };
      }
      // Account for funky spacing in the grading script.
      "-ts" => config.emit = EmitTarget::TokenStream,
      "-ast0" => config.emit = EmitTarget::AstV0,
      "-elab" => config.emit = EmitTarget::AstElab,
      "-elab2" => config.emit = EmitTarget::ElabP2,
      "-eabs" => config.emit = EmitTarget::Abstract,
      "-ebbgraph" => config.emit = EmitTarget::BasicBlockGraph,
      "-inline" => config.emit = EmitTarget::Inline,
      "-elive" => config.emit = EmitTarget::AbstractLiveness,
      "-egraph" => config.emit = EmitTarget::VarGraph,
      "-ereg" => config.emit = EmitTarget::RegAlloc,
      "-eregsub" => config.emit = EmitTarget::RegAllocSubstitute,
      "-ex86-64" => config.emit = EmitTarget::X86,
      "-debug" => config.verbose = true,
      "--unsafe" => config.unsafe_mode = true,
      "-O0" => config.optimize = DEFAULT_OPTIMIZATION,
      "-O1" => config.optimize = 1,
      "-l" => config.has_headerfile = true,
      file => {
        if let Some('-') = file.chars().next() {
        } else {
          if config.has_headerfile && config.headerfile.is_none() {
            config.headerfile = Some(file.to_string());
          } else {
            config.file = Some(file.to_string());
            if let Some(last_char) =
              config.file.as_ref().unwrap().chars().last()
            {
              config.lab_number = u32::from(last_char);
            }
          }
        }
      }
    };
    index += 1;
  }

  if config.file.is_none() {
    panic!("Expected file input");
  }

  config
}
