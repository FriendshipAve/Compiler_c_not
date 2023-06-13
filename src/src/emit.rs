// L1 Compiler
//! File emission
// Author: Dan Cascaval <dcascava@andrew.cmu.edu>

use crate::asm_processing::intrafunction_structure::BBGraph;
use crate::ast::{self, Glob};
use crate::codegen::Context;
use crate::lex::Token;
use crate::{asm_processing, codegen, elab_after_tc};
use crate::{asm_to_assem, elab};
use std::collections::{HashMap, HashSet};
use std::env;
use std::fs::File;
use std::io::prelude::*;

use crate::reg_alloc;
use crate::reg_alloc::lifetime::*;
use crate::reg_alloc::var_graph::*;

use crate::const_params::*;

// Fetches the env variable name. For those developing on Macs, you'll
// want to export the UNAME env variable as 'Darwin' in ~/.bashrc or ~/.bash_profile.
#[allow(dead_code)]
fn get_main() -> &'static str {
  if env::var("UNAME") == Ok(String::from("Darwin")) {
    "__c0_main"
  } else {
    "_c0_main"
  }
}

#[allow(dead_code)]
pub fn emit_x86(
  filename: &str,
  ctx_v: Vec<codegen::Context>,
  optimize_level: usize,
) -> std::io::Result<()> {
  let mut fname_to_ctx = HashMap::<String, Context>::new();
  for ctx in ctx_v {
    let name_of_ctx: String = ctx.get_name();
    fname_to_ctx.insert(name_of_ctx, ctx);
  }

  let mut file = File::create(format!("{}.s", filename)).unwrap();
  writeln!(file, ".file\t{:?}\t", filename)?;

  let assemb = asm_to_assem::asm_to_assem(&fname_to_ctx, optimize_level);
  for (name, ass) in assemb {
    for ass_line in ass.instrs {
      writeln!(file, "{}", ass_line)?;
    }
    writeln!(file, "")?;
  }

  writeln!(file, ".ident\t\"Rust Interpreter\"\n")?;
  Ok(())
}

/// Emits variable interference graph.
pub fn emit_vargraph(
  filename: &str,
  ctx_v: Vec<codegen::Context>,
  optimize_level: usize,
) -> std::io::Result<()> {
  let mut file = File::create(format!("{}.vg", filename))
    .expect("cannot create vargraph file");

  writeln!(file, "// Variable Inteference Graph\n")?;

  for ctx in ctx_v {
    let mut bbg = BBGraph::from_codegen_ctx(ctx, optimize_level);
    bbg
      .propagate_liveio_till_saturation()
      .expect("Failed to propagate: possibly exceeded threshold");
    let g = NodeGraphHs::from_bbgraph(&bbg);
    writeln!(file, "{}", g)?;

    if DBG_MCS {
      let v = g.max_card_search();

      let v = v.into_iter().map(|(x, y)| {
        let mut x = x.to_string();
        x.push_str(" -> ");
        x.push_str(&y.to_string().as_str());
        x
      });

      println!("MCS: {:?}", v);
    }
  }
  Ok(())
}

/// Emits liveness analysis.
pub fn emit_liveness(
  filename: &str,
  ctx_v: Vec<codegen::Context>,
  optimize_level: usize,
) -> std::io::Result<()> {
  let mut file = File::create(format!("{}.live", filename))
    .expect("cannot create liveness file");

  writeln!(file, "// Liveness Annotation\n")?;

  if CONSIDER_CTRLFLOW_LIVENESS {
    for ctx in ctx_v {
      let mut bbg = BBGraph::from_codegen_ctx(ctx, optimize_level);
      bbg
        .propagate_liveio_till_saturation()
        .expect("Failed to propagate liveio till saturate");
      writeln!(
        file,
        "// Control Flow is taken into account. \n\n{}",
        bbg.to_bbg_print()
      )?;
    }
  } else {
    unreachable!("Deprecated branch")
  }

  Ok(())
}
/// Emits the basic block graphs.
pub fn mkbbgraph(
  filename: &str,
  ctx_v: Vec<codegen::Context>,
  optimize_level: usize,
) -> std::io::Result<()> {
  let mut file = File::create(format!("{}.bbg", filename)).unwrap();
  writeln!(file, "// L2 Basic block Graph")?;
  for ctx in ctx_v {
    let mut g = BBGraph::from_codegen_ctx(ctx, optimize_level);
    g.propagate_liveio_till_saturation()
      .expect("Failed to prop liveio till saturation");
    writeln!(file, "{}", g)?;
  }
  Ok(())
}

/// Emits the abstract assemblies in the given context.
pub fn emit_abs(
  filename: &str,
  ctx_v: Vec<codegen::Context>,
) -> std::io::Result<()> {
  let mut file = File::create(format!("{}.abs", filename)).unwrap();
  writeln!(file, "// 15-411 L1 Compiler\n")?;
  for ctx in ctx_v {
    for ins in ctx.instrs {
      if let crate::asm::Instr::FnLbl(_) = ins {
        write!(file, "\n")?; // start-of-function pretty print
      }
      writeln!(file, "{}", ins)?;
    }
  }
  Ok(())
}

pub fn emit_inline(
  filename: &str,
  ctx_v: Vec<codegen::Context>,
) -> std::io::Result<()> {
  let mut file = File::create(format!("{}.inline", filename)).unwrap();
  writeln!(file, "// 15-411 L1 Compiler\n")?;
  for ctx in ctx_v {
    for ins in ctx.instrs {
      if let crate::asm::Instr::FnLbl(_) = ins {
        write!(file, "\n")?; // start-of-function pretty print
      }
      writeln!(file, "{}", ins)?;
    }
  }
  Ok(())
}

/// Emits the 2nd elab pass.
pub fn emit_elab2(
  filename: &str,
  e2: &elab_after_tc::ProgramP2,
) -> std::io::Result<()> {
  let mut file = File::create(format!("{}.elab2", filename)).unwrap();
  writeln!(file, "// Elaborated P2\n{}", e2)
}

/// Emits the elaborated ASTs.
pub fn emit_elab(
  filename: &str,
  elabbed: elab::ElabProgram,
) -> std::io::Result<()> {
  let mut file = File::create(format!("{}.elab", filename)).unwrap();
  writeln!(file, "// Elaborated AST\n{}", elabbed)
}

/// Emits the unelaborated ASTs.
pub fn emit_ast0(filename: &str, program: ast::Program) -> std::io::Result<()> {
  let program: Vec<Glob> = program.0;

  let mut file = File::create(format!("{}.ast0", filename)).unwrap();
  writeln!(file, "// Unelaborated AST\n")?;
  for item in program {
    writeln!(file, "{}", item)?;
  }

  writeln!(file, "\n")
}

/// Emits the token stream for debugging purposes
pub fn emit_ts(filename: &str, v: Vec<Token>) -> std::io::Result<()> {
  let mut file = File::create(format!("{}.tokens", filename)).unwrap();
  writeln!(file, "// Token Stream")?;
  for tok in v {
    writeln!(file, "{:?}", tok)?;
  }
  writeln!(file, "\n")
}

/// Emits the register allocation assignments for each function
pub fn emit_regalloc(
  filename: &str,
  ctx_v: Vec<codegen::Context>,
  optimize_level: usize,
) -> std::io::Result<()> {
  let mut file = File::create(format!("{}.regalloc", filename)).unwrap();
  writeln!(file, "// Register Allocation")?;
  for ctx in ctx_v {
    writeln!(
      file,
      "{}: \n",
      ctx
        .instrs
        .get(0)
        .expect("Contexts shall at least contain a function label")
    )?;
    let (map, ..) = reg_alloc::context_to_assignment(ctx, optimize_level); // force to regalloc everything
    for (k, v) in map.into_iter() {
      writeln!(file, "{} -> {}", k, v)?;
    }
  }
  writeln!(file, "\n")
}

pub fn emit_regalloc_sub(
  filename: &str,
  mut ctx_v: Vec<codegen::Context>,
  optimize_level: usize,
) -> std::io::Result<()> {
  let mut file = File::create(format!("{}.regsub", filename)).unwrap();
  writeln!(file, "// Optimized Abs")?;
  for ctx in &mut ctx_v {
    let (regalloc_map, ..) =
      reg_alloc::context_to_assignment(ctx.clone(), optimize_level); // force to regalloc everything
    asm_processing::regalloc_assign_pass::optimize(ctx, &regalloc_map)
  }
  for ctx in ctx_v {
    for ins in ctx.instrs {
      if let crate::asm::Instr::FnLbl(_) = ins {
        write!(file, "\n")?; // start-of-function pretty print
      }
      writeln!(file, "{}", ins)?;
    }
  }
  Ok(())
}
