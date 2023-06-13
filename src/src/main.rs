// L1 Compiler
//! Top Level Environment
// Author: Dan Cascaval <dcascava@andrew.cmu.edu>
#![allow(dead_code)]
#![allow(unused_imports)]
#![allow(unused_variables)]
#![allow(unused_mut)]
#![allow(unused_assignments)]
#![allow(unused_parens)]
#![allow(non_snake_case)]
#![allow(non_camel_case_types)]
#![allow(non_upper_case_globals)]

mod args;
mod asm;
mod asm_processing;
mod ast;
mod codegen;
mod codegen_elab2;
mod elab;
mod elab_after_tc;
mod emit;
mod error;
mod fn_inline;
mod lex;
mod parse;
mod ssa;
mod tc;

// custom mods
mod asm_to_assem;
mod assembly;
mod const_params;
mod reg_alloc;
mod util;

use crate::const_params::NO_TYPECHECK;
use crate::tc::tc_info;
use crate::tc::ProgContext;
use crate::util::c0spec::SourceFileType;
use crate::util::c0spec::*;
use args::EmitTarget;
use reg_alloc::ast_graph_node;
use std::fs;
use std::io::BufReader;
use std::option::Option;
use std::thread;
use std::time;

use crate::const_params::FN_INLINE;

fn main() {
  let cfg = args::parse_args();

  /// Take a filename and parse it into an AST!
  fn make_program(
    headername: &Option<String>,
    filename: &str,
  ) -> std::result::Result<ast::Program, error::Error> {
    let headerfile_opt = match headername {
      Some(headername) => Some(BufReader::new(
        fs::File::open(headername)
          .unwrap_or_else(|_| panic!("File {} not found", headername)),
      )),
      None => None,
    };
    let file = BufReader::new(
      fs::File::open(&filename)
        .unwrap_or_else(|_| panic!("File {} not found", filename)),
    );

    // init typedef context.
    let mut typ_ctxt = ast::TypCtxt::new();

    // parse header.
    let header_ast_opt = match headerfile_opt {
      Some(headerfile) => {
        let mut header_parser = parse::Parser::new(lex::Lexer::new(headerfile));
        Some(header_parser.parse(SourceFileType::Header, &mut typ_ctxt)?)
      }
      None => None,
    };

    // parse body.
    let mut body_parser = parse::Parser::new(lex::Lexer::new(file));
    let body_ast = body_parser.parse(SourceFileType::Impl, &mut typ_ctxt)?;

    // Concate potential header ast in front of body ast, then return.
    match header_ast_opt {
      Some(header_ast) => Ok(header_ast + body_ast),
      None => Ok(body_ast),
    }
  }

  // Helper macro to time evaluating an expression (like a function call.)
  macro_rules! time {
    ( $x:expr ) => {{
      let t1 = time::SystemTime::now();
      let result = $x;
      (result, t1.elapsed().unwrap())
    }};
  }

  // We call with a large stack to avoid any overflows caused
  // by overzealous 15-411 students with large test cases.
  let child = thread::Builder::new()
    .stack_size(256 * 1024 * 1024)
    .spawn(move || {
      let filename = &cfg.file.unwrap();
      let headername = &cfg.headerfile;
      if cfg.regalloc_only {
        unimplemented!("Lab1 chkpt is deprecated")
      }

      if let EmitTarget::TokenStream = cfg.emit {
        let file = BufReader::new(
          fs::File::open(&filename)
            .unwrap_or_else(|_| panic!("File {} not found", filename)),
        );
        let mut parser = parse::Parser::new(lex::Lexer::new(file));
        let v = parser.all_tokens();
        return emit::emit_ts(filename, v).is_err() as i32;
      }

      let (program, parse_time) = time!(make_program(headername, filename));
      let program = match program {
        Ok(prog) => prog,
        Err(e) => {
          eprintln!("{}", e);
          return 1; // Parse failed!
        }
      };

      if let EmitTarget::AstV0 = cfg.emit {
        return emit::emit_ast0(filename, program).is_err() as i32;
      }

      let elabbed_program = elab::elab_program(program.clone());

      if let EmitTarget::AstElab = cfg.emit {
        return emit::emit_elab(filename, elabbed_program).is_err() as i32;
      }

      let progctx = if !NO_TYPECHECK {
        let (tc_result, tc_time) =
          time!(tc::valid_elabbed_program(&elabbed_program));
        let valid_ast = tc_result.0;
        let progctx = tc_result.1;
        if cfg.dump_ast {
          println!("{}", program); // Print out the AST
        }

        if !valid_ast {
          eprintln!("Invalid AST!");
          return 1; // Tc failed (sad!)
        }

        if cfg.tc_only {
          println!("Pass typecheck.");
          return 0;
        }

        if cfg.verbose {
          println!("Typecheck: {} us", tc_time.as_micros());
        }
        progctx
      } else {
        if cfg.verbose {
          println!("Typecheck: skipped");
        }
        None
      };

      let lab4_plus = true;

      let tc_info_fn = tc_info::get_tc_info(
        &progctx.expect("tc should pass when doiung second pass elab"),
        &elabbed_program,
      );
      let ep =
        elab_after_tc::ProgramP2::from_elabpgrm(elabbed_program, &tc_info_fn);

      let (ctx_v, cg_time) = if lab4_plus {
        time!(codegen_elab2::mk_asm_l4(&ep, &tc_info_fn, !cfg.unsafe_mode))
      } else {
        unreachable!("Deprecated");
      };
      let pre_inline_ctx = ctx_v.clone();
      let (ctx_v2, inline_time) = if FN_INLINE {
        eprintln!("ctx inined");
        time!(fn_inline::convert_inline_v(&ctx_v))
      } else {
        (ctx_v, time::Duration::new(0, 0))
      };

      if cfg.dump_assem {
        for ctx in &ctx_v2 {
          ctx.print_instrs();
        }
      }

      if cfg.verbose {
        println!("Parse time: {} us", parse_time.as_micros());
        println!("Codegen: {} us", cg_time.as_micros());
      }

      match cfg.emit {
        EmitTarget::TokenStream => unreachable!(),

        // un-elaborated ast
        EmitTarget::AstV0 => unreachable!(),

        // elaborated ast
        EmitTarget::AstElab => unreachable!(),

        // abstract assembly
        EmitTarget::Abstract => {
          // unreachable!()
          emit::emit_abs(filename, pre_inline_ctx).is_err() as i32
        }
        EmitTarget::Inline => {
          emit::emit_inline(filename, ctx_v2).is_err() as i32
        }
        EmitTarget::ElabP2 => emit::emit_elab2(filename, &ep).is_err() as i32,

        // basic block graph
        EmitTarget::BasicBlockGraph => {
          emit::mkbbgraph(filename, ctx_v2, cfg.optimize).is_err() as i32
        }

        // abstract assembly with liveness annotation; for debug purposes
        EmitTarget::AbstractLiveness => {
          emit::emit_liveness(filename, ctx_v2, cfg.optimize).is_err() as i32
        }

        EmitTarget::VarGraph => {
          emit::emit_vargraph(filename, ctx_v2, cfg.optimize).is_err() as i32
        }
        EmitTarget::RegAlloc => {
          emit::emit_inline(filename, ctx_v2.clone()).is_err() as i32;
          emit::emit_regalloc(filename, ctx_v2, cfg.optimize).is_err() as i32
        }
        EmitTarget::RegAllocSubstitute => {
          emit::emit_regalloc_sub(filename, ctx_v2, cfg.optimize).is_err()
            as i32
        }

        // x86-64 assembly code
        EmitTarget::X86 => {
          emit::emit_x86(filename, ctx_v2, cfg.optimize).is_err() as i32
        }
      }
    })
    .unwrap();
  // Return the value from the child thread as the return value of the compiler.
  std::process::exit(child.join().expect("Couldn't join spawned thread"));
}
