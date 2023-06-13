// L1 Compiler
// Assembly code generator for fake assembly, similar to the triples discussed in class.
// Author: Dan Cascaval <dcascava@andrew.cmu.edu>
// Implements a 'Convenient Munch' algorithm.

//! Flattens the AST into a series of simple abstract instructions.
use crate::asm::{AsmLabel, Dest, Instr, Operand};
use crate::const_params::{
  EXPLICIT_PUSH_POP_CALLER_SAVED_REGS, NAIVE_FNCALL_DURING_CODEGEN,
};
use crate::const_params::{MOVE_FNARG_FROM_REGS_TO_TEMPS, SKIP_USELESS_CODE};
use crate::elab_after_tc::{FnDefnP2, PurityInfo};
use crate::reg_alloc::x86_register::NamedReg;
use crate::tc::tc_info::TcInfoFn;
use crate::{asm_processing, ast, codegen_elab2, elab, elab_after_tc};
use std::collections::{HashMap, HashSet};

use crate::asm::DestSize;

use crate::error::{err, errs, Result};

/// Keeps track of the loop-depth of `Temp`s, ie. how many layers of
/// nested loop are they into.
#[derive(Clone)]
pub struct TmpDepthMap(pub HashMap<u32, usize>);

impl TmpDepthMap {
  pub fn mk_empty() -> Self {
    Self(HashMap::<u32, usize>::new())
  }

  /// Updates the running max loop-depth of some temp.
  pub fn update_depth(&mut self, temp_idx: u32, depth: usize) {
    let old_depth_opt = self.0.get_mut(&temp_idx);
    match old_depth_opt {
      Some(old_depth) => {
        *old_depth = std::cmp::max(*old_depth, depth);
      }
      None => {
        self.0.insert(temp_idx, depth);
      }
    }
  }

  /// Gets the max loop-depth of some temp.
  pub fn get_depth(&self, temp_idx: &u32) -> usize {
    *self.0.get(&temp_idx).unwrap_or(&0)
  }
}

impl std::fmt::Debug for TmpDepthMap {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    write!(f, "{:?}", self.0)
  }
}

impl std::fmt::Display for TmpDepthMap {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut v: Vec<_> = self.0.iter().map(|(a, b)| (*a, *b)).collect();
    v.sort_by(|(_, d1), (_, d2)| d1.cmp(d2));
    v.reverse();
    write!(f, "[",)?;
    for (tmp, depth) in v {
      write!(f, "T{} : {}, ", tmp, depth)?;
    }
    write!(f, "]\n")
  }
}

/// Global context across functions, ie. struct definition, etc.

/// Code generation context that contains a counter for creating new temps,
/// the list of currently-generated instructions, and the mapping from variable
/// names to temps. In a valid L1 program, it's OK to reuse the temp.
///
/// [L3] Context now represents whatever is going on in a function.
#[derive(Clone)]
pub struct Context {
  pub temp_index: u32,
  pub lbl_index: u32,
  pub fn_name: String,
  pub instrs: Vec<Instr>,
  pub var_temp_map: HashMap<String, Dest>,
  pub varname_argpos_map: HashMap<String, usize>,

  /// The arity (number of arguments) represented by this context.
  pub arity: usize,

  /// The name of the function represented by this context.
  pub name: String,

  /// A temporary number recording the depth of nested loops at some point in
  /// code generation. This allows the compiler to figure out the so-called
  /// "loop-depth" of some `Temp`, ie. how many layers of nested loop is the
  /// variable into.
  pub loop_depth: usize,

  /// Maps a temporary to its maximum loop-depth.
  ///
  /// This is useful because the
  /// deeper a temporary is inside nested loops, the more important it is to
  /// prioritize allocating it to a named (ie. non-spill) register; otherwise,
  /// repeated access of L1 cache (or worse) will put a toll on performance.
  pub temp_depth_map: TmpDepthMap,
}

impl Context {
  /// l4 version of `from_glob`.
  pub fn from_glob_l4(
    fdef: &elab_after_tc::FnDefnP2,
    tc_info_fn: &TcInfoFn,
    safemode: bool,
    purity: &HashSet<String>,
  ) -> Self {
    let FnDefnP2(rt, fname, params, body) = fdef;

    let mut varname_argpos_map = HashMap::<String, usize>::new();
    let mut param_names = params.to_vec_vars();
    let mut param_counter: usize = 0;

    for param_name in param_names {
      assert!(!varname_argpos_map.contains_key(&param_name));
      varname_argpos_map.insert(param_name, param_counter);
      param_counter += 1;
    }

    let mut ctx = Context {
      fn_name: fname.clone(),
      temp_index: 0,
      lbl_index: 0,
      instrs: Vec::new(),
      var_temp_map: HashMap::new(),
      varname_argpos_map,
      arity: param_counter,
      name: fname.clone(),
      loop_depth: 0,
      temp_depth_map: TmpDepthMap::mk_empty(),
    };
    ctx.add_instr(Instr::FnLbl(fname.clone()));

    // if decides to put first six args into temps, add a few such
    // move instructions.
    if MOVE_FNARG_FROM_REGS_TO_TEMPS {
      let sizes = tc_info_fn.function_param_size(&fname);

      for (i, (ref name, reg)) in
        params.param_name_reg_pairs().iter().enumerate()
      {
        let param_size = sizes[i]; // will not be out of bound
        let param_dest = ctx
          .var(name, Some(param_size))
          .expect("shouldn't fail here because these vars are not yet in ctx");
        ctx.add_instr(Instr::Mov {
          dest: param_dest,
          src: Operand::Var(Dest::R(*reg, param_size)),
        });
      }
    }
    ctx.add_instr(Instr::Comment("endMoveArgs".to_string()));

    if SKIP_USELESS_CODE {
      let mut param_set = HashSet::<String>::new();
      for p in &params.0 {
        param_set.insert(p.1.clone());
      }

      let mut info = PurityInfo::new(purity.clone());
      info.decl_vars = param_set;

      let body = body.clone().magic(&mut info);

      codegen_elab2::munch_elabtree(
        &mut ctx, &body, tc_info_fn, safemode, purity,
      );
    } else {
      codegen_elab2::munch_elabtree(
        &mut ctx, body, tc_info_fn, safemode, purity,
      );
    }

    asm_processing::truncate_empty_basic_block(&mut ctx);

    ctx
  }

  /// Returns the arity (number of arguments) of the function.
  pub fn get_arity(&self) -> usize {
    self.arity
  }

  /// Returns the name of the function.
  pub fn get_name(&self) -> String {
    self.name.clone()
  }

  pub fn increment_loop_depth(&mut self) {
    self.loop_depth += 1;
  }

  pub fn decrement_loop_depth(&mut self) {
    self.loop_depth -= 1; // never underflows due to C0 tc.
  }

  /// Create a new label in this context.
  pub fn create_lbl(&mut self) -> AsmLabel {
    let ret_idx = self.lbl_index;
    self.lbl_index += 1;
    AsmLabel(ret_idx)
  }

  /// Creates three labels.
  pub fn create_three_lbls(&mut self) -> (AsmLabel, AsmLabel, AsmLabel) {
    (self.create_lbl(), self.create_lbl(), self.create_lbl())
  }

  /// Given the index of some `temp`, update its loop-depth.
  ///
  /// [note] This should be run each time some temp is created / fetched /
  /// touched during codegen.
  pub fn update_tmp_loop_depth(&mut self, temp_idx: u32) {
    self.temp_depth_map.update_depth(temp_idx, self.loop_depth);
  }

  /// Create a new temp in this context and updates its loop depth.
  pub fn temp(&mut self, size: DestSize) -> Dest {
    let result_idx = self.temp_index;
    self.temp_index += 1;

    self.update_tmp_loop_depth(result_idx);

    Dest::T(result_idx, size)
  }

  /// Create or fetch a variable. If create, unwraps `sizeopt` and uses
  /// as the temp size; If fetches and `sizeopt` is a `Some()` variant,
  /// asserts that the provided `DestSize` matches that of the fetched var.
  ///
  /// Note that loop depth is always updated with each call.
  pub fn var(&mut self, var: &str, sizeopt: Option<DestSize>) -> Result<Dest> {
    // Checks if the variable is actually a function argument.
    // If so, return the corresponding function argument position.
    if let Some(argpos) = self.varname_argpos_map.get(var) {
      if MOVE_FNARG_FROM_REGS_TO_TEMPS && (*argpos <= 5) {
        // do nothing because such arg will be created / fetched
      } else {
        return Ok(Dest::from_nth_function_arg(
          *argpos,
          sizeopt.expect("unreachable"),
        ));
      }
    }

    // Create or fetch a temp variable.
    match self.var_temp_map.get(var) {
      Some(Dest::T(idx, old_size)) => {
        // performs size checks.
        if let Some(size) = sizeopt {
          if size != *old_size {
            return errs(format!(
              "while fetching {}, sizes dont match: {:?} vs {:?}",
              var, size, old_size
            ));
          }
        }

        // direct update avoids borrowing issue.
        self.temp_depth_map.update_depth(*idx, self.loop_depth);

        Ok(Dest::T(*idx, *old_size))
      }

      // Impossible fetches
      Some(_) => unreachable!("Can only fetch temp"),

      // Failed to fetch, create new.
      None => {
        let result =
          self.temp(sizeopt.expect("Cannot new var() with unknown size"));
        self.var_temp_map.insert(var.to_string(), result);
        Ok(result)
      }
    }
  }

  /// Makes a new temp for some `var` of specific `size`.
  ///
  /// Note that loop depth is always updated with each call.
  fn mk_tmp_for_var(&mut self, var: &str, size: DestSize) -> Dest {
    let result = self.temp(size);
    self.var_temp_map.insert(var.to_string(), result);
    result
  }

  /// Creates or fetches a variable. If fetch but size mismatches,
  /// converts to create case.
  ///
  /// Note that loop depth is always updated with each call.
  pub fn eqsize_var(&mut self, var: &str, size: DestSize) -> Dest {
    // Checks if the variable is actually a function argument.
    // If so, return the corresponding function argument position.
    if let Some(argpos) = self.varname_argpos_map.get(var) {
      if MOVE_FNARG_FROM_REGS_TO_TEMPS && (*argpos <= 5) {
        // do nothing because such arg will be created / fetched
      } else {
        return Dest::from_nth_function_arg(*argpos, size);
      }
    }

    // Create or fetch a temp variable.
    match self.var_temp_map.get(var) {
      Some(t @ Dest::T(idx, old_size)) => {
        if size == *old_size {
          // direct update avoids borrowing issue.
          self.temp_depth_map.update_depth(*idx, self.loop_depth);

          *t
        } else {
          self.mk_tmp_for_var(var, size)
        }
      }
      Some(_) => unreachable!("Can only fetch temp"),
      None => self.mk_tmp_for_var(var, size),
    }
  }

  pub fn add_instr(&mut self, instr: Instr) {
    self.instrs.push(instr);
  }

  /// The same as `add_instr()` except restricted to only `Instr::Lbl`.
  pub fn label(&mut self, lbl_idx: AsmLabel) {
    self.instrs.push(Instr::Lbl(lbl_idx));
  }

  /// Adds conditional jump. If `cond` then `b1` else `b2`.
  pub fn add_jmp_condition(&mut self, cond: Dest, b1: AsmLabel, b2: AsmLabel) {
    self.instrs.push(Instr::JmpCondition {
      condition: cond,
      tgt_true: b1,
      tgt_false: b2,
    });
  }

  pub fn goto(&mut self, lbl_idx: AsmLabel) {
    self.instrs.push(Instr::Jmp(lbl_idx));
  }

  /// Prints generated assembly. Only works when flag '--dump-assem' is used.
  pub fn print_instrs(&self) {
    for (i, inst) in self.instrs.iter().enumerate() {
      println!("{}:\t {}", i, inst);
    }
  }

  pub fn count_var(&self) -> u32 {
    if self.temp_index < 1 {
      0 as u32
    } else {
      self.temp_index
    }
  }
}
