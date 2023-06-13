use super::ProgContext;
use crate::asm_processing::intrafunction_structure::Error;
use crate::ast;
use crate::ast::Field;
use crate::ast::Typ;
use crate::ast::Variant;
use crate::elab;

// use crate::util::c0spec::DEBUG;
const DEBUG: bool = false;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::{Debug, Display, Formatter};
use std::option::Option;

pub struct Tuples {
  pub this_id: String,
  pub this_variants: HashMap<String, Box<UnMatched>>,
  pub typ: ast::Typ,
  pub next: Option<Box<Tuples>>,
  pub matched: bool,
  pub descendants_matched: bool,
  pub expended: bool,
}

impl Display for Tuples {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(
      f,
      "Tuples {{ this_id : {}, this_variants : {:?}, typ : {:?}, next : {:?}, matched : {}, descendants_matched : {}, expended : {} }}",
      self.this_id, self.this_variants.keys(), self.typ, self.next.is_some(), self.matched, self.descendants_matched, self.expended
    )
  }
}

impl Tuples {
  pub fn new(typ: Typ) -> Tuples {
    Tuples {
      this_id: String::new(),
      this_variants: HashMap::new(),
      typ: typ,
      next: None,
      matched: false,
      descendants_matched: false,
      expended: false,
    }
  }

  pub fn deepcopy(&self) -> Tuples {
    let mut new_tuples = Tuples::new(self.typ.clone());
    new_tuples.this_id = self.this_id.clone();
    new_tuples.matched = self.matched;
    new_tuples.descendants_matched = self.descendants_matched;
    new_tuples.expended = self.expended;
    for (id, unmatched) in self.this_variants.iter() {
      new_tuples
        .this_variants
        .insert(id.clone(), Box::new(unmatched.deepcopy()));
    }
    new_tuples
  }

  /// check the tuple is matched or not
  pub fn check_matched(&mut self) -> bool {
    if self.matched {
      return true;
    }
    if self.this_variants.len() == 0 {
      return false;
    }
    let mut matched = true;
    for (_, value) in self.this_variants.iter_mut() {
      matched &= value.check_matched();
    }
    if matched {
      self.matched = true;
      let decentants_matched =
        self.next.is_some() && self.next.as_mut().unwrap().check_matched();
      self.descendants_matched = decentants_matched;
      return self.descendants_matched;
    }
    false
  }

  pub fn expend(&mut self, progctx: &ProgContext) {
    if self.expended {
      return;
    }

    let tags = progctx.ev_all_tags(&self.this_id);
    self.this_variants = HashMap::new();
    for (tag, tag_typ) in tags {
      let mut new_unmatched = Box::new(UnMatched::new());
      new_unmatched.tag = tag.clone();
      new_unmatched.typs = tag_typ.clone();
      new_unmatched.expanded = false;
      if self.next.is_some() {
        new_unmatched.lst =
          Some(Box::new(self.next.as_mut().unwrap().deepcopy()));
      }
      if DEBUG {
        eprintln!("tag : {}", tag);
        eprintln!("tag_typ : {:?}", tag_typ);
        eprintln!("new_unmatched : {}\n", new_unmatched);
      }

      self.this_variants.insert(tag.clone(), new_unmatched);
    }
    self.expended = true;
  }

  pub fn add(&mut self, patt: &ast::Patt, progctx: &ProgContext) {
    use crate::ast::Patt;
    match patt {
      Patt::Any | Patt::Variable(..) => {
        self.matched = true;
      }
      Patt::Variant(id, var, patts) => {
        // if not expanded, expand it
        self.expend(progctx);
        if self.this_variants.contains_key(var) {
          let unmatched = self.this_variants.get_mut(var).unwrap();
          unmatched.expand(progctx);
          unmatched.add(patts, progctx);
          if DEBUG {
            eprintln!("unmatched after add {}: {}\n", patt, unmatched);
          }
          if unmatched.check_matched() {
            self.this_variants.remove(var);
            if self.this_variants.len() == 0 {
              self.matched = true;
            }
          }
        } else {
          // already matched, skipped
          return;
        }
      }
    }
  }
}

// whether it is matched or not, or wildcard
pub struct UnMatched {
  pub lst: Option<Box<Tuples>>,
  // pub unexpended_next : Option<Box<Tuples>>,
  pub tag: String,
  pub typs: Vec<ast::Typ>,
  pub matched: bool,
  pub expanded: bool,
}

use std::fmt;
impl Display for UnMatched {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(
      f,
      "UnMatched {{ lst: {}, tag : {}, typs : {:?}, matched : {}, expanded : {} }}",
      self.lst.is_some() ,self.tag, self.typs, self.matched, self.expanded
    )
  }
}

impl UnMatched {
  pub fn expand(&mut self, progctx: &ProgContext) {
    if self.expanded {
      return;
    }
    let mut prev = match self.lst {
      Some(ref mut prev) => Some(Box::new(prev.deepcopy())),
      None => None,
    };
    for typ in self.typs.clone().into_iter().rev() {
      match &typ {
        ast::Typ::C0enum(name) => {
          let tags = progctx.ev_all_tags(&name);
          let mut new_tuple = Box::new(Tuples::new(typ.clone()));
          new_tuple.this_id = name.clone();
          if prev.is_some() {
            new_tuple.next = Some(prev.unwrap());
          }
          if DEBUG {
            eprintln!("new_tuple : {}", new_tuple);
          }
          prev = Some(Box::new(new_tuple.deepcopy()));
        }
        _ => {
          let mut new_tuple = Box::new(Tuples::new(typ));
          if prev.is_some() {
            new_tuple.next = Some(prev.unwrap());
          }
          if DEBUG {
            eprintln!("new_tuple : {}", new_tuple);
          }
          prev = Some(Box::new(new_tuple.deepcopy()));
        }
      }
    }
    self.lst = prev;
    self.expanded = true;
    if DEBUG {
      eprintln!("expanded : {}\n", self);
    }
  }

  pub fn add(&mut self, patts: &Vec<ast::Patt>, progctx: &ProgContext) {
    if patts.len() == 0 {
      self.matched = true;
      if DEBUG{
        eprintln!("matched becuase patt len is 0: {}\n", self);
      }
      return;
    }
    self.expand(progctx);

    // assert_eq!(self.lst.len(), patts.len());
    let mut matching_tup = self.lst.as_mut().expect(&format!(
      "no tuple to match for {} in {:?}",
      self.tag, patts
    ));
    for patt in patts {
      matching_tup.add(patt, progctx);
      let s = format!("matching_tup : {}", matching_tup);
      if DEBUG{
        eprintln!("next is {}\n", s);
      }
      // end of matching
      if matching_tup.next.is_none() {
        return;
      }
      matching_tup = matching_tup
        .next
        .as_mut()
        .expect(&format!("no tuple to match in {} for {} ", self.tag, s));
    }
    
  }

  pub fn new() -> UnMatched {
    UnMatched {
      lst: None,
      matched: false,
      tag: String::new(),
      typs: Vec::new(),
      expanded: false,
    }
  }

  pub fn deepcopy(&self) -> UnMatched {
    let mut new_unmatched = UnMatched::new();
    new_unmatched.tag = self.tag.clone();
    new_unmatched.matched = self.matched;
    new_unmatched.expanded = self.expanded;
    if self.lst.is_some() {
      new_unmatched.lst = Some(Box::new(self.lst.as_ref().unwrap().deepcopy()));
    }
    new_unmatched.typs = self.typs.clone();
    new_unmatched
  }

  pub fn check_matched(&mut self) -> bool {
    if self.matched {
      return true;
    }
    // means not initialized
    if !self.expanded {
      return false;
    }
    let mut matched =
      self.lst.is_some() && self.lst.as_mut().unwrap().check_matched();
    if matched {
      self.matched = true;
      return true;
    }
    if DEBUG {
      eprintln!("not matched : {}", self);
    }
    false
  }
}
