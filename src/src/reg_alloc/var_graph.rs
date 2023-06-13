use std::cmp::Ordering;
/// A graph structure and its auxiliaries for implementing register allocation
/// via graph coloring.
///
/// Note that Color and Register are synonyms under this context.
/// Author: Owen Li <tianwei2@andrew.cmu.edu>
use std::collections::{HashMap, HashSet};

use super::ast_graph_node::*;
use crate::asm::Dest;
use crate::asm_processing::intrafunction_structure::BBGraph;
use crate::codegen::TmpDepthMap;
use crate::const_params::{ENABLE_MCS_HEURISTICS, REGALLOC_POOL};
use crate::reg_alloc::x86_register::*;
use crate::util::datastructure::Counter;

use super::lifetime::AnnotatedInstrBlock;

// ----------------------------- Helper Functions -----------------------------

/// Converts from asm::Dest to ast_graph_node::Node.
fn d2n(d: Dest) -> Node {
  match d {
    Dest::T(n, _) => Node::Temporary(n),
    Dest::R(r, _) => Node::Register(r),
    Dest::FnArgOnStack(n, _) => Node::FnArgOnStack(n),
  }
}

// ------------------------------ Node Multimap ------------------------------

/// A multimap datastructure similar to that of C++.
type NodeMultiMap = HashMap<Node, HashSet<Node>>;

/// Tries to initialize a new `key` for multimap and lets it map to an
/// empty set. Does nothing of such a key already exists.
fn mm_try_init_key(mm: &mut NodeMultiMap, key: &Node) {
  if !mm.contains_key(key) {
    assert!(mm.insert(key.clone(), HashSet::<Node>::new()).is_none());
  }
}

/// Insert `(k,v)` into multimap.
fn mm_insert(mm: &mut NodeMultiMap, k: Node, v: Node) {
  mm_try_init_key(mm, &k);
  mm.get_mut(&k).expect("k is already init'd").insert(v);
}

/// Extend the values of `k` by `vs`.
fn mm_extend<T: Iterator<Item = Node>>(mm: &mut NodeMultiMap, k: &Node, vs: T) {
  mm_try_init_key(mm, &k);
  mm.get_mut(&k).expect("k is already init'd").extend(vs);
}

/// Removes a key from multimap.
fn mm_remove(mm: &mut NodeMultiMap, k: &Node) -> HashSet<Node> {
  mm.remove(k).unwrap_or(HashSet::new())
}

// --------------------------- Reg Coalescing Dict ---------------------------

/// A dictionary that maps each node `n` to the set of nodes coalesced into `n`.
/// In particular, it keeps track of a multimap that maps each node `n` to the
/// set of nodes `m`, such that `m` is coalesced into `n`. In other words,
///
/// `n => {m: m --coalesce--> n}`
pub struct CoalesceDict(NodeMultiMap);

impl CoalesceDict {
  /// Creates an empty coalesce dict.
  fn mk_empty_dict() -> Self {
    CoalesceDict(HashMap::<Node, HashSet<Node>>::new())
  }

  /// Book-keeps some coalesce action (`src --coalesce--> dest`).
  /// Does NOT perform any check!
  fn bookkeep(&mut self, src: &Node, dest: &Node) {
    // remove src as a coalescing target, and retrieves
    // the set of nodes already coalesced into src.
    let coalesced_into_src = mm_remove(&mut self.0, &src);

    // both the afore-mentioned set and src shall coalesce into dest.
    let mut shall_coalesce_to_dest = coalesced_into_src;
    shall_coalesce_to_dest.insert(src.clone());
    mm_extend(&mut self.0, &dest, shall_coalesce_to_dest.into_iter());
  }

  /// Expands node-color map. Specifically, for each pair of `(n, c)` in the
  /// input node-color-map `mp`, we insert into `ret` the pair `(n, c)`, the
  /// set of pairs
  ///
  /// `{(m, c) : m --coalesce--> n}`,
  ///
  /// and returns `ret`.
  pub fn expand_node_col_map(
    &self,
    mp: HashMap<Node, RegAbs86>,
  ) -> HashMap<Node, RegAbs86> {
    let mut ret = HashMap::<Node, RegAbs86>::new();
    for (n, c) in mp {
      ret.insert(n.clone(), c);

      if let Some(coalesced_into_n) = self.0.get(&n) {
        ret.extend(coalesced_into_n.iter().map(|m| (m.clone(), c)));
      }
    }
    ret
  }
}

// ------------------------- Actual Impl of Var Graph -------------------------

/// Data associated with nodes
#[derive(Hash, Debug, Clone)]
struct NodeData {
  key: Node,
  col: Option<RegAbs86>, // color of node, corresponds to physical registers
  weight: usize,         // weight of node for graph coloring
}

/// An interference graph of checkpoint::Node, implemented as adj-list.
///
/// [TODO] Uses Hashmap and does not take advantage of enumerable graphs.
/// To optimize, consider enumerable the graph.
#[derive(Debug, Clone)]
pub struct NodeGraphHs {
  vertices: HashMap<Node, NodeData>,
  edges: HashMap<Node, HashSet<Node>>,

  /// A dictionary that maps each temporary variable to the maximum layers of
  /// nested loops it appears in. This is used as part of MCS heuristics.
  tmp_depth: TmpDepthMap,

  /// A datastructure that keeps track of the number of occurrences of a
  /// particular temp var in the function. This measures how "impactful" a
  /// temp var is; and the impactful variables will be prioritized in
  /// coloring (therefore less likely to be spilled).
  impact: Counter<u32>,

  /// Some ASM instructions' destinations will inevitably be
  /// named registers (ie. `%eax` in case of function return). As a result,
  /// some nodes of the interference graph will be of the `Node::Register`
  /// variant, and shall only be assigned to its specific register.
  ///
  /// These destinations' nodes in interference graph will therefore be colored
  /// accordingly at the construction stage of the graph, and these
  /// pre-existing colors will be stored in the `starting_color` field.
  ///
  /// When performing greedy coloring, this item will be used as the `existing`
  /// argument of `Palette86::new()`, to reduce the total number of colors used.
  starting_colors: HashSet<NamedReg>,
}

impl PartialEq for NodeData {
  fn eq(&self, other: &Self) -> bool {
    self.key == other.key && self.weight == other.weight
  }
}

impl PartialOrd for NodeData {
  fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
    use std::cmp::Ordering::*;
    match self.weight.cmp(&other.weight) {
      Less => Some(Less),
      Greater => Some(Greater),
      _ => self.key.to_string().partial_cmp(&other.key.to_string()),
    }
  }
}

impl Eq for NodeData {}

impl Ord for NodeData {
  fn cmp(&self, other: &Self) -> std::cmp::Ordering {
    use std::cmp::Ordering::*;
    match self.weight.cmp(&other.weight) {
      Less => Less,
      Greater => Greater,
      _ => self.key.to_string().cmp(&other.key.to_string()),
    }
  }
}

impl NodeData {
  /// Takes in a Node, and creates its associated data.
  pub fn new(n: &Node) -> Self {
    Self {
      key: n.clone(),
      col: None,
      weight: 0,
    }
  }
}

#[allow(dead_code)]
impl NodeGraphHs {
  /// construct a new graph with no vertices nor edges.
  pub fn mk_empty(impact: Counter<u32>, tmp_depth: TmpDepthMap) -> Self {
    Self {
      vertices: HashMap::<Node, NodeData>::new(),
      edges: HashMap::<Node, HashSet<Node>>::new(),
      tmp_depth,
      impact,
      starting_colors: HashSet::<NamedReg>::new(),
    }
  }

  /// Consumes an iterable collection of Nodes, construct an edgeless graph.
  /// If any such vertex is a `Node::Register` variant, precolor according to
  /// fuzzy string-to-register conversion.
  ///
  /// [L3+] If any such vertex is a `Node::FnArgOnStack` variant, precolor
  /// accordingly.
  ///
  /// Note that such a function will also insert such precolors to the
  /// `starting_colors` field.
  pub fn mk_edgeless<T>(
    nodes: T,
    impact: Counter<u32>,
    tmp_depth: TmpDepthMap,
  ) -> Self
  where
    T: IntoIterator<Item = Node>,
  {
    let mut ret = Self::mk_empty(impact, tmp_depth);

    for node in nodes {
      ret.insert_node(&node);

      // if such vertex is a Node::Register variant, pre-color it, and
      // add relevant color to `starting_color`.
      if let Node::Register(regname) = node {
        ret.force_set_col(&node, RegAbs86::Named(regname));
        ret.force_set_wt(&node, 1); // pre-colored v shall be picked first

        ret.starting_colors.insert(regname);
      }

      // similar story here, except for extra fn args on stack. the only
      // exception is that fn arg on stack do not count toward starting cols.
      if let Node::FnArgOnStack(n) = node {
        ret.force_set_col(&node, RegAbs86::FnArgOnStack(n));
        ret.force_set_wt(&node, 1);
      }
    }

    ret
  }

  /// Consumes an `asm_processing::BBGraph` instance and crreates an
  /// interference graph
  pub fn from_bbgraph(bbg: &BBGraph) -> Self {
    let vertices: Vec<Node> = bbg.variable_set().into_iter().map(d2n).collect();

    let mut ret =
      Self::mk_edgeless(vertices, bbg.count_temp(), bbg.tmp_depth.clone());

    for (u, v) in bbg.get_interference_set() {
      ret.add_undirected_edge(&d2n(u), &d2n(v));
    }

    ret
  }

  /// Sorts a pair of nodes into src-dest order. Returns nothing if the  
  /// pair is not coalescable.
  fn put_coalesce_src_b4_dest(pair: (Node, Node)) -> Option<(Node, Node)> {
    use std::cmp::{max, min};
    match pair {
      // for a pair of temporary, coalesce large number into small number.
      (Node::Temporary(x1), Node::Temporary(x2)) => {
        Some((Node::Temporary(max(x1, x2)), Node::Temporary(min(x1, x2))))
      }

      // coalesce temporary into register.
      (t @ Node::Temporary(_), reg @ Node::Register(_))
      | (reg @ Node::Register(_), t @ Node::Temporary(_)) => Some((t, reg)),

      // do not coalesce the rest.
      _ => None,
    }
  }

  /// Heuristics comparison function for register coalescing pairs.
  ///
  /// [note] Only works for properly oriented and filtered src / dest pairs.
  fn coalesce_heuristics(p1: &(Node, Node), p2: &(Node, Node)) -> Ordering {
    let ((s1, d1), (s2, d2)) = (p1, p2);

    match (d1, d2) {
      // prefer to coalesce into named regs first
      (Node::Register(..), Node::Temporary(..)) => Ordering::Less,
      (Node::Temporary(..), Node::Register(..)) => Ordering::Greater,

      // prefer to coalesce into smaller temps, in order to avoid
      // triggering bookkeeping remap.
      (Node::Temporary(t1), Node::Temporary(t2)) => t1.cmp(&t2),

      (Node::Register(..), Node::Register(..)) => {
        match (s1, s2) {
          // prefer to coalesce from larger temps, in order to remove some
          // burden from coalesce src-dest pair mappping.
          (Node::Temporary(t1), Node::Temporary(t2)) => t2.cmp(&t1),
          (s1, s2) => unreachable!("Malformed sources: ({}, {})", s1, s2),
        }
      }

      (d1, d2) => unreachable!("Malformed dests: ({}, {})", d1, d2),
    }
  }

  /// Computes a list of possible coalesces, via obtaining a vector of pairs
  /// of `(a, b)` such that `mov a, b` is an instruction somewhere in `bbg`,
  /// and mapping these pairs to pairs of `Node`s.
  ///
  /// In particular, node interference is not checked, as such interferences
  /// may change while performing coalescing.
  pub fn maybe_coalesces(&self, bbg: &BBGraph) -> Vec<(Node, Node)> {
    bbg
      .mov_instrs()
      .into_iter()
      .map(|(s, d)| (d2n(s), d2n(d)))
      .collect()
  }

  /// Performs greedy coalescing. Returns a bookkeeping dictionary. Panics if
  /// some pairs of nodes are not in graph.
  pub fn greedy_coalesce(
    &mut self,
    mut node_pairs_to_coalesce: Vec<(Node, Node)>,
    color_threshold: usize,
  ) -> CoalesceDict {
    use std::cmp::{max, min};

    let mut coalesce_map = CoalesceDict::mk_empty_dict();

    // pre-process coalescing pairs by ordering them and filtering out
    // malformed pairs.
    node_pairs_to_coalesce = node_pairs_to_coalesce
      .into_iter()
      .filter_map(Self::put_coalesce_src_b4_dest)
      .collect();

    node_pairs_to_coalesce.sort_by(Self::coalesce_heuristics);
    node_pairs_to_coalesce.reverse();

    'coal_n1_n2_pair: while let Some((n1, n2)) = node_pairs_to_coalesce.pop() {
      // no need to coalesce self; do not coalesce interfering stuffs.
      if n1 == n2 || self.interferes(&n1, &n2) {
        continue 'coal_n1_n2_pair;
      }

      if self.joint_neighb_card(&n1, &n2, color_threshold) > color_threshold {
        continue 'coal_n1_n2_pair;
      }

      let (coal_src, coal_dest) = (n1, n2);

      self.contract(&coal_src, &coal_dest);

      coalesce_map.bookkeep(&coal_src, &coal_dest);

      // coalesce impacts of temps.
      if let (Node::Temporary(src_idx), Node::Temporary(dest_idx)) =
        (&coal_src, &coal_dest)
      {
        self.impact.coalesce(src_idx, dest_idx);
      } else if let (Node::Temporary(src_idx), Node::Register(_)) =
        (&coal_src, &coal_dest)
      {
        // src coalesces into a register and disappears, thus no impact.
        self.impact.remove(src_idx);
      }

      // updates list
      let contract_map = |x: Node| if &x == &coal_src { coal_dest } else { x };
      let contract_pair = |(x, y)| (contract_map(x), contract_map(y));
      node_pairs_to_coalesce = node_pairs_to_coalesce
        .into_iter()
        .map(contract_pair)
        .filter_map(Self::put_coalesce_src_b4_dest) // important to preserve
        .collect();
    }

    coalesce_map
  }

  /// Inserts a new node. Returns true if the node already exists.
  /// In case the to-be-inserted node already exists, do nothing.
  ///
  /// Note that when a node is inserted, it is automatically added as an
  /// entry to the edge-set, which maps to a newly-created hashset,
  /// representing its (absence of) neighbors.
  fn insert_node(&mut self, n: &Node) -> bool {
    if self.vertices.contains_key(n) {
      true
    } else {
      self.vertices.insert(n.clone(), NodeData::new(n));
      self.edges.insert(n.clone(), HashSet::<Node>::new());
      false
    }
  }

  /// Computes the max degree of graph.
  pub fn max_deg(&self) -> usize {
    use std::cmp::max;
    self
      .edges
      .iter()
      .map(|(v, nv)| nv.len())
      .reduce(max)
      .unwrap_or(0)
  }

  /// Empirically computes an upperbound for graph chromatic number.
  ///
  /// [warning] slow!
  pub fn chromatic_upperbound(&self) -> usize {
    let (.., num_spill) = self.clone().assign_register();
    num_spill + REGALLOC_POOL.len()
  }

  /// checks whether graph has a vertex v.
  fn contains_vertex(&self, u: &Node) -> bool {
    self.vertices.get(u).is_some()
  }

  /// Checks whether two nodes interferes with each other.
  fn interferes(&self, u: &Node, v: &Node) -> bool {
    match (
      self.contains_directed_edge(u, v),
      self.contains_directed_edge(v, u),
    ) {
      (true, true) => true,
      (false, false) => false,
      _ => unreachable!("Malformed graph: shall be undirected. "),
    }
  }

  /// checks whether graph has an edge from u to v.
  ///
  /// [warning] does not check whether there is an edge from v to u.
  fn contains_directed_edge(&self, u: &Node, v: &Node) -> bool {
    if let Some(h) = self.edges.get(&u) {
      h.get(&v).is_some()
    } else {
      false
    }
  }

  /// Computes the joint neighbor size of two vertices. Prematurely returns
  /// once the joint size exceeds upperbound.
  fn joint_neighb_card(&self, n1: &Node, n2: &Node, ub: usize) -> usize {
    let n1_neighb = self.edges.get(n1).expect("n1 is not in G").clone();
    let n2_neighb = self.edges.get(n2).expect("n2 is not in G").clone();

    let mut joint_neighb_size = n1_neighb.len();
    'a: for x in n2_neighb.iter().filter(|x| !n1_neighb.contains(x)) {
      joint_neighb_size += 1;
      if joint_neighb_size > ub {
        break 'a;
      }
    }

    joint_neighb_size
  }

  /// contracts node `src` into node `dest`.
  fn contract(&mut self, src: &Node, dest: &Node) {
    // N(dest) = N(dest) + N(src) - dest
    let mut src_neighbs = self.get_neighb(src).clone();
    src_neighbs.remove(dest);
    self.extend_undirected_connections(dest, src_neighbs.into_iter());

    // removes src from graph
    assert!(self.remove_vertex(src));
  }

  /// adds (directed) edge without checks.
  /// shall not be used publicly.
  ///
  /// [warning] not tested
  fn add_directed_edge(&mut self, u: &Node, v: &Node) {
    match self.edges.get_mut(&u) {
      // when u already exists
      Some(h) => {
        h.insert(v.clone());
      }

      // when u does not exist
      _ => {
        let h_tmp = HashSet::new();
        self.edges.insert(u.clone(), h_tmp);
        self
          .edges
          .get_mut(&u)
          .expect(
            "[var_graph::add_directed_edge] neighbors of u \
                shall exist",
          )
          .insert(v.clone());
      }
    }
  }

  /// Given input variables u and v, add edges (u,v) and (v,u) into the graph.  
  ///
  /// [warning] not tested
  fn add_undirected_edge(&mut self, u: &Node, v: &Node) {
    self.add_directed_edge(u, v);
    self.add_directed_edge(v, u);
  }

  /// Given a node `v` and an iterator `it` of nodes, connect `v` with
  /// everything in `it`. Panics if any vertex is not in graph.
  fn extend_undirected_connections<T>(&mut self, v: &Node, it: T)
  where
    T: Iterator<Item = Node>,
  {
    assert!(self.vertices.contains_key(v));
    assert!(self.edges.contains_key(v));

    for u in it {
      assert!(self.vertices.contains_key(&u));
      assert!(self.edges.contains_key(&u));
      self.add_undirected_edge(&u, v);
    }
  }

  /// Gets a reference to the collection of neighbor of some vertex.
  /// Panics if such vertex does not exist.
  fn get_neighb(&self, u: &Node) -> &HashSet<Node> {
    self.edges.get(&u).expect("u is not in G")
  }

  /// Increments the weight of a given vertex by one.
  ///
  /// [warning] In case `u` is not in graph, this function terminates quietly
  /// without performing any action.
  fn incr_wt(&mut self, u: &Node) {
    if let Some(dt) = self.vertices.get_mut(u) {
      dt.weight += 1;
    }
  }

  /// Calculates the impact of some node.
  fn node_impact(&self, n: &Node) -> usize {
    if let Node::Temporary(idx) = n {
      self.tmp_depth.get_depth(idx)
      // self.impact.count(idx)
    } else {
      0
    }
  }

  /// Returns the max-weight vertex, paired with its weight. Breaks tie by
  /// vertex name lex-order. Returns None if there's no node in graph.
  ///
  /// [warning] Can only call when self is not empty.
  fn get_maxwt_vert(&self) -> Option<(Node, usize)> {
    assert!(!self.vertices.is_empty());

    // running max-weight item
    let (mut max_node_opt, mut max_data_opt) = (None, None::<&NodeData>);

    for (node, data) in &self.vertices {
      match (max_node_opt, max_data_opt) {
        // already initialized
        (Some(max_node), Some(max_data)) => {
          // cmp 2 running max
          if data.weight > max_data.weight {
            (max_node_opt, max_data_opt) = (Some(node), Some(data));
          } else if data.weight == max_data.weight && ENABLE_MCS_HEURISTICS {
            // this is purposefully not put into nodedata comparison function,
            // so that such heuristics can be turned off easily.

            if self.node_impact(node) > self.node_impact(max_node) {
              (max_node_opt, max_data_opt) = (Some(node), Some(data));
            }
          }
        }

        _ => {
          // initialize running max
          (max_node_opt, max_data_opt) = (Some(node), Some(data));
        }
      }
    }

    Some((max_node_opt?.clone(), max_data_opt?.weight))
  }

  /// Removes a vertex from graph and returns whether it was present in graph.
  fn remove_vertex(&mut self, u: &Node) -> bool {
    // remove from vertex set
    if self.vertices.remove(&u).is_none() {
      assert!(
        !self.edges.contains_key(&u),
        "u is in edges but not vertices"
      );
      return false; // if u is not in graph, return false rightaway.
    }

    // remove as in-vertex
    let N_u = self
      .edges
      .remove(&u)
      .expect("u is in vertices but not edges");

    // remove as out-vertex
    for v in N_u {
      let N_v = self
        .edges
        .get_mut(&v)
        .expect("a neighb of u is not in edges");
      assert!(N_v.remove(&u), "a neighb of u does not have u as neighb");
    }

    true
  }

  /// Removes a vertex and increments the weights of all neighbors.
  /// Returns true if the graph contains the vertex.
  fn remove_and_incr_neighb_wt(&mut self, u: Node) -> bool {
    // remove from vertex set
    if self.vertices.remove(&u).is_none() {
      return false; // if u is not in graph, return false rightaway.
    }

    // remove as out-vertex
    for (_, neighb) in &mut self.edges {
      neighb.remove(&u);
    }

    // remove as in-vertex
    let neighbs_of_u = self
      .edges
      .remove(&u)
      .expect("edges shall contain u: fn would've returned otherwise");

    // incr neighb wt of u
    for vert_to_incr_wt in neighbs_of_u {
      self.incr_wt(&vert_to_incr_wt);
    }

    true
  }

  /// Gets the color of a certain vertex. None if vertex does not exist, or if
  /// vertex is uncolored.
  pub fn get_col(&self, u: &Node) -> Option<RegAbs86> {
    self.vertices.get(u)?.col.clone()
  }

  /// Gets the set of colors used by neighbors of `u`. If `u` is not in graph,
  /// returns `None`.
  pub fn get_neighb_cols(&self, u: &Node) -> Option<HashSet<RegAbs86>> {
    let mut ret: HashSet<RegAbs86> = HashSet::new();

    for neighb in self.edges.get(u)? {
      if let Some(col_to_insert) = self.get_col(neighb) {
        ret.insert(col_to_insert);
      }
    }

    Some(ret)
  }

  /// Gets the weight of a certain vertex. None if vertex does not exist.
  pub fn get_wt(&self, u: &Node) -> Option<usize> {
    Some(self.vertices.get(u)?.weight)
  }

  /// Forcibly sets `Some(new_col)` to be the color of `u`, bypassing any and
  /// all constraints.
  ///
  /// [returns] `Some(c)` if `c` is the previous color of `u`, whether
  /// `c` is `Some` or `None`. If vertex `u` is not found, `panic!`.
  fn force_set_col(&mut self, u: &Node, new_col: RegAbs86) -> Option<RegAbs86> {
    let ret = self.vertices.get_mut(u).unwrap().col;
    self.vertices.get_mut(u).unwrap().col = Some(new_col);
    ret
  }

  /// Forcibly sets `new_wt` to be the weight of `u`, bypassing any and all
  /// constraints.
  ///
  /// [returns] `Some(w)` if `w` is the previous weight of `u`. If `u` is not
  /// found, `panic!`.
  fn force_set_wt(&mut self, u: &Node, new_wt: usize) -> usize {
    let ret = self.vertices.get_mut(u).unwrap().weight;
    self.vertices.get_mut(u).unwrap().weight = new_wt;
    ret
  }

  /// Given an iterator of available registers and a specified _uncolored_ vertex `u`, colors
  /// `u` to the available register of least possible index, such that the
  /// color of `u` does not conflict with that of its neighbors.
  ///
  /// If `u` is already colored, this function has no effects, and merely
  /// returns the color of `u`.
  ///
  /// [requires] `u` must be an existing vertex in self.
  ///
  /// [requires] `color_iter` must be a brand-new iterator to the segment of
  /// available registers, ie. first call to `color_iter.next()` will return
  /// the first ever available color.
  ///
  /// [returns] The assigned color.
  pub fn color_vertex(
    &mut self,
    reg_palette: &mut Palette86,
    u: &Node,
  ) -> RegAbs86 {
    // if u is already colored, return is color.
    if let Some(c) = self.get_col(u) {
      return c;
    }

    // select the first available color by default
    let mut selected_col = reg_palette.next();

    // set of colors used by neighbors of u
    let unavailable_col: HashSet<RegAbs86> = self
      .get_neighb_cols(u)
      .expect("u must exist in graph in order for it to be colored");

    // select the next color in case of conflict with neighbor's color
    while unavailable_col.contains(&selected_col) {
      selected_col = reg_palette.next();
    }

    // assign color
    self.force_set_col(u, selected_col);
    // .expect("[color vertex] u should exist");

    selected_col
  }

  /// Consumes self, performs Max Cardinality Search (MCS) to generate an
  /// ordering of nodes.Such ordering makes greedy coloring (therefore
  /// reg-alloc) perform well.
  pub fn max_card_search(mut self) -> Vec<(Node, usize)> {
    let mut ordering: Vec<(Node, usize)> = Vec::new();

    while !self.edges.is_empty() {
      let (mw_vert, wt) = self.get_maxwt_vert().expect(
        "Graph shouldn't run out of vertex before \
          it runs out of edge",
      );

      ordering.push((mw_vert.clone(), wt));

      assert!(self.remove_and_incr_neighb_wt(mw_vert));
    }

    ordering
  }

  /// Consumes self, given a list of available registers, generate a vertex
  /// to abstract register assignment, some `HashSet` of used named
  /// registers, as well as the number of spilled registers used.
  ///
  /// If for some reason the graph is not entirely colored before return,
  /// this function will `panic!`.
  ///
  /// [requires] Nothing in `registers` shall repeat.
  pub fn assign_register(
    mut self,
  ) -> (HashMap<Node, RegAbs86>, HashSet<NamedReg>, usize) {
    let ordering = self.clone().max_card_search();

    let starting_col_vec: Vec<NamedReg> =
      self.starting_colors.iter().copied().collect();
    let mut used_named_reg = self.starting_colors.clone();
    let mut number_of_spills: usize = 0;

    for (u, _) in ordering {
      let mut color_iter = Palette86::new(&starting_col_vec);
      let used_col = self.color_vertex(&mut color_iter, &u);
      match used_col {
        RegAbs86::Named(nr) => {
          used_named_reg.insert(nr);
        }
        RegAbs86::Spill(k) => {
          // Having nth spill means there are n+1 spills in total.
          number_of_spills = std::cmp::max(number_of_spills, k + 1);
        }
        RegAbs86::FnArgOnStack(_) => {
          // This is reachable because used_col is already defined,
          // but we shall do nothing here.
        }
      }
    }

    let mp = self
      .vertices
      .into_iter()
      .map(|(n, dt)| (n, dt.col.expect("entire graph shall be colored")))
      .collect();

    (mp, used_named_reg, number_of_spills)
  }
}

impl std::fmt::Display for NodeGraphHs {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    // print node info
    for (u, data) in &self.vertices {
      let s = match &data.col {
        Some(c) => format!("{}", c),
        _ => String::from("[uncolored]"),
      };

      let res = write!(f, "{:<5}:  {}\n", u.to_string(), s);
      if res.is_err() {
        return res;
      }
    }

    let res = write!(f, "\n");
    if res.is_err() {
      return res;
    }

    // print edge conn
    for (u, neighb) in &self.edges {
      let res = write!(f, "{:<5} ->  {:?}\n", u.to_string(), neighb);
      if res.is_err() {
        return res;
      }
    }

    write!(f, "\n")
  }
}
