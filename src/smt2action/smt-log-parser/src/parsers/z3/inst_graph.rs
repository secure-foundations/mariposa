// use fxhash::{FxHashSet, FxHashMap};
// use gloo_console::log;
// use petgraph::graph::NodeIndex;
// use petgraph::stable_graph::StableGraph;
// use petgraph::visit::{Bfs, IntoEdgeReferences, Topo, IntoEdges};
// use petgraph::{
//     stable_graph::EdgeIndex,
//     visit::{Dfs, EdgeRef},
//     Direction::{Incoming, Outgoing},
// };
// use petgraph::{Direction, Graph};
// use roaring::bitmap::RoaringBitmap;
// use std::fmt;
// use std::iter::zip;
// use typed_index_collections::TiVec;

// use crate::display_with::{DisplayCtxt, DisplayWithCtxt};
// use crate::items::{BlameKind, ENodeIdx, Fingerprint, InstIdx, MatchKind, Term, TermIdx, QuantIdx, TermKind};

// use super::terms::Terms;
// use super::z3parser::Z3Parser;

// const MIN_MATCHING_LOOP_LENGTH: usize = 3;

// #[derive(Clone)]
// pub struct NodeData {
//     // pub line_nr: usize,
//     pub is_theory_inst: bool,
//     cost: f32,
//     pub inst_idx: InstIdx,
//     pub mkind: MatchKind,
//     visible: bool,
//     child_count: usize,
//     parent_count: usize,
//     pub orig_graph_idx: NodeIndex,
//     cost_rank: usize,
//     branching_rank: usize,
//     pub min_depth: Option<usize>,
//     max_depth: usize,
//     topo_ord: usize,
// }

// impl fmt::Debug for NodeData {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         write!(f, "{}", self.inst_idx)
//     }
// }

// #[derive(Clone)]
// pub enum EdgeType {
//     Direct {
//         kind: BlameKind,
//         orig_graph_idx: EdgeIndex,
//     },
//     Indirect,
// }

// impl PartialEq for EdgeType {
//     fn eq(&self, other: &Self) -> bool {
//         match (self, other) {
//             (
//                 EdgeType::Direct {
//                     orig_graph_idx: s, ..
//                 },
//                 EdgeType::Direct {
//                     orig_graph_idx: o, ..
//                 },
//             ) => s == o,
//             (EdgeType::Indirect, EdgeType::Indirect) => true,
//             _ => false,
//         }
//     }
// }

// impl EdgeType {
//     pub fn blame_term_idx(&self) -> Option<ENodeIdx> {
//         match self {
//             EdgeType::Direct { kind, .. } => kind.get_blame_node(),
//             _ => None,
//         }
//     }
//     pub fn is_direct(&self) -> bool {
//         matches!(self, EdgeType::Direct { .. })
//     }
// }

// #[derive(Clone)]
// pub struct EdgeInfo {
//     pub edge_data: BlameKind,
//     pub orig_graph_idx: EdgeIndex,
//     pub blame_term: String,
//     pub from: NodeIndex,
//     pub to: NodeIndex,
// }

// impl PartialEq for EdgeInfo {
//     fn eq(&self, other: &Self) -> bool {
//         self.orig_graph_idx == other.orig_graph_idx
//     }
// }

// impl fmt::Debug for EdgeType {
//     fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
//         match self {
//             EdgeType::Direct { .. } => write!(f, "direct edge"),
//             EdgeType::Indirect => write!(f, "indirect edge"),
//         }
//     }
// }

// #[derive(Clone, Debug)]
// pub struct InstInfo {
//     pub fingerprint: Fingerprint,
//     pub inst_idx: InstIdx,
//     pub resulting_term: Option<String>,
//     pub z3_gen: Option<u32>,
//     pub cost: f32,
//     pub mkind: MatchKind,
//     pub quant_discovered: bool,
//     pub formula: String,
//     pub pattern: Option<String>,
//     pub yields_terms: Vec<String>,
//     pub bound_terms: Vec<String>,
//     pub blamed_terms: Vec<String>,
//     pub equality_expls: Vec<String>,
//     pub dep_instantiations: Vec<NodeIndex>,
//     pub node_index: NodeIndex,
// }

// impl PartialEq for InstInfo {
//     fn eq(&self, other: &Self) -> bool {
//         self.inst_idx == other.inst_idx
//     }
// }

// #[derive(Default, Clone)]
// pub struct InstGraph {
//     orig_graph: Graph<NodeData, BlameKind>,
//     pub visible_graph: Graph<NodeData, EdgeType>,
//     node_of_inst_idx: TiVec<InstIdx, NodeIndex>,
//     cost_ranked_node_indices: Vec<NodeIndex>,
//     branching_ranked_node_indices: Vec<NodeIndex>,
//     tr_closure: Vec<RoaringBitmap>,
//     matching_loop_subgraph: Graph<NodeData, EdgeType>,
//     matching_loop_end_nodes: Vec<NodeIndex>, // these are sorted by maximal depth in descending order 
//     generalized_terms: TiVec<usize, Option<Vec<String>>>,
// }

// enum InstOrder {
//     Branching,
//     Cost,
// }

// pub struct VisibleGraphInfo {
//     pub node_count: usize,
//     pub edge_count: usize,
//     pub node_count_decreased: bool,
//     pub edge_count_decreased: bool,
// }

// impl Terms {
//     pub fn generalize(&mut self, t1: TermIdx, t2: TermIdx) -> TermIdx {
//         if t1 == t2 {
//             // if terms are equal, no need to generalize
//             t1
//         } else if let TermKind::GeneralizedPrimitive = self[t1].kind {
//             // if t1 is already generalized, no need to generalize further
//             t1
//         } else if let TermKind::GeneralizedPrimitive = self[t2].kind {
//             // if t2 is already generalized, no need to generalize further
//             t2
//         } else if self.meaning(t1) == self.meaning(t2) && self[t1].kind == self[t2].kind {
//             // if neither term is generalized, check the meanings and kinds and recurse over children
//             let a = self[t1].child_ids.clone();
//             let b = self[t2].child_ids.clone();
//             let children = zip(Vec::from(a), Vec::from(b)).map(|(c1, c2)| self.generalize(c1, c2)).collect();
//             self.new_synthetic_term(self[t1].kind, children, self.meaning(t1).copied())
//         } else {
//             // if meanings or kinds don't match up, need to generalize
//             self.new_synthetic_term(crate::items::TermKind::GeneralizedPrimitive, vec![], None)
//         }       
//     }
// }

// impl InstGraph {
//     pub fn from(parser: &Z3Parser) -> Self {
//         let mut inst_graph = Self::default();
//         inst_graph.compute_instantiation_graph(parser);
//         inst_graph
//     }

//     pub fn retain_nodes(&mut self, retain: impl Fn(&NodeData) -> bool) {
//         for node in self.orig_graph.node_weights_mut() {
//             if !retain(node) {
//                 node.visible = false;
//             }
//         }
//     }

//     pub fn retain_visible_nodes_and_reconnect(&mut self) -> VisibleGraphInfo {
//         let prev_node_count = self.visible_graph.node_count();
//         let prev_edge_count = self.visible_graph.edge_count();
//         // retain all visible nodes
//         let mut new_inst_graph = self.orig_graph.filter_map(
//             |_, node| Some(node).filter(|node| node.visible).cloned(),
//             |orig_graph_idx, edge_data| {
//                 Some(EdgeType::Direct {
//                     kind: edge_data.clone(),
//                     orig_graph_idx,
//                 })
//             },
//         );
//         // remember all direct edges (will be added to the graph in the end)
//         let direct_edges = new_inst_graph
//             .raw_edges()
//             .to_vec();
//         // nodes with missing children
//         let out_set: Vec<NodeIndex> = new_inst_graph
//             .node_indices()
//             .filter(|node| {
//                 let new_child_count = new_inst_graph.neighbors_directed(*node, Outgoing).count();
//                 let old_child_count = new_inst_graph.node_weight(*node).unwrap().child_count;
//                 new_child_count < old_child_count
//             })
//             .collect();
//         // nodes with missing parents
//         let in_set: Vec<NodeIndex> = new_inst_graph
//             .node_indices()
//             .filter(|node| {
//                 new_inst_graph.neighbors_directed(*node, Incoming).count()
//                     < new_inst_graph.node_weight(*node).unwrap().parent_count
//             })
//             .collect();
//         // add all edges (u,v) in out_set x in_set to the new_inst_graph where v is reachable from u in the original graph
//         // and (u,v) is not an edge in the original graph, i.e., all indirect edges
//         for &u in &out_set {
//             for &v in &in_set {
//                 let old_u = new_inst_graph.node_weight(u).unwrap().orig_graph_idx;
//                 let old_v = new_inst_graph.node_weight(v).unwrap().orig_graph_idx;
//                 if old_u != old_v
//                     && !self.orig_graph.contains_edge(old_u, old_v)
//                     && self.tr_closure_contains_edge(old_u, old_v)
//                 // && petgraph::algo::has_path_connecting(&self.orig_graph, old_u, old_v, None)
//                 {
//                     new_inst_graph.add_edge(u, v, EdgeType::Indirect);
//                 }
//             }
//         }
//         // compute transitive reduction to minimize |E| and not clutter the graph
//         let toposorted_dag = petgraph::algo::toposort(&new_inst_graph, None).unwrap();
//         let (intermediate, _) = petgraph::algo::tred::dag_to_toposorted_adjacency_list::<_, u32>(
//             &new_inst_graph,
//             &toposorted_dag,
//         );
//         let (tred, _) = petgraph::algo::tred::dag_transitive_reduction_closure(&intermediate);
//         // remove all edges since we only want the direct edges and the indirect edges in the transitive reduction in the final graph
//         new_inst_graph.clear_edges();
//         // add all direct edges to new_inst_graph that we removed previously
//         for direct_edge in direct_edges {
//             new_inst_graph.add_edge(
//                 direct_edge.source(),
//                 direct_edge.target(),
//                 direct_edge.weight,
//             );
//         }
//         // add all indirect edges from transitive reduction that are not direct edges
//         for indirect_edge in tred.edge_references() {
//             // in tred, the node indices are replaced by their topological rank
//             // hence we need to look up the index before adding to new_inst_graph
//             let source = toposorted_dag[indirect_edge.source() as usize];
//             let target = toposorted_dag[indirect_edge.target() as usize];
//             // we only want indirect edges
//             if !new_inst_graph.contains_edge(source, target) {
//                 new_inst_graph.add_edge(source, target, EdgeType::Indirect);
//             }
//         }
//         self.visible_graph = new_inst_graph;
//         let curr_node_count = self.visible_graph.node_count();
//         let curr_edge_count = self.visible_graph.edge_count();
//         VisibleGraphInfo {
//             node_count: self.visible_graph.node_count(),
//             edge_count: self.visible_graph.edge_count(),
//             node_count_decreased: curr_node_count < prev_node_count,
//             edge_count_decreased: curr_edge_count < prev_edge_count,
//         }
//     }

//     fn tr_closure_contains_edge(&self, from: NodeIndex, to: NodeIndex) -> bool {
//         let topo_ord_from = self.orig_graph.node_weight(from).unwrap().topo_ord;
//         let from_bitset = &self.tr_closure[topo_ord_from];
//         from_bitset.contains(to.index() as u32)
//     }

//     pub fn keep_n_most_costly(&mut self, n: usize) {
//         self.keep_n_highest_ranked(n, InstOrder::Cost)
//     }

//     pub fn keep_n_most_branching(&mut self, n: usize) {
//         self.keep_n_highest_ranked(n, InstOrder::Branching)
//     }

//     fn keep_n_highest_ranked(&mut self, n: usize, order: InstOrder) {
//         let ranked_node_indices = match order {
//             InstOrder::Branching => &self.branching_ranked_node_indices,
//             InstOrder::Cost => &self.cost_ranked_node_indices,
//         };
//         let visible_nodes: Vec<NodeIndex> = self
//             .orig_graph
//             .node_indices()
//             .filter(|n| self.orig_graph.node_weight(*n).unwrap().visible)
//             .collect();
//         if let Some(nth_highest_ranked_visible_node) = ranked_node_indices
//             .iter()
//             .filter(|nidx| visible_nodes.contains(nidx))
//             .take(n)
//             .last()
//         {
//             let nth_largest_rank = self
//                 .orig_graph
//                 .node_weight(*nth_highest_ranked_visible_node)
//                 .unwrap()
//                 .clone();
//             // among the visible nodes keep those whose cost-rank
//             // is larger than the cost rank of the n-th costliest
//             match order {
//                 InstOrder::Branching => self.retain_nodes(|node| {
//                     node.visible && node.branching_rank <= nth_largest_rank.branching_rank
//                 }),
//                 InstOrder::Cost => self.retain_nodes(|node| {
//                     node.visible && node.cost_rank <= nth_largest_rank.cost_rank
//                 }),
//             }
//         }
//     }

//     pub fn visit_descendants(&mut self, root: NodeIndex, retain: bool) {
//         let mut dfs = Dfs::new(&self.orig_graph, root);
//         while let Some(nx) = dfs.next(&self.orig_graph) {
//             self.orig_graph[nx].visible = retain;
//         }
//     }

//     pub fn visit_ancestors(&mut self, node: NodeIndex, retain: bool) {
//         let mut dfs = Dfs::new(petgraph::visit::Reversed(&self.orig_graph), node);
//         while let Some(nx) = dfs.next(petgraph::visit::Reversed(&self.orig_graph)) {
//             self.orig_graph[nx].visible = retain;
//         }
//     }

//     pub fn show_longest_path_through(&mut self, node: NodeIndex) -> Vec<NodeIndex> {
//         // construct subtree rooted at selected node
//         let mut subtree_rooted_at_node: StableGraph<NodeData, BlameKind> =
//             StableGraph::from(self.orig_graph.clone());
//         for node in subtree_rooted_at_node.node_weights_mut() {
//             node.visible = false;
//         }
//         let mut dfs = Dfs::new(&subtree_rooted_at_node, node);
//         while let Some(nx) = dfs.next(&subtree_rooted_at_node) {
//             subtree_rooted_at_node[nx].visible = true;
//         }
//         subtree_rooted_at_node = subtree_rooted_at_node.filter_map(
//             |_, node_data| {
//                 if node_data.visible {
//                     Some(node_data.clone())
//                 } else {
//                     None
//                 }
//             },
//             |_, edge| Some(edge.clone()),
//         );
//         // traverse this subtree in topological order to compute longest distances from node
//         let mut topo = Topo::new(&subtree_rooted_at_node);
//         while let Some(nx) = topo.next(&subtree_rooted_at_node) {
//             let parents = subtree_rooted_at_node.neighbors_directed(nx, Incoming);
//             let max_parent_depth = parents
//                 .map(|nx| subtree_rooted_at_node.node_weight(nx).unwrap().max_depth)
//                 .max();
//             if let Some(depth) = max_parent_depth {
//                 subtree_rooted_at_node[nx].max_depth = depth + 1;
//             }
//         }
//         let furthest_away_node_idx = subtree_rooted_at_node
//             .node_weights()
//             .max_by(|node_a, node_b| node_a.max_depth.cmp(&node_b.max_depth))
//             .unwrap()
//             .orig_graph_idx;
//         // backtrack a longest path from furthest away node in subgraph until we reach the root
//         // with respect to the subgraph, i.e., node
//         // self.backtrack(Some(&subtree_rooted_at_node), furthest_away_node_idx);
//         let mut longest_path: Vec<NodeIndex> = Vec::new();
//         let mut visitor: Vec<NodeIndex> = Vec::new();
//         if furthest_away_node_idx != node {
//             visitor.push(furthest_away_node_idx);
//         }
//         while let Some(curr) = visitor.pop() {
//             longest_path.push(curr);
//             self.orig_graph[curr].visible = true;
//             let curr_distance = subtree_rooted_at_node.node_weight(curr).unwrap().max_depth;
//             let pred = subtree_rooted_at_node
//                 .neighbors_directed(curr, Incoming)
//                 .filter(|pred| {
//                     let pred_distance =
//                         subtree_rooted_at_node.node_weight(*pred).unwrap().max_depth;
//                     pred_distance == curr_distance - 1
//                 })
//                 .next();
//             if let Some(node) = pred {
//                 visitor.push(node);
//             }
//         }
//         // backtrack a longest path from node until we reach a root with respect to the original graph
//         visitor.push(node);
//         while let Some(curr) = visitor.pop() {
//             longest_path.push(curr);
//             self.orig_graph[curr].visible = true;
//             let curr_distance = self.orig_graph.node_weight(curr).unwrap().max_depth;
//             let pred = self
//                 .orig_graph
//                 .neighbors_directed(curr, Incoming)
//                 .filter(|pred| {
//                     let pred_distance = self.orig_graph.node_weight(*pred).unwrap().max_depth;
//                     pred_distance == curr_distance - 1
//                 })
//                 .next();
//             if let Some(node) = pred {
//                 visitor.push(node);
//             }
//         }
//         longest_path
//             .iter()
//             .cloned()
//             .rev()
//             .collect::<Vec<NodeIndex>>()
//     }

//     // fn backtrack<T>(&mut self, graph: Option<T>, node: NodeIndex) where
//     // T: NodeIndexable<EdgeId = EdgeIndex, NodeId = NodeIndex> + DataMap<NodeWeight = NodeData> + IntoNeighborsDirected {
//     //     let mut visitor: Vec<NodeIndex> = Vec::new();
//     //     visitor.push(node);
//     //     while let Some(curr) = visitor.pop() {
//     //         self.orig_graph[curr].visible = true;
//     //         let curr_distance = graph.unwrap_or(self.orig_graph).node_weight(curr).unwrap().max_depth;
//     //         // log!(format!("Node {} has distance {} from {}", curr.index(), curr_distance, ))
//     //         let pred = graph
//     //             .unwrap_or_default(self.orig_graph)
//     //             .neighbors_directed(curr, Incoming)
//     //             .filter(|pred| {
//     //                 let pred_distance = graph.unwrap_or(self.orig_graph).node_weight(*pred).unwrap().max_depth;
//     //                 pred_distance == curr_distance - 1
//     //             })
//     //             .last();
//     //         if let Some(node) = pred {
//     //             visitor.push(node);
//     //         }
//     //     }
//     // }

//     pub fn search_matching_loops(&mut self) -> usize {
//         let quants: FxHashSet<_> = self
//             .orig_graph
//             .node_weights()
//             .flat_map(|node| node.mkind.quant_idx())
//             .collect();
//         let mut matching_loop_nodes_per_quant: Vec<FxHashSet<NodeIndex>> = Vec::new();
//         log!(format!("Start processing quants"));
//         for quant in quants {
//             log!(format!("Processing quant {}", quant));
//             self.reset_visibility_to(true);
//             self.retain_nodes(|node| {
//                 node.mkind
//                     .quant_idx()
//                     .map(|q| q == quant)
//                     .unwrap_or_default()
//             });
//             self.retain_visible_nodes_and_reconnect();
//             let matching_loops = Self::find_longest_paths(&mut self.visible_graph);
//             matching_loop_nodes_per_quant.push(matching_loops);
//         }
//         log!(format!("Done processing quants"));
//         self.reset_visibility_to(false);
//         for matching_loop in matching_loop_nodes_per_quant {
//             for node in matching_loop {
//                 self.orig_graph[node].visible = true;
//             }
//         }
//         self.retain_visible_nodes_and_reconnect();
//         self.matching_loop_subgraph = self.visible_graph.clone();
//         // for displaying the nth longest matching loop later on, we want to compute the end nodes of all the matching loops
//         // and sort them by max-depth in descending order
//         Self::compute_longest_distances_from_roots(&mut self.matching_loop_subgraph);
//         // compute end-nodes of matching loops 
//         self.matching_loop_end_nodes = self.matching_loop_subgraph 
//             .node_indices()
//             // only keep end-points of matching loops, i.e., nodes without any children in the matching loop subgraph
//             .filter(|nx| self.matching_loop_subgraph.neighbors_directed(*nx, Outgoing).count() == 0)
//             .collect();
//         // sort the matching loop end-nodes by the max-depth
//         self.matching_loop_end_nodes.sort_unstable_by(|node_a, node_b| {
//             let max_depth_node_a = self.matching_loop_subgraph.node_weight(*node_a).unwrap().max_depth;
//             let max_depth_node_b = self.matching_loop_subgraph.node_weight(*node_b).unwrap().max_depth;
//             if max_depth_node_a < max_depth_node_b {
//                 std::cmp::Ordering::Greater
//             } else {
//                 std::cmp::Ordering::Less
//             }
//         });
//         // return the total number of potential matching loops
//         let nr_matching_loop_end_nodes = self.matching_loop_end_nodes.len();
//         self.generalized_terms.resize(nr_matching_loop_end_nodes, None);
//         nr_matching_loop_end_nodes
//     }

//     pub fn show_nth_matching_loop(&mut self, n: usize, p: &mut Z3Parser) -> Vec<String> {
//         self.reset_visibility_to(false);
//         // relies on the fact that we have previously sorted self.matching_loop_end_nodes by max_depth in descending order in 
//         // search_matching_loops
//         let end_node_of_nth_matching_loop = self.matching_loop_end_nodes.get(n);
//         if let Some(&node) = end_node_of_nth_matching_loop {
//             // start a reverse-DFS from node and mark all the nodes as visible along the way
//             // during the reverse-DFS collect information needed to compute the generalized terms later on
//             // we abstract the edges over the from- and to-quantifiers as well as the trigger, i.e.,
//             // two edges (a,b) and (c,d) are the same abstract edge iff 
//             // - a and c correspond to an instantiation of the same quantifier
//             // - and b and d correspond to an instantiation of the same quantifier 
//             // - and b and d used the same trigger
//             let mut abstract_edge_blame_terms: FxHashMap<(QuantIdx, QuantIdx, TermIdx), Vec<TermIdx>> = FxHashMap::default(); 
//             let mut dfs = Dfs::new(petgraph::visit::Reversed(&self.matching_loop_subgraph), node);
//             while let Some(nx) = dfs.next(petgraph::visit::Reversed(&self.matching_loop_subgraph)) {
//                 let orig_index = self.matching_loop_subgraph.node_weight(nx).unwrap().orig_graph_idx;
//                 self.orig_graph[orig_index].visible = true;
//                 // add all direct dependencies which have BlameKind::Term to the correct bin in abstract_edges
//                 // such that later on we can generalize over each all edges in a matching loop that have 
//                 // identical from- and to-quantifiers
//                 // (*)
//                 // avoid unnecessary recomputation if we have already computed the generalized terms 
//                 if let None = &self.generalized_terms[n] {
//                     log!(format!("Computation I for matching loop #{}", n));
//                     if let Some(to_quant) = self.matching_loop_subgraph.node_weight(nx).unwrap().mkind.quant_idx() {
//                         for incoming_edge in self.matching_loop_subgraph.edges_directed(nx, Incoming) {
//                             let from = incoming_edge.source(); 
//                             if let Some(from_quant) = self.matching_loop_subgraph.node_weight(from).unwrap().mkind.quant_idx() {
//                                 if let Some(blame_term) = incoming_edge.weight().blame_term_idx() {
//                                     let blame_term_idx = p[blame_term].owner; 
//                                     if let Some(trigger) = self.matching_loop_subgraph.node_weight(nx).unwrap().mkind.pattern() {
//                                         if let Some(blame_terms) = abstract_edge_blame_terms.get_mut(&(from_quant, to_quant, trigger)) {
//                                             blame_terms.push(blame_term_idx);
//                                         } else {
//                                             abstract_edge_blame_terms.insert((from_quant, to_quant, trigger), vec![blame_term_idx]);
//                                         }
//                                     }
//                                 }
//                             }
//                         }
//                     }
//                 }
//             }
//             if let Some(generalized_terms) = &self.generalized_terms[n] {
//                 // check if we have already computed the generalized terms for the n-th matching loop
//                 generalized_terms.clone()
//             } else {
//                 log!(format!("Computation II for matching loop #{}", n));
//                 // if not, compute the generalized terms for each bucket in abstract_edge_blame_terms
//                 let mut generalized_terms: Vec<String> = Vec::new();
//                 for blame_terms in abstract_edge_blame_terms.values() {
//                     // let generalized_term = blame_terms.iter().reduce(|&t1, &t2| generalize(t1, t2, p)).unwrap();
//                     if let Some(t1) = blame_terms.get(0) {
//                         let mut gen_term = *t1;
//                         for &t2 in &blame_terms[1..] {
//                             gen_term = p.terms.generalize(gen_term, t2);
//                             // let ctxt = DisplayCtxt {
//                             //     parser: p,
//                             //     display_term_ids: false,
//                             //     display_quantifier_name: false,
//                             //     use_mathematical_symbols: true,
//                             // };
//                             // log!(format!("Generalized term {} and {}", gen_term.with(&ctxt), t2.with(&ctxt)));
//                         }
//                         let ctxt = DisplayCtxt {
//                             parser: p,
//                             display_term_ids: false,
//                             display_quantifier_name: false,
//                             use_mathematical_symbols: true,
//                             s_expr_mode: false,
//                             symbols: None,
//                         };
//                         let pretty_gen_term = gen_term.with(&ctxt).to_string();
//                         generalized_terms.push(pretty_gen_term);
//                     }
//                 }
//                 self.generalized_terms[n] = Some(generalized_terms.clone());
//                 generalized_terms
//             }
//             // after generalizing over the terms for each abstract edge, store the key-value pair (n, MatchingLoopInfo) in the 
//             // InstGraph such that we don't need to recompute the generalization => can check if the value is already in the map at (*)
//         } else {
//             Vec::new() 
//         }
//     }

//     pub fn show_matching_loop_subgraph(&mut self) {
//         self.reset_visibility_to(false);
//         for node in self.matching_loop_subgraph.node_weights() {
//             self.orig_graph[node.orig_graph_idx].visible = true;
//         }
//     }

//     fn compute_longest_distances_from_roots(graph: &mut Graph<NodeData, EdgeType>) {
//         let mut topo = Topo::new(&*graph);
//         while let Some(nx) = topo.next(&*graph) {
//             let parents = graph.neighbors_directed(nx, Incoming);
//             let max_parent_depth = parents
//                 .map(|nx| graph.node_weight(nx).unwrap().max_depth)
//                 .max();
//             if let Some(depth) = max_parent_depth {
//                 graph[nx].max_depth = depth + 1;
//             } else {
//                 graph[nx].max_depth = 0;
//             }
//         }
//     }

//     fn find_longest_paths(graph: &mut Graph<NodeData, EdgeType>) -> FxHashSet<NodeIndex> {
//         // traverse this subtree in topological order to compute longest distances from root nodes
//         Self::compute_longest_distances_from_roots(graph);
//         let furthest_away_end_nodes = graph
//             .node_indices()
//             // only want to keep end nodes of longest paths, i.e., nodes without any children 
//             .filter(|nx| graph.neighbors_directed(*nx, Outgoing).count() == 0)
//             // only want to show matching loops of length at least 3, hence only keep nodes with depth at least 2
//             .filter(|nx| graph.node_weight(*nx).unwrap().max_depth >= MIN_MATCHING_LOOP_LENGTH - 1) 
//             .collect();
//         // backtrack longest paths from furthest away nodes in subgraph until we reach a root
//         let mut matching_loop_nodes: FxHashSet<NodeIndex> = FxHashSet::default();
//         let mut visitor: Vec<NodeIndex> = furthest_away_end_nodes;
//         let mut visited: FxHashSet<_> = FxHashSet::default();
//         while let Some(curr) = visitor.pop() {
//             matching_loop_nodes.insert(graph.node_weight(curr).unwrap().orig_graph_idx);
//             let curr_distance = graph.node_weight(curr).unwrap().max_depth;
//             let preds = graph.neighbors_directed(curr, Incoming).filter(|pred| {
//                 let pred_distance = graph.node_weight(*pred).unwrap().max_depth;
//                 pred_distance == curr_distance - 1
//             });
//             for pred in preds {
//                 if visited.insert(pred) {
//                     visitor.push(pred);
//                 }
//             }
//         }
//         matching_loop_nodes
//     }

//     pub fn reset_visibility_to(&mut self, visibility: bool) {
//         for node in self.orig_graph.node_weights_mut() {
//             node.visible = visibility;
//         }
//     }

//     pub fn show_neighbours(&mut self, node: NodeIndex, direction: petgraph::Direction) {
//         let neighbour_indices: Vec<NodeIndex> = self
//             .orig_graph
//             .neighbors_directed(node, direction)
//             .collect();
//         for neighbour in neighbour_indices {
//             self.orig_graph.node_weight_mut(neighbour).unwrap().visible = true;
//         }
//     }

//     pub fn node_has_filtered_children(&self, node_idx: NodeIndex) -> bool {
//         self.node_has_filtered_direct_neighbours(node_idx, Outgoing)
//     }

//     pub fn node_has_filtered_parents(&self, node_idx: NodeIndex) -> bool {
//         self.node_has_filtered_direct_neighbours(node_idx, Incoming)
//     }

//     fn node_has_filtered_direct_neighbours(
//         &self,
//         node_idx: NodeIndex,
//         direction: Direction,
//     ) -> bool {
//         let neighbours =
//             self.orig_graph
//                 .edges_directed(node_idx, direction)
//                 .map(|e| match direction {
//                     Outgoing => e.target(),
//                     Incoming => e.source(),
//                 });
//         let (visible_neighbours, hidden_neighbours): (Vec<NodeIndex>, Vec<NodeIndex>) =
//             neighbours.partition(|n| self.orig_graph.node_weight(*n).unwrap().visible);
//         let nr_visible_neighbours = visible_neighbours.len();
//         let nr_hidden_neighbours = hidden_neighbours.len();
//         nr_visible_neighbours < nr_hidden_neighbours + nr_visible_neighbours
//     }

//     fn compute_instantiation_graph(&mut self, parser: &Z3Parser) {
//         for (inst_idx, inst) in parser.insts.insts.iter_enumerated() {
//             let match_ = &parser.insts[inst.match_];
//             // add new node to graph
//             self.add_node(NodeData {
//                 is_theory_inst: match_.kind.is_discovered(),
//                 cost: inst.cost,
//                 inst_idx,
//                 mkind: match_.kind.clone(),
//                 visible: true,
//                 child_count: 0,
//                 parent_count: 0,
//                 orig_graph_idx: NodeIndex::default(),
//                 cost_rank: 0,
//                 branching_rank: 0,
//                 min_depth: None,
//                 max_depth: 0,
//                 topo_ord: 0,
//             });
//             // then add all edges to previous nodes
//             for (kind, from) in match_
//                 .due_to_enodes()
//                 .filter_map(|(kind, e)| parser[e].created_by.map(|c| (kind, c)))
//             {
//                 self.add_edge(from, inst_idx, kind);
//             }
//         }
//         // precompute number of children and parents of each node
//         for idx in self.orig_graph.node_indices() {
//             let child_count = self.orig_graph.neighbors_directed(idx, Outgoing).count();
//             let parent_count = self.orig_graph.neighbors_directed(idx, Incoming).count();
//             self.orig_graph.node_weight_mut(idx).unwrap().child_count = child_count;
//             self.orig_graph.node_weight_mut(idx).unwrap().parent_count = parent_count;
//         }
//         // precompute the cost-rank of all nodes by sorting the node_indices by our cost-order
//         // in descending order and then assigning the rank to each node
//         // Our cost-order is defined as follows:
//         // inst_b > inst_a iff (cost_b > cost_a or (cost_b = cost_a and line_nr_b < line_nr_a))
//         // This is a total order since the line numbers are always guaranteed to be distinct
//         // integers.
//         let mut cost_ranked_node_indices: Vec<NodeIndex> = self.orig_graph.node_indices().collect();
//         let cost_order = |node_a: &NodeIndex, node_b: &NodeIndex| {
//             let node_a_data = self.orig_graph.node_weight(*node_a).unwrap();
//             let node_b_data = self.orig_graph.node_weight(*node_b).unwrap();
//             if node_a_data.cost < node_b_data.cost || (node_a_data.cost == node_b_data.cost
//                 && node_b_data.inst_idx < node_a_data.inst_idx) {
//                 std::cmp::Ordering::Greater
//             } else {
//                 std::cmp::Ordering::Less
//             }
//         };
//         cost_ranked_node_indices.sort_unstable_by(cost_order);
//         for (i, nidx) in cost_ranked_node_indices.iter().enumerate() {
//             self.orig_graph.node_weight_mut(*nidx).unwrap().cost_rank = i;
//         }
//         self.cost_ranked_node_indices = cost_ranked_node_indices;
//         // precompute BFS depth such that we can filter the graph up to some specified depth
//         let roots: Vec<NodeIndex> = self
//             .orig_graph
//             .node_indices()
//             .filter(|nx| self.orig_graph.node_weight(*nx).unwrap().parent_count == 0)
//             .collect();
//         for root in roots {
//             let mut bfs = Bfs::new(&self.orig_graph, root);
//             while let Some(nx) = bfs.next(&self.orig_graph) {
//                 let parents = self.orig_graph.neighbors_directed(nx, Incoming);
//                 let min_parent_depth = parents
//                     .filter_map(|parent| self.orig_graph.node_weight(parent).unwrap().min_depth)
//                     .min();
//                 if let Some(depth) = min_parent_depth {
//                     self.orig_graph[nx].min_depth = Some(depth + 1);
//                 } else {
//                     // the min_depth is None iff the node at nx has no parents, hence we set the depth to 0
//                     self.orig_graph[nx].min_depth = Some(0);
//                 }
//             }
//         }
//         // precompute the branching-rank of all nodes by sorting the node_indices by our branching-order
//         // in descending order and then assigning the rank to each node
//         // Our branching-order is defined as follows:
//         // inst_b > inst_a iff (child_count(b) > child_count(a) or (child_count(b) = child_count(a) and line_nr_b < line_nr_a))
//         // This is a total order since the line numbers are always guaranteed to be distinct
//         // integers.
//         let mut branching_ranked_node_indices: Vec<NodeIndex> =
//             self.orig_graph.node_indices().collect();
//         let branching_order = |node_a: &NodeIndex, node_b: &NodeIndex| {
//             let node_a_data = self.orig_graph.node_weight(*node_a).unwrap();
//             let node_b_data = self.orig_graph.node_weight(*node_b).unwrap();
//             if node_a_data.child_count < node_b_data.child_count || (node_a_data.child_count == node_b_data.child_count
//                 && node_b_data.inst_idx < node_a_data.inst_idx) {
//                 std::cmp::Ordering::Greater
//             } else {
//                 std::cmp::Ordering::Less
//             }
//         };
//         branching_ranked_node_indices.sort_unstable_by(branching_order);
//         for (i, nidx) in branching_ranked_node_indices.iter().enumerate() {
//             self.orig_graph
//                 .node_weight_mut(*nidx)
//                 .unwrap()
//                 .branching_rank = i;
//         }
//         self.branching_ranked_node_indices = branching_ranked_node_indices;
//         // compute the longest distances from root nodes by traversing the graph in topological order
//         // and taking max distance among parents + 1. Needed to compute longest paths through selected
//         // nodes
//         // root nodes (i.e., nodes without parents) have distance 0
//         let mut topo = Topo::new(&self.orig_graph);
//         while let Some(node) = topo.next(&self.orig_graph) {
//             let max_parent_depth = self
//                 .orig_graph
//                 .neighbors_directed(node, Incoming)
//                 .map(|nx| self.orig_graph.node_weight(nx).unwrap().max_depth)
//                 .max();
//             if let Some(depth) = max_parent_depth {
//                 let node_weight = self.orig_graph.node_weight_mut(node).unwrap();
//                 node_weight.max_depth = depth + 1;
//             }
//         }
//         // efficiently compute transitive closure with a vector of FixedBitSet's
//         let mut topo = Topo::new(petgraph::visit::Reversed(&self.orig_graph));
//         // assign topological orders to each node
//         let mut topo_ord = self.orig_graph.node_count() - 1;
//         while let Some(nx) = topo.next(petgraph::visit::Reversed(&self.orig_graph)) {
//             self.orig_graph[nx].topo_ord = topo_ord;
//             topo_ord = topo_ord.saturating_sub(1);
//         }
//         self.tr_closure = vec![RoaringBitmap::new(); self.orig_graph.node_count()];
//         // note that we are storing the bitsets's of each node index in topological order!
//         let mut topo = Topo::new(petgraph::visit::Reversed(&self.orig_graph));
//         let mut bitsets = self.tr_closure.as_mut_slice();
//         let mut ord = self.orig_graph.node_count() - 1;
//         while let Some((last, others)) = bitsets.split_last_mut() {
//             if let Some(nx) = topo.next(petgraph::visit::Reversed(&self.orig_graph)) {
//                 last.insert(nx.index() as u32);
//                 for pred in self.orig_graph.neighbors_directed(nx, Incoming) {
//                     let pred_topo_ord = self.orig_graph.node_weight(pred).unwrap().topo_ord;
//                     let pred_bitset = others.get_mut(pred_topo_ord).unwrap();
//                     *pred_bitset |= &*last;
//                 }
//             }
//             bitsets = others;
//             ord = ord.saturating_sub(1);
//         }
//         log!("Finished computing transitive closure");
//         self.visible_graph = self.orig_graph.map(
//             |_, n| n.clone(),
//             |orig_graph_idx, e| EdgeType::Direct {
//                 kind: e.clone(),
//                 orig_graph_idx,
//             },
//         )
//     }

//     fn add_node(&mut self, node_data: NodeData) {
//         let inst_idx = node_data.inst_idx;
//         let node = self.orig_graph.add_node(node_data);
//         let ins_idx = self.node_of_inst_idx.push_and_get_key(node);
//         assert_eq!(ins_idx, inst_idx);
//         // store original node-index in each node
//         // self.inst_graph.node_weight_mut(node).unwrap().orig_graph_idx = node;
//         // store original node-idx such that when we compute reachability, we
//         // can use the old indices.
//         // this is necessary since filtering out nodes will changes node-indices
//         // Also, using StableGraph where node-indices stay stable across removals
//         // is not viable here since StableGraph does not implement NodeCompactIndexable
//         // which is needed for petgraph::algo::tred::dag_to_toposorted_adjacency_list
//         self.orig_graph[node].orig_graph_idx = node;
//     }

//     fn add_edge(&mut self, from: InstIdx, to: InstIdx, blame: &BlameKind) {
//         let (from, to) = (self.node_of_inst_idx[from], self.node_of_inst_idx[to]);
//         self.orig_graph.add_edge(from, to, blame.clone());
//     }

//     pub fn get_node_info_map(&self) -> NodeInfoMap {
//         let mut node_info_map = FxHashMap::default();
//         for node_index in self.orig_graph.node_indices() {
//             let NodeData { inst_idx, .. } = self.orig_graph[node_index];
//             node_info_map.insert(node_index, inst_idx);
//         }
//         NodeInfoMap::from(node_info_map)
//     }

//     pub fn get_edge_info_map(&self) -> EdgeInfoMap {
//         let mut edge_info_map = FxHashMap::default(); 
//         for edge_index in self.orig_graph.edge_indices() {
//             let edge_data = &self.orig_graph[edge_index];
//             let (from, to) = self.orig_graph.edge_endpoints(edge_index).unwrap();
//             edge_info_map.insert(edge_index, (edge_data.clone(), (from, to)));
//         }
//         EdgeInfoMap::from(edge_info_map)
//     }
// }

// pub struct NodeInfoMap(FxHashMap<NodeIndex, InstIdx>); 

// impl NodeInfoMap {

//     fn from(map: FxHashMap<NodeIndex, InstIdx>) -> Self {
//         NodeInfoMap(map) 
//     }

//     pub fn get_instantiation_info(
//         &self,
//         node_index: usize,
//         parser: &Z3Parser,
//         ignore_ids: bool,
//     ) -> InstInfo {
//         let inst_idx = self.0.get(&NodeIndex::new(node_index)).unwrap();
//         let ctxt = DisplayCtxt {
//             parser,

//             display_term_ids: !ignore_ids,
//             display_quantifier_name: false,
//             use_mathematical_symbols: true,

//             s_expr_mode: false,
//             symbols: None,
//         };

//         let inst = &parser.insts[*inst_idx];
//         let match_ = &parser.insts[inst.match_];
//         let pretty_blamed_terms = match_
//             .due_to_terms()
//             .map(|eidx| eidx.with(&ctxt).to_string())
//             .collect::<Vec<String>>();
//         let inst_info = InstInfo {
//             fingerprint: inst.fingerprint,
//             inst_idx: *inst_idx,
//             resulting_term: inst
//                 .get_resulting_term()
//                 .map(|rt| rt.with(&ctxt).to_string()),
//             z3_gen: inst.z3_generation,
//             cost: inst.cost,
//             mkind: match_.kind.clone(),
//             quant_discovered: match_.kind.is_discovered(),
//             formula: match_.kind.with(&ctxt).to_string(),
//             pattern: match_.kind.pattern().map(|p| p.with(&ctxt).to_string()),
//             yields_terms: inst
//                 .yields_terms
//                 .iter()
//                 .map(|&tidx| format!("{}", tidx.with(&ctxt)))
//                 .collect(),
//             bound_terms: match_
//                 .kind
//                 .bound_terms(|e| e.with(&ctxt).to_string(), |t| t.with(&ctxt).to_string()),
//             blamed_terms: pretty_blamed_terms,
//             equality_expls: match_
//                 .due_to_equalities()
//                 .map(|eq| eq.with(&ctxt).to_string())
//                 .collect(),
//             dep_instantiations: Vec::new(),
//             node_index: NodeIndex::new(node_index),
//         };
//         inst_info
//     }
// }

// pub struct EdgeInfoMap(FxHashMap<EdgeIndex, (BlameKind, (NodeIndex, NodeIndex))>); 

// impl EdgeInfoMap {

//     fn from(map: FxHashMap<EdgeIndex, (BlameKind, (NodeIndex, NodeIndex))>) -> Self {
//         EdgeInfoMap(map)
//     }

//     pub fn get_edge_info(
//         &self,
//         edge_index: EdgeIndex,
//         parser: &Z3Parser,
//         ignore_ids: bool,
//     ) -> EdgeInfo {
//         let (edge_data, (from, to)) = self.0.get(&edge_index).unwrap();
//         let ctxt = DisplayCtxt {
//             parser,

//             display_term_ids: !ignore_ids,
//             display_quantifier_name: false,
//             use_mathematical_symbols: true,
//             s_expr_mode: false,
//             symbols: None,
//         };
//         let blame_term_idx = edge_data.get_blame_node().unwrap();
//         let blame_term = blame_term_idx.with(&ctxt).to_string();
//         EdgeInfo {
//             edge_data: edge_data.clone(),
//             orig_graph_idx: edge_index,
//             blame_term,
//             from: *from,
//             to: *to,
//         }
//     }
// }