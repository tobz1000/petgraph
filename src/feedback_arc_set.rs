use std::collections::{HashMap, VecDeque};

use crate::{
    graph::{GraphIndex, NodeIndex},
    stable_graph::StableDiGraph,
    visit::{EdgeRef, GraphProp, IntoEdgeReferences},
    Directed, Direction,
};

/// Isomorphic to input graph; used in the process of determining a good node sequence from which to
/// extract a feedback arc set.
type SeqSourceGraph = StableDiGraph<(), (), SeqGraphIx>;
type SeqGraphIx = usize;

/// \[Generic\] Finds a [feedback arc set]: a set of edges in the given directed graph, which when
/// removed, make the graph acyclic.
///
/// Uses a [greedy heuristic algorithm] to select a small number of edges, but does not necessarily
/// find the minimum feedback arc set. Time complexity is **O(|V|² + |E|)**, for an input graph with
/// nodes **V** and edges **E**.
///
/// Does not consider edge/node weights when selecting edges for the feedback arc set.
///
/// Loops (edges to and from the same node) are always included in the returned set.
///
/// # Example
///
/// ```
/// use petgraph::{
///     algo::{greedy_feedback_arc_set, is_cyclic_directed},
///     graph::EdgeIndex,
///     stable_graph::StableGraph,
///     visit::EdgeRef,
/// };
///
/// let mut g: StableGraph<(), ()> = StableGraph::from_edges(&[
///     (0, 1),
///     (1, 2),
///     (2, 3),
///     (3, 4),
///     (4, 5),
///     (5, 0),
///     (4, 1),
///     (1, 3),
/// ]);
///
/// assert!(is_cyclic_directed(&g));
///
/// let fas: Vec<EdgeIndex> = greedy_feedback_arc_set(&g).map(|e| e.id()).collect();
///
/// // Remove edges in feedback arc set from original graph
/// for edge_id in fas {
///     g.remove_edge(edge_id);
/// }
///
/// assert!(!is_cyclic_directed(&g));
/// ```
///
/// [feedback arc set]: https://en.wikipedia.org/wiki/Feedback_arc_set
/// [greedy heuristic algorithm]: https://doi.org/10.1016/0020-0190(93)90079-O
pub fn greedy_feedback_arc_set<G>(g: G) -> impl Iterator<Item = G::EdgeRef>
where
    G: IntoEdgeReferences + GraphProp<EdgeType = Directed>,
    G::NodeId: GraphIndex,
{
    // TODO: remove intermediate stable graph if we don't have to remove from it

    // TODO: see if we can support 32-bit graphs now
    let node_seq = good_node_sequence(g.edge_references().map(|e| {
        (
            NodeIndex::new(e.source().index()),
            NodeIndex::new(e.target().index()),
        )
    }));

    g.edge_references()
        .filter(move |e| node_seq[&e.source().index()] >= node_seq[&e.target().index()])
}

fn good_node_sequence(
    edge_refs: impl Iterator<Item = (NodeIndex<SeqGraphIx>, NodeIndex<SeqGraphIx>)>,
) -> HashMap<SeqGraphIx, usize> {
    let mut nodes = Vec::new(); // Backing storage for nodes
    let mut buckets = Buckets {
        sinks_or_isolated: LinkedListHead::default(),
        sources: LinkedListHead::default(),
        bidirectional: HashMap::new(),
    };
    // Lookup of node indices from input graph to indices into `nodes`
    let mut graph_ix_lookup = HashMap::new();

    // Build node entries
    for (from_g_ix, to_g_ix) in edge_refs {
        let mut fas_node_entry = |g_ix: NodeIndex<SeqGraphIx>| -> FasNodeIndex {
            match graph_ix_lookup.get(&g_ix) {
                Some(fas_ix) => *fas_ix,
                None => {
                    let fas_ix = FasNodeIndex(nodes.len());

                    nodes.push(FasNode {
                        graph_ix: g_ix,
                        out_edges: Vec::new(),
                        in_edges: Vec::new(),
                        out_degree: 0,
                        in_degree: 0,
                        ll_entry: None,
                    });

                    graph_ix_lookup.insert(g_ix, fas_ix);

                    fas_ix
                }
            }
        };

        let from_fas_ix = fas_node_entry(from_g_ix);
        let to_fas_ix = fas_node_entry(to_g_ix);

        nodes[from_fas_ix.0].out_edges.push(to_fas_ix);
        nodes[to_fas_ix.0].out_edges.push(from_fas_ix);
    }

    // Set initial in/out-degrees
    for node in nodes.iter_mut() {
        node.out_degree = node.out_edges.len();
        node.in_degree = node.in_edges.len();
    }

    // Add nodes to initial lists
    for i in 0..nodes.len() {
        let fas_ix = FasNodeIndex(i);
        buckets
            .get_bucket(fas_ix, &mut nodes)
            .push_front(fas_ix, &mut nodes);
    }

    let mut s_1 = VecDeque::new();
    let mut s_2 = VecDeque::new();

    loop {
        let mut some_moved = false;

        while let Some(sink_fas_ix) = buckets.sinks_or_isolated.pop(&mut nodes) {
            some_moved = true;
            buckets
                .get_bucket(sink_fas_ix, &mut nodes)
                .remove(sink_fas_ix, &mut nodes);
            buckets.update_neighbour_node_buckets(sink_fas_ix, &mut nodes);
            s_2.push_front(nodes[sink_fas_ix.0].graph_ix);
        }

        while let Some(source_fas_ix) = buckets.sources.pop(&mut nodes) {
            some_moved = true;
            buckets
                .get_bucket(source_fas_ix, &mut nodes)
                .remove(source_fas_ix, &mut nodes);
            buckets.update_neighbour_node_buckets(source_fas_ix, &mut nodes);
            s_1.push_back(nodes[source_fas_ix.0].graph_ix);
        }

        if let Some(bucket) = buckets
            .bidirectional
            .iter_mut()
            .max_by_key(|(bucket, _head)| *bucket)
            .map(|(_bucket, head)| head)
        {
            if let Some(highest_dd_fas_ix) = bucket.pop(&mut nodes) {
                some_moved = true;
                buckets
                    .get_bucket(highest_dd_fas_ix, &mut nodes)
                    .remove(highest_dd_fas_ix, &mut nodes);
                buckets.update_neighbour_node_buckets(highest_dd_fas_ix, &mut nodes);
                s_1.push_back(nodes[highest_dd_fas_ix.0].graph_ix);
            }
        }

        if !some_moved {
            break;
        }
    }

    s_1.into_iter()
        .chain(s_2)
        .enumerate()
        .map(|(seq_order, node_index)| (node_index.index(), seq_order))
        .collect()
}

#[derive(Debug)]
struct Buckets {
    sinks_or_isolated: LinkedListHead,
    sources: LinkedListHead,
    bidirectional: HashMap<isize, LinkedListHead>,
}

#[derive(Clone, Copy, PartialEq, Debug)]
struct FasNodeIndex(usize);

#[derive(PartialEq, Default, Debug)]
struct LinkedListHead {
    start: Option<FasNodeIndex>,
}

#[derive(Debug)]
struct LinkedListEntry {
    prev: Option<FasNodeIndex>,
    next: Option<FasNodeIndex>,
}

/// Represents a node from the input graph, tracking its current delta degree
#[derive(Debug)]
struct FasNode {
    /// Node index in input graph.
    graph_ix: NodeIndex<SeqGraphIx>,

    /// All outward edges from this node (not removed during processing)
    out_edges: Vec<FasNodeIndex>,

    /// All inward edges from this node (not removed during processing)
    in_edges: Vec<FasNodeIndex>,

    /// Current out-degree of this node (decremented during processing as connected nodes are
    /// removed)
    out_degree: usize,

    /// Current in-degree of this node (decremented during processing as connected nodes are
    /// removed)
    in_degree: usize,

    /// Information about current linked list location. `None` when node is removed from all
    /// buckets.
    ll_entry: Option<LinkedListEntry>,
}

impl LinkedListHead {
    fn push_front(&mut self, push_ix: FasNodeIndex, nodes: &mut [FasNode]) {
        if let Some(start_ix) = self.start {
            let start_node = &mut nodes[start_ix.0];
            start_node.ll_entry.as_mut().unwrap().prev = Some(push_ix);

            let push_node = &mut nodes[push_ix.0];
            push_node.ll_entry.as_mut().unwrap().next = Some(start_ix);
        }

        self.start = Some(push_ix);
    }

    fn pop(&mut self, nodes: &mut [FasNode]) -> Option<FasNodeIndex> {
        if let Some(start_ix) = self.start {
            let start_node = &mut nodes[start_ix.0];
            let start_ll_entry = start_node.ll_entry.take().unwrap();

            if let Some(next_ix) = start_ll_entry.next {
                let next_node = &mut nodes[next_ix.0];
                next_node.ll_entry.as_mut().unwrap().prev = None;

                self.start = Some(next_ix);
            } else {
                self.start = None;
            }

            Some(start_ix)
        } else {
            None
        }
    }

    /// `remove_ix` **must** be a member of the list headed by `self`
    fn remove(&mut self, remove_ix: FasNodeIndex, nodes: &mut [FasNode]) {
        let remove_node = &mut nodes[remove_ix.0];
        let ll_entry = remove_node.ll_entry.take().unwrap();

        if let Some(prev_ix) = ll_entry.prev {
            let prev_node = &mut nodes[prev_ix.0];
            prev_node.ll_entry.as_mut().unwrap().next = ll_entry.next;
        }

        if let Some(next_ix) = ll_entry.next {
            let next_node = &mut nodes[next_ix.0];
            next_node.ll_entry.as_mut().unwrap().prev = ll_entry.prev;
        }

        if self.start == Some(remove_ix) {
            self.start = ll_entry.next;
        }
    }
}

impl Buckets {
    /// Returns the bucket that a node should belong to, not the list it's necessarily currently in
    fn get_bucket(&mut self, ix: FasNodeIndex, nodes: &mut [FasNode]) -> &mut LinkedListHead {
        let node = &mut nodes[ix.0];

        if node.out_degree == 0 {
            &mut self.sinks_or_isolated
        } else if node.in_degree == 0 {
            &mut self.sources
        } else {
            let delta_degree = node.out_degree as isize - node.in_degree as isize;
            self.bidirectional
                .entry(delta_degree)
                .or_insert(Default::default())
        }
    }

    fn update_neighbour_node_buckets(&mut self, ix: FasNodeIndex, nodes: &mut [FasNode]) {
        for i in 0..nodes[ix.0].out_edges.len() {
            let out_ix = nodes[ix.0].out_edges[i];

            if out_ix == ix {
                continue;
            }

            // Ignore nodes which have already been moved to the good sequence
            if nodes[out_ix.0].ll_entry.is_none() {
                continue;
            }

            self.get_bucket(out_ix, nodes).remove(ix, nodes);

            // Other node has lost an in-edge; reduce in-degree by 1
            nodes[out_ix.0].in_degree -= 1;

            self.get_bucket(out_ix, nodes).push_front(ix, nodes);
        }

        for i in 0..nodes[ix.0].in_edges.len() {
            let in_ix = nodes[ix.0].in_edges[i];

            if in_ix == ix {
                continue;
            }

            // Ignore nodes which have already been moved to the good sequence
            if nodes[in_ix.0].ll_entry.is_none() {
                continue;
            }

            self.get_bucket(in_ix, nodes).remove(ix, nodes);

            // Other node has lost an out-edge; reduce out-degree by 1
            nodes[in_ix.0].out_degree -= 1;

            self.get_bucket(in_ix, nodes).push_front(ix, nodes);
        }
    }
}

#[cfg(test)]
mod test {
    use crate::{
        algo::is_cyclic_directed,
        graph::{DiGraph, EdgeIndex},
        visit::EdgeRef,
    };

    use super::greedy_feedback_arc_set;

    #[test]
    fn fas_debug() {
        let mut g = DiGraph::<(), ()>::with_capacity(0, 0);

        for _ in 0..4 {
            g.add_node(());
        }

        for i in g.node_indices() {
            for j in g.node_indices() {
                // if i >= j {
                //     continue;
                // }

                g.add_edge(i, j, ());
            }
        }

        let fas: Vec<EdgeIndex> = greedy_feedback_arc_set(&g).map(|e| e.id()).collect();

        for edge_id in fas {
            g.remove_edge(edge_id);
        }

        assert!(!is_cyclic_directed(&g));
    }
}
