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
    let mut dd_buckets = DeltaDegreeBuckets {
        nodes: Vec::new(),
        sinks: Default::default(),
        sources: Default::default(),
        buckets: HashMap::new(), // TODO: replace with another linked list?
        graph_ix_lookup: HashMap::new(),
    };

    let fas_node_entry = |g_ix: NodeIndex<SeqGraphIx>| -> FasNodeIndex {
        match dd_buckets.graph_ix_lookup.get(&g_ix) {
            Some(fas_ix) => *fas_ix,
            None => {
                let fas_ix = FasNodeIndex(dd_buckets.nodes.len());

                dd_buckets.nodes.push(FasNode {
                    graph_ix: g_ix,
                    out_edges: Vec::new(),
                    in_edges: Vec::new(),
                    out_degree: 0,
                    in_degree: 0,
                    ll_entry: None,
                });

                dd_buckets.graph_ix_lookup.insert(g_ix, fas_ix);

                fas_ix
            }
        }
    };

    let push_to_bucket = |fas_ix: FasNodeIndex| {
        let node = &mut dd_buckets.nodes[fas_ix.0];

        let list = if node.out_degree == 0 {
            &mut dd_buckets.sinks
        } else if node.in_degree == 0 {
            &mut dd_buckets.sources
        } else {
            let delta_degree = node.out_degree as isize - node.in_degree as isize;
            dd_buckets
                .buckets
                .entry(delta_degree)
                .or_insert(Default::default())
        };

        list.push_front(fas_ix, &mut dd_buckets.nodes);
    };

    // Build node entries
    for (from_g_ix, to_g_ix) in edge_refs {
        let from_fas_ix = fas_node_entry(from_g_ix);
        let to_fas_ix = fas_node_entry(to_g_ix);

        dd_buckets.nodes[from_fas_ix.0].out_edges.push(to_fas_ix);
        dd_buckets.nodes[to_fas_ix.0].out_edges.push(from_fas_ix);
    }

    // Set initial in/out-degrees
    for node in dd_buckets.nodes {
        node.out_degree = node.out_edges.len();
        node.in_degree = node.in_edges.len();
    }

    // Add nodes to initial lists
    for (i, node) in dd_buckets.nodes.iter_mut().enumerate() {
        let fas_ix = FasNodeIndex(i);
        push_to_bucket(fas_ix);
    }

    let mut s_1 = VecDeque::new();
    let mut s_2 = VecDeque::new();

    let update_connected_node_buckets = |node: &FasNode| {
        for out_ix in node.out_edges {
            let out_node = &mut dd_buckets.nodes[out_ix.0];
            out_node.in_degree -= 1;

            // Ignore nodes which have already been moved to the good sequence
            if out_node.ll_entry.is_some() {
                push_to_bucket(out_ix);
            }
        }

        for in_ix in node.in_edges {
            let in_node = &mut dd_buckets.nodes[in_ix.0];
            in_node.in_degree += 1;

            // Ignore nodes which have already been moved to the good sequence
            if in_node.ll_entry.is_some() {
                push_to_bucket(in_ix);
            }
        }
    };

    loop {
        let mut some_moved = false;

        while let Some(sink_fas_ix) = dd_buckets.sinks.pop(&mut dd_buckets.nodes) {
            some_moved = true;
            let sink_node = &dd_buckets.nodes[sink_fas_ix.0];
            update_connected_node_buckets(sink_node);
            s_2.push_front(sink_node.graph_ix);
        }

        while let Some(source_fas_ix) = dd_buckets.sources.pop(&mut dd_buckets.nodes) {
            some_moved = true;
            let source_node = &dd_buckets.nodes[source_fas_ix.0];
            update_connected_node_buckets(source_node);
            s_1.push_back(source_node.graph_ix);
        }

        if let Some(bucket) = dd_buckets
            .buckets
            .iter_mut()
            .max_by_key(|(bucket, _head)| bucket)
            .map(|(_bucket, head)| head)
        {
            if let Some(highest_dd_fas_ix) = bucket.pop(&mut dd_buckets.nodes) {
                some_moved = true;
                let highest_dd_node = &dd_buckets.nodes[highest_dd_fas_ix.0];
                update_connected_node_buckets(highest_dd_node);
                s_1.push_back(highest_dd_node.graph_ix);
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
// TODO: can probably split out this struct's fields in function variables & remove this def
struct DeltaDegreeBuckets {
    /// Backing storage for delta degree lists
    nodes: Vec<FasNode>,

    sinks: LinkedListHead,
    sources: LinkedListHead,

    /// Linked lists for unprocessed graph nodes-so-far, grouped by their current delta degree
    buckets: HashMap<isize, LinkedListHead>,

    graph_ix_lookup: HashMap<NodeIndex<SeqGraphIx>, FasNodeIndex>,
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
