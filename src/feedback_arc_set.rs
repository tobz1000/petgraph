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
    let mut dd_buckets = {
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
                        ll_entry: None,
                    });

                    dd_buckets.graph_ix_lookup.insert(g_ix, fas_ix);

                    fas_ix
                }
            }
        };

        // Build node entries
        for (from_g_ix, to_g_ix) in edge_refs {
            let from_fas_ix = fas_node_entry(from_g_ix);
            let to_fas_ix = fas_node_entry(to_g_ix);

            dd_buckets.node(from_fas_ix).out_edges.push(to_fas_ix);
            dd_buckets.node(to_fas_ix).out_edges.push(from_fas_ix);
        }

        // Add nodes to initial lists
        for (i, node) in dd_buckets.nodes.iter_mut().enumerate() {
            let fas_ix = FasNodeIndex(i);

            let list = match node.classifier() {
                NodeClassifier::SinkOrIsolated => &mut dd_buckets.sinks,
                NodeClassifier::Source => &mut dd_buckets.sources,
                NodeClassifier::Bidirectional => dd_buckets
                    .buckets
                    .entry(node.delta_degree())
                    .or_insert(Default::default()),
            };

            list.push_front(fas_ix, &mut dd_buckets.nodes);
        }

        dd_buckets
    };

    let mut s_1 = VecDeque::new();
    let mut s_2 = VecDeque::new();

    // TODO: consider how loop edges are handled here
    loop {
        while let Some(sink_ll_ix) = dd_buckets.sinks.pop(&mut dd_buckets.nodes) {
            let sink_graph_ix = remove_graph_node(sink_ll_ix, &mut graaph, &mut dd_buckets);
            s_2.push_front(sink_graph_ix);
        }

        while let Some(source_ll_ix) = dd_buckets.sources.start {
            let source_graph_ix = remove_graph_node(source_ll_ix, &mut graaph, &mut dd_buckets);
            s_1.push_back(source_graph_ix);
        }

        if let Some(highest_dd_ll_ix) = dd_buckets.highest_degree_bucket().start {
            let highest_dd_graph_ix =
                remove_graph_node(highest_dd_ll_ix, &mut graaph, &mut dd_buckets);
            s_1.push_back(highest_dd_graph_ix);
        }
    }

    s_1.into_iter()
        .chain(s_2)
        .enumerate()
        .map(|(seq_order, node_index)| (node_index.index(), seq_order))
        .collect()
}

/// Removes node from graph, and re-adjusts classification buckets. Returns the graph ID of the
/// removed node.
fn remove_graph_node(
    ll_index: FasNodeIndex,
    graaph: &mut SeqSourceGraph,
    dd_buckets: &mut DeltaDegreeBuckets,
) -> NodeIndex<SeqGraphIx> {
    dd_buckets.remove(ll_index);
    let graph_ix = dd_buckets.node(ll_index).graph_ix;

    // Adjust buckets of each connected outgoing node
    for edge in graaph.edges_directed(graph_ix, Direction::Outgoing) {
        let other_node_graph_ix = edge.target();

        if other_node_graph_ix == graph_ix {
            // Loop edge
            continue;
        }

        let other_node_ll_ix = dd_buckets.graph_ix_lookup[&other_node_graph_ix];
        let classifier = graph_node_classifier(other_node_graph_ix, graaph);
        // TODO: cannot read correct classifier from the petgraph-graph here, because the original node has not yet been removed, so the "other" node's edge list is not correct for reading
        // let classifier = match g
        //     .edges_directed(other_node_graph_ix, Direction::Incoming)
        //     .count()
        // {
        //     0 => panic!(),
        //     // The only remaining incoming edge on this node is the one to be removed; it will then
        //     // become a source
        //     1 => GraphNodeClassifier::Source,
        //     _ => GraphNodeClassifier,
        // };

        dd_buckets.remove(other_node_ll_ix);

        // Other node is losing an incoming edge; increment delta_degree
        let other_ll_node = dd_buckets.node(other_node_ll_ix);
        other_ll_node.delta_degree += 1;
        other_ll_node.classifier = classifier;
        dd_buckets.set_node_bucket(other_node_ll_ix);
    }

    // Adjust buckets of each connected incoming node
    for edge in graaph.edges_directed(graph_ix, Direction::Incoming) {
        let other_node_graph_ix = edge.source();

        if other_node_graph_ix == graph_ix {
            // Loop edge
            continue;
        }

        let other_node_ll_ix = dd_buckets.graph_ix_lookup[&other_node_graph_ix];
        let classifier = graph_node_classifier(other_node_graph_ix, graaph);

        dd_buckets.remove(other_node_ll_ix);

        // Other node is losing an outgoing edge; decrement delta_degree
        let other_ll_node = dd_buckets.node(other_node_ll_ix);
        other_ll_node.delta_degree -= 1;
        other_ll_node.classifier = classifier;
        dd_buckets.set_node_bucket(other_node_ll_ix);
    }

    assert!(graaph.remove_node(graph_ix).is_some());

    graph_ix
}

fn graph_node_classifier(n: NodeIndex<SeqGraphIx>, g: &SeqSourceGraph) -> NodeClassifier {
    // TODO: `edges_directed` is O(E); replace with an O(1) check
    if !g.edges_directed(n, Direction::Outgoing).any(|_| true) {
        NodeClassifier::SinkOrIsolated
    } else if !g.edges_directed(n, Direction::Incoming).any(|_| true) {
        NodeClassifier::Source
    } else {
        NodeClassifier::Bidirectional
    }
}

fn delta_degree(n: NodeIndex<SeqGraphIx>, g: &SeqSourceGraph) -> isize {
    g.edges_directed(n, Direction::Outgoing).count() as isize
        - g.edges_directed(n, Direction::Incoming).count() as isize
}

#[derive(Debug)]
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
    graph_ix: NodeIndex<SeqGraphIx>,
    out_edges: Vec<FasNodeIndex>,
    in_edges: Vec<FasNodeIndex>,
    ll_entry: Option<LinkedListEntry>,
}

#[derive(Clone, Copy, Debug)]
enum NodeClassifier {
    SinkOrIsolated,
    Source,
    Bidirectional,
}

impl DeltaDegreeBuckets {
    fn node(&mut self, ll_index: FasNodeIndex) -> &mut FasNode {
        &mut self.nodes[ll_index.0]
    }

    /// Gets the head of the list of the specified linked list node. The list the node belongs to is
    /// inferred by its graph state (degree, classification).
    fn head(&mut self, ll_index: FasNodeIndex) -> &mut LinkedListHead {
        let (classifier, delta_degree) = {
            let node = self.node(ll_index);
            (node.classifier, node.delta_degree)
        };

        match classifier {
            NodeClassifier::SinkOrIsolated => &mut self.sinks,
            NodeClassifier::Source => &mut self.sources,
            NodeClassifier::Bidirectional => self
                .buckets
                .entry(delta_degree)
                .or_insert(Default::default()),
        }
    }

    fn highest_degree_bucket(&mut self) -> &mut LinkedListHead {
        // TODO: replace this with O(1) operation, probably by replacing HashMap with linked list
        self.buckets.iter_mut().max_by_key(|(k, _v)| *k).unwrap().1
    }

    fn remove(&mut self, ll_index: FasNodeIndex) {
        let (is_head, prev_ix, next_ix) = {
            let ll_node = self.node(ll_index);

            debug_assert!(
                !(ll_node.is_head && ll_node.prev.is_some()),
                "Linked list head node should not have prev node set"
            );

            let is_head = ll_node.is_head;
            ll_node.is_head = false;
            let prev = ll_node.prev.take();
            let next = ll_node.next.take();

            (is_head, prev, next)
        };

        if let Some(prev_ix) = prev_ix {
            let prev_node = self.node(prev_ix);

            debug_assert!(
                prev_node.next == Some(ll_index),
                "'prev' node should have its 'next' set as this node"
            );

            prev_node.next = next_ix;
        }

        if let Some(next_ix) = next_ix {
            let next_node = self.node(next_ix);
            next_node.prev = prev_ix;

            debug_assert!(
                next_node.prev == Some(ll_index),
                "'next' node should have its 'prev' set as this node"
            );
            debug_assert!(
                !next_node.is_head,
                "'next' node should not have is_head=true"
            );

            if is_head {
                next_node.is_head = true;
            }
        }

        if is_head {
            self.head(ll_index).start = next_ix;
        }
    }

    /// Adds the node to the appropriate bucket based on its state. Should be `.remove()`d prior
    /// to this, if necessary.
    fn set_node_bucket(&mut self, ll_index: FasNodeIndex) {
        let node = self.node(ll_index);

        debug_assert!(!node.is_head);
        debug_assert!(node.prev.is_none());
        debug_assert!(node.next.is_none());

        node.is_head = true;

        let delta_degree = node.delta_degree;

        let list = match node.classifier {
            NodeClassifier::SinkOrIsolated => &mut self.sinks,
            NodeClassifier::Source => &mut self.sources,
            NodeClassifier::Bidirectional => self
                .buckets
                .entry(delta_degree)
                .or_insert(Default::default()),
        };

        if let Some(head_ix) = list.start {
            let head_node = &mut self.nodes[head_ix.0];

            debug_assert!(head_node.is_head);
            debug_assert!(head_node.prev.is_none());

            head_node.is_head = false;
            head_node.prev = Some(ll_index);

            let node = &mut self.nodes[ll_index.0];
            node.next = Some(head_ix);
        }

        list.start = Some(ll_index);
    }
}

impl FasNode {
    fn delta_degree(&self) -> isize {
        self.out_edges.len() as isize - self.in_edges.len() as isize
    }

    fn classifier(&self) -> NodeClassifier {
        if self.out_edges.len() == 0 {
            NodeClassifier::SinkOrIsolated
        } else if self.in_edges.len() == 0 {
            NodeClassifier::Source
        } else {
            NodeClassifier::Bidirectional
        }
    }
}

impl LinkedListHead {
    fn push_front(&mut self, push_ix: FasNodeIndex, nodes: &mut [FasNode]) {
        if let Some(start_ix) = self.start {
            let start_node = &mut nodes[start_ix.0];
            start_node.ll_entry.unwrap().prev = Some(push_ix);

            let push_node = &mut nodes[push_ix.0];
            push_node.ll_entry.unwrap().next = Some(start_ix);
        }

        self.start = Some(push_ix);
    }

    fn pop(&mut self, nodes: &mut [FasNode]) -> Option<FasNodeIndex> {
        if let Some(start_ix) = self.start {
            let start_node = &mut nodes[start_ix.0];
            let start_ll_entry = start_node.ll_entry.take().unwrap();

            if let Some(next_ix) = start_ll_entry.next {
                let next_node = &mut nodes[next_ix.0];
                next_node.ll_entry.unwrap().prev = None;

                self.start = Some(next_ix);
            } else {
                self.start = None;
            }

            Some(start_ix)
        } else {
            None
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
