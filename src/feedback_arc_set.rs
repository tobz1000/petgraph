use std::{
    collections::{HashMap, VecDeque},
    hash::Hash,
};

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
    let stable_clone = SeqSourceGraph::from_edges(
        g.edge_references()
            .map(|e| (e.source().index(), e.target().index())),
    );
    let node_seq = good_node_sequence(stable_clone);

    g.edge_references()
        .filter(move |e| node_seq[&e.source().index()] >= node_seq[&e.target().index()])
}

fn good_node_sequence(mut g: SeqSourceGraph) -> HashMap<SeqGraphIx, usize> {
    let mut s_1 = VecDeque::new();
    let mut s_2 = VecDeque::new();

    let mut dd_buckets = DeltaDegreeBuckets {
        buckets: HashMap::new(),
        graph_ll_lookup: HashMap::new(),
        sinks: None,
        sources: None,
        ll_nodes: Vec::new(),
    };

    for (i, graph_ix) in g.node_indices().enumerate() {
        let ll_ix = LinkedListIndex(i);
        let delta_degree = delta_degree(graph_ix, &g);

        dd_buckets.ll_nodes.push(LinkedListNode {
            delta_degree,
            graph_ix,
            is_head: false,
            prev: None,
            next: None,
        });

        dd_buckets.graph_ll_lookup.insert(graph_ix, ll_ix);

        if node_is_sink(graph_ix, &g) {
            dd_buckets.set_sink(ll_ix);
        } else if node_is_source(graph_ix, &g) {
            dd_buckets.set_source(ll_ix);
        } else {
            dd_buckets.set_dd_bucket(ll_ix, delta_degree);
        }
    }

    while g.node_count() > 0 {
        while let Some(sink_ll_ix) = dd_buckets.sinks {
            dd_buckets.remove(sink_ll_ix);
            let sink_node = dd_buckets.node(sink_ll_ix).graph_ix;

            // Adjust buckets of each connected outgoing node
            for edge in g.edges_directed(sink_node, Direction::Outgoing) {
                let other_node = edge.target();
                let other_node_ll_ix = dd_buckets.graph_ll_lookup[&other_node];

                let delta_degree = {
                    let other_ll_node = dd_buckets.node(other_node_ll_ix);
                    other_ll_node.delta_degree += 1;
                    other_ll_node.delta_degree
                };

                dd_buckets.remove(other_node_ll_ix);

                if node_is_source(other_node, &g) {
                    dd_buckets.set_source(other_node_ll_ix);
                } else {
                    dd_buckets.set_dd_bucket(other_node_ll_ix, delta_degree);
                }
            }

            // Adjust buckets of each connected incoming node
            for edge in g.edges_directed(sink_node, Direction::Incoming) {
                let other_node = edge.source();
                let other_node_ll_ix = dd_buckets.graph_ll_lookup[&other_node];

                let delta_degree = {
                    let other_ll_node = dd_buckets.node(other_node_ll_ix);
                    other_ll_node.delta_degree -= 1;
                    other_ll_node.delta_degree
                };

                dd_buckets.remove(other_node_ll_ix);

                if node_is_sink(other_node, &g) {
                    dd_buckets.set_sink(other_node_ll_ix);
                } else {
                    dd_buckets.set_dd_bucket(other_node_ll_ix, delta_degree);
                }
            }
        }
        while let Some(sink_node) = g.node_indices().find(|n| node_is_sink(*n, &g)) {
            g.remove_node(sink_node);
            s_2.push_front(sink_node);
        }

        while let Some(source_node) = g.node_indices().find(|n| node_is_source(*n, &g)) {
            g.remove_node(source_node);
            s_1.push_back(source_node);
        }

        if g.node_count() > 0 {
            let to_remove = g
                .node_indices()
                .max_by_key(|n| delta_degree(*n, &g))
                .unwrap();

            g.remove_node(to_remove);
            s_1.push_back(to_remove);
        }
    }

    s_1.into_iter()
        .chain(s_2)
        .enumerate()
        .map(|(seq_order, node_index)| (node_index.index(), seq_order))
        .collect()
}

fn node_is_sink(n: NodeIndex<SeqGraphIx>, g: &SeqSourceGraph) -> bool {
    // TODO: `edges_directed` is O(E); replace with an O(1) check
    !g.edges_directed(n, Direction::Outgoing).any(|_| true)
}

fn node_is_source(n: NodeIndex<SeqGraphIx>, g: &SeqSourceGraph) -> bool {
    !g.edges_directed(n, Direction::Incoming).any(|_| true)
}

fn delta_degree(n: NodeIndex<SeqGraphIx>, g: &SeqSourceGraph) -> isize {
    g.edges_directed(n, Direction::Outgoing).count() as isize
        - g.edges_directed(n, Direction::Incoming).count() as isize
}

struct DeltaDegreeBuckets {
    /// Linked lists for unprocessed graph nodes-so-far, grouped by their current delta degree
    buckets: HashMap<isize, Option<LinkedListIndex>>,

    graph_ll_lookup: HashMap<NodeIndex<SeqGraphIx>, LinkedListIndex>,

    sinks: Option<LinkedListIndex>,
    sources: Option<LinkedListIndex>,

    /// Backing storage for delta degree lists
    ll_nodes: Vec<LinkedListNode>,
}

#[derive(Clone, Copy, PartialEq)]
struct LinkedListIndex(usize);

struct LinkedListHead {
    start: Option<LinkedListIndex>,
}

/// Represents a node in the input graph, tracking the node's current delta degree
struct LinkedListNode {
    delta_degree: isize,
    graph_ix: NodeIndex<SeqGraphIx>,
    is_head: bool,
    prev: Option<LinkedListIndex>,
    next: Option<LinkedListIndex>,
}

impl DeltaDegreeBuckets {
    fn node(&mut self, ll_index: LinkedListIndex) -> &mut LinkedListNode {
        &mut self.ll_nodes[ll_index.0]
    }

    fn remove(&mut self, ll_index: LinkedListIndex) {
        let (delta_degree, is_head, prev_ix, next_ix) = {
            let LinkedListNode {
                delta_degree,
                is_head,
                prev,
                next,
                ..
            } = self.node(ll_index);
            (*delta_degree, *is_head, prev.take(), next.take())
        };

        debug_assert!(
            !(self.node(ll_index).is_head && prev_ix.is_some()),
            "Linked list head node should not have prev node set"
        );
        debug_assert!(
            {
                let bucket_head = self.buckets.get(&delta_degree);
                bucket_head == Some(&Some(ll_index))
            },
            "Linked list head node should be set as its bucket lookup index"
        );

        if let Some(prev_ix) = prev_ix {
            let prev_node = self.node(prev_ix);
            prev_node.next = next_ix;
        }

        if let Some(next_ix) = next_ix {
            let next_node = self.node(next_ix);
            next_node.prev = prev_ix;

            if is_head {
                next_node.is_head = true;

                // TODO: this is wrong if we're removing from source/sink lists
                self.buckets.insert(delta_degree, Some(next_ix));
            }
        }
    }

    fn set_dd_bucket(&mut self, ll_index: LinkedListIndex, bucket: isize) {
        let bucket = self.buckets.entry(bucket).or_insert(None);

        DeltaDegreeBuckets::set_as_list_head(&mut self.ll_nodes, ll_index, bucket);
    }

    fn set_source(&mut self, ll_index: LinkedListIndex) {
        DeltaDegreeBuckets::set_as_list_head(&mut self.ll_nodes, ll_index, &mut self.sources);
    }

    fn set_sink(&mut self, ll_index: LinkedListIndex) {
        DeltaDegreeBuckets::set_as_list_head(&mut self.ll_nodes, ll_index, &mut self.sinks);
    }

    fn set_as_list_head(
        nodes: &mut [LinkedListNode],
        ll_index: LinkedListIndex,
        list: &mut Option<LinkedListIndex>,
    ) {
        {
            let node = &mut nodes[ll_index.0];
            node.is_head = true;
        }

        if let Some(head_ix) = list {
            let head_node = &mut nodes[head_ix.0];
            head_node.is_head = false;
            head_node.prev = Some(ll_index);

            let node = &mut nodes[ll_index.0];
            node.next = Some(*head_ix);
        }

        *list = Some(ll_index);
    }
}

// impl ... {
//     pub fn remove(&mut self, entry: LinkedListEntry) {
//         let node = self.node_mut(entry);
//         let prev_e = node.prev.take();
//         let next_e = node.next.take();

//         if let Some(prev_e) = prev_e {
//             let prev_node = self.node_mut(prev_e);
//             prev_node.next = next_e;
//         }

//         if let Some(next_e) = next_e {
//             let next_node = self.node_mut(next_e);
//             next_node.prev = prev_e;
//         }
//     }

//     pub fn insert_before(&mut self, insert: LinkedListEntry, before: LinkedListEntry) {
//         self.remove(insert);

//         let insert_node = self.node_mut(insert);
//         insert_node.next = Some(before);

//         let target_node = self.node_mut(before);
//         let prev_e = target_node.prev;
//         target_node.prev = Some(insert);

//         if let Some(prev_e) = prev_e {
//             let prev_node = self.node_mut(prev_e);
//             prev_node.next = Some(insert);

//             let insert_node = self.node_mut(insert);
//             insert_node.prev = Some(prev_e);
//         }
//     }

//     pub fn insert_after(&mut self, insert: LinkedListEntry, after: LinkedListEntry) {
//         self.remove(insert);

//         let insert_node = self.node_mut(insert);
//         insert_node.prev = Some(after);

//         let target_node = self.node_mut(after);
//         let next_e = target_node.next;
//         target_node.next = Some(insert);

//         if let Some(next_e) = next_e {
//             let next_node = self.node_mut(next_e);
//             next_node.prev = Some(insert);

//             let insert_node = self.node_mut(insert);
//             insert_node.next = Some(next_e);
//         }
//     }

//     fn node(&self, index: LinkedListEntry) -> &LinkedListNode {
//         &self.nodes[index.0]
//     }

//     fn node_mut(&mut self, index: LinkedListEntry) -> &mut LinkedListNode {
//         &mut self.nodes[index.0]
//     }
// }
