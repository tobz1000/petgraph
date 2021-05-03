use std::collections::{HashMap, VecDeque};

use crate::{
    graph::{GraphIndex, NodeIndex},
    stable_graph::StableDiGraph,
    visit::{EdgeRef, GraphProp, IntoEdgeReferences},
    Directed, Direction,
};

use linked_list::{IndexLinkedList, LinkedListEntry};

/// Isomorphic to input graph; used in the process of determining a good node sequence from which to
/// extract a feedback arc set.
type SeqSourceGraph = StableDiGraph<Option<LinkedListEntry>, (), SeqGraphIx>;
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

    let delta_buckets = IndexLinkedList::new()

    // let mut sinks_or_isolated = VecDeque::new(); // V_d
    // let mut sources = VecDeque::new(); // V_(-n+2)
    // let mut other_nodes = VecDeque::new(); // V_(n-1)

    // for node_index in g.node_indices() {
    //     if node_is_sink(node_index, &g) {
    //         sinks_or_isolated.push_back(node_index);
    //     } else if node_is_source(node_index, &g) {
    //         sources.push_back(node_index);
    //     } else {
    //         // Assert that all other nodes have the expected delta degree
    //         debug_assert!({
    //             let dd = delta_degree(node_index, &g);
    //             let n = g.node_count() as isize;
    //             let expected_dd_bounds = (-n + 3)..=(n - 3);

    //             expected_dd_bounds.contains(&dd)
    //         });

    //         other_nodes.push_back(node_index);
    //     }
    // }

    // while let Some(sink_node) = sinks_or_isolated.pop_front() {
    //     s_2.push_front(sink_node);
    // }

    // while let Some(source_node) = sources.pop_front() {
    //     s_1.push_back(source_node)
    // }

    // while let Some(other) = other_nodes.pop_front() {}

    while g.node_count() > 0 {
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

mod linked_list {
    #[derive(Clone, Copy)]
    pub struct LinkedListEntry(usize);

    pub struct IndexLinkedList<T> {
        nodes: Vec<Node<T>>,
    }

    impl<T> IndexLinkedList<T> {
        pub fn new(vals: impl Iterator<Item = T>) -> Self {
            let nodes = vals
                .map(|v| Node {
                    head: None,
                    prev: None,
                    next: None,
                    val: v,
                })
                .collect();

            IndexLinkedList { nodes }
        }
        pub fn val(&self, entry: LinkedListEntry) -> &T {
            &self.node(entry).val
        }

        pub fn val_mut(&mut self, entry: LinkedListEntry) -> &mut T {
            &mut self.node_mut(entry).val
        }

        pub fn remove(&mut self, entry: LinkedListEntry) {
            let node = self.node_mut(entry);
            let prev_e = node.prev.take();
            let next_e = node.next.take();

            if let Some(prev_e) = prev_e {
                let prev_node = self.node_mut(prev_e);
                prev_node.next = next_e;
            }

            if let Some(next_e) = next_e {
                let next_node = self.node_mut(next_e);
                next_node.prev = prev_e;
            }
        }

        pub fn insert_before(&mut self, insert: LinkedListEntry, before: LinkedListEntry) {
            self.remove(insert);

            let insert_node = self.node_mut(insert);
            insert_node.next = Some(before);

            let target_node = self.node_mut(before);
            let prev_e = target_node.prev;
            target_node.prev = Some(insert);

            if let Some(prev_e) = prev_e {
                let prev_node = self.node_mut(prev_e);
                prev_node.next = Some(insert);

                let insert_node = self.node_mut(insert);
                insert_node.prev = Some(prev_e);
            }
        }

        pub fn insert_after(&mut self, insert: LinkedListEntry, after: LinkedListEntry) {
            self.remove(insert);

            let insert_node = self.node_mut(insert);
            insert_node.prev = Some(after);

            let target_node = self.node_mut(after);
            let next_e = target_node.next;
            target_node.next = Some(insert);

            if let Some(next_e) = next_e {
                let next_node = self.node_mut(next_e);
                next_node.prev = Some(insert);

                let insert_node = self.node_mut(insert);
                insert_node.next = Some(next_e);
            }
        }

        fn node(&self, index: LinkedListEntry) -> &Node<T> {
            &self.nodes[index.0]
        }

        fn node_mut(&mut self, index: LinkedListEntry) -> &mut Node<T> {
            &mut self.nodes[index.0]
        }
    }

    struct Node<T> {
        head: Option<Head>,
        prev: Option<LinkedListEntry>,
        next: Option<LinkedListEntry>,
        val: T,
    }

    struct Head {
        first: Option<LinkedListEntry>
    }

    // /// Internal doubly-linked list implementation. Nodes pre-allocated and connected via references
    // /// (rather than boxed as in [`std::collections::LinkedList`]).
    // pub struct LinkedList<'a, T> {
    //     pub head: Option<&'a mut LinkedListNode<'a, T>>,
    //     pub tail: Option<&'a mut LinkedListNode<'a, T>>,
    // }

    // pub struct LinkedListNode<'a, T> {
    //     pub prev: Option<&'a mut LinkedListNode<'a, T>>,
    //     pub next: Option<&'a mut LinkedListNode<'a, T>>,
    //     val: T,
    // }

    // impl<'a, T> LinkedListNode<'a, T> {
    //     pub fn remove(&mut self) {
    //         let prev = self.prev.take();
    //         let next = self.next.take();

    //         // match (prev, next) {
    //         //     (Some(prev), Some(next)) => {
    //         //         prev.next =
    //         //     }
    //         // }

    //         if let Some(prev) = prev {
    //             prev.next = next;
    //         }

    //         if let Some(next) = next {
    //             next.prev = prev;
    //         }
    //     }
    // }
}
