use std::collections::{HashMap, VecDeque};

use crate::{
    graph::{GraphIndex, NodeIndex},
    visit::{EdgeRef, GraphProp, IntoEdgeReferences},
    Directed,
};

use self::linked_list as ll;
use self::linked_list::LinkedList;

// TODO: see if we can support 32-bit graphs now
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
    G: crate::visit::NodeCount,
{
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
    let mut fas_stg = ll::Storage::new();
    let mut bkt_stg = ll::Storage::new();
    let mut buckets = Buckets {
        sinks_or_isolated: LinkedList::new(),
        sources: LinkedList::new(),
        bidirectional: LinkedList::new(),
    };
    // Lookup of node indices from input graph to indices into `nodes`
    let mut graph_ix_lookup = HashMap::new();

    let bkt_0_ix = Buckets::bucket_index(0, &mut bkt_stg);

    // Build node entries
    for (from_g_ix, to_g_ix) in edge_refs {
        let mut fas_node_entry = |g_ix: NodeIndex<SeqGraphIx>,
                                  fas_stg: &mut ll::Storage<FasNode>|
         -> ll::Index<FasNode> {
            match graph_ix_lookup.get(&g_ix) {
                Some(fas_ix) => *fas_ix,
                None => {
                    let fas_ix = fas_stg.push(FasNode {
                        graph_ix: g_ix,
                        // Assume all nodes are bidirectional while edges still being added
                        list_loc: Some(FasNodeLocation::Bidirectional(bkt_0_ix)),
                        out_edges: Vec::new(),
                        in_edges: Vec::new(),
                        out_degree: 0,
                        in_degree: 0,
                    });

                    graph_ix_lookup.insert(g_ix, fas_ix);

                    fas_ix
                }
            }
        };

        let from_fas_ix = fas_node_entry(from_g_ix, &mut fas_stg);
        let from_node = fas_stg[from_fas_ix].data();
        from_node.out_degree += 1;
        buckets.move_to_adjacent_bucket(
            from_fas_ix,
            &mut fas_stg,
            &mut bkt_stg,
            DeltaChange::PlusOne,
        );

        let to_fas_ix = fas_node_entry(to_g_ix, &mut fas_stg);
        let to_node = fas_stg[to_fas_ix].data();
        to_node.in_degree += 1;
        buckets.move_to_adjacent_bucket(
            to_fas_ix,
            &mut fas_stg,
            &mut bkt_stg,
            DeltaChange::MinusOne,
        );
    }

    let mut s_1 = VecDeque::new();
    let mut s_2 = VecDeque::new();

    loop {
        let mut some_moved = false;

        while let Some(sink_fas_ix) = buckets.sinks_or_isolated.pop(&mut fas_stg) {
            some_moved = true;
            buckets.update_neighbour_node_buckets(sink_fas_ix, &mut fas_stg, &mut bkt_stg);
            s_2.push_front(fas_stg[sink_fas_ix].data().graph_ix);
        }

        while let Some(source_fas_ix) = buckets.sources.pop(&mut fas_stg) {
            some_moved = true;
            buckets.update_neighbour_node_buckets(source_fas_ix, &mut fas_stg, &mut bkt_stg);
            s_1.push_back(fas_stg[source_fas_ix].data().graph_ix);
        }

        let highest_dd_ix =
            if let Some(mut highest_dd_bucket) = buckets.highest_bidirectional(&mut bkt_stg) {
                highest_dd_bucket.get().pop(&mut fas_stg)
            } else {
                None
            };

        if let Some(highest_dd_ix) = highest_dd_ix {
            some_moved = true;
            buckets.update_neighbour_node_buckets(highest_dd_ix, &mut fas_stg, &mut bkt_stg);
            s_1.push_back(fas_stg[highest_dd_ix].data().graph_ix);
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

/// Represents a node from the input graph, tracking its current delta degree
#[derive(Debug)]
struct FasNode {
    /// Node index in input graph.
    graph_ix: NodeIndex<SeqGraphIx>,

    /// `None` if not currently in a list
    list_loc: Option<FasNodeLocation>,

    /// All outward edges from this node (not removed during processing)
    out_edges: Vec<ll::Index<FasNode>>,

    /// All inward edges from this node (not removed during processing)
    in_edges: Vec<ll::Index<FasNode>>,

    /// Current out-degree of this node (decremented during processing as connected nodes are
    /// removed)
    out_degree: usize,

    /// Current in-degree of this node (decremented during processing as connected nodes are
    /// removed)
    in_degree: usize,
}

impl FasNode {
    fn suitable_bucket(&self, bkt_stg: &mut ll::Storage<BucketNode>) -> FasNodeLocation {
        if self.out_degree == 0 {
            FasNodeLocation::SinksOrIsolated
        } else if self.in_degree == 0 {
            FasNodeLocation::Sources
        } else {
            let delta_degree = self.out_degree as isize - self.in_degree as isize;
            let bkt_ix = Buckets::bucket_index(delta_degree, bkt_stg);
            FasNodeLocation::Bidirectional(bkt_ix)
        }
    }
}

#[derive(Debug)]
enum FasNodeLocation {
    SinksOrIsolated,
    Sources,
    Bidirectional(ll::Index<BucketNode>),
}

#[derive(Debug)]
struct BucketNode {
    delta_degree: isize,
    list: LinkedList<FasNode>,
}

#[derive(Debug)]
struct Buckets {
    sinks_or_isolated: LinkedList<FasNode>,
    sources: LinkedList<FasNode>,

    /// Meta-list of lists (buckets) of FAS nodes, organised by delta degree, descending order. Only
    /// populated buckets should reside in this list.
    bidirectional: LinkedList<BucketNode>,
}

/// Proxy for a [`LinkedList<FasNode>`] which, if the list is non-permanent and ends up empty,
/// removes the list from the bucket meta-list on drop.
struct BucketHandle<'a> {
    bkt_stg: &'a mut ll::Storage<BucketNode>,
    bkts_list: &'a mut LinkedList<BucketNode>,
    bkt_ix: ll::Index<BucketNode>,
}

/// Represents a change in a FAS node's degree-delta when constructing or removing nodes from
/// buckets.
enum DeltaChange {
    PlusOne,
    MinusOne,
}

impl<'a> BucketHandle<'a> {
    fn get<'b>(&'b mut self) -> &'b mut LinkedList<FasNode> {
        let BucketHandle {
            bkt_stg, bkt_ix, ..
        } = self;
        &mut bkt_stg[*bkt_ix].data().list
    }

    /// Gets a handle for an adjacent bucket, allocating and adding to bucket list if necessary.
    fn adjacent_bucket(self, change: DeltaChange) -> BucketHandle<'a> {
        let BucketHandle {
            bkt_stg,
            bkt_ix,
            bkts_list,
        } = self;
        let bkt = bkt_stg[bkt_ix].data();
        let next_dd = match change {
            DeltaChange::PlusOne => bkt.delta_degree + 1,
            DeltaChange::MinusOne => bkt.delta_degree - 1,
        };
        let next_ix = Buckets::bucket_index(next_dd, bkt_stg);
        let bkt_entry = &mut bkt_stg[bkt_ix];

        if !bkt_entry.is_in_list() {
            match change {
                DeltaChange::PlusOne => {
                    bkts_list.insert_before(next_ix, bkt_ix, bkt_stg);
                }
                DeltaChange::MinusOne => {
                    bkts_list.insert_after(next_ix, bkt_ix, bkt_stg);
                }
            }
        }

        BucketHandle {
            bkt_stg,
            bkts_list,
            bkt_ix: next_ix,
        }
    }
}

impl<'bkts> Drop for BucketHandle<'bkts> {
    fn drop(&mut self) {
        let BucketHandle {
            bkt_stg,
            bkts_list,
            bkt_ix,
        } = self;
        let bkt_node = bkt_stg[*bkt_ix].data();
        if bkt_node.list.start.is_none() {
            bkts_list.remove(*bkt_ix, bkt_stg);
        }
    }
}

impl Buckets {
    /// Deterministic gets the storage index for the bucket of a given delta degree. Extends storage with empty buckets
    /// if necessary.
    fn bucket_index(
        delta_degree: isize,
        bkt_stg: &mut ll::Storage<BucketNode>,
    ) -> ll::Index<BucketNode> {
        // Buckets stored by delta degree in positions [0, -1, 1, -2, 2, ...]
        let dd_to_ix = |dd| (isize::abs(dd * 2) - (if dd < 0 { 1 } else { 0 })) as usize;
        let ix_to_dd = |ix| (ix / 2) as isize * (if ix % 2 == 0 { 0 } else { -1 });
        let stg_pos = dd_to_ix(delta_degree);

        while bkt_stg.len() <= stg_pos {
            bkt_stg.push(BucketNode {
                delta_degree: ix_to_dd(bkt_stg.len()),
                list: LinkedList::new(),
            });
        }

        ll::Index::new(stg_pos)
    }

    fn highest_bidirectional<'a>(
        &'a mut self,
        bkt_stg: &'a mut ll::Storage<BucketNode>,
    ) -> Option<BucketHandle<'a>> {
        if let Some(highest_bucket) = self.bidirectional.start {
            Some(BucketHandle {
                bkt_stg,
                bkts_list: &mut self.bidirectional,
                bkt_ix: highest_bucket,
            })
        } else {
            None
        }
    }

    fn bidirectional_bucket_handle<'a>(
        &'a mut self,
        fas_ix: ll::Index<FasNode>,
        fas_stg: &mut ll::Storage<FasNode>,
        bkt_stg: &'a mut ll::Storage<BucketNode>,
    ) -> BucketHandle<'a> {
        let fas_node = &fas_stg[fas_ix].data();
        if let Some(FasNodeLocation::Bidirectional(bkt_ix)) = fas_node.list_loc {
            BucketHandle {
                bkt_stg,
                bkts_list: &mut self.bidirectional,
                bkt_ix,
            }
        } else {
            panic!("node not in bidirectional buckets")
        }
    }

    fn move_to_adjacent_bucket(
        &mut self,
        fas_node_ix: ll::Index<FasNode>,
        fas_stg: &mut ll::Storage<FasNode>,
        bkt_stg: &mut ll::Storage<BucketNode>,
        change: DeltaChange,
    ) {
        let fas_node = fas_stg[fas_node_ix].data();
        let dest_pos = fas_node.suitable_bucket(bkt_stg);

        let mut curr_bkt = self.bidirectional_bucket_handle(fas_node_ix, fas_stg, bkt_stg);
        let mut adjacent_bkt;

        // Remove from current bucket
        curr_bkt.get().remove(fas_node_ix, fas_stg);

        let dest_bkt = match dest_pos {
            FasNodeLocation::SinksOrIsolated => {
                drop(curr_bkt);
                &mut self.sinks_or_isolated
            }
            FasNodeLocation::Sources => {
                drop(curr_bkt);
                &mut self.sources
            }
            FasNodeLocation::Bidirectional(_) => {
                adjacent_bkt = curr_bkt.adjacent_bucket(change);
                adjacent_bkt.get()
            }
        };

        dest_bkt.push(fas_node_ix, fas_stg);
    }

    fn update_neighbour_node_buckets(
        &mut self,
        ix: ll::Index<FasNode>,
        fas_stg: &mut ll::Storage<FasNode>,
        bkt_stg: &mut ll::Storage<BucketNode>,
    ) {
        let out_edge_count = 0..fas_stg[ix].data().out_edges.len();

        for i in out_edge_count {
            let out_ix = fas_stg[ix].data().out_edges[i];

            // Ignore loops
            if out_ix == ix {
                continue;
            }

            // Ignore nodes which have already been moved to the good sequence
            if !fas_stg[out_ix].is_in_list() {
                continue;
            }

            // Other node has lost an in-edge; reduce in-degree by 1
            let out_node = fas_stg[out_ix].data();
            out_node.in_degree -= 1;
            self.move_to_adjacent_bucket(out_ix, fas_stg, bkt_stg, DeltaChange::PlusOne);
        }

        let in_edge_count = fas_stg[ix].data().in_edges.len();

        for i in 0..in_edge_count {
            let in_ix = fas_stg[ix].data().out_edges[i];

            if in_ix == ix {
                continue;
            }

            if !fas_stg[in_ix].is_in_list() {
                continue;
            }

            // Other node has lost an out-edge; reduce out-degree by 1
            let in_node = fas_stg[in_ix].data();
            in_node.out_degree -= 1;
            self.move_to_adjacent_bucket(in_ix, fas_stg, bkt_stg, DeltaChange::MinusOne);
        }
    }
}

mod linked_list {
    use std::marker::PhantomData;

    #[derive(Debug)]
    pub struct Index<Data> {
        val: usize,
        marker: PhantomData<Data>,
    }

    impl<Data> Index<Data> {
        pub fn new(val: usize) -> Self {
            Index {
                val,
                marker: PhantomData,
            }
        }
    }

    impl<Data> std::cmp::PartialEq for Index<Data> {
        fn eq(&self, other: &Self) -> bool {
            self.val.eq(&other.val)
        }
    }

    impl<Data> Clone for Index<Data> {
        fn clone(&self) -> Self {
            Index {
                val: self.val,
                marker: PhantomData,
            }
        }
    }

    impl<Data> Copy for Index<Data> {}

    pub struct Storage<Data> {
        entries: Vec<Entry<Data>>,
    }

    impl<Data> Storage<Data> {
        pub fn new() -> Self {
            Storage {
                entries: Vec::new(),
            }
        }

        pub fn push(&mut self, data: Data) -> Index<Data> {
            let ix = Index::new(self.entries.len());
            self.entries.push(Entry::new(data));
            ix
        }

        pub fn len(&self) -> usize {
            self.entries.len()
        }
    }

    impl<Data> std::ops::Index<Index<Data>> for Storage<Data> {
        type Output = Entry<Data>;

        fn index(&self, ix: Index<Data>) -> &Self::Output {
            &self.entries[ix.val]
        }
    }

    impl<Data> std::ops::IndexMut<Index<Data>> for Storage<Data> {
        fn index_mut(&mut self, ix: Index<Data>) -> &mut Self::Output {
            &mut self.entries[ix.val]
        }
    }

    #[derive(PartialEq, Debug)]
    pub struct LinkedList<Data> {
        pub start: Option<Index<Data>>,
    }

    #[derive(Debug)]
    struct Position<Data> {
        prev: Option<Index<Data>>,
        next: Option<Index<Data>>,
    }

    /// Wrapper of payload data stored in [`Storage`].
    #[derive(Debug)]
    pub struct Entry<Data> {
        /// `None` when not a member of any list
        pos: Option<Position<Data>>,
        data: Data,
    }
    impl<Data> Entry<Data> {
        pub fn new(data: Data) -> Self {
            Entry { pos: None, data }
        }

        pub fn next(&self) -> Option<Index<Data>> {
            self.pos
                .as_ref()
                .expect("expected linked list entry to have populated position")
                .next
        }

        pub fn prev(&self) -> Option<Index<Data>> {
            self.pos
                .as_ref()
                .expect("expected linked list entry to have populated position")
                .prev
        }

        pub fn data(&mut self) -> &mut Data {
            &mut self.data
        }

        pub fn is_in_list(&mut self) -> bool {
            self.pos.is_some()
        }

        fn pos_mut(&mut self) -> &mut Position<Data> {
            self.pos
                .as_mut()
                .expect("expected linked list entry to have populated position")
        }
    }

    impl<Data> LinkedList<Data> {
        pub fn new() -> Self {
            LinkedList { start: None }
        }

        pub fn push(&mut self, push_ix: Index<Data>, stg: &mut Storage<Data>) {
            if let Some(start_ix) = self.start {
                let entry = &mut stg[start_ix];
                entry.pos_mut().prev = Some(push_ix);
            }

            let push_entry = &mut stg[push_ix];

            debug_assert!(push_entry.pos.is_none());

            push_entry.pos = Some(Position {
                next: self.start,
                prev: None,
            });

            self.start = Some(push_ix);
        }

        pub fn pop(&mut self, stg: &mut Storage<Data>) -> Option<Index<Data>> {
            if let Some(remove_ix) = self.start {
                self.remove(remove_ix, stg);
                Some(remove_ix)
            } else {
                None
            }
        }

        /// `insert_ix` and `after_ix `should members of `self`
        pub fn insert_after(
            &mut self,
            insert_ix: Index<Data>,
            after_ix: Index<Data>,
            stg: &mut Storage<Data>,
        ) {
            let after_entry = &mut stg[after_ix];

            debug_assert!(after_entry.pos.is_some());

            after_entry.pos_mut().next = Some(insert_ix);

            let next_ix = after_entry.next();

            if let Some(next_ix) = next_ix {
                let next_entry = &mut stg[next_ix];
                next_entry.pos_mut().prev = Some(insert_ix);
            }

            let insert_entry = &mut stg[insert_ix];
            debug_assert!(insert_entry.pos.is_none());

            insert_entry.pos = Some(Position {
                prev: Some(after_ix),
                next: next_ix,
            })
        }

        /// `insert_ix` and `before_ix` **must** members of `self
        pub fn insert_before(
            &mut self,
            insert_ix: Index<Data>,
            before_ix: Index<Data>,
            stg: &mut Storage<Data>,
        ) {
            let before_entry = &mut stg[before_ix];

            debug_assert!(before_entry.pos.is_some());

            before_entry.pos_mut().next = Some(insert_ix);

            let prev_ix = before_entry.next();

            if let Some(prev_ix) = prev_ix {
                let prev_entry = &mut stg[prev_ix];
                prev_entry.pos_mut().next = Some(insert_ix);
            }

            let insert_entry = &mut stg[insert_ix];
            debug_assert!(insert_entry.pos.is_none());

            insert_entry.pos = Some(Position {
                prev: prev_ix,
                next: Some(before_ix),
            })
        }

        /// `remove_ix` **must** be a member of `self`
        pub fn remove(&mut self, remove_ix: Index<Data>, stg: &mut Storage<Data>) {
            debug_assert!(
                self.to_vec(stg).contains(&remove_ix),
                "node to remove should be member of current linked list"
            );

            let remove_entry = &mut stg[remove_ix];
            let ll_entry = remove_entry.pos.take().unwrap();

            if let Some(prev_ix) = ll_entry.prev {
                let prev_node = &mut stg[prev_ix];
                prev_node.pos_mut().next = ll_entry.next;
            }

            if let Some(next_ix) = ll_entry.next {
                let next_node = &mut stg[next_ix];
                next_node.pos_mut().prev = ll_entry.prev;
            }

            // If the removed node was head of the list
            if self.start == Some(remove_ix) {
                self.start = ll_entry.next;
            }
        }

        /// For debug purposes
        fn to_vec(&self, stg: &mut Storage<Data>) -> Vec<Index<Data>> {
            let mut ixs = Vec::new();

            let mut node_ix = self.start;

            while let Some(n_ix) = node_ix {
                ixs.push(n_ix);

                node_ix = stg[n_ix].pos_mut().next;
            }

            ixs
        }
    }
}
