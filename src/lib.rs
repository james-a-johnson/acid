#![deny(clippy::perf)]
#![deny(clippy::style)]
#![deny(clippy::missing_errors_doc)]
#![deny(clippy::missing_safety_doc)]
#![deny(clippy::missing_panics_doc)]

//! Simple graph library

pub mod dom;

use std::collections::{HashSet, VecDeque};
use std::iter::FusedIterator;
use std::marker::PhantomData;

/// Directed graph where each node holds a `T`.
pub struct Graph<T> {
    nodes: Vec<Node<T>>,
}

/// A node in a [`Graph`].
///
/// Keeps track of the value in this node and all edges into or out of this node.
pub struct Node<T> {
    val: T,
    entry: Vec<Id>,
    exit: Vec<Id>,
}

/// Reference to a specific node in a graph.
#[repr(transparent)]
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash)]
pub struct Id(usize);

impl Id {
    /// Id of the entry node of a graph.
    ///
    /// This is guaranteed to be valid for any [`Graph`].
    pub const ENTRY: Self = Self(0);
    pub const INVALID: Self = Self(usize::MAX);
}

const _: () = assert!(size_of::<Id>() == size_of::<usize>());
const _: () = assert!(align_of::<Id>() == size_of::<usize>());

impl From<SafeId<'_>> for Id {
    fn from(id: SafeId) -> Self {
        Id(id.idx)
    }
}

impl<T> From<T> for Node<T> {
    fn from(value: T) -> Self {
        Self {
            val: value,
            entry: vec![],
            exit: vec![],
        }
    }
}

#[allow(clippy::len_without_is_empty)]
impl<T> Graph<T> {
    /// Create a new graph with `entry` as the entry node of the graph.
    pub fn new(entry: T) -> Self {
        Self {
            nodes: vec![entry.into()],
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Get the Id of the entry node.
    pub fn entry_id(&self) -> Id {
        Id(0)
    }

    /// Create a new graph with `entry` as the entry node of the graph and pre-allocate
    /// space to hold `cap` nodes.
    pub fn with_capacity(entry: T, cap: usize) -> Self {
        let mut nodes = Vec::with_capacity(cap);
        nodes.push(entry.into());
        Self { nodes }
    }

    /// Get the entry node of the graph
    pub fn entry(&self) -> &Node<T> {
        // SAFETY: All constructors guarantee that there will be at least one node in the
        // graph and the graph does not allow for removing nodes from the graph. So there
        // will always be at least a single node in the graph making this access safe.
        unsafe { self.nodes.get_unchecked(0) }
    }

    /// Get a mutable reference to the entry node
    pub fn entry_mut(&mut self) -> &mut Node<T> {
        // SAFETY: See safety comment for `entry`.
        unsafe { self.nodes.get_unchecked_mut(0) }
    }

    /// Get a reference to the node with id `id`.
    pub fn get(&self, id: Id) -> Option<&Node<T>> {
        self.nodes.get(id.0)
    }

    /// Get a mutable reference to the node with id `id`.
    pub fn get_mut(&mut self, id: Id) -> Option<&mut Node<T>> {
        self.nodes.get_mut(id.0)
    }

    /// Update nodes in the graph.
    pub fn update<'g, U>(&'g mut self, changes: U)
    where
        U: for<'id> FnOnce(SafeGraph<'id, 'g, T>),
    {
        let sg = SafeGraph::new(&mut self.nodes);
        changes(sg);
    }

    /// Add a new node to the graph.
    ///
    /// Returns the id that can be used to reference the added node.
    pub fn add(&mut self, val: T) -> Id {
        let id = self.nodes.len();
        self.nodes.push(val.into());
        Id(id)
    }

    /// Create a new edge between two nodes.
    ///
    /// Uses `start` as the start node of the edge and `end` as the end node of the edge.
    ///
    /// # Errors
    /// If either `start` or `end` is invalid, it will return the id that was invalid as the error.
    /// Checks `start` then `end`.
    pub fn create_edge(&mut self, start: Id, end: Id) -> Result<(), Id> {
        // Need to check both indexes first to make sure they are valid. Otherwise, an invalid edge could be
        // added to the graph.
        if start.0 >= self.nodes.len() {
            return Err(start);
        }
        if end.0 >= self.nodes.len() {
            return Err(end);
        }
        if let Some(n) = self.nodes.get_mut(start.0) {
            n.exit.push(end);
        }
        if let Some(n) = self.nodes.get_mut(end.0) {
            n.entry.push(start);
        }
        Ok(())
    }

    /// Get the postorder traversal of the graph.
    ///
    /// This just creates a vector that is the list of node Id's in postorder traversal order.
    ///
    /// Algorithm used comes from [Eli Bendersky](https://eli.thegreenplace.net/2015/directed-graph-traversal-orderings-and-applications-to-data-flow-analysis/)
    pub fn postorder(&self) -> Vec<Id> {
        let mut order = Vec::with_capacity(self.nodes.len());
        let mut visited = HashSet::<Id>::new();
        self.postorder_helper(&mut order, &mut visited, self.entry_id());
        order
    }

    /// Helper for doing postorder traversal. This is the recursive function that will be called. Makes the
    /// implementation quite simple.
    fn postorder_helper(&self, order: &mut Vec<Id>, visited: &mut HashSet<Id>, curr_node: Id) {
        visited.insert(curr_node);
        let node = self
            .get(curr_node)
            .expect("This must be valid since graph does not allow removal");
        for succ in &node.exit {
            if !visited.contains(succ) {
                self.postorder_helper(order, visited, *succ);
            }
        }
        order.push(curr_node);
    }
}

impl<T: Eq> Graph<T> {
    #[inline]
    pub fn find(&self, value: &T) -> Option<Id> {
        for i in 0..self.nodes.len() {
            if self.nodes[i].val == *value {
                return Some(Id(i));
            }
        }
        None
    }

    pub fn find_or_insert(&mut self, value: T) -> Id {
        if let Some(n) = self.find(&value) {
            n
        } else {
            self.add(value)
        }
    }
}

pub struct BreadthFirst<'g, T> {
    graph: &'g Graph<T>,
    visited: HashSet<Id>,
    queue: VecDeque<Id>,
}

impl<'g, T> BreadthFirst<'g, T> {
    pub fn new(graph: &'g Graph<T>) -> Self {
        let mut visited = HashSet::new();
        visited.insert(graph.entry_id());
        let mut queue = VecDeque::new();
        queue.push_back(graph.entry_id());
        Self {
            graph,
            visited,
            queue,
        }
    }
}

impl<'g, T> Iterator for BreadthFirst<'g, T> {
    type Item = &'g Node<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(n) = self.queue.pop_front() {
            // Get next node to visit and then add all children to queue
            for succ in self.graph.get(n).unwrap().exit.iter() {
                if !self.visited.contains(succ) {
                    self.queue.push_back(*succ);
                }
            }
            Some(self.graph.get(n).unwrap())
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.graph.nodes.len() - self.visited.len();
        (size - 1, Some(size))
    }
}

impl<'g, T> FusedIterator for BreadthFirst<'g, T> {}

pub struct DepthFirst<'g, T> {
    graph: &'g Graph<T>,
    visited: HashSet<Id>,
    queue: Vec<Id>,
}

impl<'g, T> DepthFirst<'g, T> {
    pub fn new(graph: &'g Graph<T>) -> Self {
        let mut visited = HashSet::new();
        visited.insert(graph.entry_id());
        let queue = vec![graph.entry_id()];
        Self {
            graph,
            visited,
            queue,
        }
    }
}

impl<'g, T> Iterator for DepthFirst<'g, T> {
    type Item = &'g Node<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some(n) = self.queue.pop() {
            for succ in self.graph.get(n).unwrap().exit.iter() {
                if !self.visited.contains(succ) {
                    self.queue.push(*succ);
                }
            }
            Some(self.graph.get(n).unwrap())
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let size = self.graph.nodes.len() - self.visited.len();
        (size - 1, Some(size))
    }
}

impl<'g, T> FusedIterator for DepthFirst<'g, T> {}

impl<T: std::fmt::Display> Graph<T> {
    /// Write the graph to a file in graphviz format.
    ///
    /// # Params
    /// - `file` Where to write the file to
    /// - `name` Name of the graph
    ///
    /// # Errors
    /// Returns an error if any of the writes fail.
    pub fn dot_viz<W: std::io::Write>(&self, file: W, name: &str) -> std::io::Result<()> {
        use std::io::BufWriter;
        use std::io::Write;

        let mut writer = BufWriter::new(file);

        writeln!(writer, "digraph {name} {{")?;
        for n in self.nodes.iter() {
            for succ in n.exit.iter() {
                writeln!(writer, "\t{} -> {};", n.val, unsafe {
                    &self.nodes.get_unchecked(succ.0).val
                })?;
            }
        }
        writeln!(writer, "}}")?;

        Ok(())
    }
}

impl<T> Node<T> {
    /// Get a reference to the value held in this node
    pub fn val(&self) -> &T {
        &self.val
    }

    /// Get a mutable reference to the value held in this node
    pub fn val_mut(&mut self) -> &mut T {
        &mut self.val
    }

    /// Get a list of the ids of the nodes that have an edge to this node
    pub fn entry_nodes(&self) -> &[Id] {
        self.entry.as_slice()
    }

    /// Get a list of the ids of the nodes that this node has an edge to
    pub fn exit_nodes(&self) -> &[Id] {
        self.exit.as_slice()
    }
}

impl<T> AsRef<T> for Node<T> {
    fn as_ref(&self) -> &T {
        &self.val
    }
}

impl<T> AsMut<T> for Node<T> {
    fn as_mut(&mut self) -> &mut T {
        &mut self.val
    }
}

type Brand<'id> = PhantomData<fn(&'id ()) -> &'id ()>;

/// Graph that allows for completely safe and unchecked accesses to nodes via an [`SafeId`].
pub struct SafeGraph<'id, 'g, T> {
    nodes: &'g mut Vec<Node<T>>,
    _brand: Brand<'id>,
}

/// Id of a node tied to a specific graph.
///
/// Using it as an index into a graph is guaranteed to be a safe unchecked access if using it
/// compiles.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct SafeId<'id> {
    idx: usize,
    _brand: Brand<'id>,
}

const _: () = assert!(
    align_of::<usize>() == align_of::<SafeId<'_>>(),
    "Id alignment differs from usize"
);
const _: () = assert!(
    size_of::<usize>() == size_of::<SafeId<'_>>(),
    "Id size differs from usize"
);

impl<'id> SafeId<'id> {
    /// Create a new id for a specific index.
    ///
    /// This should not be used by anyone outside of this crate so it is not fully public. It
    /// doesn't make sense for anything outside of this crate to make one of these ids even though
    /// it is safe to do so.
    pub(crate) fn new(idx: usize) -> Self {
        Self {
            idx,
            _brand: PhantomData,
        }
    }
}

impl<'id, 'g, T> SafeGraph<'id, 'g, T> {
    /// Create a new SafeGraph from a Vec of Nodes.
    ///
    /// This is not public because it assumes that the Vec of Nodes will always have at least one element in it.
    /// That will be guaranteed when this constructor is called from this module but can't be guaranteed if a user
    /// calls this method.
    pub(crate) fn new(nodes: &'g mut Vec<Node<T>>) -> Self {
        debug_assert!(
            !nodes.is_empty(),
            "Safe graph constructor with empty vector"
        );
        Self {
            nodes,
            _brand: PhantomData,
        }
    }

    /// Get the id of the entry node of the graph.
    #[inline]
    pub fn entry(&self) -> SafeId<'id> {
        // SAFETY: See the safety comment for Graph::entry
        SafeId::new(0)
    }

    /// Get a reference to a specific element in the graph.
    #[inline]
    pub fn get(&self, id: SafeId<'id>) -> &Node<T> {
        // SAFETY: An Id is only created with valid indexes into a graph. Nodes cannot be removed from the
        // graph so the index can never become invalid. Additionally, the brand of the Node will tie it to
        // a specific instantiation of a SafeGraph so the specific index will be valid for this specific
        // instantiation of the graph.
        unsafe { self.nodes.get_unchecked(id.idx) }
    }

    /// Get a mutable reference to a specific element in the graph.
    #[inline]
    pub fn get_mut(&mut self, id: SafeId<'id>) -> &mut Node<T> {
        // SAFETY: See safety for `get`.
        unsafe { self.nodes.get_unchecked_mut(id.idx) }
    }

    /// Add a new node to the graph.
    ///
    /// Returns the [`SafeId`] that can be used to reference the node that was just added.
    pub fn add(&mut self, val: T) -> SafeId<'id> {
        let index = self.nodes.len();
        self.nodes.push(val.into());
        SafeId::new(index)
    }

    /// Create a new edge in the graph from node `start` to node `end`.
    pub fn create_edge(&mut self, start: SafeId<'id>, end: SafeId<'id>) {
        self.get_mut(start).exit.push(end.into());
        self.get_mut(end).entry.push(start.into());
    }

    /// Convert an id of a node into an [`SafeId`].
    ///
    /// Checks if the id is in this graph and returns the safe Id if possible or returns None otherwise.
    pub fn safe_index(&mut self, idx: Id) -> Option<SafeId<'id>> {
        if idx.0 < self.nodes.len() {
            Some(SafeId::new(idx.0))
        } else {
            None
        }
    }

    /// Get the predecessors of a node.
    pub fn predecessors(&mut self, node: SafeId<'id>) -> &[SafeId<'id>] {
        let node = self.get(node);
        // SAFETY: Id and SafeId have the same size and alignment and both only contain a single
        // usize. Transmuting an Id to an Id that has a phantom lifetime associated with it is
        // safe.
        unsafe { std::mem::transmute(node.entry_nodes()) }
    }

    /// Get the successors of a node.
    pub fn successors(&mut self, node: SafeId<'id>) -> &[SafeId<'id>] {
        let node = self.get(node);
        // SAFETY: See safety comment in predecessors.
        unsafe { std::mem::transmute(node.exit_nodes()) }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn min_graph() {
        let g = Graph::new(0u32);
        let entry = g.entry();
        assert_eq!(*entry.val(), 0);
        assert_eq!(entry.exit_nodes(), &[]);
        assert_eq!(entry.entry_nodes(), &[]);
    }

    #[test]
    fn modify() {
        let mut g = Graph::new(0u32);
        let one = g.add(1);
        let two = g.add(2);
        g.create_edge(g.entry_id(), one)
            .expect("Failed to create valid edge");
        g.create_edge(g.entry_id(), two)
            .expect("Failed to create valid edge");

        let e1 = g.create_edge(Id(100), two);
        assert_eq!(e1, Err(Id(100)));
        let e2 = g.create_edge(two, Id(102));
        assert_eq!(e2, Err(Id(102)));
    }

    #[test]
    fn update() {
        let mut g = Graph::new(0u32);
        g.update(|mut sg| {
            let two = sg.add(2);
            let three = sg.add(3);
            let four = sg.add(4);
            sg.create_edge(sg.entry(), two);
            sg.create_edge(two, three);
            sg.create_edge(three, four);

            let invalid = sg.safe_index(Id(1000));
            assert!(invalid.is_none(), "Invalid index turned into an Id");
        });
        let vals = g.nodes.iter().map(|n| *n.val()).collect::<Vec<u32>>();
        assert_eq!(vals.as_slice(), &[0, 2, 3, 4]);
    }

    #[test]
    fn postorder() {
        let mut g = Graph::new('A');
        g.update(|mut sg| {
            let a = sg.entry();
            let t = sg.add('T');
            let c = sg.add('C');
            let b = sg.add('B');
            let e = sg.add('E');
            let d = sg.add('D');

            sg.create_edge(a, t);
            sg.create_edge(a, b);
            sg.create_edge(a, c);
            sg.create_edge(t, b);
            sg.create_edge(c, b);
            sg.create_edge(c, e);
            sg.create_edge(b, d);
            sg.create_edge(e, d);
        });

        let order = g.postorder();
        let letters: Vec<char> = order.into_iter().map(|i| g.get(i).unwrap().val).collect();
        assert_eq!(&letters, &['D', 'B', 'T', 'E', 'C', 'A']);
    }

    // This test is included so that it can be uncommented every once in a while to make sure it does not
    // compile. This guarantees the safety properties of Id not being able to be used with other safe graphs.
    // #[test]
    // fn compile_error() {
    //     let mut g1 = Graph::new('a');
    //     let mut g2 = Graph::new('b');
    //     g1.update(|mut sg1| {
    //         g2.update(|mut sg2| {
    //             let entry2 = sg2.entry();
    //             let node = sg1.get(entry2);
    //         })
    //     })
    // }
}
