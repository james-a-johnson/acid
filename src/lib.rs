//! Simple graph library

/// Directed graph where each node holds a `T`.
pub struct Graph<T> {
    nodes: Vec<Node<T>>,
}

/// A node in a [`Graph`].
///
/// Keeps track of the value in this node and all edges into or out of this node.
pub struct Node<T> {
    val: T,
    entry: Vec<usize>,
    exit: Vec<usize>,
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

impl<T> Graph<T> {
    /// Create a new graph with `entry` as the entry node of the graph.
    pub fn new(entry: T) -> Self {
        Self {
            nodes: vec![entry.into()],
        }
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
    pub fn get(&self, id: usize) -> Option<&Node<T>> {
        self.nodes.get(id)
    }

    /// Get a mutable reference to the node with id `id`.
    pub fn get_mut(&mut self, id: usize) -> Option<&mut Node<T>> {
        self.nodes.get_mut(id)
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
    pub fn entry_nodes(&self) -> &[usize] {
        self.entry.as_slice()
    }

    /// Get a list of the ids of the nodes that this node has an edge to
    pub fn exit_nodes(&self) -> &[usize] {
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
