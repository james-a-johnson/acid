//! Support for finding the dominators of nodes in a graph.

use std::io::{BufWriter, Write};
use crate::{Graph, Node, Id};

/// [`Graph`] that contains extra information about what nodes dominate other nodes.
///
/// The graph cannot be changed when in this state. [`Dominator`] will not recalculate any dominator
/// information if the graph changes so it does not allow any changes. The [`Id`]s from a graph
/// will still work with the [`Dominator`] created from the [`Graph`].
pub struct Dominator<T> {
    // This is the boxed slice of nodes from a Graph. It's a boxed slice because no nodes should
    // ever be added or removed from the Dominator structure or else the dominators of nodes could
    // change and this is the dominators of a graph at a specific time.
    nodes: Box<[Node<T>]>,
    idoms: Box<[Id]>,
}

impl<T> Dominator<T> {
    /// Create a new dominator graph from the given [`Graph`].
    ///
    /// # Panics
    /// This constructor will panic if there are `usize::MAX` nodes in the graph.
    pub fn new(graph: Graph<T>) -> Dominator<T> {
        const INVALID: Id = Id(usize::MAX);
        // Creation of the dominator struct is mostly taken from
        // https://github.com/baziotis/compiler-optimization/blob/master/dominance/dtree.h
        if graph.nodes.len() == 0 {
            return Self {
                nodes: graph.nodes.into_boxed_slice(),
                idoms: Vec::new().into_boxed_slice(),
            };
        }
        if graph.nodes.len() == 1 {
            return Self {
                nodes: graph.nodes.into_boxed_slice(),
                idoms: vec![Id(0)].into_boxed_slice(),
            };
        }
        if graph.nodes.len() == usize::MAX {
            panic!("Invalid number of nodes");
        }
        let mut idoms: Box<[Id]> = unsafe {
            let mut dom_slice = Vec::with_capacity(graph.nodes.len());
            dom_slice.set_len(graph.nodes.len());
            dom_slice.into_boxed_slice()
        };
        idoms.fill(INVALID);
        // Entry node is always the first node and the entry has itself as the immediate dominator
        idoms[0] = Id(0);
        let postorder = graph.postorder_dfs_ids();
        debug_assert!(!postorder.is_empty(), "Postorder is empty");

        // This is an array of basic block index to the order it will be traversed in a post order dfs traversal
        let postorder_map: Box<[usize]> = unsafe {
            let mut map = Vec::with_capacity(postorder.len());
            map.set_len(postorder.len());
            let mut data = map.into_boxed_slice();
            for (i, n) in postorder.iter().enumerate() {
                data[n.0] = i;
            }
            data
        };
        let mut changed;
        loop {
            changed = false;
            let mut po = postorder.iter().rev();
            po.next().unwrap();
            for node in po {
                let bb = &graph.nodes[node.0];
                // SAFETY: Node must have at least one predecessor to be in the postorder.
                let mut new_idom = unsafe { *bb.entry.get_unchecked(0) };
                for p in 1..bb.entry.len() {
                    let pred = bb.entry[p];
                    if idoms[pred.0] != INVALID {
                        new_idom = intersect(new_idom, pred, idoms.as_ref(), postorder_map.as_ref());
                    }
                }
                if idoms[node.0] != new_idom {
                    changed = true;
                    idoms[node.0] = new_idom;
                }
            }
            if !changed { break; }
        }
        
        Self {
            nodes: graph.nodes.into_boxed_slice(),
            idoms,
        }
    }
    
    pub fn idom(&self, node: Id) -> Option<Id> {
        self.idoms.get(node.0).map(|id| *id)
    }

    /// Convert dominator graph back into the [`Graph`] that it came from.
    pub fn into_graph(self) -> Graph<T> {
        Graph { nodes: self.nodes.into_vec() }
    }
    
    /// Checks if `node1` dominates `node2`.
    pub fn dominates(&self, node1: Id, node2: Id) -> bool {
        let mut dom = self.idoms[node2.0];
        loop {
            if dom == node1 { return true; }
            if dom == Id(0) { return false; }
            dom = self.idoms[dom.0];
        }
    }
}

#[cfg(feature = "viz")]
impl<T: std::fmt::Display> Dominator<T> {
    pub fn dot_viz(&self, file: impl Write, name: &str) -> std::io::Result<()> {
        let mut writer = BufWriter::new(file);

        writeln!(writer, "digraph {} {{", name)?;
        writeln!(writer, "\t{};", self.nodes[0].val)?;
        for i in 1..self.idoms.len() {
            let node = &self.nodes[i];
            let idom = &self.nodes[self.idoms[i].0];
            writeln!(writer, "\t{} -> {};", idom.val, node.val)?;
        }
        writeln!(writer, "}}")?;
        writer.flush()?;
        Ok(())
    }
}

impl<T> From<Graph<T>> for Dominator<T> {
    fn from(graph: Graph<T>) -> Self {
        Self::new(graph)
    }
}

fn intersect(mut b1: Id, mut b2: Id, idoms: &[Id], postorder: &[usize]) -> Id {
    while b1 != b2 {
        if postorder[b1.0] < postorder[b2.0] {
            b1 = idoms[b1.0];
        } else {
            b2 = idoms[b2.0];
        }
    }
    b1
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn domination() {
        let mut g = Graph::new(0u32);
        g.update(|mut sg| {
            let zero = sg.entry();
            let one = sg.add(1);
            let two = sg.add(2);
            let three = sg.add(3);
            let four = sg.add(4);
            
            sg.create_edge(zero, one);
            sg.create_edge(one, two);
            sg.create_edge(one, three);
            sg.create_edge(two, four);
            sg.create_edge(three, four);
        });
        
        let entry = g.entry_id();
        let one = g.get(entry).unwrap().exit[0];
        let two = g.get(one).unwrap().exit[0];
        let three = g.get(one).unwrap().exit[1];
        let four = g.get(two).unwrap().exit[0];
        
        let dom = Dominator::new(g);
        assert_eq!(dom.idom(entry), Some(entry));
        assert_eq!(dom.idom(one), Some(entry));
        assert_eq!(dom.idom(two), Some(one));
        assert_eq!(dom.idom(three), Some(one));
        assert_eq!(dom.idom(four), Some(one));
        
        assert!(dom.dominates(one, four));
        assert!(!dom.dominates(two, four));
    }
}