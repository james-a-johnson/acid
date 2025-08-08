use crate::{Graph, Id, Node};

pub struct DomTree<T> {
    nodes: Vec<Node<T>>,
    idoms: Vec<Id>,
}

impl<T> DomTree<T> {
    /// Create a new dominator tree from a graph.
    ///
    /// # Panics
    /// This will panic if there are [`usize::MAX`] nodes in the graph.
    pub fn new(g: Graph<T>) -> Self {
        assert_ne!(
            g.nodes.len(),
            usize::MAX,
            "Graph has too many nodes to construct dominator tree"
        );
        let mut idoms = Vec::with_capacity(g.nodes.len());
        for _ in 0..g.nodes.len() {
            idoms.push(Id::INVALID);
        }
        // The entry of the graph is its own dominator.
        idoms[0] = Id::ENTRY;
        let mut rpo = g.postorder();
        rpo.reverse();
        // Maps a node id to the order in which it would be seen in a postorder traversal
        let mut rpo_map = vec![0usize; g.nodes.len()];
        // SAFETY: An Id is just a usize. So any bit pattern is valid. We're immediately going to fill all of them in
        // with a specific value so no uninitialized memory will be accessed.
        for (i, id) in rpo.iter().enumerate() {
            rpo_map[id.0] = i;
        }

        loop {
            let mut changed = false;
            // Skip the entry node which already has its dominator calculated.
            for node_id in rpo.iter().skip(1) {
                let curr_node = g.get(*node_id).expect("This must be valid since the graph has not changed and it came from this graph");
                // This must exist. If the node did not have at least one predecessor then there would be no path from the entry node
                // to it and then it would not be in the postorder traversal.
                let mut new_idom = curr_node.entry[0];
                for pred_node_id in curr_node.entry.iter().skip(1) {
                    if idoms[pred_node_id.0] != Id::INVALID {
                        new_idom = intersect(*pred_node_id, new_idom, &idoms, &rpo_map);
                    }
                }
                if idoms[node_id.0] != new_idom {
                    idoms[node_id.0] = new_idom;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }

        Self {
            nodes: g.nodes,
            idoms,
        }
    }

    pub fn doms(&self, node_id: Id) -> Option<Vec<Id>> {
        if node_id.0 >= self.nodes.len() {
            return None;
        }

        let mut dominators = Vec::new();

        let mut curr_node = node_id;
        loop {
            dominators.push(curr_node);
            if curr_node == Id::ENTRY {
                break;
            }
            curr_node = self.idoms[curr_node.0];
        }

        Some(dominators)
    }

    #[inline]
    pub fn get(&self, node_id: Id) -> Option<&Node<T>> {
        self.nodes.get(node_id.0)
    }

    #[inline]
    pub fn idom(&self, node_id: Id) -> Option<Id> {
        self.idoms.get(node_id.0).copied()
    }
}

impl<T> From<Graph<T>> for DomTree<T> {
    fn from(value: Graph<T>) -> Self {
        Self::new(value)
    }
}

fn intersect(mut node1: Id, mut node2: Id, idoms: &[Id], map: &[usize]) -> Id {
    while node1 != node2 {
        if map[node1.0] > map[node2.0] {
            node1 = idoms[node1.0];
        } else {
            node2 = idoms[node2.0];
        }
    }
    node1
}

#[cfg(test)]
mod test {
    use super::*;

    // This is the graph from page 6 of the paper for the algorithm.
    // http://www.hipersoft.rice.edu/grads/publications/dom14.pdf
    #[test]
    fn graph_from_paper() {
        let mut g = Graph::new(5u8);
        g.update(|mut sg| {
            let five = sg.entry();
            let four = sg.add(4);
            let three = sg.add(3);
            let two = sg.add(2);
            let one = sg.add(1);

            sg.create_edge(five, four);
            sg.create_edge(five, three);
            sg.create_edge(three, two);
            sg.create_edge(four, one);
            sg.create_edge(one, two);
            sg.create_edge(two, one);
        });
        let dt = DomTree::new(g);
        assert_eq!(Id::ENTRY, dt.idom(Id::ENTRY).unwrap());
        assert_eq!(Id(0), dt.idom(Id(1)).unwrap());
        assert_eq!(Id(0), dt.idom(Id(2)).unwrap());
        assert_eq!(Id(0), dt.idom(Id(3)).unwrap());
        assert_eq!(Id(0), dt.idom(Id(4)).unwrap());
    }

    // This graph is taken from the example graph on wikipedia
    // https://en.wikipedia.org/wiki/Dominator_(graph_theory)
    #[test]
    fn wikipedia_example() {
        let mut g = Graph::new(1u8);
        let one = g.entry_id();
        let two = g.add(2);
        let three = g.add(3);
        let four = g.add(4);
        let five = g.add(5);
        let six = g.add(6);

        g.create_edge(one, two).unwrap();
        g.create_edge(two, three).unwrap();
        g.create_edge(two, four).unwrap();
        g.create_edge(two, six).unwrap();
        g.create_edge(three, five).unwrap();
        g.create_edge(four, five).unwrap();
        g.create_edge(five, two).unwrap();

        let dom = DomTree::new(g);
        assert_eq!(one, dom.idom(one).unwrap());
        assert_eq!(one, dom.idom(two).unwrap());
        assert_eq!(two, dom.idom(three).unwrap());
        assert_eq!(two, dom.idom(four).unwrap());
        assert_eq!(two, dom.idom(five).unwrap());
        assert_eq!(two, dom.idom(six).unwrap());
    }
}
