use std::borrow::Cow;
use std::io::Write;

use crate::icfg::graph::{Edge, Fact, SubGraph, Variable};

pub fn render_to<W: Write>(graph: &SubGraph, output: &mut W) {
    dot::render(graph, output).unwrap()
}

impl<'a> dot::Labeller<'a, Fact, Edge> for SubGraph {
    //TODO name of the graph
    fn graph_id(&'a self) -> dot::Id<'a> {
        dot::Id::new("example1").unwrap()
    }

    fn node_id(&'a self, n: &Fact) -> dot::Id<'a> {
        dot::Id::new(format!("Fact{}", n.id)).unwrap()
    }
}

impl<'a> dot::GraphWalk<'a, Fact, Edge> for SubGraph {
    fn nodes(&self) -> dot::Nodes<'a, Fact> {
        // (assumes that |N| * 2 \approxeq |E|)
        let mut nodes = Vec::with_capacity(self.edges.len() * 2);
        for edge in &self.edges {
            match edge {
                Edge::Normal { from, to } => {
                    nodes.push(Fact { id: *from });
                    nodes.push(Fact { id: *to });
                }
                _ => {}
            }
        }
        nodes.sort();
        nodes.dedup();
        Cow::Owned(nodes)
    }

    fn edges(&'a self) -> dot::Edges<'a, Edge> {
        //let &Edges(ref edges) = self;
        let edges = &self.edges;
        Cow::Borrowed(&edges[..])
    }

    fn source(&self, e: &Edge) -> Fact {
        match e {
            Edge::Normal { from, to } => Fact { id: from.clone() },
            _ => unimplemented!("Please add"),
        }
    }

    fn target(&self, e: &Edge) -> Fact {
        match e {
            Edge::Normal { from, to } => Fact { id: to.clone() },
            _ => unimplemented!("Please add"),
        }
    }
}
