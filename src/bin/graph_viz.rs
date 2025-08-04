use acid::Graph;
use std::fs::File;

fn main() -> std::io::Result<()> {
    let mut g = Graph::new("main");
    let main = g.entry_id();
    let parse = g.add("parse");
    let cleanup = g.add("cleanup");
    let init = g.add("init");
    let exec = g.add("exec");
    let make_string = g.add("make_string");
    let compare = g.add("compare");
    let printf = g.add("printf");

    g.create_edge(main, init).unwrap();
    g.create_edge(main, cleanup).unwrap();
    g.create_edge(main, parse).unwrap();
    g.create_edge(main, printf).unwrap();
    g.create_edge(parse, exec).unwrap();
    g.create_edge(init, make_string).unwrap();
    g.create_edge(exec, make_string).unwrap();
    g.create_edge(exec, compare).unwrap();
    g.create_edge(exec, printf).unwrap();

    let viz = File::create("/home/jaj/Documents/acid/viz_test.dot")?;
    g.dot_viz(viz, "cfg")?;

    Ok(())
}
