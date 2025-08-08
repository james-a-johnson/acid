use acid::Graph;

fn main() {
    let mut g = Graph::new('A');
    g.update(|mut sg| {
        let a = sg.entry();
        let b = sg.add('B');
        let c = sg.add('C');
        let d = sg.add('D');

        sg.create_edge(a, b);
        sg.create_edge(a, c);
        sg.create_edge(c, d);
        sg.create_edge(d, c);
    });

    //      A
    //    B    C
    //           D

    // B, D, C, A
    let postorder: Vec<char> = g
        .postorder()
        .into_iter()
        .map(|n| *g.get(n).unwrap().val())
        .collect();
    println!("{postorder:?}");
}
