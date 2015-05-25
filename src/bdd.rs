use std::collections::HashMap;

type Var = usize;
type NodeId = usize;
type Node = (Var, NodeId, NodeId);
struct ROBDD {
    T: Vec<Node>,
    H: HashMap<Node, NodeId>
}

impl ROBDD {
    pub fn mk(&mut self, i: Var, l: NodeId, h: NodeId) -> NodeId {
        let n = (i, l, h);
        if l == h {
            return l;
        }
        match self.H.get(&n) {
            Some(nid) => return *nid,
            None => ()
        }
        let nid = self.T.len();
        self.T.push(n);
        self.H.insert(n, nid);
        return nid
    }
}
