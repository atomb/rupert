use std::collections::HashMap;

pub type Var = usize;
pub type NodeId = usize;
pub type Node = (Var, NodeId, NodeId);
pub struct ROBDD {
    tab: Vec<Node>,
    hash: HashMap<Node, NodeId>
}

impl ROBDD {
    pub fn new() -> ROBDD { ROBDD { tab: vec![], hash: HashMap::new() } }
    pub fn mk(&mut self, i: Var, l: NodeId, h: NodeId) -> NodeId {
        let n = (i, l, h);
        if l == h {
            return l;
        }
        match self.hash.get(&n) {
            Some(nid) => return *nid,
            None => ()
        }
        let nid = self.tab.len();
        self.tab.push(n);
        self.hash.insert(n, nid);
        return nid
    }
}
