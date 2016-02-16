use std::collections::HashMap;

#[derive (Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Var(pub usize);

#[derive (Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct NodeId(usize);

pub type Node = (Var, NodeId, NodeId);
pub struct ROBDD {
    tab: Vec<Node>,
    hash: HashMap<Node, NodeId>
}

pub type Op = Fn(bool, bool) -> bool;
type AppTab = HashMap<(NodeId, NodeId), NodeId>;

pub static FALSE : NodeId = NodeId(0);
pub static TRUE : NodeId = NodeId(1);

pub enum SatResult {
    Unsat,
    Sat(HashMap<Var,bool>),
    Error
}

use std::fmt;
impl fmt::Display for SatResult {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            &SatResult::Unsat => write!(f, "unsat"),
            &SatResult::Error => write!(f, "error"),
            &SatResult::Sat(ref m) => {
                try!(write!(f, "sat"));
                for (&Var(v), b) in m {
                    try!(write!(f, " {}:{}", v, b));
                }
                Ok(())
            }
        }
    }
}

use std::io;
use std::io::Write;
pub fn show_table<W: Write>(t: &Vec<Node>, w: &mut W) -> io::Result<()> {
    try!(writeln!(w, " Node    Var    Low   High"));
    try!(writeln!(w, "_____  _____  _____  _____"));
    let mut i = 0;
    for &(Var(v), NodeId(l), NodeId(h)) in t {
        try!(writeln!(w, "{:>5}  {:>5}  {:>5}  {:>5}", i, v, l, h));
        i = i + 1;
    }
    Ok(())
}

impl ROBDD {
    pub fn new(nvars: usize) -> ROBDD {
        let t = vec![(Var(nvars), TRUE, FALSE), (Var(nvars), FALSE, TRUE)];
        ROBDD { tab: t, hash: HashMap::new() }
    }

    pub fn mk(&mut self, v: Var, l: NodeId, h: NodeId) -> NodeId {
        let n = (v, l, h);
        if l == h {
            return l;
        }
        if let Some(nid) = self.hash.get(&n) {
            return *nid;
        }
        let nid = NodeId(self.tab.len());
        self.tab.push(n);
        self.hash.insert(n, nid);
        nid
    }

    pub fn get(&self, NodeId(u): NodeId) -> Option<&Node> {
        self.tab.get(u)
    }

    pub fn var(&mut self, v: Var) -> NodeId {
        self.mk(v, FALSE, TRUE)
    }

    fn app(&mut self, g: &mut AppTab, op: &Op, u1: NodeId, u2: NodeId) -> NodeId {
        if u1 <= TRUE && u2 <= TRUE {
            let b = op(u1 != FALSE, u2 != FALSE);
            let n = NodeId(b as usize);
            g.insert((u1, u2), n);
            return n;
        } else if let Some(r) = g.get(&(u1, u2)) {
            return *r;
        }

        let &(v1, l1, h1) = self.get(u1).unwrap(); // TODO
        let &(v2, l2, h2) = self.get(u2).unwrap(); // TODO

        let u;
        if v1 == v2 {
            let l = self.app(g, op, l1, l2);
            let h = self.app(g, op, h1, h2);
            u = self.mk(v1, l, h);
        } else if v1 < v2 {
            let l = self.app(g, op, l1, u2);
            let h = self.app(g, op, h1, u2);
            u = self.mk(v1, l, h);
        } else /* v1 > v2 */ {
            let l = self.app(g, op, u1, l2);
            let h = self.app(g, op, u1, h2);
            u = self.mk(v2, l, h);
        }

        g.insert((u1, u2), u);
        u
    }

    pub fn apply(&mut self, op: &Op, u1: NodeId, u2: NodeId) -> NodeId {
        let mut g = HashMap::new();
        self.app(&mut g, op, u1, u2)
    }

    pub fn and(&mut self, u1: NodeId, u2: NodeId) -> NodeId {
        self.apply(&|a, b| a && b, u1, u2)
    }

    pub fn or(&mut self, u1: NodeId, u2: NodeId) -> NodeId {
        self.apply(&|a, b| a || b, u1, u2)
    }

    pub fn xor(&mut self, u1: NodeId, u2: NodeId) -> NodeId {
        self.apply(&|a, b| a ^ b, u1, u2)
    }

    pub fn eq(&mut self, u1: NodeId, u2: NodeId) -> NodeId {
        self.apply(&|a, b| a == b, u1, u2)
    }

    // NB: same as xor, but convenient
    pub fn neq(&mut self, u1: NodeId, u2: NodeId) -> NodeId {
        self.apply(&|a, b| a != b, u1, u2)
    }

    pub fn not(&mut self, u: NodeId) -> NodeId {
        let &(v, l, h) = self.get(u).unwrap(); // TODO
        self.mk(v, h, l)
    }

    fn sat(&self, acc: &mut HashMap<Var, bool>, u: NodeId) -> SatResult {
        if u == FALSE {
            return SatResult::Unsat;
        }
        if u == TRUE {
            return SatResult::Sat(acc.clone()); // TODO: can we avoid this?
        }

        if let Some(&(v, l, h)) = self.get(u) {
            if l == FALSE {
                acc.insert(v, true);
                self.sat(acc, h)
            } else {
                acc.insert(v, false);
                self.sat(acc, l)
            }
        } else {
            SatResult::Error
        }
    }

    pub fn anysat(&self, u: NodeId) -> SatResult {
        self.sat(&mut HashMap::new(), u)
    }
}

mod tests {
    #[test]
    pub fn sat_test() {
        use super::ROBDD;
        use super::TRUE;
        use super::FALSE;
        use super::Var;

        let mut bdd = ROBDD::new(4);
        let xv = Var(0);
        let yv = Var(1);
        let zv = Var(2);
        let wv = Var(3);
        let x = bdd.var(xv);
        let y = bdd.var(yv);
        let z = bdd.var(zv);
        let w = bdd.var(wv);
        let n1 = bdd.eq(x, TRUE);
        let n2 = bdd.eq(y, FALSE);
        let n3 = bdd.eq(z, TRUE);
        let n4 = bdd.eq(w, FALSE);
        let n5 = bdd.and(n1, n2);
        let n6 = bdd.and(n3, n4);
        let n7 = bdd.and(n5, n6);
        let r = bdd.anysat(n7);
        match r {
            super::SatResult::Sat(m) => {
                assert_eq!(m.len(), 4);
                assert_eq!(m.get(&xv), Some(&true));
                assert_eq!(m.get(&yv), Some(&false));
                assert_eq!(m.get(&zv), Some(&true));
                assert_eq!(m.get(&wv), Some(&false));
            }
            _ => assert!(false)
        }
    }
}
