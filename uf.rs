// TODO: Would using SmallIntMap be better than using Vec here?
struct EquivClass {
    ranks : Vec<uint>,
    parents : Vec<uint>
}

impl EquivClass {
    pub fn new(n : uint) -> EquivClass {
        EquivClass {
            ranks: Vec::from_elem(n, 0),
            parents: Vec::from_fn(n, |i| { i })
        }
    }

    pub fn union(&mut self, x: uint, y: uint) {
        let xroot = self.find(x);
        let yroot = self.find(y);
        if xroot == yroot {
            return
        }
        let xrank = self.ranks[xroot];
        let yrank = self.ranks[yroot];
        let ps = self.parents.as_mut_slice();
        let rs = self.ranks.as_mut_slice();
        if xrank < yrank {
            ps[xroot] = yroot;
        } else if xrank > yrank {
            ps[yroot] = xroot;
        } else {
            ps[yroot] = xroot;
            rs[xroot] = xrank + 1;
        }
    }

    pub fn find(&mut self, x: uint) -> uint {
        let p = self.parents[x];
        let newp = if p != x { self.find(p) } else { p };
        self.parents.as_mut_slice()[x] = newp;
        newp
    }
    
    pub fn find_pure(&self, x: uint) -> uint {
        self.parents.as_slice()[x]
    }
}

fn main() {
    let mut ec = EquivClass::new(10);
    ec.union(1,2);
    ec.union(2,3);
    println!("{}", ec.find(1));
    println!("{}", ec.find(2));
    println!("{}", ec.find(3));
    println!("{}", ec.find_pure(3));
}
