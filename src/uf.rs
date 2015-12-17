// TODO: Would using SmallIntMap be better than using Vec here?
pub struct EquivClass {
    ranks : Vec<usize>,
    parents : Vec<usize>
}

impl EquivClass {
    pub fn new(n : usize) -> EquivClass {
        EquivClass {
            ranks: vec![0; n],
            parents: (0..n).map(|i| { i }).collect()
        }
    }

    pub fn union(&mut self, x: usize, y: usize) {
        let xroot = self.find(x);
        let yroot = self.find(y);
        if xroot == yroot {
            return
        }
        let xrank = self.ranks[xroot];
        let yrank = self.ranks[yroot];
        let ref mut ps = self.parents;
        let ref mut rs = self.ranks;
        if xrank < yrank {
            ps[xroot] = yroot;
        } else if xrank > yrank {
            ps[yroot] = xroot;
        } else {
            ps[yroot] = xroot;
            rs[xroot] = xrank + 1;
        }
    }

    pub fn find(&mut self, x: usize) -> usize {
        let p = self.parents[x];
        let newp = if p != x { self.find(p) } else { p };
        self.parents[x] = newp;
        newp
    }

    pub fn find_pure(&self, x: usize) -> usize {
        self.parents[x]
    }
}

#[cfg(test)]
mod tests {
    use super::EquivClass;

    #[test]
    fn test_one_class() {
        let mut ec = EquivClass::new(4);
        ec.union(1,2);
        ec.union(2,3);
        assert_eq!(ec.find(1), ec.find(2));
        assert_eq!(ec.find(1), ec.find(3));
        assert_eq!(ec.find(2), ec.find(3));
        assert_eq!(ec.find(1), ec.find_pure(2));
        assert_eq!(ec.find(1), ec.find_pure(3));
        assert_eq!(ec.find(2), ec.find_pure(3));
    }
}
