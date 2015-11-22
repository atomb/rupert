use cnf;
use cnf::Clause;
use cnf::Formula;
use cnf::SatResult;
use cnf::SatResult::*;
use std::collections::BTreeSet;
use std::io;
use std::io::Read;

/*
struct Solver {
    clauses : Vec<Clause>,
    occurs  : Vec<Vec<isize>>,
    maxvar  : isize,
}
*/

fn find_lit(c: &Clause, l: isize) -> Option<usize> {
    for i in 0..c.lits.len() {
        if c.lits[i] == l { return Some(i) }
    }
    return None
}

fn is_unit_clause(c: &Clause) -> Option<isize> {
    if c.lits.len() != 1 {
        None
    } else {
        Some(c.lits[0])
    }
}

fn mk_unit_clause(l: isize) -> Clause {
    Clause { lits : vec![l] }
}

fn is_all_units(f: &Formula) -> Option<BTreeSet<isize>> {
    let mut r = BTreeSet::new();
    for c in &f.clauses {
        match is_unit_clause(c) {
            Some(l) => { r.insert(l); },
            None => return None
        }
    }
    return Some(r)
}

fn unit_clauses(f: &Formula) -> Vec<isize> {
    f.clauses.iter().filter_map(is_unit_clause).collect()
}

fn pure_literals(f: &Formula) -> Vec<isize> {
    let mut vsum : Vec<isize> = vec![0; f.maxvar + 1];
    let mut vcount : Vec<isize> = vec![0; f.maxvar + 1];
    for c in &f.clauses {
        for l in &c.lits {
            let v = l.abs() as usize;
            vsum[v] = vsum[v] + l.signum();
            vcount[v] = vcount[v] + 1;
        }
    }
    let mut res = Vec::with_capacity(f.maxvar);
    for v in (1 .. f.maxvar + 1) {
        let sum = vsum[v];
        if sum.abs() == vcount[v] && sum != 0 {
            res.push(v as isize * sum.signum());
        }
    }
    return res
}

fn assign(f: &mut Formula, l: isize) {
    for c in &mut f.clauses {
        if c.lits.iter().any(|ll| { *ll == l }) {
            *c = mk_unit_clause(l);
        } else {
            let lneg = -l;
            match find_lit(&c, lneg) {
                Some(i) => { c.lits.swap_remove(i); }
                None => ()
            }
        }
    }
}

// Can return a negative value, in which case the negated literal will
// be the first one to try, and only if it fails will the positive
// version be tried.
// TODO: this can choose a literal that has already been assigned
fn choose_literal(f: &Formula) -> isize {
    // No clause can have more than maxvar literals
    let mut minlen = f.maxvar;
    let mut lit = 0;
    for c in &f.clauses {
        if c.lits.len() < minlen && c.lits.len() > 1 {
            minlen = c.lits.len();
            lit = c.lits[0];
        }
    }
    return lit
}

pub fn dpll(f: &mut Formula) -> SatResult {
    if f.clauses.iter().any(|c| { c.is_empty() }) { return Unsat };
    match is_all_units(f) {
        Some(ls) => {
            let mut lv : Vec<isize> = ls.iter().cloned().collect();
            lv.sort_by(|a,b| (a.abs()).cmp(&b.abs()));
            Sat(lv)
        }
        None => {
            //println!("{}", f);
            for l in &unit_clauses(f)  { assign(f, *l) };
            for l in &pure_literals(f) { assign(f, *l) };
            //println!("{}", f);
            // TODO: deal with return value of 0
            let l = choose_literal(f);
            //println!("{}", l);
            let mut fcopy = f.clone();
            assign(f, l);
            assign(&mut fcopy, -l);
            match dpll(f) { Unsat => dpll(&mut fcopy), r => r }
        }
    }
}

pub fn read_file(file: &String, buf: &mut Vec<u8>) -> io::Result<usize> {
    use std::path;
    use std::fs;
    let path = &path::Path::new(file);
    let mut fh = fs::File::open(path).ok().unwrap();
    fh.read_to_end(buf)
}

pub fn do_dpll(f: Formula) {
    let mut f0 = f.clone();
    let r = dpll(&mut f0);
    match cnf::write_sat_result(&f, r, &mut io::stdout()) {
        Ok(()) => (),
        Err(e) => println!("{}", e)
    }
}
