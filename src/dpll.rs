use cnf;
use cnf::Clause;
use cnf::Formula;
use cnf::SatResult;
use cnf::SatResult::*;
use std::collections::BTreeSet;
use std::io;
use std::io::Read;

fn is_unit_clause(c: &Clause) -> Option<isize> {
    if c.lits.len() != 1 {
        None
    } else {
        Some(c.lits[0])
    }
}

fn unit_clauses(f: &Formula) -> BTreeSet<isize> {
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
    for v in 1 .. f.maxvar + 1 {
        let sum = vsum[v];
        if sum.abs() == vcount[v] && sum != 0 {
            res.push(v as isize * sum.signum());
        }
    }
    return res
}

fn assign(f: &Formula, l: isize) -> Formula {
    let mut newcs = Vec::with_capacity(f.clauses.len());
    for c in &f.clauses {
        if c.lits.binary_search(&l).is_err() {
            let lneg = -l;
            let lsnew =
                c.lits.iter().cloned().filter(|ll| *ll != lneg).collect();
            newcs.push(Clause { lits : lsnew });
        }
    }
    Formula {
        clauses: newcs,
        maxvar: f.maxvar
    }
}

// Can return a negative value, in which case the negated literal will
// be the first one to try, and only if it fails will the positive
// version be tried.
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

pub fn dpll(f0: &Formula, assgn0: &Vec<isize>) -> SatResult {
    let mut assgn = assgn0.clone();
    if f0.clauses.iter().any(|c| { c.is_empty() }) { return Unsat };
    if f0.clauses.len() == 0 {
        assgn.sort_by(|a,b| a.abs().cmp(&b.abs()));
        Sat(assgn)
    } else {
        let mut f = f0.clone();
        for l in &unit_clauses(&f)  { f = assign(&f, *l); assgn.push(*l); };
        for l in &pure_literals(&f) { f = assign(&f, *l); assgn.push(*l); };
        let l = choose_literal(&f);
        if l == 0 {
            // Couldn't find a literal to assign, so one further call
            // should finish things.
            dpll(&f, &assgn)
        } else {
            let f1 = assign(&f, l);
            let mut a1 = assgn.clone();
            a1.push(l);
            match dpll(&f1, &a1) {
                Unsat => {
                    let f2 = assign(&f, -l);
                    let mut a2 = assgn.clone();
                    a2.push(-l);
                    dpll(&f2, &a2)
                },
                r => r
            }
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

pub fn do_dpll(f: &Formula) {
    let r = dpll(f, &vec![]);
    let sr = cnf::write_sat_result(&r, &mut io::stdout());
    sr.unwrap_or_else(|e| println!("{}", e));
    let vr = cnf::write_sat_valid(f, &r, &mut io::stdout());
    vr.unwrap_or_else(|e| println!("{}", e));
}
