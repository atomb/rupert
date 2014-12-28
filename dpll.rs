extern crate cnf;
use cnf::Clause;
use cnf::Formula;
use cnf::SatResult;

/*
struct Solver {
    clauses : Vec<Clause>,
    occurs  : Vec<Vec<int>>,
    maxvar  : int,
}
*/

fn is_empty_clause(c: &Clause) -> bool {
    c.lits.len() == 0
}

fn is_unit_clause(c: &Clause) -> Option<int> {
    match c.lits.as_slice() {
        [l] => Some(l),
        _ => None
    }
}

fn mk_unit_clause(l: int) -> Clause {
    Clause { lits : vec![l] }
}

fn is_all_units(f: &Formula) -> Option<Vec<int>> {
    let mut r = Vec::with_capacity(f.clauses.len());
    for c in f.clauses.iter() {
        match is_unit_clause(c) {
            Some(l) => r.push(l),
            None => return None
        }
    }
    return Some(r)
}

fn unit_clauses(f: &Formula) -> Vec<int> {
    f.clauses.iter().filter_map(is_unit_clause).collect()
}

fn pure_literals(f: &Formula) -> Vec<int> {
    use std::num;
    let mut vsum = Vec::from_elem(f.maxvar + 1, 0i);
    let mut vcount = Vec::from_elem(f.maxvar + 1, 0i);
    for c in f.clauses.iter() {
        for l in c.lits.iter() {
            let v = num::abs(*l) as uint;
            *vsum.get_mut(v) = vsum[v] + num::signum(*l);
            *vcount.get_mut(v) = vcount[v] + 1;
        }
    }
    let mut res = Vec::with_capacity(f.maxvar);
    for v in range(1, f.maxvar + 1) {
        let sum = vsum[v];
        if num::abs(sum) == vcount[v] && sum != 0 {
            res.push(v as int * num::signum(sum));
        }
    }
    return res
}

fn assign(f: &mut Formula, l: int) {
    for c in f.clauses.iter_mut() {
        if c.lits.iter().any(|ll| { *ll == l }) {
            *c = mk_unit_clause(l);
        } else {
            let lneg = -l;
            match c.lits.as_slice().position_elem(&lneg) {
                Some(i) => { c.lits.swap_remove(i); }
                None => ()
            }
        }
    }
}

// Can return a negative value, in which case the negated literal will
// be the first one to try, and only if it fails will the positive
// version be tried.
fn choose_literal(f: &Formula) -> int {
    // No clause can have more than maxvar literals
    let mut minlen = f.maxvar;
    let mut lit = 0;
    for c in f.clauses.iter() {
        if c.lits.len() < minlen && c.lits.len() > 1 {
            minlen = c.lits.len();
            lit = *c.lits.as_slice().head().unwrap();
        }
    }
    return lit
}

fn dpll(f: &mut Formula) -> SatResult {
    if f.clauses.iter().any(is_empty_clause) { return cnf::Unsat };
    match is_all_units(f) {
        Some(ls) => cnf::Sat(ls),
        None => {
            //println!("{}", f);
            for l in unit_clauses(f).iter()  { assign(f, *l) };
            for l in pure_literals(f).iter() { assign(f, *l) };
            //println!("{}", f);
            let l = choose_literal(f);
            //println!("{}", l);
            let mut fcopy = f.clone();
            assign(f, l);
            assign(&mut fcopy, -l);
            match dpll(f) { cnf::Unsat => dpll(&mut fcopy), r => r }
        }
    }
}

fn read_file(file: &String) -> std::io::IoResult<String> {
    let path = &Path::new(file.as_slice());
    let ref mut fh = std::io::File::open(path);
    fh.read_to_string()
}

fn do_dpll(f: Formula) {
    let mut f0 = f;
    let r = cnf::render_sat_result_new(dpll(&mut f0));
    println!("{}", r);
}

fn main() {
    use std::os;
    let args = os::args();
    if args.len() < 2 {
        println!("Usage: dpll <filename(s)>");
        os::set_exit_status(1);
        return
    }
    let files = args.as_slice().tail();
    for file in files.iter() {
        let mcontents = read_file(file);
        match mcontents {
            Err(e) => println!("Error reading file: {}", e),
            Ok(contents) => {
                match cnf::parse_dimacs_formula(contents.as_slice()) {
                    None => println!("Failed to parse formula."),
                    Some(f) => do_dpll(f)
                }
            }
        }
    }
}
