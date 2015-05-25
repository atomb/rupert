use std::cmp;

#[derive (Debug, Clone)]
pub struct Clause { pub lits: Vec<isize> }

#[derive (Debug, Clone)]
pub struct Formula { pub clauses: Vec<Clause>, pub maxvar: usize }

#[derive (Debug)]
pub enum SatResult {
    Unsat,
    Sat(Vec<isize>)
}

impl Formula {
    pub fn add_clause(&mut self, c: Clause) {
        self.maxvar = cmp::max(self.maxvar, max_clause_var(&c));
        self.clauses.push(c);
    }

    pub fn num_clauses(&self) -> usize { self.clauses.len() }
}

fn parse_dimacs_clause(l: &str) -> Option<Clause> {
    let mut ls = Vec::new();
    for w in l.split(' ') {
        match w.trim().parse::<isize>() {
            Ok(0) => (),
            Ok(l) => ls.push(l),
            Err(_) => return None
        }
    };
    return Some(Clause { lits : ls })
}

pub fn parse_dimacs_formula(s: &str) -> Option<Formula> {
    let mut ls = s.lines().filter(|s| {
        !s.starts_with("c") &&
            !s.starts_with("%") &&
            !s.starts_with("0") &&
            !(s.len() == 0)
    });
    let header = ls.next().unwrap_or("p cnf 0 0");
    let w = header.split(' ').nth(3).unwrap_or("0");
    let ncs = w.parse::<usize>().unwrap_or(0);
    let cs = Vec::with_capacity(ncs);
    let mut f = Formula { clauses: cs, maxvar: 0 };
    for l in ls {
        match parse_dimacs_clause(l) {
            Some(c) => f.add_clause(c),
            None => return None
        }
    };
    return Some(f)
}

// TODO: make this a method?

fn max_clause_var(c: &Clause) -> usize {
    c.lits.iter().map(|x| { x.abs() }).max().unwrap_or(0) as usize
}

/*
fn max_formula_var(f: &Formula) -> isize {
    f.clauses.iter().map(max_clause_var).max().unwrap_or(0)
}
*/

pub fn render_dimacs_clause(c: &Clause, s: &mut String) {
    for l in c.lits.iter() {
        s.push_str(l.to_string().as_ref());
        s.push(' ');
    }
    s.push('0');
}

pub fn render_dimacs_formula(f: &Formula, s: &mut String) {
    s.push_str("p cnf ");
    s.push_str(f.maxvar.to_string().as_ref());
    s.push(' ');
    s.push_str(f.clauses.len().to_string().as_ref());
    s.push('\n');
    for c in f.clauses.iter() {
        render_dimacs_clause(c, s);
        s.push('\n');
    }
}

pub fn render_sat_result_new(r: SatResult) -> String {
    match r {
        SatResult::Unsat => "s UNSATISFIABLE".to_string(),
        SatResult::Sat(ls) => {
            let mut s = String::with_capacity(ls.len() * 8);
            s.push_str("s SATISFIABLE\n");
            s.push('v');
            for l in ls.iter() {
                s.push(' ');
                s.push_str(l.to_string().as_ref());
            }
            s.push_str(" 0");
            s
        }
    }
}

pub fn render_dimacs_clause_new(c: &Clause) -> String {
    let mut s = String::with_capacity(c.lits.len() * 8);
    render_dimacs_clause(c, &mut s);
    return s
}

pub fn render_dimacs_formula_new(f: &Formula) -> String {
    let maxcl = f.clauses.iter().map(|c| { c.lits.len() }).max().unwrap_or(0);
    let mut s = String::with_capacity(maxcl * f.clauses.len() * 8);
    render_dimacs_formula(f, &mut s);
    return s
}

/*
fn main() {
    let mc = parse_dimacs_clause("1 2 -3 0");
    match mc {
        None => println!("Clause parse failed."),
        Some(c) => println!("{}", render_dimacs_clause_new(&c))
    }
    let mf = parse_dimacs_formula("p cnf 6 2\n1 -2 3 0\nc blah\n-4 5 6 0");
    match mf {
        None => println!("Formula parse failed."),
        Some(f) => print!("{}", render_dimacs_formula_new(&f))
    }
}
*/
