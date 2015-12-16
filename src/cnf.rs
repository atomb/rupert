use std::cmp;
use std::io;
use std::io::Write;

#[derive (Debug, Clone)]
pub struct Clause { pub lits: Vec<isize> }

#[derive (Debug, Clone)]
pub struct Formula { pub clauses: Vec<Clause>, pub maxvar: usize }

#[derive (Debug)]
pub enum SatResult {
    Unsat,
    Sat(Vec<isize>)
}

impl Clause {
    pub fn max_var(&self) -> usize {
        self.lits.iter().map(|x| { x.abs() }).max().unwrap_or(0) as usize
    }

    pub fn is_empty(&self) -> bool { self.lits.len() == 0 }
}

impl Formula {
    pub fn add_clause(&mut self, c: Clause) {
        self.maxvar = cmp::max(self.maxvar, c.max_var());
        self.clauses.push(c);
    }

    pub fn num_clauses(&self) -> usize { self.clauses.len() }

    pub fn max_var(&self) -> usize {
        self.clauses.iter().map(|c| { c.max_var() }).max().unwrap_or(0)
    }
}

fn sat_vec_to_model(m: &Vec<isize>, maxvar: usize) -> Vec<bool> {
    let mut r = vec![false; maxvar + 1];
    for &l in m {
        r[l.abs() as usize] = l > 0;
    }
    return r
}

fn eval_clause(c: &Clause, m: &Vec<bool>) -> bool {
    c.lits.iter().any(|&l| m[l.abs() as usize] == (l > 0))
}

fn eval_formula(f: &Formula, m: &Vec<bool>) -> bool {
    f.clauses.iter().all(|c| eval_clause(c, m))
}

fn eval_formula_on_result(f: &Formula, r: &Vec<isize>) -> bool {
    eval_formula(f, &sat_vec_to_model(r, f.maxvar))
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
        match parse_dimacs_clause(l.trim()) {
            Some(c) => f.add_clause(c),
            None => return None
        }
    };
    return Some(f)
}


pub fn write_dimacs_clause<W: Write>(c: &Clause, w: &mut W)
                                     -> io::Result<()> {
    for l in &c.lits {
        try!(write!(w, "{} ", l))
    }
    write!(w, "{}", '0')
}

pub fn write_dimacs_formula<W: Write>(f: &Formula, w: &mut W)
                                      -> io::Result<()> {
    try!(writeln!(w, "p cnf {} {}", f.maxvar, f.clauses.len()));
    for c in &f.clauses {
        try!(write_dimacs_clause(c, w));
        try!(write!(w, "{}", '\n'));
    }
    return Ok(())
}

pub fn write_sat_result<W: Write>(f: &Formula, r: SatResult, w: &mut W)
                                  -> io::Result<()> {
    match r {
        SatResult::Unsat => writeln!(w, "{}", "s UNSATISFIABLE"),
        SatResult::Sat(ls) => {
            try!(writeln!(w, "{}", "s SATISFIABLE"));
            try!(write!(w, "{}", 'v'));
            for l in &ls {
                try!(write!(w, " {}", l));
            }
            try!(writeln!(w, "{}", " 0"));
            let good = eval_formula_on_result(f, &ls);
            if !good { try!(writeln!(w, "{}", "**BAD RESULT**")); }
            return Ok(());
        }
    }
}

/*
pub fn write_dimacs_clause_new<W: Write>(c: &Clause) -> String {
    let mut s = String::with_capacity(c.lits.len() * 8);
    write_dimacs_clause(c, &mut s);
    return s
}

pub fn write_dimacs_formula_new<W: Write>(f: &Formula) -> String {
    let maxcl = f.clauses.iter().map(|c| { c.lits.len() }).max().unwrap_or(0);
    let mut s = String::with_capacity(maxcl * f.clauses.len() * 8);
    write_dimacs_formula(f, &mut s);
    return s
}
    */

/*
fn main() {
    let mc = parse_dimacs_clause("1 2 -3 0");
    match mc {
        None => println!("Clause parse failed."),
        Some(c) => println!("{}", write_dimacs_clause_new(&c))
    }
    let mf = parse_dimacs_formula("p cnf 6 2\n1 -2 3 0\nc blah\n-4 5 6 0");
    match mf {
        None => println!("Formula parse failed."),
        Some(f) => print!("{}", write_dimacs_formula_new(&f))
    }
}
*/
