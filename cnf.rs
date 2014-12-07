#[deriving (Show)]
struct Clause { lits: Vec<int> }

#[deriving (Show)]
struct Formula { clauses: Vec<Clause>, maxvar: int }

#[deriving (Show)]
enum SatResult {
    Unsat,
    Sat(Vec<int>)
}

impl Formula {
    fn add_clause(&mut self, c: Clause) {
        self.maxvar = std::cmp::max(self.maxvar, max_clause_var(&c));
        self.clauses.push(c);
    }

    fn num_clauses(&self) -> uint { self.clauses.len() }
}

fn parse_dimacs_clause(l: &str) -> Option<Clause> {
    let mut ls = Vec::new();
    for w in l.words() {
        match from_str(w) {
            Some(0) => (),
            Some(l) => ls.push(l),
            None => return None
        }
    };
    return Some(Clause { lits : ls })
}

fn parse_dimacs_formula(s: &str) -> Option<Formula> {
    let mut ls = s.lines();
    let header = ls.next().unwrap_or("p cnf 0 0");
    let w = header.words().nth(3).unwrap_or("0");
    let ncs = from_str(w).unwrap_or(0);
    let cs = Vec::with_capacity(ncs);
    let mut f = Formula { clauses: cs, maxvar: 0 };
    for l in ls {
        if l.starts_with("c") {
        } else {
            match parse_dimacs_clause(l) {
                Some(c) => f.add_clause(c),
                None => return None
            }
        }
    };
    return Some(f)
}

// TODO: make this a method?

fn max_clause_var(c: &Clause) -> int {
    c.lits.iter().map(|x| { x.abs() }).max().unwrap_or(0)
}

/*
fn max_formula_var(f: &Formula) -> int {
    f.clauses.iter().map(max_clause_var).max().unwrap_or(0)
}
*/

fn render_dimacs_clause(c: &Clause, s: &mut String) {
    for l in c.lits.iter() {
        s.push_str(l.to_string().as_slice());
        s.push(' ');
    }
    s.push('0');
}

fn render_dimacs_formula(f: &Formula, s: &mut String) {
    s.push_str("p cnf ");
    s.push_str(f.maxvar.to_string().as_slice());
    s.push(' ');
    s.push_str(f.clauses.len().to_string().as_slice());
    s.push('\n');
    for c in f.clauses.iter() {
        render_dimacs_clause(c, s);
        s.push('\n');
    }
}

fn render_sat_result(r: SatResult, s: &mut String) {
    match r {
        Unsat => s.push_str("UNSAT"),
        Sat(ls) => {
            s.push_str("SAT");
            for l in ls.iter() {
                s.push(' ');
                s.push_str(l.to_string().as_slice());
            }
        }
    }
}

fn render_dimacs_clause_new(c: &Clause) -> String {
    let mut s = String::with_capacity(c.lits.len() * 8);
    render_dimacs_clause(c, &mut s);
    return s
}

fn render_dimacs_formula_new(f: &Formula) -> String {
    let maxcl = f.clauses.iter().map(|c| { c.lits.len() }).max().unwrap_or(0);
    let mut s = String::with_capacity(maxcl * f.clauses.len() * 8);
    render_dimacs_formula(f, &mut s);
    return s
}

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
