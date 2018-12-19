use std::collections::HashMap;
use std::io;
use std::io::Write;

use batsat::BasicSolver;
use batsat::callbacks;
use batsat::clause;
use batsat::core::SolverOpts;
use batsat::interface::SolverInterface;
use batsat::lbool;

use crate::aig;
use crate::aig::MapAIG;
use crate::aig::AIG;

type VarMap = HashMap<aig::Var, clause::Var>;

fn var_to_var(v: aig::Var, solver: &mut BasicSolver, map: &mut VarMap) -> clause::Var {
    match map.get(&v) {
        Some(bv) => *bv,
        None => {
            let bv = solver.new_var_default();
            map.insert(v, bv);
            bv
        }
    }
}

fn var_to_lit(v: aig::Var, solver: &mut BasicSolver, map: &mut VarMap) -> clause::Lit {
    clause::Lit::new(var_to_var(v, solver, map), true)
}

fn lit_to_lit(l: aig::Lit, solver: &mut BasicSolver, map: &mut VarMap) -> clause::Lit {
    clause::Lit::new(var_to_var(aig::lit_to_var(l), solver, map), !aig::lit_inverted(l))
}

pub fn aig_sat(aig: &MapAIG) {
    let nvars = aig::var_to_int(aig.maxvar()) + 1;
    let nclauses = 3 * aig.num_ands() + aig.num_outputs() + 1;
    let mut solver = BasicSolver::new(SolverOpts::default(), callbacks::Basic::new());
    let mut lits : Vec<clause::Lit> = vec![];
    let mut varmap : VarMap = HashMap::new();

    // Each gate defines its LHS.
    for (v, (l, r)) in aig {
        let n = var_to_lit(v, &mut solver, &mut varmap);
        let lv = lit_to_lit(l, &mut solver, &mut varmap);
        let rv = lit_to_lit(r, &mut solver, &mut varmap);

        lits.clear();
        lits.push(!n);
        lits.push(lv);
        solver.add_clause_reuse(&mut lits);

        lits.clear();
        lits.push(!n);
        lits.push(rv);
        solver.add_clause_reuse(&mut lits);

        lits.clear();
        lits.push(n);
        lits.push(!lv);
        lits.push(!rv);
        solver.add_clause_reuse(&mut lits);
    }

    // All outputs are true.
    for l in aig.outputs() {
        let bl = lit_to_lit(l, &mut solver, &mut varmap);
        lits.clear();
        lits.push(bl);
        solver.add_clause_reuse(&mut lits);
    }

    // The constant node is false.
    let ltrue = lit_to_lit(aig::TRUE_LIT, &mut solver, &mut varmap);
    lits.clear();
    lits.push(ltrue);
    solver.add_clause_reuse(&mut lits);

    let ret = solver.solve_limited(&[]);

    if ret == lbool::TRUE {
        println!("s SATISFIABLE");
        println!("{}", solver.dimacs_model());
    } else if ret == lbool::FALSE {
        println!("s UNSATISFIABLE");
    } else {
        println!("s INDETERMINATE");
    }
}