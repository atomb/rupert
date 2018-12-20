use std::collections::HashMap;

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

#[derive(Debug)]
pub enum Result {
    Sat(Vec<aig::Lit>),
    Unsat,
    Unknown
}

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

pub fn aig_sat(aig: &MapAIG) -> Result {
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

    // The TRUE node is true.
    let ltrue = lit_to_lit(aig::TRUE_LIT, &mut solver, &mut varmap);
    lits.clear();
    lits.push(ltrue);
    solver.add_clause_reuse(&mut lits);

    let mut revmap = HashMap::new();
    for (av, bv) in &varmap {
        revmap.insert(bv.idx(), av);
    }

    if !solver.simplify() {
        return Result::Unsat;
    }
    let ret = solver.solve_limited(&[]);

    if ret == lbool::TRUE {
        let mut model = vec![];
        for (i, &val) in solver.get_model().iter().enumerate() {
            match revmap.get(&(i as u32)) {
                Some(v) => {
                    let l = aig::var_to_lit(**v);
                    if val == lbool::TRUE {
                        model.push(l)
                    } else if val == lbool::FALSE {
                        model.push(!l)
                    }
                }
                None => panic!("Variable not found."),
            }
        }
        return Result::Sat(model);
    } else if ret == lbool::FALSE {
        return Result::Unsat;
    } else {
        return Result::Unknown;
    }
}