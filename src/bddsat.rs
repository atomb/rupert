use std::collections::HashMap;
use std::io;

use crate::bdd;
use crate::bdd::Var;
use crate::cnf;
use crate::cnf::Formula;
use crate::cnf::SatResult;
use crate::cnf::SatResult::*;

fn bdd_sat_to_cnf_sat(m: &HashMap<bdd::Var, bool>) -> Vec<isize> {
    let mut res = Vec::new();
    for (&Var(v), &b) in m.iter() {
        let sv = (v + 1) as isize;
        let i = if b { sv } else { -sv };
        res.push(i);
    }
    res.sort_by(|a, b| a.abs().cmp(&b.abs()));
    res
}

pub fn bddsat(f: &Formula) -> SatResult {
    let mut bdd = bdd::ROBDD::new(f.maxvar);
    let mut top = bdd::TRUE;
    for c in &f.clauses {
        let mut clf = bdd::FALSE;
        for &l in &c.lits {
            let ln = if l > 0 {
                bdd.var(Var(l as usize - 1))
            } else {
                let n = bdd.var(Var((-l) as usize - 1));
                bdd.not(n)
            };
            clf = bdd.or(ln, clf)
        }
        top = bdd.and(clf, top);
    }
    let r = bdd.anysat(top);
    match r {
        bdd::SatResult::Unsat => Unsat,
        bdd::SatResult::Sat(m) => Sat(bdd_sat_to_cnf_sat(&m)),
        bdd::SatResult::Error => panic!("SAT check error"),
    }
}

pub fn do_bddsat(f: &Formula) {
    let r = bddsat(f);
    let sr = cnf::write_sat_result(&r, &mut io::stdout());
    sr.unwrap_or_else(|e| println!("{}", e));
    let vr = cnf::write_sat_valid(f, &r, &mut io::stdout());
    vr.unwrap_or_else(|e| println!("{}", e));
}
