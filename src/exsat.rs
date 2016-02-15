use cnf;
use cnf::Formula;
use cnf::SatResult;
use cnf::SatResult::*;

pub fn exhaust_sat(f: &Formula) -> SatResult {
    let mut current = vec!(false; f.maxvar);
    loop {
        if cnf::eval_formula(f, &current) {
            return Sat(cnf::model_to_sat_vec(&current))
        }
        // Increment.
        for b in &mut current {
            *b = !(*b);
            if *b { break; }
        }
        if current.iter().all(|&b| b == false) {
            // If the result after incrementing is zero, we've wrapped
            // around.
            return Unsat
        }
    }
}
