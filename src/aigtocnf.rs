use std::io;
use std::io::Write;

use crate::aig;
use crate::aig::Lit;
use crate::aig::MapAIG;
use crate::aig::AIG;

fn lit_to_int(l: Lit) -> isize {
    let n = aig::var_to_int(aig::lit_to_var(l));
    if aig::lit_inverted(l) {
        -(n + 1)
    } else {
        n + 1
    }
}

/// Direct AIG to DIMACS conversion with no intermediate data
/// structures.
pub fn aig_to_dimacs<W: Write>(aig: &MapAIG, out: &mut W) -> io::Result<()> {
    let nvars = aig::var_to_int(aig.maxvar()) + 1;
    let nclauses = 3 * aig.num_ands() + aig.num_outputs() + 1;

    writeln!(out, "p cnf {} {}", nvars, nclauses)?;

    // Each gate defines its LHS.
    for (v, (l, r)) in aig {
        let n = aig::var_to_int(v) + 1;
        let lv = lit_to_int(l);
        let rv = lit_to_int(r);
        writeln!(out, "{} {} 0", -n, lv)?;
        writeln!(out, "{} {} 0", -n, rv)?;
        writeln!(out, "{} {} {} 0", n, -lv, -rv)?;
    }

    // All outputs are true.
    for l in aig.outputs() {
        writeln!(out, "{} 0", lit_to_int(l))?;
    }

    // The constant node is false.
    writeln!(out, "{}", "-1 0")
}
