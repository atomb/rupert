//#![feature(exit_status)]

extern crate rust_prover;

use rust_prover::cnf;
use rust_prover::dpll;
use std::env;
use std::str;

pub fn main() {
    let vargs : Vec<String> = env::args().collect();
    if vargs.len() != 2 {
        println!("Usage: dpll <filename(s)>");
        //env::set_exit_status(1);
        return
    }
    let ref name = vargs[1];
    let mut contents : Vec<u8> = Vec::new();
    match dpll::read_file(name, &mut contents) {
        Err(e) => println!("Error reading file: {}", e),
        Ok(_) => {
            let s = str::from_utf8(contents.as_ref()).ok().unwrap();
            match cnf::parse_dimacs_formula(s) {
                None => println!("Failed to parse formula."),
                Some(f) => dpll::do_dpll(f)
            }
        }
    }
}
