extern crate rupert;

use rupert::cnf;
use rupert::dpll;
use std::env;
use std::process;
use std::str;

pub fn main() {
    if env::args().len() < 2 {
        println!("Usage: dpll <filename(s)>");
        process::exit(1);
    }
    for name in env::args().skip(1) {
        let mut contents: Vec<u8> = Vec::new();
        println!("Processing {}", name);
        match dpll::read_file(&name, &mut contents) {
            Err(e) => println!("Error reading file {}: {}", name, e),
            Ok(_) => {
                let s = str::from_utf8(contents.as_ref()).ok().unwrap();
                match cnf::parse_dimacs_formula(s) {
                    None => println!("Failed to parse formula in {}.", name),
                    Some(f) => dpll::do_dpll(&f),
                }
            }
        }
    }
}
