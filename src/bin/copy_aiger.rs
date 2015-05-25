extern crate rust_prover;

use rust_prover::aig;

use std::fs::File;
use std::io::BufReader;
use std::io::BufWriter;
use std::path::Path;

fn main() {
    let vargs : Vec<String> = std::env::args().collect();
    if vargs.len() != 3 {
        println!("Usage: tests <infile> <outfile>");
        return;
    }
    let iname = &vargs[1];
    let oname = &vargs[2];
    let ipath = Path::new(iname);
    let opath = Path::new(oname);
    let fin = File::open(&ipath).ok().unwrap();
    let mut ib = BufReader::new(fin);
    let fout = File::create(&opath).ok().unwrap();
    let mut ob = BufWriter::new(fout);
    let r = aig::copy_aiger(&mut ib, &mut ob);
    match r {
        Ok(()) => println!("Success."),
        Err(e) => println!("Error: {}", e)
    }
}
