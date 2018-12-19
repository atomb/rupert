use std::fs::File;
use std::io::BufReader;
use std::io::BufWriter;
use std::path::Path;

use rupert::aig;
use rupert::aigsat;

fn file_reader(name: &String) -> BufReader<File> {
    let msg = format!("Opening {} for reading", name);
    let fin = File::open(Path::new(&name)).expect(&msg);
    BufReader::new(fin)
}

pub fn main() {
    let vargs: Vec<String> = std::env::args().collect();
    if vargs.len() != 2 {
        println!("Usage: aigsat <infile>");
        return;
    }
    let infile = &vargs[1];
    let parse_msg = format!("Parsing AIGER file {}", infile);
    let aig = aig::parse_aiger(&mut file_reader(infile)).expect(&parse_msg);
    aigsat::aig_sat(&aig.get_body());
}
