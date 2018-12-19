use rupert::aig;
use rupert::aigtocnf;

use std::fs::File;
//use std::io;
//use std::io::Write;
use std::io::BufReader;
use std::io::BufWriter;
use std::path::Path;

fn file_reader(name: &String) -> BufReader<File> {
    let msg = format!("Opening {} for reading", name);
    let fin = File::open(Path::new(&name)).expect(&msg);
    BufReader::new(fin)
}

fn file_writer(name: &String) -> BufWriter<File> {
    let msg = format!("Opening {} for writing", name);
    let fin = File::create(Path::new(&name)).expect(&msg);
    BufWriter::new(fin)
}

/*
fn catch_err<T>(r: io::Result<T>, msg: &String) -> T {
    match r {
        Ok(x) => x,
        Err(e) => {
            writeln!(io::stderr(), "Error: {}: {}", msg, e);
            panic!("Exiting.")
        }
    }
}
*/

pub fn main() {
    let vargs: Vec<String> = std::env::args().collect();
    if vargs.len() != 3 {
        println!("Usage: aigtocnf <infile> <outfile>");
        return;
    }
    let infile = &vargs[1];
    let parse_msg = format!("Parsing AIGER file {}", infile);
    let aig = aig::parse_aiger(&mut file_reader(infile)).expect(&parse_msg);
    let mut ob = file_writer(&vargs[2]);
    let cvt_msg = format!("Converting {} to DIMACS format", &vargs[1]);
    aigtocnf::aig_to_dimacs(&aig.get_body(), &mut ob).expect(&cvt_msg);
}
