extern crate rust_prover;

use rust_prover::aig;

use std::fs::File;
use std::io::BufReader;
use std::io::Read;
use std::path::Path;

fn test_copy_aiger(filename: &str) -> bool {
    let ipath = Path::new(filename);
    let fin = File::open(&ipath).ok().unwrap(); // Panic = failed test
    let mut ib = BufReader::new(fin);
    let mut ivec = Vec::new();
    let size = ib.read_to_end(&mut ivec).ok().unwrap();
    let mut ovec : Vec<u8> = Vec::with_capacity(size);
    let mut islice = &ivec[..];
    let r = aig::copy_aiger(&mut islice, &mut ovec);
    match r { Ok(_) => ivec == ovec, Err(_) => false }
}

#[test]
fn test_copy_aigers() {
    // TODO: just list the files in the directory
    let aig_files = ["test-aig/JavaMD5.aig",
                     "test-aig/and.aag",
                     "test-aig/and.aig",
                     "test-aig/buffer.aag",
                     "test-aig/buffer.aig",
                     // These use liveness
                     //"test-aig/cnt1.aag",
                     //"test-aig/cnt1.aig",
                     //"test-aig/cnt1e.aag",
                     //"test-aig/cnt1e.aig",
                     "test-aig/empty.aag",
                     "test-aig/empty.aig",
                     "test-aig/false.aag",
                     "test-aig/false.aig",
                     "test-aig/halfadder.aag",
                     "test-aig/halfadder.aig",
                     "test-aig/inverter.aag",
                     "test-aig/inverter.aig",
                     // These use liveness
                     //"test-aig/notcnt1.aag",
                     //"test-aig/notcnt1.aig",
                     //"test-aig/notcnt1e.aag",
                     //"test-aig/notcnt1e.aig",
                     "test-aig/or.aag",
                     "test-aig/or.aig",
                     "test-aig/toggle-re.aag",
                     "test-aig/toggle-re.aig",
                     "test-aig/toggle.aag",
                     "test-aig/toggle.aig",
                     "test-aig/true.aag",
                     "test-aig/true.aig"];
    for f in aig_files.iter() {
        if !test_copy_aiger(f) {
            panic!("Failed to copy ".to_string() + f);
        }
    }
}
