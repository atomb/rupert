extern crate rupert;

use rupert::aig;
use rupert::aig::AIG;

use std::fs::File;
use std::io::BufRead;
use std::io::BufReader;
use std::iter::FromIterator;
use std::path::Path;

fn parse_stim<R: BufRead>(r: &mut R) -> Option<Vec<Vec<bool>>> {
    let mut vals = Vec::new();
    for l in r.lines() {
        let l = match l.ok() {
            Some(l) => l,
            None => return None,
        };
        let mut ivals = Vec::new();
        for c in l.trim().chars() {
            match c {
                '0' => ivals.push(false),
                '1' => ivals.push(true),
                _ => return None,
            }
        }
        vals.push(ivals);
    }
    return Some(vals);
}

fn bool_to_char(b: bool) -> char {
    match b {
        false => '0',
        true => '1',
    }
}

fn render(vals: &Vec<bool>) -> String {
    String::from_iter(vals.iter().map(|&b| bool_to_char(b)))
}

pub fn main() {
    let vargs: Vec<String> = std::env::args().collect();
    if vargs.len() != 3 {
        println!("Usage: aigsim <model file> <stimulus file>");
        return;
    }
    let mpath = Path::new(&vargs[1]);
    let spath = Path::new(&vargs[2]);
    let fmod = File::open(&mpath).ok().unwrap();
    let fstim = File::open(&spath).ok().unwrap();
    let mut modread = BufReader::new(fmod);
    let mut stimread = BufReader::new(fstim);
    let r1 = aig::parse_aiger(&mut modread);
    let r2 = parse_stim(&mut stimread);
    match (r1, r2) {
        (Ok(aig), Some(vals)) => for val in &vals {
            if val.len() != aig.num_inputs() {
                println!(
                    "Line has {} values but model has {} inputs.",
                    val.len(),
                    aig.num_inputs()
                );
                return;
            }
            let result = aig::eval_aig(aig.get_body(), val);
            println!(" {} {}", render(val), render(&result));
        },
        (Err(e), _) => println!("Error: {}", e),
        (_, None) => println!("Failed to parse stimulus file."),
    }
}
