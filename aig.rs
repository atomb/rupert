#![allow(dead_code)] // TODO!
#![allow(unused_variables)] // TODO!
#![feature(str_words)]
#![feature(core)]

use std::collections::HashMap;
use std::str::StrExt;
use std::str::Bytes;

use AIGType::*;
pub enum AIGType { ASCII, Binary }

pub type Var = u64;
pub type Lit = u64;
pub type PosLit = u64;
pub type DiffLit = u32;

pub type Latch = (PosLit, Lit);
pub type And = (PosLit, (Lit, Lit));
pub type CompactAnd = (DiffLit, DiffLit);

struct Header {
    aigtype: AIGType,
    maxvar: u64,
    ninputs: u64,
    nlatches: u64,
    noutputs: u64,
    nands: u64
}

struct AIGER {
    header: Header,
    body: AIG,
    comments: Vec<String>
}

struct AIG {
    inputs: Vec<PosLit>,
    latches: Vec<(PosLit, Lit)>,
    outputs: Vec<Lit>,
    ands: HashMap<PosLit, (Lit, Lit)>
}

/*
struct CompactAIG {
    inputs: Vec<PosLit>,
    latches: Vec<Lit>,
    outputs: Vec<Lit>,
    ands: Vec<CompactAnd>
}
*/

/*
struct HashedAIG {
    aig: AIG,
    hash: HashMap<(Lit, Lit), Var>
}
*/

static FALSE_LIT : Lit = 0;
static TRUE_LIT  : Lit = 1;
fn lit_sign   (l: Lit) -> bool { l & 1 == 1 }
fn lit_strip  (l: Lit) -> Lit  { l & (!1) }
fn lit_not    (l: Lit) -> Lit  { l ^ 1 }
fn var_to_lit (v: Var) -> Lit  { v << 1 }
fn lit_to_var (l: Lit) -> Var  { l >> 1 }
/*
fn mk_diff_lit(l: Lit, n: PosLit) -> DiffLit {
    (var_to_lit((v - lit_to_var(l))) as u32) | ((l & 1) as u32)
}

fn compact_and(a: And) -> CompactAnd {
    match a {
        (n, (l, r)) => (mk_diff_lit(l, n), mk_diff_lit(r, n))
    }
}
*/

fn expand_and(a: CompactAnd, n: PosLit) -> And {
    match a { (ld, rd) => (n, (n + ld as u64, n + rd as u64)) }
}

fn push_delta(delta: u32, v: &mut Vec<u8>) {
    let mut tmp = delta;
    while (tmp & !0x7f) != 0 {
        v.push(((tmp & 0x7f) | 0x80) as u8);
        tmp = tmp >> 7;
    }
    v.push(tmp as u8);
}

fn pop_delta(v: &mut Bytes) -> Option<u32> {
    let mut x : u32 = 0;
    let mut i : u8  = 0;
    loop {
        match v.next() {
            Some(ch) => {
                if ch & 0x80 == 0 {
                    return Some (x | (ch << (7 * i)) as u32);
                }
                x = x | ((ch & 0x07f) << (7 * i)) as u32;
                i = i + 1;
            },
            None => return None
        }
    }
}

fn parse_lit(s: &str) -> Result<Lit, String> {
    match s.parse::<Lit>() {
        Err(_) => Err("Failed to parse literal".to_string()),
        Ok(l) => Ok(l)
    }
}

fn parse_header(l: &str) -> Result<Header, String> {
    let mut ws = l.words();
    let ty =
        match ws.next() {
            Some("aig") => Binary,
            Some("aag") => ASCII,
            _ => return Err("Invalid format identifier".to_string())
        };
    let rest: Vec<&str> = ws.collect();
    match &rest[..] {
        [mvs, nis, nls, nos, nas] => {
            let mv = try!(parse_lit(mvs));
            let ni = try!(parse_lit(nis));
            let nl = try!(parse_lit(nls));
            let no = try!(parse_lit(nos));
            let na = try!(parse_lit(nas));
            let h = Header {
                aigtype: ty,
                maxvar: mv,
                ninputs: ni,
                nlatches: nl,
                noutputs: no,
                nands: na
            };
            return Ok(h)
        },
        _ => return Err("Wrong number of words in header".to_string())
    }
}

fn parse_io(l: &str) -> Result<u64, String> {
    let ws : Vec<&str> = l.words().collect();
    match &ws[..] {
        [ns] => parse_lit(ns),
        _ => Err("Wrong number of words on I/O line.".to_string())
    }
}

fn parse_latch_ascii(l: &str) -> Result<Latch, String> {
    let ws : Vec<&str> = l.words().collect();
    match &ws[..] {
        [is, ns] => {
            let i = try!(parse_lit(is));
            let n = try!(parse_lit(ns));
            return Ok((i, n));
        },
        _ => Err("Wrong number of words on latch line.".to_string())
    }
}

fn parse_and_ascii(l: &str) -> Result<And, String> {
    let ws : Vec<&str> = l.words().collect();
    match &ws[..] {
        [ns, ls, rs] => {
            let n = try!(parse_lit(ns));
            let l = try!(parse_lit(ls));
            let r = try!(parse_lit(rs));
            return Ok((n, (l, r)));
        },
        _ => Err("Wrong number of words on gate line.".to_string())
    }
}

fn parse_latch_binary(l: &str, i: u64) -> Result<Latch, String> {
    let ws : Vec<&str> = l.words().collect();
    match &ws[..] {
        [ns] => {
            let n = try!(parse_lit(ns));
            Ok((i, n))
        }
        _ => Err("Wrong number of words on binary latch line.".to_string())
    }
}

fn parse_cand_binary(l: &mut Bytes) -> Result<CompactAnd, String> {
    match (pop_delta(l), pop_delta(l)) {
        (Some(ld), Some(rd)) => Ok ((ld, rd)),
        _ => Err("Failed to pop two deltas.".to_string())
    }
}

pub fn parse_and_binary(n: PosLit, l: &mut Bytes) -> Result<And, String> {
    let a = try!(parse_cand_binary(l));
    Ok(expand_and(a, n))
}

fn parse_aiger(l: &str) -> Result<AIGER, String> {
    let mut lns = l.lines();
    let l = try!(lns.next().ok_or("No header".to_string()));
    let h = try!(parse_header(l));
    let mut is = Vec::with_capacity(h.ninputs as usize);
    let mut ls = Vec::with_capacity(h.nlatches as usize);
    let mut os = Vec::with_capacity(h.noutputs as usize);
    let mut gs = HashMap::new(); // TODO: capacity?
    for n in 0 .. h.ninputs {
        let s = try!(lns.next().ok_or("Too few inputs".to_string()));
        let i = try!(parse_io(s));
        is.push(i);
    }
    for n in 0 .. h.nlatches {
        let s = try!(lns.next().ok_or("Too few latches".to_string()));
        let l =
            match h.aigtype {
                ASCII => try!(parse_latch_ascii(s)),
                // TODO: is the node id in the following correct?
                Binary => try!(parse_latch_binary(s, n + h.ninputs))
            };
        ls.push(l);
    }
    for n in 0 .. h.noutputs {
        let s = try!(lns.next().ok_or("Too few outputs".to_string()));
        let i = try!(parse_io(s));
        os.push(i);
    }
    match h.aigtype {
        ASCII => for n in 0 .. h.nands {
            let s = try!(lns.next().ok_or("Too few ands".to_string()));
            let (nid, a) = try!(parse_and_ascii(s));
            gs.insert(nid, a);
        },
        Binary => {
            let v = try!(lns.next().ok_or("Binary and block missing".to_string()));
            let ref mut i = v.bytes();
            for n in 0 .. h.nands {
                // TODO: is nid correct here?
                let nid = n + h.ninputs + h.nlatches + h.noutputs;
                let (nid2, a) = try!(parse_and_binary(n, i));
                gs.insert(nid2, a);
            }
        }
    };
    let aig =
        AIG {
            inputs: is,
            outputs: os,
            latches: ls,
            ands: gs
        };
    let aiger =
        AIGER {
            header: h,
            body: aig,
            comments: vec![]
        };
    Ok(aiger)
}

/*
fn main() {
}
*/
