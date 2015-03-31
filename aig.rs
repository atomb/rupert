#![allow(dead_code)] // TODO!
#![allow(unused_variables)] // TODO!
#![feature(str_words)]
#![feature(core)]
#![feature(old_io)]

use std::collections::BTreeMap;
use std::collections::HashMap;
use std::str::StrExt;
use std::old_io::IoError;

use AIGType::*;
pub enum AIGType { ASCII, Binary }

pub type Var = u64;
pub type Lit = u64;
pub type PosLit = u64;
pub type DiffLit = u32;

pub type Latch = (PosLit, Lit);
pub type And = (PosLit, (Lit, Lit));
pub type CompactAnd = (DiffLit, DiffLit);

pub struct Header {
    aigtype: AIGType,
    maxvar: u64,
    ninputs: u64,
    nlatches: u64,
    noutputs: u64,
    nands: u64
}

pub struct AIGER {
    header: Header,
    body: AIG,
    comments: Vec<String>
}

pub struct AIG {
    inputs: Vec<PosLit>,
    latches: Vec<(PosLit, Lit)>,
    outputs: Vec<Lit>,
    ands: BTreeMap<PosLit, (Lit, Lit)>
}

/*
struct CompactAIG {
    ninputs: u64,
    nlatches: u64,
    noutputs: u64,
    ands: Vec<CompactAnd>
}
*/

pub struct HashedAIG {
    aig: AIG,
    hash: HashMap<(Lit, Lit), Var>
}

pub type ParseResult<T> = Result<T, String>;

static FALSE_LIT : Lit = 0;
static TRUE_LIT  : Lit = 1;
fn lit_sign   (l: Lit) -> bool { l & 1 == 1 }
fn lit_strip  (l: Lit) -> Lit  { l & (!1) }
fn lit_not    (l: Lit) -> Lit  { l ^ 1 }
fn var_to_lit (v: Var) -> Lit  { v << 1 }
fn lit_to_var (l: Lit) -> Var  { l >> 1 }

fn mk_diff_lit(l: Lit, n: PosLit) -> DiffLit {
    (var_to_lit((n - lit_to_var(l))) as u32) | ((l & 1) as u32)
}

fn compact_and(a: And) -> CompactAnd {
    match a {
        (n, (l, r)) => (mk_diff_lit(l, n), mk_diff_lit(r, n))
    }
}

fn expand_and(a: CompactAnd, n: PosLit) -> And {
    match a { (ld, rd) => (n, (n + ld as u64, n + rd as u64)) }
}

fn push_delta<W: Writer>(delta: u32, w: &mut W) -> Result<(), IoError> {
    let mut tmp = delta;
    while (tmp & !0x7f) != 0 {
        try!(w.write_u8(((tmp & 0x7f) | 0x80) as u8));
        tmp = tmp >> 7;
    }
    w.write_u8(tmp as u8)
}

fn pop_delta<R: Reader>(r: &mut R) -> ParseResult<u32> {
    let mut x : u32 = 0;
    let mut i : u8  = 0;
    loop {
        match r.read_byte() {
            Ok(ch) => {
                if ch & 0x80 == 0 {
                    return Ok (x | (ch << (7 * i)) as u32);
                }
                x = x | ((ch & 0x07f) << (7 * i)) as u32;
                i = i + 1;
            },
            // TODO: make the following more informative?
            Err(err) => return Err("I/O error".to_string())
        }
    }
}

fn parse_lit(s: &str) -> ParseResult<Lit> {
    match s.parse::<Lit>() {
        Err(_) => Err("Failed to parse literal".to_string()),
        Ok(l) => Ok(l)
    }
}

fn parse_header(l: String) -> ParseResult<Header> {
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

fn parse_io(l: String) -> ParseResult<u64> {
    parse_lit(l.as_slice().trim())
}

fn parse_latch_ascii(l: String) -> ParseResult<Latch> {
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

fn parse_and_ascii(l: String) -> ParseResult<And> {
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

fn parse_latch_binary(l: String, i: u64) -> ParseResult<Latch> {
    let ws : Vec<&str> = l.words().collect();
    match &ws[..] {
        [ns] => {
            let n = try!(parse_lit(ns));
            Ok((i, n))
        }
        _ => Err("Wrong number of words on binary latch line.".to_string())
    }
}

fn parse_cand_binary<R: Reader>(r: &mut R) -> ParseResult<CompactAnd> {
    let ld = try!(pop_delta(r));
    let rd = try!(pop_delta(r));
    Ok((ld, rd))
}

fn parse_and_binary<R: Reader>(n: PosLit, r: &mut R) -> ParseResult<And> {
    let a = try!(parse_cand_binary(r));
    Ok(expand_and(a, n))
}

fn read_aiger_line<R: Buffer>(r: &mut R) -> ParseResult<String> {
    match r.read_line() {
        Ok(s) => Ok(s),
        // TODO: make the following more informative?
        Err(_) => Err("I/O error reading line".to_string())
    }
}

fn parse_aiger<R: Buffer>(r: &mut R) -> ParseResult<AIGER> {
    let l = try!(read_aiger_line(r));
    let h = try!(parse_header(l));
    let mut is = Vec::with_capacity(h.ninputs as usize);
    let mut ls = Vec::with_capacity(h.nlatches as usize);
    let mut os = Vec::with_capacity(h.noutputs as usize);
    let mut gs = BTreeMap::new(); // TODO: capacity?
    for n in 0 .. h.ninputs {
        let s = try!(read_aiger_line(r));
        let i = try!(parse_io(s));
        is.push(i);
    }
    for n in 0 .. h.nlatches {
        let s = try!(read_aiger_line(r));
        let l =
            match h.aigtype {
                ASCII => try!(parse_latch_ascii(s)),
                // TODO: is the var arg in the following correct? Add 2?
                Binary =>
                    try!(parse_latch_binary(s, var_to_lit(n + h.ninputs)))
            };
        ls.push(l);
    }
    for n in 0 .. h.noutputs {
        let s = try!(read_aiger_line(r));
        let i = try!(parse_io(s));
        os.push(i);
    }
    match h.aigtype {
        ASCII => for n in 0 .. h.nands {
            let s = try!(read_aiger_line(r));
            let (nid, a) = try!(parse_and_ascii(s));
            gs.insert(nid, a);
        },
        Binary => {
            for n in 0 .. h.nands {
                // TODO: is the var arg correct here? Add 2?
                let lit = var_to_lit(n + h.ninputs + h.nlatches + h.noutputs);
                let (lit2, a) = try!(parse_and_binary(lit, r));
                gs.insert(lit2, a);
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

fn write_header<W: Writer>(h: &Header, w: &mut W) -> Result<(), IoError> {
    let typestr =
        match h.aigtype {
            ASCII => "aag",
            Binary => "aig"
        };
    writeln!(w,
             "{} {} {} {} {} {}",
             typestr,
             h.maxvar,
             h.ninputs,
             h.nlatches,
             h.noutputs,
             h.nands)
}

fn write_io<W: Writer>(v: u64, w: &mut W) -> Result<(), IoError> {
    writeln!(w, "{}", v)
}

fn write_latch_ascii<W: Writer>(l: Latch, w: &mut W) -> Result<(), IoError> {
    let (i, n) = l;
    writeln!(w, "{} {}", i, n)
}

fn write_latch_binary<W: Writer>(l: Latch, w: &mut W) -> Result<(), IoError> {
    let (_i, n) = l;
    writeln!(w, "{}", n)
}

fn write_and_ascii<W: Writer>(a: And, w: &mut W) -> Result<(), IoError> {
    let (i, (l, r)) = a;
    writeln!(w, "{} {} {}", i, l, r)
}

fn write_and_binary<W: Writer>(a: And, w: &mut W) -> Result<(), IoError> {
    let (ld, rd) = compact_and(a);
    try!(push_delta(ld, w));
    push_delta(rd, w)
}

fn write_aiger<W: Writer>(g: AIGER, w: &mut W) -> Result<(), IoError> {
    try!(write_header(&(g.header), w));
    let b = g.body;
    for i in b.inputs {
        try!(write_io(i, w));
    }
    match g.header.aigtype {
        ASCII  => for l in b.latches { try!(write_latch_ascii(l, w)); },
        Binary => for l in b.latches { try!(write_latch_binary(l, w)); }
    };
    for o in b.outputs {
        try!(write_io(o, w));
    }
    match g.header.aigtype {
        ASCII  => for l in b.ands { try!(write_and_ascii(l, w)); },
        Binary => for l in b.ands { try!(write_and_binary(l, w)); }
    };
    return Ok(())
}

pub fn copy_aiger<R: Buffer, W: Writer>(r: &mut R, w: &mut W) -> ParseResult<()> {
    let aiger = try!(parse_aiger(r));
    match write_aiger(aiger, w) {
        Ok(()) => Ok(()),
        // TODO: make the following more informative?
        Err(e) => Err("I/O error".to_string())
    }
}

/*
fn main() {
}
*/
