use std::cmp;
use std::collections::BTreeMap;
//use std::collections::HashMap;
use std::error::Error;
use std::io;
use std::io::BufRead;
use std::io::Read;
use std::io::Write;
use std::ops::BitAnd;
use std::ops::Not;
use std::result::Result;

pub enum AIGType { ASCII, Binary }
use aig::AIGType::*;

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

pub struct AIGER<T: AIG> {
    header: Header,
    body: T,
    symbols: Vec<String>,
    comments: Vec<String>
}

pub struct MapAIG {
    inputs: Vec<PosLit>,
    latches: Vec<(PosLit, Lit)>,
    outputs: Vec<Lit>,
    ands: BTreeMap<PosLit, (Lit, Lit)>,
    maxlit: PosLit
}

/*
pub struct CompactAIG {
    ninputs: u64,
    latches: Vec<Lit>,
    outputs: Vec<Lit>,
    ands: Vec<CompactAnd>
}

pub struct HashedAIG<T> {
    aig: T,
    hash: HashMap<(Lit, Lit), Var>
}

type CompactHashedAIG = HashedAIG<CompactAIG>;
type CompactHashedAIGER = AIGER<HashedAIG<CompactAIG>>;
*/

pub trait AIG {
    fn add_and(&mut self, l: Lit, r: Lit) -> PosLit;
    fn add_output(&mut self, o: Lit);
    fn set_next(&mut self, l: PosLit, n: Lit);
    /*
    fn get_and(&self, l: PosLit) -> (Lit, Lit);
    fn get_next(&self, l: PosLit) -> Lit;
    */
    fn outputs(&self) -> &Vec<Lit>;
    fn num_inputs(&self) -> usize;
    fn num_latches(&self) -> usize;
    fn num_outputs(&self) -> usize;
    fn num_ands(&self) -> usize;
    fn maxlit(&self) -> PosLit;
    //fn eval(&self, ...) -> ...;
}

impl AIG for MapAIG {
    fn add_and(&mut self, l: Lit, r: Lit) -> PosLit {
        let n = self.maxlit + 2;
        self.ands.insert(n, (l, r));
        self.maxlit = n;
        n
    }
    fn add_output(&mut self, o: Lit) {
        self.outputs.push(o);
    }
    fn set_next(&mut self, l: PosLit, n: Lit) {
        self.latches.push((l, n));
    }
    fn num_inputs(&self)  -> usize  { self.inputs.len() }
    fn num_latches(&self) -> usize  { self.latches.len() }
    fn num_outputs(&self) -> usize  { self.outputs.len() }
    fn num_ands(&self)    -> usize  { self.ands.len() }
    fn maxlit(&self)      -> PosLit { self.maxlit }
    fn outputs(&self)     -> &Vec<Lit> { &self.outputs }
}

pub type ParseResult<T> = Result<T, String>;

pub static FALSE_LIT : Lit = 0;
pub static TRUE_LIT  : Lit = 1;
#[inline(always)]
pub fn lit_sign   (l: Lit) -> bool { l & 1 == 1 }
#[inline(always)]
pub fn lit_strip  (l: Lit) -> Lit  { l & (!1) }
#[inline(always)]
pub fn lit_not    (l: Lit) -> Lit  { l ^ 1 }
#[inline(always)]
pub fn var_to_lit (v: Var) -> Lit  { v << 1 }
#[inline(always)]
pub fn lit_to_var (l: Lit) -> Var  { l >> 1 }

fn compact_and(a: And) -> CompactAnd {
    match a { (n, (l, r)) => ((n - l) as u32, (l - r) as u32) }
}

fn expand_and(a: CompactAnd, n: PosLit) -> And {
    match a { (ld, rd) => (n, (n - ld as u64, n - (ld + rd) as u64)) }
}

pub fn input_to_var(h: &Header, i: u64) -> Option<Var> {
    if i < h.ninputs { Some(i + 1) } else { None }
}

pub fn latch_to_var(h: &Header, l: u64) -> Option<Var> {
    if l < h.nlatches { Some(l + 1 + h.ninputs) } else { None }
}

pub fn and_idx_to_var(h: &Header, l: u64) -> Option<Var> {
    if l < h.nands { Some(l + 1 + h.ninputs + h.nlatches) } else { None }
}

fn push_delta<W: Write>(delta: u32, w: &mut W) -> io::Result<()> {
    let mut tmp = delta;
    while (tmp & !0x7f) != 0 {
        try!(w.write_all(&[((tmp & 0x7f) | 0x80) as u8]));
        tmp = tmp >> 7;
    }
    w.write_all(&[tmp as u8])
}

fn pop_delta<R: Read>(r: &mut R) -> ParseResult<u32> {
    let mut x : u32 = 0;
    let mut i : u8  = 0;
    loop {
        match r.bytes().next() {
            Some(Ok(ch)) => {
                x = x | (((ch & 0x7f) as u32) << (7 * i));
                if ch & 0x80 == 0 { return Ok (x) }
                i = i + 1;
            },
            Some(Err(e)) => return Err("I/O error: ".to_string() +
                                       e.description()),
            None => return Err("Binary AND ended prematurely.".to_string())
        }
    }
}

fn parse_lit(s: &str) -> ParseResult<Lit> {
    match s.trim().parse::<u64>() {
        Err(_) => Err("Failed to parse literal: ".to_string() + s),
        Ok(l) => Ok(l)
    }
}

fn parse_lit_error(os: Option<&str>, msg: &str) -> ParseResult<Lit> {
    let s = try!(os.ok_or(msg.to_string()));
    let l = try!(parse_lit(s));
    return Ok(l)
}

fn parse_header(l: &str) -> ParseResult<Header> {
    let ref mut ws = l.split(' ');
    let ty = match ws.next() {
        Some("aig") => Binary,
        Some("aag") => ASCII,
        Some(fmt) => return Err("Invalid format identifier: ".to_string() +
                                fmt),
        None => return Err("Missing format identifier.".to_string())
    };
    let mv = try!(parse_lit_error(ws.next(), "Missing maxvar in header"));
    let ni = try!(parse_lit_error(ws.next(), "Missing input count in header"));
    let nl = try!(parse_lit_error(ws.next(), "Missing latch count in header"));
    let no = try!(parse_lit_error(ws.next(), "Missing output count in header"));
    let na = try!(parse_lit_error(ws.next(), "Missing gate count in header"));
    // Allow stray words: used for AIGER extensions
    //if ws.next().is_none() {
        let h = Header {
            aigtype: ty,
            maxvar: mv,
            ninputs: ni,
            nlatches: nl,
            noutputs: no,
            nands: na
        };
        return Ok(h)
    //} else {
    //    return Err("Stray words on header line".to_string());
    //}
}

fn parse_io(s: &str) -> ParseResult<u64> {
    parse_lit(s)
}

fn parse_latch_ascii(l: &str) -> ParseResult<Latch> {
    let ref mut ws = l.split(' ');
    let i = try!(parse_lit_error(ws.next(), "Missing latch ID"));
    let n = try!(parse_lit_error(ws.next(), "Missing latch next"));
    if ws.next().is_none() {
        return Ok((i, n))
    } else {
        return Err("Stray words on ASCII latch line".to_string());
    }
}

fn parse_and_ascii(l: &str) -> ParseResult<And> {
    let ref mut ws = l.split(' ');
    let n = try!(parse_lit_error(ws.next(), "Missing AND ID"));
    let l = try!(parse_lit_error(ws.next(), "Missing AND left"));
    let r = try!(parse_lit_error(ws.next(), "Missing AND right"));
    if ws.next().is_none() {
        return Ok((n, (l, r)))
    } else {
        return Err("Stray words on ASCII and line".to_string());
    }
}

fn parse_latch_binary(l: &str, i: u64) -> ParseResult<Latch> {
    let ref mut ws = l.split(' ');
    let n = try!(parse_lit_error(ws.next(), "Missing latch next"));
    if ws.next().is_none() {
        return Ok((i, n))
    } else {
        return Err("Stray words on binary latch line".to_string());
    }
}

fn parse_cand_binary<R: Read>(r: &mut R) -> ParseResult<CompactAnd> {
    let ld = try!(pop_delta(r));
    let rd = try!(pop_delta(r));
    Ok((ld, rd))
}

fn parse_and_binary<R: Read>(n: PosLit, r: &mut R) -> ParseResult<And> {
    let a = try!(parse_cand_binary(r));
    Ok(expand_and(a, n))
}

fn read_aiger_line<R: BufRead>(r: &mut R) -> ParseResult<String> {
    let mut l : String = String::new();
    match r.read_line(&mut l) {
        Ok(_) => Ok(l),
        Err(e) => Err("I/O error reading line: ".to_string() +
                      e.description())
    }
}

pub fn parse_aiger<R: BufRead>(r: &mut R) -> ParseResult<AIGER<MapAIG>> {
    let l = try!(read_aiger_line(r));
    let h = try!(parse_header(l.as_ref()));
    let mut is = Vec::with_capacity(h.ninputs as usize);
    let mut ls = Vec::with_capacity(h.nlatches as usize);
    let mut os = Vec::with_capacity(h.noutputs as usize);
    let mut gs = BTreeMap::new(); // TODO: capacity?
    let ic = h.ninputs;
    let lc = h.nlatches;
    let ac = h.nands;
    match h.aigtype {
        ASCII =>
            for _n in 0 .. ic {
                let s = try!(read_aiger_line(r));
                let i = try!(parse_io(s.as_ref()));
                is.push(i);
            },
        Binary => ()
    }
    for n in 0 .. lc {
        let s = try!(read_aiger_line(r));
        let l =
            match h.aigtype {
                ASCII => try!(parse_latch_ascii(s.as_ref())),
                Binary => {
                    let l0 = var_to_lit(n + ic + 1);
                    try!(parse_latch_binary(s.as_ref(), l0))
                }
            };
        ls.push(l);
    }
    for _n in 0 .. h.noutputs {
        let s = try!(read_aiger_line(r));
        let i = try!(parse_io(s.as_ref()));
        os.push(i);
    }
    let mut maxlit = 0;
    match h.aigtype {
        ASCII => for _n in 0 .. ac {
            let s = try!(read_aiger_line(r));
            let (nid, a) = try!(parse_and_ascii(s.as_ref()));
            gs.insert(nid, a);
            maxlit = cmp::max(maxlit, nid);
        },
        Binary => {
            for n in 0 .. ac {
                let lit = var_to_lit(n + ic + lc + 1);
                let (lit2, a) = try!(parse_and_binary(lit, r));
                gs.insert(lit2, a);
                maxlit = cmp::max(maxlit, lit2);
            }
        }
    };
    let mut in_comments = false;
    let mut syms = Vec::new();
    let mut cmnts = Vec::new();
    while let Ok(s) = read_aiger_line(r) {
        if s.is_empty() {
            break
        } else if in_comments {
            cmnts.push(s.trim_right().to_string());
        } else {
            match s.chars().nth(0) {
                Some('i') => syms.push(s.trim_right().to_string()),
                Some('l') => syms.push(s.trim_right().to_string()),
                Some('o') => syms.push(s.trim_right().to_string()),
                Some('c') => in_comments = true,
                Some(_) =>
                    return Err("Invalid symbol table character".to_string()),
                None =>
                    // Should never happen
                    return Err("Empty symbol table line".to_string()),
            }
        }
    }
    if r.bytes().count() != 0 {
        return Err("Parsing did not consume all bytes".to_string());
    }
    let aig =
        MapAIG {
            inputs: is,
            outputs: os,
            latches: ls,
            ands: gs,
            maxlit: maxlit
        };
    let aiger =
        AIGER {
            header: h,
            body: aig,
            symbols: syms,
            comments: cmnts
        };
    Ok(aiger)
}

/*
fn valid_aig(aig: AIG) -> bool {

}
*/

fn write_header<W: Write>(h: &Header, w: &mut W) -> io::Result<()> {
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

fn write_io<W: Write>(v: u64, w: &mut W) -> io::Result<()> {
    writeln!(w, "{}", v)
}

fn write_latch_ascii<W: Write>(l: Latch, w: &mut W) -> io::Result<()> {
    let (i, n) = l;
    writeln!(w, "{} {}", i, n)
}

fn write_latch_binary<W: Write>(l: Latch, w: &mut W) -> io::Result<()> {
    let (_i, n) = l;
    writeln!(w, "{}", n)
}

fn write_and_ascii<W: Write>(a: And, w: &mut W) -> io::Result<()> {
    let (i, (l, r)) = a;
    writeln!(w, "{} {} {}", i, l, r)
}

fn write_and_binary<W: Write>(a: And, w: &mut W) -> io::Result<()> {
    let (ld, rd) = compact_and(a);
    try!(push_delta(ld, w));
    push_delta(rd, w)
}

pub fn write_aiger<W: Write>(g: AIGER<MapAIG>, w: &mut W) -> io::Result<()> {
    try!(write_header(&(g.header), w));
    let b = g.body;
    match g.header.aigtype {
        ASCII => for i in b.inputs { try!(write_io(i, w)); },
        Binary => ()
    }
    match g.header.aigtype {
        ASCII  => for l in b.latches { try!(write_latch_ascii(l, w)); },
        Binary => for l in b.latches { try!(write_latch_binary(l, w)); }
    }
    for o in b.outputs {
        try!(write_io(o, w));
    }
    match g.header.aigtype {
        ASCII  => for l in b.ands { try!(write_and_ascii(l, w)); },
        Binary => for l in b.ands { try!(write_and_binary(l, w)); }
    }
    for s in g.symbols      { try!(writeln!(w, "{}", s)) }
    if g.comments.len() > 0 { try!(writeln!(w, "c"))     }
    for s in g.comments     { try!(writeln!(w, "{}", s)) }
    return Ok(())
}

// TODO: implement Zero once it's stable
// NB: this is only reasonable for types for which clone() is a no-op
pub trait LitValue : Clone + Not<Output=Self> + BitAnd<Output=Self> {
    fn zero() -> Self;
}

impl LitValue for u64 {
    fn zero() -> u64 { 0 }
}

// NB: this is only reasonable for types for which clone() is a no-op
#[inline(always)]
fn eval_lit<T: LitValue>(vals: &Vec<T>, l: Lit) -> T {
    let val = vals[lit_to_var(l) as usize].clone();
    if lit_sign(l) { !val } else { val }
}

pub fn eval_aig<T: LitValue>(aig: &MapAIG, ins: &Vec<T>) -> Vec<T> {
    let ni = aig.num_inputs();
    assert!(ni == ins.len());
    let nl = aig.num_latches();
    let no = aig.num_outputs();
    let na = aig.num_ands();
    let mut vals = Vec::with_capacity(ni + nl + na);
    for  v in ins   { vals.push(v.clone()); }
    for _i in 0..nl { vals.push(LitValue::zero()); }
    for (l, &(r0, r1)) in &aig.ands {
        let r0v = eval_lit(&vals, r0);
        let r1v = eval_lit(&vals, r1);
        vals[lit_to_var(*l) as usize] = r0v & r1v;
    }
    let mut outs = Vec::with_capacity(no);
    for l in aig.outputs() {
        outs.push(eval_lit(&vals, *l));
    }
    return outs
}

pub fn copy_aiger<R: BufRead, W: Write>(r: &mut R,
                                        w: &mut W) -> ParseResult<()> {
    let aiger = try!(parse_aiger(r));
    match write_aiger(aiger, w) {
        Ok(()) => Ok(()),
        Err(e) => Err("I/O error: ".to_string() + e.description())
    }
}

#[cfg(test)]
mod tests {
    use super::push_delta;
    use super::pop_delta;
    use super::compact_and;
    use super::expand_and;
    use super::And;

    fn prop_push_pop(delta: u32) -> bool {
        let mut b : Vec<u8> = Vec::new();
        match push_delta(delta, &mut b) {
            Ok(_) => {
                let mut b2 = &b[..];
                match pop_delta(&mut b2) {
                    Ok(rdelta) => delta == rdelta,
                    Err(_) => false,
                }
            },
            Err(_) => false,
        }
    }

    fn prop_expand_compact(a: And) -> bool {
        a == expand_and(compact_and(a), a.0)
    }

    #[test]
    fn do_push_pop() {
        assert!(prop_push_pop(0));
        assert!(prop_push_pop(1));
        assert!(prop_push_pop(34));
        assert!(prop_push_pop(0x7f));
        assert!(prop_push_pop(0x80));
        assert!(prop_push_pop(0xff));
        assert!(prop_push_pop(0x100));
        assert!(prop_push_pop(0xffff));
        assert!(prop_push_pop(0x10000));
        assert!(prop_push_pop(0xfffffffe));
        assert!(prop_push_pop(0xffffffff));
    }

    #[test]
    fn do_expand_compact() {
        assert!(prop_expand_compact((2, (1, 0))));
        assert!(prop_expand_compact((4096, (1024, 1023))));
    }
}
