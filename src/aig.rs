use std::cmp;
use std::collections::BTreeMap;
use std::collections::btree_map;
use std::collections::HashMap;
use std::error::Error;
use std::io;
use std::io::BufRead;
use std::io::Read;
use std::io::Write;
use std::ops::BitAnd;
use std::ops::Not;
use std::result::Result;
use std::slice;

pub enum AIGType { ASCII, Binary }
use aig::AIGType::*;

/// A variable is the basic notion in an AIG. Constants, inputs and
/// latches form the initial set of variables, and every gate defines an
/// additional variable.
#[derive (Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Var(u64);

/// A literal is a positive or negative reference to a variable.
#[derive (Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Lit(u64);

/// A literal represented as an offset from some previous literal. Note:
/// this assumes we never have more than 32 bits of difference!
#[derive (Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DiffLit(u32);

pub type Latch = (Var, Lit);
pub type And = (Var, (Lit, Lit));
pub type CompactAnd = (DiffLit, DiffLit);

pub struct Header {
    aigtype: AIGType,
    maxvar: Var,
    ninputs: usize,
    nlatches: usize,
    noutputs: usize,
    nands: usize
}

pub struct AIGER<T: AIG> {
    header: Header,
    body: T,
    symbols: Vec<String>,
    comments: Vec<String>
}

impl<A: AIG> AIGER<A> {
    pub fn new(aig: A, typ: AIGType) -> Self {
        AIGER {
            header: Header {
                aigtype: typ,
                maxvar: aig.maxvar(),
                ninputs: aig.num_inputs(),
                nlatches: aig.num_latches(),
                noutputs: aig.num_outputs(),
                nands: aig.num_ands()
            },
            body: aig,
            symbols: vec![],
            comments: vec![]
        }
    }
    pub fn add_symbol(&mut self, sym: String) {
        self.symbols.push(sym)
    }
    pub fn add_comment(&mut self, cmt: String) {
        self.comments.push(cmt)
    }

    pub fn get_body(&self) -> &A { &self.body }
    pub fn get_symbols(&self) -> &Vec<String> {
        &self.symbols
    }
    pub fn get_comments(&self) -> &Vec<String> {
        &self.comments
    }
}

/// A flexible AIG implementation. New inputs and latches can be created
/// at any time, and their variable IDs can be interspersed with those
/// of the gates.
///
/// Invariants:
///
///  * The `Vars`s appearing in `inputs`, `latches`, and `ands` must be
///  distinct.
///
///  * Every `Lit` in `latches`, `outputs`, and `ands` must refer to a
///  variable defined in exactly one of `inputs`, `latches`, or `ands`.
pub struct MapAIG {
    inputs: Vec<Var>,
    latches: BTreeMap<Var, Lit>,
    outputs: Vec<Lit>,
    // NB: this must be a BTreeMap to generate valid AIGER files without
    // an explicit sorting step.
    ands: BTreeMap<Var, (Lit, Lit)>,
    maxvar: Var
}

/// A compact representation of an AIG using only vectors. Requires all
/// inputs to come before all latches, and for both to come before all
/// gates. The first variable, index 0, is the constant variable for
/// TRUE and FALSE.
pub struct VecAIG {
    /// The first `inputs` variables after 0 are inputs.
    inputs: usize,

    /// The next `latches.len()` variables are latches, with these next
    /// literals.
    latches: Vec<Lit>,

    /// The literals in this vector are outputs.
    outputs: Vec<Lit>,

    /// Each literal in this vector refers to either inputs/latches or
    /// the outputs of other gates. The entry at index `i` of this
    /// vector corresponds to the definition of variable `i +
    /// latches.len() + inputs`.
    ands: Vec<CompactAnd>,
}

/// An AIG with an associated hash table. The hash table keeps track of
/// which pairs of inputs already exist, and only creates new gates when
/// necessary.
pub struct HashedAIG<T: AIG> {
    aig: T,
    hash: HashMap<(Lit, Lit), Var>
}

type CompactHashedAIG = HashedAIG<VecAIG>;
type CompactHashedAIGER = AIGER<CompactHashedAIG>;

/// A generic interface to AIG structures.
pub trait AIG {
    /// Add an AND gate with the given literals as inputs. Always
    /// constructs a new variable which can be used positively, but
    /// returns a literal for symmetry with the other logical
    /// operations.
    fn add_and(&mut self, l: Lit, r: Lit) -> Lit;

    /// Add an OR gate with the given literals as inputs. This function
    /// builds on conjunction and negation through the identity `l | r
    /// == ~(~l & ~r)`.
    fn add_or(&mut self, l: Lit, r: Lit) -> Lit {
        lit_not(self.add_and(lit_not(l), lit_not(r)))
    }

    /// Add an XOR gate with the given literals as inputs. This function
    /// builds on conjunction, disjunction, and negation through the
    /// identity `l ^ r == (l & ~r) | (~l & r)`.
    fn add_xor(&mut self, l: Lit, r: Lit) -> Lit {
        let l1 = self.add_and(l, lit_not(r));
        let r1 = self.add_and(lit_not(l), r);
        self.add_or(l1, r1)
    }

    /// Set the given literal as an output.
    fn add_output(&mut self, o: Lit);

    /// Retrieve the literals that feed into the gate defining the given
    /// variable.
    fn get_and_inputs(&self, v: &Var) -> (Lit, Lit);

    /*
    fn get_latch_next(&self, l: Var) -> Lit;
    */

    /// Return a vector of the variables representing the inputs of this
    /// circuit (not including latches).
    fn inputs(&self) -> Vec<Var>;

    /// Return a vector of the variables representing the latches of this
    /// circuit.
    fn latches(&self) -> Vec<Var>;

    /// Return a vector of the literals that are the outputs of this
    /// circuit.
    fn outputs(&self) -> Vec<Lit>;

    /// Return the number of inputs that this circuit has (not including
    /// latches).
    fn num_inputs(&self) -> usize;

    /// Return the number of latches that this circuit has.
    fn num_latches(&self) -> usize;

    /// Return the number of outputs that this circuit has.
    fn num_outputs(&self) -> usize;

    /// Return the number of gates that this circuit has.
    fn num_ands(&self) -> usize;

    /// Return the largest variable defined in this circuit.
    fn maxvar(&self) -> Var;
}

/// AIG structures dynamic enough to allow inputs and latches to be
/// added after initial construction.
pub trait DynamicAIG {
    /// Create a new input and return the variable that represents it.
    fn add_input(&mut self) -> Var;

    /// Create a new latch, with the given literal as its value for the
    /// next clock cycle, returning a variable representing the value of
    /// the latch in the current clock cycle.
    fn add_latch(&mut self, n: Lit) -> Var;
}

impl MapAIG {
    pub fn new() -> MapAIG {
        MapAIG {
            inputs: Vec::new(),
            latches: BTreeMap::new(),
            outputs: Vec::new(),
            ands: BTreeMap::new(),
            // The variable associated with TRUE and FALSE is always
            // present.
            maxvar: Var(0)
        }
    }
}

/// An iterator over the gates in a `MapAIG`.
pub struct MapAndIter<'a> {
    inner: btree_map::Iter<'a, Var, (Lit, Lit)>
}

impl<'a> Iterator for MapAndIter<'a> {
    type Item = And;
    fn next(&mut self) -> Option<And> {
        match self.inner.next() {
            None => None,
            Some((&a, &(l, r))) => Some((a, (l, r)))
        }
    }
}

impl<'a> IntoIterator for &'a MapAIG {
    type Item = And;
    type IntoIter = MapAndIter<'a>;
    fn into_iter(self) -> MapAndIter<'a> {
        MapAndIter { inner: self.ands.iter() }
    }
}

impl AIG for MapAIG {
    fn add_and(&mut self, l: Lit, r: Lit) -> Lit {
        let v = next_var(self.maxvar);
        let l1 = cmp::max(l, r);
        let r1 = cmp::min(l, r);
        self.ands.insert(v, (l1, r1));
        self.maxvar = v;
        var_to_lit(v)
    }
    fn add_output(&mut self, o: Lit) {
        self.outputs.push(o);
    }
    fn get_and_inputs(&self, v: &Var) -> (Lit, Lit) {
        self.ands[v]
    }
    fn num_inputs(&self)  -> usize  { self.inputs.len() }
    fn num_latches(&self) -> usize  { self.latches.len() }
    fn num_outputs(&self) -> usize  { self.outputs.len() }
    fn num_ands(&self)    -> usize  { self.ands.len() }
    fn maxvar(&self)      -> Var    { self.maxvar }
    fn inputs(&self)      -> Vec<Var> { self.inputs.clone() }
    fn latches(&self)     -> Vec<Var> { self.latches.keys().cloned().collect() }
    fn outputs(&self)     -> Vec<Lit> { self.outputs.clone() }
}

impl DynamicAIG for MapAIG {
    fn add_input(&mut self) -> Var {
        let v = next_var(self.maxvar);
        self.maxvar = v;
        self.inputs.push(v);
        v
    }
    fn add_latch(&mut self, n: Lit) -> Var {
        let v = next_var(self.maxvar);
        self.maxvar = v;
        self.latches.insert(v, n);
        v
    }
}

/// An iterator over the gates in a `VecAIG`.
pub struct VecAndIter<'a> {
    inner: slice::Iter<'a, CompactAnd>,
    idx: u64
}

impl<'a> Iterator for VecAndIter<'a> {
    type Item = And;
    fn next(&mut self) -> Option<And> {
        match self.inner.next() {
            None => None,
            Some(&args) => {
                let v = Var(self.idx);
                self.idx = self.idx + 1;
                Some(expand_and(args, v))
            }
        }
    }
}

impl<'a> IntoIterator for &'a VecAIG {
    type Item = And;
    type IntoIter = VecAndIter<'a>;
    fn into_iter(self) -> VecAndIter<'a> {
        VecAndIter {
            inner: self.ands.iter(),
            idx: (self.inputs + self.latches.len() + 1) as u64
        }
    }
}


impl<A: AIG> AIG for HashedAIG<A> {
    fn add_and(&mut self, l: Lit, r: Lit) -> Lit {
        let l1 = cmp::max(l, r);
        let r1 = cmp::min(l, r);
        match self.hash.get(&(l1, r1)) {
            Some(&v) => var_to_lit(v),
            None => self.aig.add_and(l1, r1)
        }
    }
    fn add_output(&mut self, o: Lit) {
        self.aig.add_output(o)
    }
    fn get_and_inputs(&self, v: &Var) -> (Lit, Lit) {
        self.aig.get_and_inputs(v)
    }
    fn num_inputs(&self)  -> usize  { self.aig.num_inputs() }
    fn num_latches(&self) -> usize  { self.aig.num_latches() }
    fn num_outputs(&self) -> usize  { self.aig.num_outputs() }
    fn num_ands(&self)    -> usize  { self.aig.num_ands() }
    fn maxvar(&self)      -> Var    { self.aig.maxvar() }
    fn inputs(&self)      -> Vec<Var> { self.aig.inputs() }
    fn latches(&self)     -> Vec<Var> { self.aig.latches() }
    fn outputs(&self)     -> Vec<Lit> { self.aig.outputs() }
}

impl<A: AIG> AIG for AIGER<A> {
    fn add_and(&mut self, l: Lit, r: Lit) -> Lit {
        self.header.nands = self.header.nands + 1;
        self.body.add_and(l, r)
    }
    fn add_output(&mut self, o: Lit) {
        self.header.noutputs = self.header.noutputs + 1;
        self.body.add_output(o)
    }
    fn get_and_inputs(&self, v: &Var) -> (Lit, Lit) {
        self.body.get_and_inputs(v)
    }
    fn num_inputs(&self)  -> usize  { self.body.num_inputs() }
    fn num_latches(&self) -> usize  { self.body.num_latches() }
    fn num_outputs(&self) -> usize  { self.body.num_outputs() }
    fn num_ands(&self)    -> usize  { self.body.num_ands() }
    fn maxvar(&self)      -> Var    { self.body.maxvar() }
    fn inputs(&self)      -> Vec<Var> { self.body.inputs() }
    fn latches(&self)     -> Vec<Var> { self.body.latches() }
    fn outputs(&self)     -> Vec<Lit> { self.body.outputs() }
}

impl VecAIG {
    pub fn new(ninputs: usize, nlatches: usize) -> VecAIG {
        VecAIG {
            inputs: ninputs,
            // By default, the next value of all latches is FALSE.
            latches: vec![Lit(0); nlatches],
            outputs: Vec::new(),
            ands: Vec::new()
        }
    }
}

impl AIG for VecAIG {
    fn add_and(&mut self, l: Lit, r: Lit) -> Lit {
        let l1 = cmp::max(l, r);
        let r1 = cmp::min(l, r);
        let v = next_var(Var(self.ands.len() as u64));
        self.ands.push(compact_and((v, (l1, r1))));
        var_to_lit(v)
    }
    fn add_output(&mut self, o: Lit) {
        self.outputs.push(o);
    }
    fn get_and_inputs(&self, &Var(v): &Var) -> (Lit, Lit) {
        let base = self.inputs as usize + self.latches.len();
        let c = self.ands[v as usize - base];
        let (_, a) = expand_and(c, Var(v));
        a
    }
    fn num_inputs(&self)  -> usize  { self.inputs as usize }
    fn num_latches(&self) -> usize  { self.latches.len() }
    fn num_outputs(&self) -> usize  { self.outputs.len() }
    fn num_ands(&self)    -> usize  { self.ands.len() }
    fn maxvar(&self)      -> Var    {
        Var((self.inputs + self.num_latches() + self.num_ands()) as u64)
    }
    fn inputs(&self)      -> Vec<Var> {
        (1..self.inputs+1).map(|i| Var(i as u64)).collect()
    }
    fn latches(&self)     -> Vec<Var> {
        let mi = self.inputs + 1;
        (mi..mi+self.latches.len()).map(|i| Var(i as u64)).collect()
    }
    fn outputs(&self)     -> Vec<Lit> { self.outputs.clone() }
}

pub type ParseResult<T> = Result<T, String>;

pub const FALSE_LIT : Lit = Lit(0);
pub const TRUE_LIT  : Lit = Lit(1);
pub const MAX_VAR : Var = Var(!0 >> 1);

/// Return true if the given literal represents a negated variable.
#[inline(always)]
pub fn lit_inverted (Lit(l): Lit) -> bool { l & 1 == 1 }

/// Strip the negation bit from a literal making it unconditionally
/// positive.
#[inline(always)]
pub fn lit_strip  (Lit(l): Lit) -> Lit  { Lit(l & (!1)) }

/// Negate a literal.
#[inline(always)]
pub fn lit_not    (Lit(l): Lit) -> Lit  { Lit(l ^ 1) }

/// Translate a variable to a positive literal.
#[inline(always)]
pub fn var_to_lit (Var(v): Var) -> Lit  { Lit(v << 1) }

/// Return the variable that a literal refers to.
#[inline(always)]
pub fn lit_to_var (Lit(l): Lit) -> Var  { Var(l >> 1) }

/// Return a version of the given literal that refers to the next larger
/// variable.
#[inline(always)]
pub fn next_lit   (Lit(l): Lit) -> Lit  { Lit(l + 2)  }

/// Return the next variable larger than the given one.
#[inline(always)]
pub fn next_var   (Var(v): Var) -> Var  { Var(v + 1)  }

/// Convert a variable to an integer. For "friend" use only.
#[inline(always)]
pub fn var_to_int (Var(v): Var) -> isize { v as isize }

/// Translate a normal gate into a compact gate.
fn compact_and((v, (Lit(l), Lit(r))): And) -> CompactAnd {
    let Lit(n) = var_to_lit(v);
    assert!(n - l <= 0xFFFFFFFF);
    assert!(l - r <= 0xFFFFFFFF);
    (DiffLit((n - l) as u32), DiffLit((l - r) as u32))
}

/// Transform a compact gate into a normal gate.
fn expand_and((DiffLit(ld), DiffLit(rd)): CompactAnd, v: Var) -> And {
    let Lit(n) = var_to_lit(v);
    (v, (Lit(n - ld as u64), Lit(n - (ld + rd) as u64)))
}

/// Add the binary AIGER encoding of a delta to the given writer.
fn push_delta<W: Write>(DiffLit(delta): DiffLit, w: &mut W) -> io::Result<()> {
    let mut tmp = delta;
    while (tmp & !0x7f) != 0 {
        try!(w.write_all(&[((tmp & 0x7f) | 0x80) as u8]));
        tmp = tmp >> 7;
    }
    w.write_all(&[tmp as u8])
}

/// Retrieve the next binary AIGER delta encoded in the given reader.
fn pop_delta<R: Read>(r: &mut R) -> ParseResult<DiffLit> {
    let mut x : u32 = 0;
    let mut i : u8  = 0;
    loop {
        match r.bytes().next() {
            Some(Ok(ch)) => {
                x = x | (((ch & 0x7f) as u32) << (7 * i));
                if ch & 0x80 == 0 { return Ok(DiffLit(x)) }
                i = i + 1;
            },
            Some(Err(e)) => return Err("I/O error: ".to_string() +
                                       e.description()),
            None => return Err("Binary AND ended prematurely.".to_string())
        }
    }
}

fn parse_u64(s: &str) -> ParseResult<u64> {
    match s.trim().parse::<u64>() {
        Err(_) => Err("Failed to parse value: ".to_string() + s),
        Ok(l) => Ok(l)
    }
}

fn parse_u64_error(os: Option<&str>, msg: &str) -> ParseResult<u64> {
    let s = try!(os.ok_or(msg.to_string()));
    let l = try!(parse_u64(s));
    Ok(l)
}

fn parse_lit_error(os: Option<&str>, msg: &str) -> ParseResult<Lit> {
    let l = try!(parse_u64_error(os, msg));
    Ok(Lit(l))
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
    let mv = try!(parse_u64_error(ws.next(), "Missing maxvar in header"));
    let ni = try!(parse_u64_error(ws.next(), "Missing input count in header"));
    let nl = try!(parse_u64_error(ws.next(), "Missing latch count in header"));
    let no = try!(parse_u64_error(ws.next(), "Missing output count in header"));
    let na = try!(parse_u64_error(ws.next(), "Missing gate count in header"));
    let h = Header {
        aigtype: ty,
        maxvar: Var(mv),
        ninputs: ni as usize,
        nlatches: nl as usize,
        noutputs: no as usize,
        nands: na as usize
    };
    if h.maxvar > MAX_VAR {
        return Err("File has too many variables".to_string());
    }
    Ok(h)
}

fn parse_input(s: &str) -> ParseResult<Var> {
    let i = try!(parse_u64(s));
    Ok(lit_to_var(Lit(i)))
}

fn parse_output(s: &str) -> ParseResult<Lit> {
    let i = try!(parse_u64(s));
    Ok(Lit(i))
}

fn parse_latch_ascii(l: &str) -> ParseResult<Latch> {
    let ref mut ws = l.split(' ');
    let l = try!(parse_lit_error(ws.next(), "Missing latch ID"));
    let n = try!(parse_lit_error(ws.next(), "Missing latch next"));
    if ws.next().is_none() {
        return Ok((lit_to_var(l), n))
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
        return Ok((lit_to_var(n), (l, r)))
    } else {
        return Err("Stray words on ASCII and line".to_string());
    }
}

fn parse_latch_binary(s: &str) -> ParseResult<Lit> {
    let ref mut ws = s.split(' ');
    let n = try!(parse_lit_error(ws.next(), "Missing latch next"));
    if ws.next().is_none() {
        return Ok(n)
    } else {
        return Err("Stray words on binary latch line".to_string());
    }
}

fn parse_cand_binary<R: Read>(r: &mut R) -> ParseResult<CompactAnd> {
    let ld = try!(pop_delta(r));
    let rd = try!(pop_delta(r));
    Ok((ld, rd))
}

fn parse_and_binary<R: Read>(v: Var, r: &mut R) -> ParseResult<And> {
    let a = try!(parse_cand_binary(r));
    Ok(expand_and(a, v))
}

fn read_aiger_line<R: BufRead>(r: &mut R) -> ParseResult<String> {
    let mut l : String = String::new();
    match r.read_line(&mut l) {
        Ok(_) => Ok(l),
        Err(e) => Err("I/O error reading line: ".to_string() +
                      e.description())
    }
}

fn parse_symbols_and_comments<R: BufRead>(r: &mut R) ->
        ParseResult<(Vec<String>, Vec<String>)> {
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
    Ok((syms, cmnts))
}

/// Parse an AIGER file, in either ASCII or binary format. This
/// constructs a MapAIG because the ASCII AIGER file format technically
/// allows weird orderings, which MapAIG supports but VecAIG does not.
pub fn parse_aiger<R: BufRead>(r: &mut R) -> ParseResult<AIGER<MapAIG>> {
    let l = try!(read_aiger_line(r));
    let h = try!(parse_header(l.as_ref()));
    let mut is = Vec::with_capacity(h.ninputs as usize);
    let mut ls = BTreeMap::new();
    let mut os = Vec::with_capacity(h.noutputs as usize);
    let mut gs = BTreeMap::new();
    let ic = h.ninputs;
    let lc = h.nlatches;
    let ac = h.nands;
    match h.aigtype {
        ASCII =>
            for _n in 0 .. ic {
                let s = try!(read_aiger_line(r));
                let i = try!(parse_input(s.as_ref()));
                is.push(i);
            },
        Binary => for n in 0 .. ic { is.push(Var(n as u64 + 1)); }
    }
    for n in 0 .. lc {
        let s = try!(read_aiger_line(r));
        let (v, nx) =
            match h.aigtype {
                ASCII => try!(parse_latch_ascii(s.as_ref())),
                Binary => {
                    let nx = try!(parse_latch_binary(s.as_ref()));
                    (Var((n + ic + 1) as u64), nx)
                }
            };
        ls.insert(v, nx);
    }
    for _n in 0 .. h.noutputs {
        let s = try!(read_aiger_line(r));
        let i = try!(parse_output(s.as_ref()));
        os.push(i);
    }
    let mut maxvar = Var(0);
    match h.aigtype {
        ASCII => for _n in 0 .. ac {
            let s = try!(read_aiger_line(r));
            let (v, a) = try!(parse_and_ascii(s.as_ref()));
            gs.insert(v, a);
            maxvar = cmp::max(maxvar, v);
        },
        Binary => {
            for n in 0 .. ac {
                let v = Var((n + ic + lc + 1) as u64);
                let (v2, a) = try!(parse_and_binary(v, r));
                gs.insert(v2, a);
                maxvar = cmp::max(maxvar, v2);
            }
        }
    };
    let (syms, cmnts) = try!(parse_symbols_and_comments(r));
    if r.bytes().count() != 0 {
        return Err("Parsing did not consume all bytes".to_string());
    }
    let aig =
        MapAIG {
            inputs: is,
            outputs: os,
            latches: ls,
            ands: gs,
            maxvar: maxvar
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

/// Parse an AIGER file, in binary format, constructing a VecAIG.
pub fn parse_aiger_vec<R: BufRead>(r: &mut R) -> ParseResult<AIGER<VecAIG>> {
    let l = try!(read_aiger_line(r));
    let h = try!(parse_header(l.as_ref()));
    let mut ls = Vec::with_capacity(h.nlatches as usize);
    let mut os = Vec::with_capacity(h.noutputs as usize);
    let mut gs = Vec::with_capacity(h.nands as usize);
    match h.aigtype {
        ASCII => return Err("ASCII format not supported by parse_aiger_vec.".to_string()),
        Binary => ()
    }
    for _n in 0 .. h.nlatches {
        let s = try!(read_aiger_line(r));
        let nx = try!(parse_latch_binary(s.as_ref()));
        ls.push(nx);
    }
    for _n in 0 .. h.noutputs {
        let s = try!(read_aiger_line(r));
        let i = try!(parse_output(s.as_ref()));
        os.push(i);
    }
    for _n in 0 .. h.nands {
        let a = try!(parse_cand_binary(r));
        gs.push(a);
    }
    let (syms, cmnts) = try!(parse_symbols_and_comments(r));
    if r.bytes().count() != 0 {
        return Err("Parsing did not consume all bytes".to_string());
    }
    let aig =
        VecAIG {
            inputs: h.ninputs,
            latches: ls,
            outputs: os,
            ands: gs,
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

/// Check the one globally valid property of an AIG: that every gate is
/// valid according to the valid_and function.
pub fn valid_aig<A: IntoIterator<Item=And>>(aig: A) -> bool {
    aig.into_iter().all(valid_and)
}

/// Check the one globally valid property of a gate in an AIG: that the
/// node being defined is greater than its left child, and its left
/// child is greater than or equal to its right child.
pub fn valid_and((v, (l, r)): And) -> bool {
    var_to_lit(v) > l && l >= r
}

fn write_header<W: Write>(h: &Header, w: &mut W) -> io::Result<()> {
    let typestr =
        match h.aigtype {
            ASCII => "aag",
            Binary => "aig"
        };
    let Var(mv) = h.maxvar;
    writeln!(w,
             "{} {} {} {} {} {}",
             typestr,
             mv,
             h.ninputs,
             h.nlatches,
             h.noutputs,
             h.nands)
}

fn write_input<W: Write>(v: Var, w: &mut W) -> io::Result<()> {
    let Lit(l) = var_to_lit(v);
    writeln!(w, "{}", l)
}

fn write_output<W: Write>(Lit(l): Lit, w: &mut W) -> io::Result<()> {
    writeln!(w, "{}", l)
}

fn write_latch_ascii<W: Write>((v, Lit(n)): Latch, w: &mut W) -> io::Result<()> {
    let Lit(l) = var_to_lit(v);
    writeln!(w, "{} {}", l, n)
}

fn write_latch_binary<W: Write>(Lit(n): Lit, w: &mut W) -> io::Result<()> {
    writeln!(w, "{}", n)
}

fn write_and_ascii<W: Write>(a: And, w: &mut W) -> io::Result<()> {
    let (v, (Lit(l), Lit(r))) = a;
    let Lit(i) = var_to_lit(v);
    writeln!(w, "{} {} {}", i, l, r)
}

fn write_and_binary<W: Write>(a: And, w: &mut W) -> io::Result<()> {
    let (ld, rd) = compact_and(a);
    write_compact_and_binary((ld, rd), w)
}

fn write_compact_and_binary<W: Write>((ld, rd): CompactAnd, w: &mut W) -> io::Result<()> {
    try!(push_delta(ld, w));
    push_delta(rd, w)
}

/// Write a MapAIG to a file in AIGER format. The choice of ASCII or
/// binary format is taken from the AIGER header.
pub fn write_aiger<W: Write>(g: &AIGER<MapAIG>, w: &mut W) -> io::Result<()> {
    try!(write_header(&(g.header), w));
    let ref b = g.body;
    match g.header.aigtype {
        ASCII => for &i in &b.inputs { try!(write_input(i, w)); },
        Binary => ()
    }
    match g.header.aigtype {
        ASCII  => for (&v, &n) in &b.latches { try!(write_latch_ascii((v, n), w)); },
        Binary => for (_, &n) in &b.latches { try!(write_latch_binary(n, w)); }
    }
    for &o in &b.outputs {
        try!(write_output(o, w));
    }
    // NB: the following would need to include an explicit sorting step
    // in order to use HashMap instead of BTreeMap.
    match g.header.aigtype {
        ASCII  => for (&n, &(l, r)) in &b.ands {
            try!(write_and_ascii((n, (l, r)), w));
        },
        Binary => for (&n, &(l, r)) in &b.ands {
            try!(write_and_binary((n, (l, r)), w));
        }
    }
    for s in &g.symbols      { try!(writeln!(w, "{}", s)) }
    if  g.comments.len() > 0 { try!(writeln!(w, "c"))     }
    for s in &g.comments     { try!(writeln!(w, "{}", s)) }
    Ok(())
}

/// Write a VecAIG to a file in binary AIGER format.
pub fn write_aiger_vec<W: Write>(g: &AIGER<VecAIG>, w: &mut W) -> io::Result<()> {
    try!(write_header(&(g.header), w));
    let ref b = g.body;
    for &n in &b.latches     { try!(write_latch_binary(n, w)); }
    for &o in &b.outputs     { try!(write_output(o, w)); }
    for &a in &b.ands        { try!(write_compact_and_binary(a, w)); }
    for s in &g.symbols      { try!(writeln!(w, "{}", s)) }
    if  g.comments.len() > 0 { try!(writeln!(w, "c"))     }
    for s in &g.comments     { try!(writeln!(w, "{}", s)) }
    Ok(())
}

/// Add a hash table to a MapAIG, consuming the original value in the
/// process.
pub fn hash_aig(aig: MapAIG) -> HashedAIG<MapAIG> {
    let mut table = HashMap::new();
    for (n, (l, r)) in &aig {
        table.insert((l, r), n);
    }
    HashedAIG {
        aig: aig,
        hash: table
    }
}

/// Drop the hash table from a hashed AIG, consuming the original value
/// in the process.
pub fn drop_hash<A: AIG>(aig: HashedAIG<A>) -> A {
    aig.aig
}

// TODO: implement Zero once it's stable
// NB: this is only reasonable for types for which clone() is a no-op
/// A `LitValue` is a value for something like a `Lit`. This is used to
/// allow parallel evaluation. A `bool` can represent the value of a
/// `Lit` in one possible world, whereas a larger word can represent
/// multiple possible worlds simultaneously.
pub trait LitValue : Not<Output=Self> + BitAnd<Output=Self> + Copy {
    fn zero() -> Self;
}

impl LitValue for bool {
    fn zero() -> bool { false }
}

impl LitValue for u64 {
    fn zero() -> u64 { 0 }
}

/// Evaluate a literal given a vector of values for each variable.
#[inline(always)]
fn eval_lit<T: LitValue>(vals: &Vec<T>, l: Lit) -> T {
    let Var(n) = lit_to_var(l);
    let val = vals[n as usize];
    if lit_inverted(l) { !val } else { val }
}

/// Evaluate an AIG on a given vector of input values. Generic over
/// input type. For `bool`, this will do standard evaluation. For larger
/// types, it will evaluate multiple possible inputs at once. For
/// instance, for a vector of `u64` values, it will yield a vector of
/// `u64` outputs, corresponding to the outputs for each set of bits in
/// the inputs.
///
/// Invariants: all variables must be in order of constants followed by
/// inputs followed by latches followed by gates, and the number of
/// values in `ins` must match the number of inputs in the AIG. TODO:
/// compare performance of this implementation to one based on a map
/// instead of a vector. If the map is similarly fast, it will depend on
/// fewer invariants.
pub fn eval_aig<T: LitValue>(aig: &MapAIG, ins: &Vec<T>) -> Vec<T> {
    let ni = aig.num_inputs();
    assert!(ni == ins.len());
    let nl = aig.num_latches();
    let no = aig.num_outputs();
    let na = aig.num_ands();
    //let mut vals = vec![LitValue::zero(); ni + nl + na + 1];
    let mut vals = Vec::with_capacity(ni + nl + na + 1);
    vals.push(LitValue::zero());
    for &v in ins   { vals.push(v); }
    for _i in 0..nl { vals.push(LitValue::zero()); }
    let mut n = ni + nl + 1;
    for (v, (r0, r1)) in aig {
        assert!(v == Var(n as u64));
        let r0v = eval_lit(&vals, r0);
        let r1v = eval_lit(&vals, r1);
        vals.push(r0v & r1v);
        n = n + 1;
    }
    let mut outs = Vec::with_capacity(no);
    for l in aig.outputs() {
        outs.push(eval_lit(&vals, l));
    }
    outs
}

/// Copy an AIG in AIGER format from a reader to a writer, preserving
/// the type.
pub fn copy_aiger<R: BufRead, W: Write>(r: &mut R,
                                        w: &mut W) -> ParseResult<()> {
    let aiger = try!(parse_aiger(r));
    match write_aiger(&aiger, w) {
        Ok(()) => Ok(()),
        Err(e) => Err("I/O error: ".to_string() + e.description())
    }
}

/// Copy an AIG in binary AIGER format from a reader to a writer.
pub fn copy_aiger_vec<R: BufRead, W: Write>(r: &mut R,
                                            w: &mut W) -> ParseResult<()> {
    let aiger = try!(parse_aiger_vec(r));
    match write_aiger_vec(&aiger, w) {
        Ok(()) => Ok(()),
        Err(e) => Err("I/O error: ".to_string() + e.description())
    }
}

#[cfg(test)]
mod tests {
    extern crate heapsize;
    extern crate quickcheck;

    use self::heapsize::HeapSizeOf;
    use self::quickcheck::quickcheck;
    use self::quickcheck::Arbitrary;
    use self::quickcheck::Gen;
    use self::quickcheck::TestResult;

    use std::io::Seek;
    use std::io::SeekFrom;

    use super::MAX_VAR;
    use super::push_delta;
    use super::pop_delta;
    use super::compact_and;
    use super::expand_and;
    use super::valid_and;
    use super::lit_to_var;
    use super::var_to_lit;
    use super::lit_strip;
    use super::parse_aiger;
    use super::parse_aiger_vec;
    use super::And;
    use super::DiffLit;
    use super::Lit;
    use super::Var;
    use super::Header;
    use super::AIGER;
    use super::AIG;
    use super::MapAIG;
    use super::VecAIG;

    impl HeapSizeOf for Header {
        fn heap_size_of_children(&self) -> usize { 0 }
    }

    impl HeapSizeOf for Var {
        fn heap_size_of_children(&self) -> usize { 0 }
    }

    impl HeapSizeOf for Lit {
        fn heap_size_of_children(&self) -> usize { 0 }
    }

    impl HeapSizeOf for DiffLit {
        fn heap_size_of_children(&self) -> usize { 0 }
    }

    impl HeapSizeOf for MapAIG {
        fn heap_size_of_children(&self) -> usize {
            self.inputs.heap_size_of_children() +
                self.latches.heap_size_of_children() +
                self.outputs.heap_size_of_children() +
                self.ands.heap_size_of_children()
        }
    }

    impl HeapSizeOf for VecAIG {
        fn heap_size_of_children(&self) -> usize {
                self.latches.heap_size_of_children() +
                self.outputs.heap_size_of_children() +
                self.ands.heap_size_of_children()
        }
    }

    impl <A: HeapSizeOf + AIG> HeapSizeOf for AIGER<A> {
        fn heap_size_of_children(&self) -> usize {
            self.header.heap_size_of_children() +
                self.body.heap_size_of_children() +
                self.symbols.heap_size_of_children() +
                self.comments.heap_size_of_children()
        }
    }

    impl Arbitrary for Lit {
        fn arbitrary<G: Gen>(g: &mut G) -> Lit { Lit(g.gen()) }
    }

    impl Arbitrary for Var {
        fn arbitrary<G: Gen>(g: &mut G) -> Var { Var(g.gen()) }
    }

    fn check_aig_size (filename: &str) -> bool {
        use std::fs::File;
        use std::io::BufReader;
        use std::path::Path;
        use std::mem;
        let ipath = Path::new(filename);
        let fin = File::open(&ipath).ok().unwrap(); // Panic = failed test
        let mut ib = BufReader::new(fin);
        let mr = parse_aiger(&mut ib);
        ib.seek(SeekFrom::Start(0));
        let vr = parse_aiger_vec(&mut ib);
        match (mr, vr) {
            (Ok(maig), Ok(vaig)) => {
                println!("Entire MapAIG: {}", maig.heap_size_of_children() +
                         mem::size_of::<MapAIG>());
                println!("MapAIG Ands: {}", maig.body.ands.heap_size_of_children());
                println!("Entire VecAIG: {}", vaig.heap_size_of_children() +
                         mem::size_of::<VecAIG>());
                println!("VecAIG Ands: {}", vaig.body.ands.heap_size_of_children());
                true
            }
            (Err(_), _) => false,
            (_, Err(_)) => false
        }
    }

    fn prop_push_pop(delta: u32) -> bool {
        let mut b : Vec<u8> = Vec::new();
        match push_delta(DiffLit(delta), &mut b) {
            Ok(_) => {
                let mut b2 = &b[..];
                match pop_delta(&mut b2) {
                    Ok(DiffLit(rdelta)) => delta == rdelta,
                    Err(_) => false,
                }
            },
            Err(_) => false,
        }
    }

    /// Note: this is only true for small variables!
    fn prop_expand_compact(a: And) -> TestResult {
        match a {
            (v, (_, _)) if !valid_and(a) || v > Var(0xFFFFFFFF) => TestResult::discard(),
            _ => TestResult::from_bool(a == expand_and(compact_and(a), a.0))
        }
    }

    fn prop_lit_var(l: Lit) -> TestResult {
        TestResult::from_bool(lit_strip(l) == var_to_lit(lit_to_var(l)))
    }

    fn prop_var_lit(v: Var) -> TestResult {
        TestResult::from_bool(v == lit_to_var(var_to_lit(v)) || v >= MAX_VAR)
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
        quickcheck(prop_push_pop as fn(u32) -> bool);
    }

    #[test]
    fn do_expand_compact() {
        assert!(!prop_expand_compact((Var(2), (Lit(1), Lit(0)))).is_failure());
        assert!(!prop_expand_compact((Var(5), (Lit(3), Lit(2)))).is_failure());
        assert!(!prop_expand_compact((Var(4096), (Lit(1024), Lit(1023)))).is_failure());
        quickcheck(prop_expand_compact as fn(And) -> TestResult);
    }

    #[test]
    fn do_lits() {
        quickcheck(prop_var_lit as fn(Var) -> TestResult);
        quickcheck(prop_lit_var as fn(Lit) -> TestResult);
    }

    #[test]
    fn test_map_aig_size() {
        let aig_files = ["test-aig/JavaMD5.aig"];
        for f in aig_files.iter() {
            if !check_aig_size(f) {
                panic!("AIG size check failed for ".to_string() + f);
            }
        }
    }
}
