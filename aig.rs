enum AIGType { ASCII, Binary }

type latch = (uint, uint);

type gate = (uint, uint, uint);

struct Header {
    aigtype: AIGType,
    maxvar: uint,
    ninputs: uint,
    nlatches: uint,
    noutputs: uint,
    ngates: uint
}

/*
struct AIG {
    inputs: Vec<uint>,
    latches: Vec<uint>,
    outputs: Vec<uint>,
    gates: Vec<gate>
}
*/

fn parse_header(l: &str) -> Option<Header> {
    let mut ws = l.words();
    let ty =
        match ws.next() {
            Some("aig") => Binary,
            Some("aag") => ASCII,
            _ => return None
        };
    let rest: Vec<&str> = ws.collect();
    match rest.as_slice() {
        [mvs, nis, nls, nos, nas] => {
            let mv = match from_str(mvs) { None => return None, Some(x) => x };
            let ni = match from_str(nis) { None => return None, Some(x) => x };
            let nl = match from_str(nls) { None => return None, Some(x) => x };
            let no = match from_str(nos) { None => return None, Some(x) => x };
            let na = match from_str(nas) { None => return None, Some(x) => x };
            let h = Header {
                aigtype: ty,
                maxvar: mv,
                ninputs: ni,
                nlatches: nl,
                noutputs: no,
                ngates: na
            };
            return Some(h)
        },
        _ => return None
    }
}

fn parse_io(l: &str) -> Option<uint> {
    let ws : Vec<&str> = l.words().collect();
    match ws.as_slice() {
        [ns] => from_str(ns),
        _ => None
    }
}

fn parse_latch_ascii(l: &str) -> Option<latch> {
    let ws : Vec<&str> = l.words().collect();
    match ws.as_slice() {
        [is, ns] =>
            match (from_str(is), from_str(ns)) {
                (Some(i), Some(n)) => Some((i, n)),
                _ => None
            },
        _ => None
    }
}

fn parse_gate_ascii(l: &str) -> Option<gate> {
    let ws : Vec<&str> = l.words().collect();
    match ws.as_slice() {
        [ns, ls, rs] =>
            match (from_str(ns), from_str(ls), from_str(rs)) {
                (Some(n), Some(l), Some(r)) => Some((n, l, r)),
                _ => None
            },
        _ => None
    }
}

fn parse_latch_binary(l: &str, i: uint) -> Option<latch> {
    let ws : Vec<&str> = l.words().collect();
    match ws.as_slice() {
        [ns] =>
            match from_str(ns) {
                None => None,
                Some(n) => Some((i, n))
            },
        _ => None
    }
}

fn parse_gate_binary(l: &[u8]) -> Option<gate> {
    None
}

/*
fn parse_aiger(l: &str) -> Option<AIG> {
    None
}
*/

fn main() {
}
