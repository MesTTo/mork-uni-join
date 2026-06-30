//! Terms and MORK's exact tag-byte encoding.
//!
//! A `Term` is a symbol, a variable, or an expression (a tuple of sub-terms). This is
//! the MeTTa atom model. We serialize a term to a flat, self-delimiting byte string
//! using MORK's real tag scheme (`expr/src/lib.rs`): one leading byte per item, whose
//! top two bits classify it.
//!
//! ```text
//!   0b00xxxxxx  Arity(a)        an expression with `a` children   (a in 0..=63)
//!   0b10xxxxxx  VarRef(i)       a back-reference to variable i     (De Bruijn level)
//!   0b11000000  NewVar          a fresh variable  ($)
//!   0b11xxxxxx  SymbolSize(s)   a symbol; `s` raw bytes follow     (s in 1..=63)
//! ```
//!
//! Variables are stored *anonymously and by position* (De Bruijn levels): the first
//! `$` introduced is variable 0, the next is 1, and a repeat is `VarRef(level)`. So
//! alpha-equivalent terms (same up to renaming) encode to identical bytes, which is
//! exactly what makes the trie treat `($x $x)` and `($y $y)` as one path.

use std::collections::HashMap;
use std::fmt;

/// A term: the MeTTa atom model.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Term {
    /// A symbol / atom name, e.g. `f`, `Cons`, `:`. 1..=63 bytes.
    Sym(String),
    /// A variable, identified by an id. Ids are local names; the *encoding*
    /// canonicalizes them to De Bruijn levels, so the id value itself carries no
    /// meaning beyond "which occurrences are the same variable".
    Var(u32),
    /// An expression (tuple). Arity 0..=63. The head is just child 0; nothing is special.
    App(Vec<Term>),
}

// --- tag bytes (mirrors MORK `expr::item_byte` / `byte_item`) ---
const TOP2: u8 = 0b1100_0000;
const TAG_ARITY: u8 = 0b0000_0000;
const TAG_VARREF: u8 = 0b1000_0000;
const TAG_SYMSIZE: u8 = 0b1100_0000; // NewVar is exactly this byte (low bits 0).
const NEWVAR_BYTE: u8 = 0b1100_0000;
const LOW6: u8 = 0b0011_1111;

/// The maximum arity / symbol length / variable count, from the single-byte tag.
pub const MAX6: usize = 63;

impl Term {
    /// Convenience constructor for a symbol.
    pub fn sym(s: &str) -> Term {
        Term::Sym(s.to_string())
    }

    /// Serialize to MORK tag bytes, canonicalizing variables to De Bruijn levels.
    pub fn encode(&self) -> Vec<u8> {
        let mut out = Vec::new();
        // `intro` maps a variable id to the De Bruijn level it was first introduced at.
        let mut intro: HashMap<u32, u8> = HashMap::new();
        self.encode_into(&mut out, &mut intro);
        out
    }

    fn encode_into(&self, out: &mut Vec<u8>, intro: &mut HashMap<u32, u8>) {
        match self {
            Term::Sym(s) => {
                let b = s.as_bytes();
                assert!(
                    (1..=MAX6).contains(&b.len()),
                    "symbol length {} out of 1..=63",
                    b.len()
                );
                out.push(TAG_SYMSIZE | b.len() as u8);
                out.extend_from_slice(b);
            }
            Term::Var(id) => {
                if let Some(&level) = intro.get(id) {
                    out.push(TAG_VARREF | level); // repeat: reference the introduced level
                } else {
                    let level = intro.len();
                    assert!(level < 64, "more than 64 distinct variables");
                    intro.insert(*id, level as u8);
                    out.push(NEWVAR_BYTE); // first occurrence: anonymous `$`
                }
            }
            Term::App(args) => {
                assert!(args.len() <= MAX6, "arity {} out of 0..=63", args.len());
                out.push(TAG_ARITY | args.len() as u8);
                for a in args {
                    a.encode_into(out, intro);
                }
            }
        }
    }

    /// Parse the canonical (De Bruijn) term back from bytes. `Var` ids in the result are
    /// the De Bruijn levels, so `decode(encode(t))` is `t` in canonical variable form.
    pub fn decode(bytes: &[u8]) -> Term {
        let mut pos = 0usize;
        let mut next_level = 0u32;
        let t = Term::decode_at(bytes, &mut pos, &mut next_level);
        assert_eq!(pos, bytes.len(), "trailing bytes after a complete term");
        t
    }

    fn decode_at(bytes: &[u8], pos: &mut usize, next_level: &mut u32) -> Term {
        let b = bytes[*pos];
        *pos += 1;
        match b & TOP2 {
            TAG_ARITY => {
                let a = (b & LOW6) as usize;
                let mut args = Vec::with_capacity(a);
                for _ in 0..a {
                    args.push(Term::decode_at(bytes, pos, next_level));
                }
                Term::App(args)
            }
            TAG_VARREF => Term::Var((b & LOW6) as u32),
            _ => {
                if b == NEWVAR_BYTE {
                    let level = *next_level;
                    *next_level += 1;
                    Term::Var(level)
                } else {
                    let len = (b & LOW6) as usize;
                    let s = String::from_utf8(bytes[*pos..*pos + len].to_vec())
                        .expect("symbol bytes are utf-8 in this prototype");
                    *pos += len;
                    Term::Sym(s)
                }
            }
        }
    }

    /// True if the term contains no variables.
    pub fn is_ground(&self) -> bool {
        match self {
            Term::Sym(_) => true,
            Term::Var(_) => false,
            Term::App(a) => a.iter().all(Term::is_ground),
        }
    }

    /// Collect the distinct variable ids occurring in the term, in first-occurrence order.
    pub fn var_ids(&self) -> Vec<u32> {
        let mut seen = Vec::new();
        self.collect_vars(&mut seen);
        seen
    }

    fn collect_vars(&self, seen: &mut Vec<u32>) {
        match self {
            Term::Sym(_) => {}
            Term::Var(id) => {
                if !seen.contains(id) {
                    seen.push(*id);
                }
            }
            Term::App(a) => a.iter().for_each(|t| t.collect_vars(seen)),
        }
    }

    /// Shift every variable id by `offset`, so two terms can be made variable-disjoint
    /// before being joined (rename-apart, as in resolution / e-matching).
    pub fn rename_apart(&self, offset: u32) -> Term {
        match self {
            Term::Sym(s) => Term::Sym(s.clone()),
            Term::Var(id) => Term::Var(id + offset),
            Term::App(a) => Term::App(a.iter().map(|t| t.rename_apart(offset)).collect()),
        }
    }
}

// ---------------------------------------------------------------------------
// A tiny S-expression reader so tests and demos read like `.mm2`.
//   symbols:  foo   :   ->
//   variables: $x   (interned per parse; same name => same id)
//   tuples:   (a b (c $x))
// ---------------------------------------------------------------------------

/// Parse one S-expression. Variables are interned within this call: `$x` twice is the
/// same variable. Use [`Term::rename_apart`] to make separate patterns disjoint.
pub fn parse(s: &str) -> Term {
    let toks = tokenize(s);
    let mut pos = 0usize;
    let mut scope: HashMap<String, u32> = HashMap::new();
    let t = parse_one(&toks, &mut pos, &mut scope);
    assert_eq!(pos, toks.len(), "trailing tokens in {s:?}");
    t
}

/// Parse several S-expressions sharing one variable scope: `$f` in different strings is
/// the *same* variable. Used to build a conjunctive query whose patterns share variables.
pub fn parse_all(strs: &[&str]) -> Vec<Term> {
    let mut scope: HashMap<String, u32> = HashMap::new();
    strs.iter()
        .map(|s| {
            let toks = tokenize(s);
            let mut pos = 0usize;
            let t = parse_one(&toks, &mut pos, &mut scope);
            assert_eq!(pos, toks.len(), "trailing tokens in {s:?}");
            t
        })
        .collect()
}

/// Parse one S-expression against a caller-owned variable scope, so the same `$name`
/// keeps the same id across calls no matter which call sees it first. `parse_all` fixes
/// ids by first occurrence within its own list; this lets the caller fix them once and
/// reuse them while permuting the patterns, which is how the order-independence test
/// keeps a stable answer-tuple layout across factor and elimination orderings.
pub fn parse_with_scope(s: &str, scope: &mut HashMap<String, u32>) -> Term {
    let toks = tokenize(s);
    let mut pos = 0usize;
    let t = parse_one(&toks, &mut pos, scope);
    assert_eq!(pos, toks.len(), "trailing tokens in {s:?}");
    t
}

fn tokenize(s: &str) -> Vec<String> {
    let mut toks = Vec::new();
    let mut cur = String::new();
    for c in s.chars() {
        match c {
            '(' | ')' => {
                if !cur.is_empty() {
                    toks.push(std::mem::take(&mut cur));
                }
                toks.push(c.to_string());
            }
            c if c.is_whitespace() => {
                if !cur.is_empty() {
                    toks.push(std::mem::take(&mut cur));
                }
            }
            c => cur.push(c),
        }
    }
    if !cur.is_empty() {
        toks.push(cur);
    }
    toks
}

fn parse_one(toks: &[String], pos: &mut usize, scope: &mut HashMap<String, u32>) -> Term {
    let tok = &toks[*pos];
    *pos += 1;
    if tok == "(" {
        let mut args = Vec::new();
        while toks[*pos] != ")" {
            args.push(parse_one(toks, pos, scope));
        }
        *pos += 1; // consume ")"
        Term::App(args)
    } else if let Some(name) = tok.strip_prefix('$') {
        let next = scope.len() as u32;
        let id = *scope.entry(name.to_string()).or_insert(next);
        Term::Var(id)
    } else {
        Term::Sym(tok.clone())
    }
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Sym(s) => write!(f, "{s}"),
            Term::Var(i) => write!(f, "${i}"),
            Term::App(a) => {
                write!(f, "(")?;
                for (k, t) in a.iter().enumerate() {
                    if k > 0 {
                        write!(f, " ")?;
                    }
                    write!(f, "{t}")?;
                }
                write!(f, ")")
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ground_encoding_matches_mork_tags() {
        // (f a b): arity 3, then three length-1 symbols.
        let b = parse("(f a b)").encode();
        assert_eq!(
            b,
            vec![0x03, 0xC1, b'f', 0xC1, b'a', 0xC1, b'b'],
            "arity byte 0x03, SymbolSize(1)=0xC1 then the letter"
        );
    }

    #[test]
    fn coreference_uses_newvar_then_varref() {
        // ($x $x): arity 2, NewVar (0xC0), VarRef(0) (0x80).
        assert_eq!(parse("($x $x)").encode(), vec![0x02, 0xC0, 0x80]);
        // ($x $y): two fresh vars, NewVar twice.
        assert_eq!(parse("($x $y)").encode(), vec![0x02, 0xC0, 0xC0]);
    }

    #[test]
    fn de_bruijn_collapses_alpha_equivalent_terms() {
        // Names are stripped: ($x $x) and ($p $p) are the SAME bytes.
        assert_eq!(parse("($x $x)").encode(), parse("($p $p)").encode());
        // But the sharing structure is kept: ($x $x) != ($x $y).
        assert_ne!(parse("($x $x)").encode(), parse("($x $y)").encode());
    }

    #[test]
    fn nested_expression_encoding() {
        // (: ($f) A): arity 3 = [ ":" , ($f) , "A" ]; ($f) is arity-1 with a NewVar.
        let b = parse("(: ($f) A)").encode();
        assert_eq!(
            b,
            vec![0x03, 0xC1, b':', 0x01, 0xC0, 0xC1, b'A'],
            "arity3, sym ':', arity1+NewVar, sym 'A'"
        );
    }

    #[test]
    fn roundtrip_decode_reencode_is_stable() {
        for s in [
            "(f a b)",
            "($x $x)",
            "($x $y)",
            "(: ($f) A)",
            "(Cons $x (Cons $y Nil))",
            "()",
            "(parent (mother Alice) $who)",
        ] {
            let bytes = parse(s).encode();
            let decoded = Term::decode(&bytes);
            assert_eq!(
                decoded.encode(),
                bytes,
                "decode then re-encode must reproduce the bytes for {s:?}"
            );
        }
    }

    #[test]
    fn ground_and_vars_reported() {
        assert!(parse("(f a b)").is_ground());
        assert!(!parse("(f $x b)").is_ground());
        assert_eq!(parse("(f $x (g $y $x))").var_ids(), vec![0, 1]);
    }

    #[test]
    fn rename_apart_shifts_ids_only() {
        let p = parse("(f $x $x)"); // Var(0) twice
        let q = p.rename_apart(10);
        assert_eq!(q, Term::App(vec![Term::sym("f"), Term::Var(10), Term::Var(10)]));
        // Encoding is unaffected by the shift (De Bruijn normalizes it away).
        assert_eq!(p.encode(), q.encode());
    }
}
