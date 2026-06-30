//! A byte-trie over encoded terms, with a subterm cursor, mirroring MORK's PathMap +
//! `zipper_join::SubtermCursor`. The point is fidelity to the kernel: the join built on
//! top of this (see `trie_join`) ports to the live PathMap by swapping this trie for a
//! `ReadZipper`, because the navigation primitives (`child_mask` / `descend_to_byte` /
//! `ascend_byte`) and the cursor contract (`first` / `key` / `next` / `seek`) are the same.
//!
//! The encoding is MORK's own (see `term`): prefix-free, so a complete subterm has a
//! definite byte span. A stored variable is a one-byte wildcard (`NewVar` `0xC0`, or a
//! `VarRef`), which the retrieval in `trie_join` treats as a data variable that captures.

use crate::term::Term;
use std::collections::BTreeMap;

const TOP2: u8 = 0b1100_0000;
const TAG_ARITY: u8 = 0b0000_0000;
const TAG_VARREF: u8 = 0b1000_0000;
const NEWVAR_BYTE: u8 = 0b1100_0000;
const LOW6: u8 = 0b0011_1111;

/// A 256-bit set of present child bytes, like `pathmap::utils::ByteMask`.
#[derive(Clone, Copy, Default)]
pub struct ByteMask(pub [u64; 4]);

impl ByteMask {
    #[inline]
    fn has(&self, b: u8) -> bool {
        (self.0[(b >> 6) as usize] >> (b & 63)) & 1 == 1
    }
    /// The least set bit strictly greater than `b`, or `None`.
    fn next_bit(&self, b: u8) -> Option<u8> {
        // Within b's word, mask off bits <= (b & 63).
        let mut word = (b >> 6) as usize;
        let off = b & 63;
        if off < 63 {
            let masked = self.0[word] & !((1u128 << (off + 1)) - 1) as u64;
            if masked != 0 {
                return Some((word as u8) << 6 | masked.trailing_zeros() as u8);
            }
        }
        word += 1;
        while word < 4 {
            if self.0[word] != 0 {
                return Some((word as u8) << 6 | self.0[word].trailing_zeros() as u8);
            }
            word += 1;
        }
        None
    }
}

/// The least byte present in `mask` that is `>= k`, or `None`. Mirrors `zipper_join::least_ge`.
#[inline]
pub fn least_ge(mask: &ByteMask, k: u8) -> Option<u8> {
    if mask.has(k) {
        Some(k)
    } else {
        mask.next_bit(k)
    }
}

/// One step of the incremental subterm parse (mirrors `zipper_join::step_parse`).
#[inline]
fn step_parse(b: u8, subterms: &mut usize, payload: &mut usize) {
    if *payload > 0 {
        *payload -= 1;
    } else {
        *subterms -= 1;
        match b & TOP2 {
            TAG_ARITY => *subterms += (b & LOW6) as usize,
            TAG_VARREF => {}
            _ => {
                if b != NEWVAR_BYTE {
                    *payload += (b & LOW6) as usize;
                }
            }
        }
    }
}

/// Whether `bytes` spell exactly one complete subterm (mirrors `zipper_join::is_complete`).
#[inline]
pub fn is_complete(bytes: &[u8]) -> bool {
    let (mut subterms, mut payload) = (1usize, 0usize);
    for &b in bytes {
        step_parse(b, &mut subterms, &mut payload);
    }
    subterms == 0 && payload == 0
}

/// A byte-trie of encoded terms. Each root-to-`end` path is one stored term's bytes.
#[derive(Default)]
pub struct ByteTrie {
    children: BTreeMap<u8, ByteTrie>,
    end: bool,
}

impl ByteTrie {
    pub fn new() -> ByteTrie {
        ByteTrie::default()
    }

    pub fn insert_bytes(&mut self, bytes: &[u8]) {
        let mut node = self;
        for &b in bytes {
            node = node.children.entry(b).or_default();
        }
        node.end = true;
    }

    /// Build from terms by encoding each (the MORK byte form).
    pub fn from_terms(terms: &[Term]) -> ByteTrie {
        let mut t = ByteTrie::new();
        for term in terms {
            t.insert_bytes(&term.encode());
        }
        t
    }
}

/// A navigation cursor into a `ByteTrie`, holding the path from the root. Mirrors the subset
/// of the PathMap `ReadZipper` API the join uses.
pub struct TrieZipper<'a> {
    stack: Vec<&'a ByteTrie>,
}

impl<'a> TrieZipper<'a> {
    pub fn new(root: &'a ByteTrie) -> TrieZipper<'a> {
        TrieZipper { stack: vec![root] }
    }

    fn node(&self) -> &'a ByteTrie {
        self.stack[self.stack.len() - 1]
    }

    /// The child bytes present at the focus.
    pub fn child_mask(&self) -> ByteMask {
        let mut m = ByteMask::default();
        for &b in self.node().children.keys() {
            m.0[(b >> 6) as usize] |= 1u64 << (b & 63);
        }
        m
    }

    /// Descend along `b`; returns false (without moving) if there is no such child.
    pub fn descend_to_byte(&mut self, b: u8) -> bool {
        match self.node().children.get(&b) {
            Some(child) => {
                self.stack.push(child);
                true
            }
            None => false,
        }
    }

    pub fn ascend_byte(&mut self) {
        self.stack.pop();
    }

    pub fn depth(&self) -> usize {
        self.stack.len() - 1
    }
}

/// A cursor over the complete subterms branching from a `TrieZipper`'s focus, in ascending
/// byte order, with a leapfrog `seek`. A faithful port of `zipper_join::SubtermCursor` over
/// `TrieZipper` instead of a PathMap zipper.
pub struct SubtermCursor<'a> {
    z: TrieZipper<'a>,
    key: Vec<u8>,
    at_end: bool,
}

impl<'a> SubtermCursor<'a> {
    pub fn new(z: TrieZipper<'a>) -> SubtermCursor<'a> {
        SubtermCursor { z, key: Vec::new(), at_end: true }
    }

    fn reset_to_floor(&mut self) {
        while self.key.pop().is_some() {
            self.z.ascend_byte();
        }
        self.at_end = false;
    }

    fn complete_leftmost(&mut self) -> bool {
        while !is_complete(&self.key) {
            let mask = self.z.child_mask();
            match least_ge(&mask, 0) {
                Some(b) => {
                    self.z.descend_to_byte(b);
                    self.key.push(b);
                }
                None => return false,
            }
        }
        true
    }

    fn backtrack_then_leftmost(&mut self) -> bool {
        loop {
            let Some(last) = self.key.pop() else {
                return false;
            };
            self.z.ascend_byte();
            let mask = self.z.child_mask();
            if let Some(b) = mask.next_bit(last) {
                self.z.descend_to_byte(b);
                self.key.push(b);
                return self.complete_leftmost();
            }
        }
    }

    pub fn first(&mut self) {
        self.reset_to_floor();
        if !self.complete_leftmost() {
            self.at_end = true;
        }
    }

    pub fn next(&mut self) {
        if self.at_end {
            return;
        }
        if !self.backtrack_then_leftmost() {
            self.at_end = true;
        }
    }

    pub fn key(&self) -> Option<&[u8]> {
        if self.at_end {
            None
        } else {
            Some(&self.key)
        }
    }

    pub fn at_end(&self) -> bool {
        self.at_end
    }

    /// Position at the least subterm `>= target` (a complete subterm). Mirrors the kernel seek.
    pub fn seek(&mut self, target: &[u8]) {
        self.reset_to_floor();
        let mut ti = 0usize;
        loop {
            if is_complete(&self.key) {
                self.at_end = false;
                return;
            }
            let mask = self.z.child_mask();
            if ti < target.len() {
                let t = target[ti];
                if mask.has(t) {
                    self.z.descend_to_byte(t);
                    self.key.push(t);
                    ti += 1;
                    continue;
                }
                match mask.next_bit(t) {
                    Some(b) => {
                        self.z.descend_to_byte(b);
                        self.key.push(b);
                        if !self.complete_leftmost() {
                            self.at_end = true;
                        }
                        return;
                    }
                    None => {
                        if !self.backtrack_then_leftmost() {
                            self.at_end = true;
                        }
                        return;
                    }
                }
            } else if !self.complete_leftmost() {
                self.at_end = true;
                return;
            } else {
                return;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::parse;

    /// Enumerate every complete subterm branching at the zipper positioned after `prefix`.
    fn subterms_after(trie: &ByteTrie, prefix: &[u8]) -> Vec<Vec<u8>> {
        let mut z = TrieZipper::new(trie);
        for &b in prefix {
            assert!(z.descend_to_byte(b), "prefix not in trie");
        }
        let mut cur = SubtermCursor::new(z);
        let mut out = Vec::new();
        cur.first();
        while let Some(k) = cur.key() {
            out.push(k.to_vec());
            cur.next();
        }
        out
    }

    #[test]
    fn cursor_enumerates_columns_in_order() {
        // facts (e a b), (e a c), (e b d): under prefix [arity3, sym e], the first column is
        // {a, b}; under [.. , a] the second column is {b, c}.
        let facts = [parse("(e a b)"), parse("(e a c)"), parse("(e b d)")];
        let trie = ByteTrie::from_terms(&facts);
        let head = {
            let mut h = vec![0x03u8];
            h.extend(parse("e").encode());
            h
        };
        let col0 = subterms_after(&trie, &head);
        let a = parse("a").encode();
        let b = parse("b").encode();
        assert_eq!(col0, vec![a.clone(), b.clone()], "first column distinct values a,b");

        let mut head_a = head.clone();
        head_a.extend(&a);
        let col1 = subterms_after(&trie, &head_a);
        assert_eq!(col1, vec![b.clone(), parse("c").encode()], "second column after a: b,c");
    }

    #[test]
    fn cursor_seek_finds_ge() {
        let facts = [parse("(r a)"), parse("(r c)"), parse("(r e)")];
        let trie = ByteTrie::from_terms(&facts);
        let head = {
            let mut h = vec![0x02u8];
            h.extend(parse("r").encode());
            h
        };
        let mut z = TrieZipper::new(&trie);
        for &b in &head {
            z.descend_to_byte(b);
        }
        let mut cur = SubtermCursor::new(z);
        cur.seek(&parse("b").encode());
        assert_eq!(cur.key(), Some(parse("c").encode().as_slice()), "seek b -> c");
        cur.seek(&parse("e").encode());
        assert_eq!(cur.key(), Some(parse("e").encode().as_slice()), "seek e -> e (exact)");
    }

    #[test]
    fn wildcard_subterm_is_one_byte() {
        // A stored variable is a single NewVar byte; the cursor yields it as a 1-byte subterm.
        let facts = [parse("(r $w)")];
        let trie = ByteTrie::from_terms(&facts);
        let head = {
            let mut h = vec![0x02u8];
            h.extend(parse("r").encode());
            h
        };
        let cols = subterms_after(&trie, &head);
        assert_eq!(cols, vec![vec![NEWVAR_BYTE]], "stored var column is the NewVar byte");
    }
}
