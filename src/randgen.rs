//! A small deterministic generator of random conjunctive queries and schematic fact sets,
//! biased so the facts carry data variables and shallow compounds (so capture is actually
//! exercised). Shared by the prototype's `trie_join` differential and the kernel's
//! live-PathMap differential, so both stress the same distribution.

use crate::oracle::Conj;
use crate::term::Term;

/// A tiny xorshift RNG (deterministic, seedable).
pub struct Rng(pub u64);

impl Rng {
    pub fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    pub fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    pub fn chance(&mut self, a: usize, b: usize) -> bool {
        self.below(b) < a
    }
}

const SYMS: &[&str] = &["a", "b", "c"];
const RELS: &[(&str, usize)] = &[("e", 2), ("r", 2), ("p", 1)];

/// A random argument: a variable from `pool`, a symbol, or a shallow compound (a compound is
/// what lets a stored variable capture something non-ground).
fn gen_arg(rng: &mut Rng, pool: usize, depth: usize) -> Term {
    let r = rng.below(10);
    if r < 4 && pool > 0 {
        Term::Var(rng.below(pool) as u32)
    } else if r < 8 || depth == 0 {
        Term::sym(SYMS[rng.below(SYMS.len())])
    } else {
        let n = 1 + rng.below(2);
        let mut args = vec![Term::sym(SYMS[rng.below(SYMS.len())])];
        for _ in 0..n {
            args.push(gen_arg(rng, pool, depth - 1));
        }
        Term::App(args)
    }
}

/// A random `(rel arg..)` atom over a shared variable pool.
fn gen_atom(rng: &mut Rng, pool: usize) -> Term {
    let (rel, arity) = RELS[rng.below(RELS.len())];
    let mut args = vec![Term::sym(rel)];
    for _ in 0..arity {
        args.push(gen_arg(rng, pool, 2));
    }
    Term::App(args)
}

/// A query: 1..=3 atoms sharing a small variable pool (so they join and corefer).
pub fn gen_query(rng: &mut Rng) -> Conj {
    let pool = 1 + rng.below(3);
    let nf = 1 + rng.below(3);
    let patterns: Vec<Term> = (0..nf).map(|_| gen_atom(rng, pool)).collect();
    let mut query_vars = Vec::new();
    for p in &patterns {
        for v in p.var_ids() {
            if !query_vars.contains(&v) {
                query_vars.push(v);
            }
        }
    }
    Conj { patterns, query_vars }
}

/// A fact set: several atoms, some ground and some schematic (their variables are data-side).
pub fn gen_facts(rng: &mut Rng) -> Vec<Term> {
    let n = 3 + rng.below(6);
    (0..n)
        .map(|_| {
            let pool = if rng.chance(1, 2) { 1 + rng.below(2) } else { 0 };
            gen_atom(rng, pool)
        })
        .collect()
}
