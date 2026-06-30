//! The lazy trie capture-join must equal the sealed materialized join on everything: the
//! genuine-unification corpus, and a large random schematic differential whose facts carry
//! data variables and compounds so capture is actually exercised. Because
//! `leapfrog_unify_join` is sealed against SWI-Prolog occurs-check (tests/prolog_seal.rs),
//! agreement here transitively pins the trie join to the independent oracle too.

use mork_uni_join::corpus;
use mork_uni_join::oracle::Conj;
use mork_uni_join::term::{self, Term};
use mork_uni_join::trie_join::trie_unify_join;
use mork_uni_join::unijoin::leapfrog_unify_join;

#[test]
fn trie_join_matches_sealed_join_on_corpus() {
    for case in corpus::cases() {
        let q = Conj::parse(case.patterns);
        let space: Vec<Term> = case.facts.iter().map(|f| term::parse(f)).collect();
        let got = trie_unify_join(&q, &space);
        let want = leapfrog_unify_join(&q, &space);
        assert_eq!(got, want, "case {:?}: trie join != sealed join", case.name);
    }
}

// --- random schematic differential ---

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
    fn chance(&mut self, a: usize, b: usize) -> bool {
        self.below(b) < a
    }
}

const SYMS: &[&str] = &["a", "b", "c"];
const RELS: &[(&str, usize)] = &[("e", 2), ("r", 2), ("p", 1)];

/// A random argument term: a variable from `pool`, a symbol, or a shallow compound (which is
/// what makes a stored variable able to capture something non-ground).
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
fn gen_query(rng: &mut Rng) -> Conj {
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
fn gen_facts(rng: &mut Rng) -> Vec<Term> {
    let n = 3 + rng.below(6);
    (0..n)
        .map(|_| {
            // half the facts are schematic (carry data variables), half ground-ish.
            let pool = if rng.chance(1, 2) { 1 + rng.below(2) } else { 0 };
            gen_atom(rng, pool)
        })
        .collect()
}

#[test]
fn trie_join_matches_sealed_join_random() {
    let mut rng = Rng(0x9E3779B97F4A7C15);
    let mut nonempty = 0usize;
    let mut nonground = 0usize;
    let mut total_answers = 0usize;
    let trials = 20000;
    for i in 0..trials {
        let q = gen_query(&mut rng);
        let facts = gen_facts(&mut rng);
        let got = trie_unify_join(&q, &facts);
        let want = leapfrog_unify_join(&q, &facts);
        assert_eq!(
            got, want,
            "trial {i}: trie join != sealed join\n  query={:?}\n  facts={:?}\n  trie-only={:?}\n  leapfrog-only={:?}",
            q.patterns.iter().map(|t| t.to_string()).collect::<Vec<_>>(),
            facts.iter().map(|t| t.to_string()).collect::<Vec<_>>(),
            got.difference(&want).map(|k| Term::decode(k).to_string()).collect::<Vec<_>>(),
            want.difference(&got).map(|k| Term::decode(k).to_string()).collect::<Vec<_>>(),
        );
        if !got.is_empty() {
            nonempty += 1;
        }
        total_answers += got.len();
        if got.iter().any(|k| !Term::decode(k).is_ground()) {
            nonground += 1;
        }
    }
    eprintln!(
        "random differential: {trials} trials, {nonempty} non-empty, {nonground} with non-ground (capture) answers, {total_answers} total answers"
    );
    // Guard against a vacuous pass: the distribution must actually produce answers, and a real
    // share of them must be non-ground (a stored variable captured something), or the random
    // test is not exercising the unification path the corpus targets.
    assert!(nonempty > trials / 10, "too few non-empty results ({nonempty}/{trials})");
    assert!(nonground > 50, "too few capture (non-ground) results ({nonground})");
}
