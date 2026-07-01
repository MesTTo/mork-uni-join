//! The lazy trie capture-join must equal the sealed materialized join on everything: the
//! genuine-unification corpus, and a large random schematic differential whose facts carry
//! data variables and compounds so capture is actually exercised. Because
//! `leapfrog_unify_join` is sealed against SWI-Prolog occurs-check (tests/prolog_seal.rs),
//! agreement here transitively pins the trie join to the independent oracle too.

use mork_uni_join::corpus;
use mork_uni_join::oracle::Conj;
use mork_uni_join::randgen::{gen_facts, gen_query, Rng};
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
    assert!(
        nonempty > trials / 10,
        "too few non-empty results ({nonempty}/{trials})"
    );
    assert!(
        nonground > 50,
        "too few capture (non-ground) results ({nonground})"
    );
}
