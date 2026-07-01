//! Independent seal: SWI-Prolog with `occurs_check` is the gold oracle for the prototype's
//! unification join.
//!
//! The proto's `leapfrog_unify_join` and `naive_match` agree, but both are the same crate's code
//! over the same `unify.rs`. This test pins them to an engine that shares no code with the proto
//! at all: standard Prolog clause resolution (the bridge lives in `mork_uni_join::prolog`). A
//! query pattern becomes a goal `fact(<pattern>)`, a stored fact `assertz(fact(<fact>))` (its
//! variables fresh per use, the rename-apart), shared query variables across goals the join, and
//! `set_prolog_flag(occurs_check, true)` makes resolution sound. If the proto and Prolog answer
//! sets ever diverge, one is wrong, and we find out before trusting either as the oracle.

use std::collections::BTreeSet;

use mork_uni_join::corpus;
use mork_uni_join::oracle::Conj;
use mork_uni_join::prolog;
use mork_uni_join::term::{self, Term};
use mork_uni_join::unijoin::leapfrog_unify_join;

#[test]
fn proto_join_sealed_against_swipl_occurs_check() {
    if !prolog::available() {
        eprintln!("skip proto_join_sealed_against_swipl_occurs_check: swipl not found");
        return;
    }
    let mut failures = Vec::new();
    let mut total_answers = 0usize;
    let mut nonground_cases = 0usize;
    for (idx, case) in corpus::cases().iter().enumerate() {
        let q = Conj::parse(case.patterns);
        let space: Vec<Term> = case.facts.iter().map(|f| term::parse(f)).collect();

        // Proto: full-unification answer set, each key already alpha-canonical.
        let proto: BTreeSet<String> =
            leapfrog_unify_join(&q, &space).iter().map(|k| prolog::canon(&Term::decode(k))).collect();

        // Prolog: independent occurs-checked resolution over the same structure.
        let program = prolog::program(&q, &space);
        let swipl = prolog::run(&program, &format!("seal_case{idx}"));

        total_answers += proto.len();
        if proto.iter().any(|s| s.contains('_')) {
            nonground_cases += 1;
        }
        eprintln!(
            "case {idx:2} {:<44} proto={:2} prolog={:2} {}",
            case.name,
            proto.len(),
            swipl.len(),
            if proto == swipl { "OK" } else { "DIVERGE" }
        );

        if proto != swipl {
            failures.push(format!(
                "case {idx} {:?}:\n  proto-only  = {:?}\n  prolog-only = {:?}",
                case.name,
                proto.difference(&swipl).collect::<Vec<_>>(),
                swipl.difference(&proto).collect::<Vec<_>>()
            ));
        }
    }
    eprintln!(
        "SEAL: {} cases, {} total answers, {} cases with non-ground answers",
        corpus::cases().len(),
        total_answers,
        nonground_cases
    );
    // Guard against a vacuous pass: the corpus must produce answers, and some must be non-ground
    // (capture / coreference), or it is not exercising unification.
    assert!(total_answers >= corpus::cases().len(), "corpus produced too few answers to be meaningful");
    assert!(nonground_cases >= 3, "corpus has too few non-ground (capture) answer sets");
    assert!(failures.is_empty(), "proto != SWI-Prolog occurs-check:\n{}", failures.join("\n"));
}
