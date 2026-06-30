//! Validation against the real MORK matcher.
//!
//! The unit tests check the routed join against this crate's own unification oracle. This
//! integration test goes further: it checks the routed join against the answers MORK's
//! actual ProductZipper produced, captured as a golden fixture (`mork_fixture.txt`). Each
//! fixture line is a body, a space, and the ground answers the live matcher emitted, run
//! through MORK's `exec` + `metta_calculus` and rendered with this crate's own decoder. The
//! fixture is real matcher output, not a model of it. The test checks:
//!
//!   - the routed join never misses a ground answer the real matcher produced
//!     (`fork ⊆ routed`), the soundness/completeness floor, and
//!   - where they differ it is only the routed join finding MORE: the data-side variable
//!     capture case (issue-29), which the naive reference unifier returns too. The fixture
//!     does not try to settle that case.

use mork_uni_join::join::uni_join;
use mork_uni_join::oracle::Conj;
use mork_uni_join::term::{Term, parse};
use std::collections::BTreeSet;

/// The routed join's ground answers for a case, rendered as `(ans ...)` so they line up
/// with the fixture (which was rendered through this same decoder/`Display`).
fn routed_join_answers(patterns: &[&str], facts: &[&str]) -> BTreeSet<String> {
    let q = Conj::parse(patterns);
    let space: Vec<Term> = facts.iter().map(|f| parse(f)).collect();
    let (solutions, _stats) = uni_join(&q, &space);
    let mut out = BTreeSet::new();
    for sol in &solutions {
        let args = match Term::decode(sol) {
            Term::App(a) => a,
            t => vec![t],
        };
        let mut ans = vec![Term::sym("ans")];
        ans.extend(args);
        let wrapped = Term::App(ans);
        // The live matcher's exec keeps only ground results, so compare on ground answers.
        if wrapped.is_ground() {
            out.insert(wrapped.to_string());
        }
    }
    out
}

fn items(section: &str) -> Vec<&str> {
    section.split('|').map(|s| s.trim()).filter(|s| !s.is_empty()).collect()
}

#[test]
fn routed_join_matches_real_mork_fixture() {
    let fixture = include_str!("mork_fixture.txt");
    let mut cases = 0;
    let mut exact = 0;
    let mut superset = 0;
    for line in fixture.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let parts: Vec<&str> = line.split(";;").collect();
        assert_eq!(parts.len(), 3, "malformed fixture line: {line}");
        let patterns = items(parts[0]);
        let facts = items(parts[1]);
        let fork: BTreeSet<String> = items(parts[2]).into_iter().map(str::to_string).collect();

        cases += 1;
        let routed = routed_join_answers(&patterns, &facts);

        // Floor: the routed join must never miss a ground answer the real matcher produced.
        assert!(
            fork.is_subset(&routed),
            "routed join missed a real MORK answer\n  patterns={patterns:?}\n  facts={facts:?}\n  missing={:?}",
            fork.difference(&routed).collect::<Vec<_>>(),
        );
        if routed == fork {
            exact += 1;
        } else {
            superset += 1;
        }
    }

    eprintln!("real-MORK fixture: {cases} cases | exact={exact} superset={superset}");
    assert!(cases >= 20, "fixture should cover a representative corpus, got {cases}");
    // At least the data-side-capture case is a strict superset (the routed join finds extra
    // answers the live matcher does not, which the naive reference unifier also returns).
    assert!(superset >= 1, "expected the documented data-side-capture superset case");
}
