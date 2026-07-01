//! Order independence (MORK issue #29): the answer set of a conjunctive unification
//! query must not depend on the order the join visits things. Two orders are at play and
//! both are tested here against the same corpus:
//!
//!   - factor order — permute the patterns, keep one variable-elimination order;
//!   - elimination order — keep the patterns, permute `query_vars` (the join plan).
//!
//! Permuting `query_vars` also permutes the answer-tuple layout, so each answer is
//! re-canonicalized onto one fixed variable order (ids ascending) before comparison;
//! only then is set equality meaningful. A divergence here would mean the join's result
//! leaks its plan, which is the bug issue #29 is about.

use std::collections::{BTreeSet, HashMap};

use mork_uni_join::corpus;
use mork_uni_join::oracle::Conj;
use mork_uni_join::term::{self, Term};
use mork_uni_join::unijoin::leapfrog_unify_join;

/// All permutations of a small slice (corpus sizes are tiny: <= 4 vars, <= 3 patterns).
fn perms<T: Clone>(items: &[T]) -> Vec<Vec<T>> {
    if items.len() <= 1 {
        return vec![items.to_vec()];
    }
    let mut out = Vec::new();
    for i in 0..items.len() {
        let mut rest = items.to_vec();
        let head = rest.remove(i);
        for mut tail in perms(&rest) {
            tail.insert(0, head.clone());
            out.push(tail);
        }
    }
    out
}

/// Run the join and re-key every answer onto `canonical_order` so the result is
/// independent of the order `q.query_vars` happens to use.
fn answers_canonical(q: &Conj, space: &[Term], canonical_order: &[u32]) -> BTreeSet<Vec<u8>> {
    let mut out = BTreeSet::new();
    for key in &leapfrog_unify_join(q, space) {
        let tuple = match Term::decode(key) {
            Term::App(a) => a,
            t => vec![t],
        };
        let map: HashMap<u32, Term> = q.query_vars.iter().copied().zip(tuple).collect();
        let recanon = Term::App(canonical_order.iter().map(|v| map[v].clone()).collect());
        out.insert(recanon.encode());
    }
    out
}

#[test]
fn join_answer_set_is_order_independent() {
    for case in corpus::cases() {
        // One fixed name->id scope from the original pattern order, and a fixed
        // canonical variable order (ids ascending) for re-keying every answer.
        let mut scope: HashMap<String, u32> = HashMap::new();
        for p in case.patterns {
            let _ = term::parse_with_scope(p, &mut scope);
        }
        let mut canonical: Vec<u32> = scope.values().copied().collect();
        canonical.sort_unstable();
        let space: Vec<Term> = case.facts.iter().map(|f| term::parse(f)).collect();

        // Reference: original pattern order, canonical elimination order.
        let parse_in = |order: &[usize], sc: &HashMap<String, u32>| -> Vec<Term> {
            let mut sc = sc.clone();
            order
                .iter()
                .map(|&i| term::parse_with_scope(case.patterns[i], &mut sc))
                .collect()
        };
        let identity: Vec<usize> = (0..case.patterns.len()).collect();
        let reference = answers_canonical(
            &Conj {
                patterns: parse_in(&identity, &scope),
                query_vars: canonical.clone(),
            },
            &space,
            &canonical,
        );

        // A. factor-order independence: permute the patterns.
        for perm in perms(&identity) {
            let q = Conj {
                patterns: parse_in(&perm, &scope),
                query_vars: canonical.clone(),
            };
            let got = answers_canonical(&q, &space, &canonical);
            assert_eq!(
                got,
                reference,
                "case {:?}: factor order {:?} changed the answer set\n  +{:?}\n  -{:?}",
                case.name,
                perm,
                got.difference(&reference)
                    .map(|k| Term::decode(k).to_string())
                    .collect::<Vec<_>>(),
                reference
                    .difference(&got)
                    .map(|k| Term::decode(k).to_string())
                    .collect::<Vec<_>>(),
            );
        }

        // B. elimination-order independence: permute query_vars (the plan).
        let patterns_fixed = parse_in(&identity, &scope);
        for vperm in perms(&canonical) {
            let q = Conj {
                patterns: patterns_fixed.clone(),
                query_vars: vperm.clone(),
            };
            let got = answers_canonical(&q, &space, &canonical);
            assert_eq!(
                got, reference,
                "case {:?}: elimination order {:?} changed the answer set",
                case.name, vperm,
            );
        }
    }
}
