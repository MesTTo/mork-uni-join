//! The exact matcher generalized over a semiring (improvement #1). One matcher; with the
//! Reach semiring and an exact leaf it is the exact matcher, with Tropical and a distance
//! leaf it is fuzzy best-cost matching, with Count it counts derivations. The same engine,
//! parameterized by the cost algebra, which makes "fuzzy is exact over a tropical semiring"
//! executable.
//!
//! Hard structure (arity) stays exact: a structural mismatch is the annihilator. Only
//! *leaves* are scored, which is the guardrail from Ben's paper (fuzz the symbol spans,
//! never the tag bytes). A repeated variable re-checks against its binding carrying a
//! cost, so a shared join key can match approximately: that is the fuzzy join.
//!
//! The string/edit-distance case is a separate scored source (see `string_fuzzy.rs`):
//! "fuzzy-match the keys, aggregate their values" is exactly the `⊕` this module
//! accumulates per answer.

use crate::oracle::{answer_key, Conj};
use crate::semiring::{Semiring, Tropical};
use crate::term::Term;
use crate::unify::Env;
use std::collections::BTreeMap;

/// Structural match of `pattern` against `data` under `env`, accumulating leaf costs in
/// the semiring `S`. A variable matches anything at cost `one` (the top element / meet
/// identity); a bound variable re-checks against its value carrying a cost; an arity
/// mismatch is `zero` (the annihilator).
pub fn match_cost<S: Semiring>(
    pattern: &Term,
    data: &Term,
    env: &mut Env,
    leaf: &impl Fn(&Term, &Term) -> S,
) -> S {
    let p = env.walk(pattern).clone();
    let d = env.walk(data).clone();
    match (&p, &d) {
        (Term::Var(x), Term::Var(y)) if x == y => S::one(),
        (Term::Var(x), _) => {
            env.bind_var(*x, d);
            S::one()
        }
        (_, Term::Var(y)) => {
            env.bind_var(*y, p);
            S::one()
        }
        (Term::Sym(_), Term::Sym(_)) => leaf(&p, &d),
        (Term::App(ps), Term::App(ds)) if ps.len() == ds.len() => {
            let mut acc = S::one();
            for (pi, di) in ps.iter().zip(ds.iter()) {
                acc = acc.mul(&match_cost(pi, di, env, leaf));
                if acc.is_zero() {
                    break;
                }
            }
            acc
        }
        _ => S::zero(),
    }
}

/// Every answer to `q` against `space`, each with its aggregated semiring score: `mul`
/// along the conjunction, `add` across the alternative ways to reach the same answer.
pub fn eval_cost<S: Semiring>(
    q: &Conj,
    space: &[Term],
    leaf: &impl Fn(&Term, &Term) -> S,
) -> BTreeMap<Vec<u8>, S> {
    let mut out: BTreeMap<Vec<u8>, S> = BTreeMap::new();
    let mut env = Env::new();
    let mut fresh = 1_000_000u32;
    go(q, space, 0, &mut env, &mut fresh, S::one(), leaf, &mut out);
    out
}

#[allow(clippy::too_many_arguments)]
fn go<S: Semiring>(
    q: &Conj,
    space: &[Term],
    i: usize,
    env: &mut Env,
    fresh: &mut u32,
    acc: S,
    leaf: &impl Fn(&Term, &Term) -> S,
    out: &mut BTreeMap<Vec<u8>, S>,
) {
    if acc.is_zero() {
        return;
    }
    if i == q.patterns.len() {
        let key = answer_key(env, &q.query_vars);
        out.entry(key)
            .and_modify(|c| *c = c.add(&acc))
            .or_insert(acc);
        return;
    }
    for fact in space {
        let f = fact.rename_apart(*fresh);
        *fresh += 64;
        let m = env.mark();
        let c = match_cost(&q.patterns[i], &f, env, leaf);
        let combined = acc.mul(&c);
        if !combined.is_zero() {
            go(q, space, i + 1, env, fresh, combined, leaf, out);
        }
        env.rollback(m);
    }
}

/// Exact leaf: `one` if equal, `zero` otherwise. With the Reach semiring this is exact
/// matching; with Count it counts exact derivations.
pub fn exact_leaf<S: Semiring>(p: &Term, d: &Term) -> S {
    if p == d {
        S::one()
    } else {
        S::zero()
    }
}

/// Tropical leaf: equal symbols cost 0; two integers cost their absolute difference; any
/// other symbol pair is incompatible (infinity). The numeric dimension is fuzzy, the rest
/// is hard, which is the guardrail.
pub fn tropical_leaf(p: &Term, d: &Term) -> Tropical {
    match (p, d) {
        (Term::Sym(a), Term::Sym(b)) => {
            if a == b {
                Tropical(Some(0))
            } else if let (Ok(x), Ok(y)) = (a.parse::<i64>(), b.parse::<i64>()) {
                Tropical(Some((x - y).abs()))
            } else {
                Tropical(None)
            }
        }
        _ => Tropical(None),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::oracle::naive_match;
    use crate::semiring::{Count, Reach};
    use crate::term::parse;
    use std::collections::BTreeSet;

    fn space(f: &[&str]) -> Vec<Term> {
        f.iter().map(|s| parse(s)).collect()
    }

    #[test]
    fn reach_semiring_recovers_the_exact_matcher() {
        // Across a batch, the Reach+exact answers (score = true) must equal the exact
        // oracle's answer set. Exact is the Reach corner of the same engine.
        let cases: &[(&[&str], &[&str])] = &[
            (
                &["(e $x $y)", "(e $y $z)", "(e $x $z)"],
                &["(e a b)", "(e a c)", "(e b c)", "(e b d)"],
            ),
            (
                &["(: ($f) A)", "(: $f (-> A))"],
                &["(: (f) A)", "(: f (-> A))"],
            ),
            (&["(p $x)", "(q $x)"], &["(p a)", "(q a)", "(q b)"]),
            (&["(rel $x b)"], &["(rel a $w)"]),
        ];
        for (pats, facts) in cases {
            let q = Conj::parse(pats);
            let s = space(facts);
            let scored = eval_cost::<Reach>(&q, &s, &|p, d| exact_leaf(p, d));
            let reach_keys: BTreeSet<Vec<u8>> = scored
                .into_iter()
                .filter(|(_, c)| c.0)
                .map(|(k, _)| k)
                .collect();
            let oracle: BTreeSet<Vec<u8>> = naive_match(&q, &s).into_iter().collect();
            assert_eq!(reach_keys, oracle, "Reach must recover exact for {pats:?}");
        }
    }

    #[test]
    fn tropical_makes_the_join_key_fuzzy() {
        // (a $x) (b $x): $x must be the same in both, but a holds 5 and b holds 7.
        // Exact: no match. Tropical: one answer at cost |5-7| = 2 (a fuzzy coreference).
        let q = Conj::parse(&["(a $x)", "(b $x)"]);
        let s = space(&["(a 5)", "(b 7)"]);
        assert!(naive_match(&q, &s).is_empty(), "exact finds nothing");
        let scored = eval_cost(&q, &s, &tropical_leaf);
        assert_eq!(scored.len(), 1);
        assert_eq!(scored.values().next().unwrap(), &Tropical(Some(2)));
    }

    #[test]
    fn tropical_keeps_the_best_alternative() {
        // (t $x)(u $x) over (t 10),(u 10),(u 13): $x=10, the (u 10) alternative is exact
        // (cost 0), the (u 13) alternative costs 3; min keeps 0.
        let q = Conj::parse(&["(t $x)", "(u $x)"]);
        let s = space(&["(t 10)", "(u 10)", "(u 13)"]);
        let scored = eval_cost(&q, &s, &tropical_leaf);
        assert_eq!(scored.len(), 1);
        assert_eq!(scored.values().next().unwrap(), &Tropical(Some(0)));
    }

    #[test]
    fn mixed_crisp_structure_and_fuzzy_number_in_one_pass() {
        // Mix-and-match: crisp logic (the region symbol must match exactly) AND fuzzy
        // numeric proximity (the year near a target), in ONE tropical evaluation.
        // The crisp symbols cost 0 (or infinity on mismatch); only the number is scored.
        let q = Conj::parse(&["(reading europe $t)", "(around $t)"]);
        let s = space(&[
            "(reading europe 1995)",
            "(reading europe 1998)",
            "(reading asia 1995)", // excluded: region is crisp
            "(around 1992)",
        ]);
        let scored = eval_cost(&q, &s, &tropical_leaf);
        // Best europe reading near 1992 is 1995 (cost |1995-1992| = 3); 1998 costs 6.
        // Reduce with the semiring sum (which is min for tropical) to get the best.
        let best = scored
            .values()
            .cloned()
            .fold(Tropical::zero(), |a, v| a.add(&v));
        assert_eq!(best, Tropical(Some(3)));
        // asia never appears (the crisp region filter is exact), so every answer is a
        // europe year: two answers, 1995 and 1998.
        assert_eq!(scored.len(), 2);
    }

    #[test]
    fn count_semiring_counts_derivations() {
        // The aggregation shape: how many ways does each answer arise.
        // (e $x) over (e a),(e a),(e b): $x=a from two facts, $x=b from one.
        let q = Conj::parse(&["(e $x)"]);
        let s = space(&["(e a)", "(e a)", "(e b)"]);
        let scored = eval_cost::<Count>(&q, &s, &|p, d| exact_leaf(p, d));
        let a = parse("a");
        let b = parse("b");
        assert_eq!(scored[&Term::App(vec![a]).encode()], Count(2));
        assert_eq!(scored[&Term::App(vec![b]).encode()], Count(1));
    }
}
