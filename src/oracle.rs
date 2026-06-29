//! The differential oracle: a naive, obviously-correct matcher for a conjunctive query.
//!
//! This is the ground truth the fast join is checked against. It mirrors the
//! `complete_match` semantics certified in MORK's `SidecarSchematicDecline.rs`: a
//! data-side variable in a stored fact matches any query subterm (it is a wildcard that
//! captures), otherwise shapes must agree and children match pairwise, and coreference
//! is enforced by unification. It is "complete" by construction: it tries every
//! assignment of one stored fact per pattern and unifies them all simultaneously.

use crate::term::Term;
use crate::unify::Env;
use std::collections::BTreeSet;

/// A conjunctive query: patterns that must all match, sharing variables.
pub struct Conj {
    pub patterns: Vec<Term>,
    /// The query (head) variables we report bindings for: every variable in the query,
    /// in first-occurrence order.
    pub query_vars: Vec<u32>,
}

impl Conj {
    /// Build from S-expression strings that share a variable scope.
    pub fn parse(pats: &[&str]) -> Conj {
        let patterns = crate::term::parse_all(pats);
        let mut query_vars = Vec::new();
        for p in &patterns {
            for v in p.var_ids() {
                if !query_vars.contains(&v) {
                    query_vars.push(v);
                }
            }
        }
        Conj {
            patterns,
            query_vars,
        }
    }
}

/// Canonical key for one answer: the tuple of query-variable bindings, encoded to MORK
/// bytes so it is normalized up to renaming of any leftover (data) variables. Two
/// substitutions that agree on the query variables up to renaming map to one key.
pub fn answer_key(env: &Env, query_vars: &[u32]) -> Vec<u8> {
    let tuple = Term::App(
        query_vars
            .iter()
            .map(|v| env.resolve(&Term::Var(*v)))
            .collect(),
    );
    tuple.encode()
}

/// Data-side variables get fresh ids disjoint from the query and from each other, so a
/// schematic fact used twice (or matched against two patterns) does not accidentally
/// share variables. Query vars are small; data ids start here.
const DATA_VAR_BASE: u32 = 1_000_000;
const DATA_VAR_STRIDE: u32 = 64; // one fact has at most 64 variables

/// All answers to `q` against `space`, as a set of canonical keys.
pub fn naive_match(q: &Conj, space: &[Term]) -> BTreeSet<Vec<u8>> {
    let mut out = BTreeSet::new();
    let mut env = Env::new();
    let mut fresh = DATA_VAR_BASE;
    go(q, space, 0, &mut env, &mut fresh, &mut out);
    out
}

fn go(
    q: &Conj,
    space: &[Term],
    i: usize,
    env: &mut Env,
    fresh: &mut u32,
    out: &mut BTreeSet<Vec<u8>>,
) {
    if i == q.patterns.len() {
        out.insert(answer_key(env, &q.query_vars));
        return;
    }
    for fact in space {
        // Fresh data variables for this fact occurrence (rename-apart).
        let fact_i = fact.rename_apart(*fresh);
        let saved_fresh = *fresh;
        *fresh += DATA_VAR_STRIDE;

        let m = env.mark();
        if env.unify(&q.patterns[i], &fact_i) {
            go(q, space, i + 1, env, fresh, out);
        }
        env.rollback(m);
        *fresh = saved_fresh + DATA_VAR_STRIDE; // keep ids monotone, but reusable per branch
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::parse;

    fn space(facts: &[&str]) -> Vec<Term> {
        facts.iter().map(|s| parse(s)).collect()
    }

    #[test]
    fn ground_conjunction_two_answers() {
        let q = Conj::parse(&["(edge $x $y)"]);
        let s = space(&["(edge a b)", "(edge b c)"]);
        let ans = naive_match(&q, &s);
        assert_eq!(ans.len(), 2);
        // {$x=a,$y=b}
        assert!(ans.contains(&Term::App(vec![parse("a"), parse("b")]).encode()));
        assert!(ans.contains(&Term::App(vec![parse("b"), parse("c")]).encode()));
    }

    #[test]
    fn func_type_unification_yields_f() {
        // The MORK func_type_unification scenario, inner forms, sharing $f.
        let q = Conj::parse(&["(: ($f) A)", "(: $f (-> A))"]);
        let s = space(&["(: (f) A)", "(: f (-> A))"]);
        let ans = naive_match(&q, &s);
        assert_eq!(ans.len(), 1, "exactly one answer: $f = f");
        assert!(ans.contains(&Term::App(vec![parse("f")]).encode()));
    }

    #[test]
    fn schematic_fact_is_matched_not_dropped() {
        // (rel a $w) is a SCHEMATIC fact: `a` relates to anything. The ground equijoin
        // would decline/drop it; the complete matcher must find $x = a.
        let q = Conj::parse(&["(rel $x b)"]);
        let s = space(&["(rel a $w)"]);
        let ans = naive_match(&q, &s);
        assert_eq!(ans.len(), 1);
        assert!(ans.contains(&Term::App(vec![parse("a")]).encode()));
    }

    #[test]
    fn triangle_join_finds_only_the_triangle() {
        // edges a->b, a->c, b->c, b->d ; triangle(x,y,z): x->y, y->z, x->z.
        let q = Conj::parse(&["(e $x $y)", "(e $y $z)", "(e $x $z)"]);
        let s = space(&["(e a b)", "(e a c)", "(e b c)", "(e b d)"]);
        let ans = naive_match(&q, &s);
        assert_eq!(ans.len(), 1, "only (a,b,c)");
        assert!(ans.contains(
            &Term::App(vec![parse("a"), parse("b"), parse("c")]).encode()
        ));
    }

    #[test]
    fn no_match_is_empty() {
        let q = Conj::parse(&["(edge $x $x)"]); // a self-loop
        let s = space(&["(edge a b)", "(edge b c)"]);
        assert!(naive_match(&q, &s).is_empty());
    }
}
