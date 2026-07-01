//! The unification-aware conjunctive join.
//!
//! The leapfrog triejoin, the COUNT/EXISTS aggregates, and the multi-pattern conjunctive
//! lowering are already in MesTTo's MORK fork (`da7e8e1` trie-join sidecar, `960c17c`
//! aggregate kernels, `1cc2d70` streamed intersections, `641e46f` conjunction lowering).
//! This module is the layer on top: integrating that join with unification, by routing on
//! a precise condition.
//!
//! THE CONTRIBUTION, stated exactly:
//!   Unification is free for the worst-case-optimal leapfrog as long as it resolves every
//!   JOIN-position variable to a GROUND value. Then the join key is a ground term and the
//!   leapfrog's equality intersection is exact, so even a query needing real unification
//!   (e.g. `func_type_unification`, where `($f)` unifies `(f)` to bind `$f = f`) runs on
//!   the fast path. The leapfrog only fails when a schematic stored fact binds a join
//!   variable to a NON-ground term: then the column-wise intersection aliases a free data
//!   column to a value fixed by another relation and fabricates answers that are not
//!   per-fact-tuple unifiers. That case routes to the coupled per-tuple path.
//!
//! This refines a fork's all-or-nothing `SidecarSchematicDecline` route (decline the whole
//! join if any fact is schematic; upstream MORK does the capture instead) to a per-position
//! admission: admit schematic facts into the worst-case-optimal join whenever their variables
//! do not land on a join position.

use crate::oracle::Conj;
use crate::term::Term;
use crate::unify::Env;
use crate::wcojoin::{wco_join, Relation};
use std::collections::{BTreeMap, BTreeSet};

/// Which path answered the query.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Path {
    /// The worst-case-optimal leapfrog (ground at every join position).
    Leapfrog,
    /// The coupled per-tuple path (a data variable reached a join position).
    Coupled,
}

#[derive(Debug, Clone, Copy)]
pub struct Stats {
    pub path: Path,
    /// Leapfrog node visits (the worst-case-optimal work measure); 0 on the coupled path.
    pub leapfrog_visits: u64,
}

/// Answer `q` against `space`, choosing the path by the join-position condition.
pub fn uni_join(q: &Conj, space: &[Term]) -> (BTreeSet<Vec<u8>>, Stats) {
    // A join variable occurs in two or more patterns (the shared keys).
    let join_vars: Vec<u32> = q
        .query_vars
        .iter()
        .copied()
        .filter(|v| {
            q.patterns
                .iter()
                .filter(|p| p.var_ids().contains(v))
                .count()
                >= 2
        })
        .collect();

    // Materialize each pattern's relation by matching it against the space. While doing so,
    // detect a non-ground binding at a join position, the one case the leapfrog cannot do.
    let mut fresh = 1_000_000u32;
    let mut rels: Vec<Relation> = Vec::with_capacity(q.patterns.len());
    let mut leapfrog_safe = true;
    for p in &q.patterns {
        let vars = p.var_ids();
        let mut tuples: Vec<BTreeMap<u32, Term>> = Vec::new();
        let mut seen = BTreeSet::new();
        for fact in space {
            let f = fact.rename_apart(fresh);
            fresh += 64;
            let mut env = Env::new();
            if env.unify(p, &f) {
                let mut tup = BTreeMap::new();
                for &v in &vars {
                    let val = env.resolve(&Term::Var(v));
                    if join_vars.contains(&v) && !val.is_ground() {
                        leapfrog_safe = false;
                    }
                    tup.insert(v, val);
                }
                let key = Term::App(vars.iter().map(|v| tup[v].clone()).collect()).encode();
                if seen.insert(key) {
                    tuples.push(tup);
                }
            }
        }
        if tuples.is_empty() {
            // A pattern that matches nothing makes the whole conjunction empty.
            return (
                BTreeSet::new(),
                Stats {
                    path: Path::Leapfrog,
                    leapfrog_visits: 0,
                },
            );
        }
        rels.push(Relation { vars, tuples });
    }

    if !leapfrog_safe {
        // A data variable reached a join position. Stay on the leapfrog, but make its
        // per-variable intersection a unification step: the unification triejoin handles the
        // schematic case worst-case-optimally rather than falling back to a nested loop.
        return (
            crate::unijoin::leapfrog_unify_join(q, space),
            Stats {
                path: Path::Coupled,
                leapfrog_visits: 0,
            },
        );
    }

    // Ground at every join position: the worst-case-optimal leapfrog is exact.
    let mut visits = 0u64;
    let sols = wco_join(&rels, &q.query_vars, &mut visits);
    let mut out = BTreeSet::new();
    for sol in sols {
        let tuple = Term::App(
            q.query_vars
                .iter()
                .map(|v| sol.get(v).cloned().unwrap_or(Term::Var(*v)))
                .collect(),
        );
        out.insert(tuple.encode());
    }
    (
        out,
        Stats {
            path: Path::Leapfrog,
            leapfrog_visits: visits,
        },
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::oracle::naive_match;
    use crate::term::parse;

    fn space(facts: &[&str]) -> Vec<Term> {
        facts.iter().map(|s| parse(s)).collect()
    }

    /// The join must agree with the oracle, exactly. Returns the stats so a test can also
    /// assert which path was taken.
    fn agrees(pats: &[&str], facts: &[&str]) -> Stats {
        let q = Conj::parse(pats);
        let s = space(facts);
        let (got, stats) = uni_join(&q, &s);
        let want = naive_match(&q, &s);
        assert_eq!(got, want, "join != oracle for {pats:?} over {facts:?}");
        stats
    }

    #[test]
    fn ground_triangle_uses_leapfrog_and_prunes() {
        let st = agrees(
            &["(e $x $y)", "(e $y $z)", "(e $x $z)"],
            &["(e a b)", "(e a c)", "(e b c)", "(e b d)"],
        );
        assert_eq!(st.path, Path::Leapfrog);
        // Worst-case-optimal: far fewer node visits than the oracle's |space|^3 = 64.
        assert!(st.leapfrog_visits < 20, "expected pruning, got {st:?}");
    }

    #[test]
    fn func_type_unification_rides_the_leapfrog() {
        // Needs unification (`($f)` ~ `(f)` => `$f = f`), but `$f` resolves GROUND, so the
        // join key is ground and the fast leapfrog path is exact.
        let st = agrees(
            &["(: ($f) A)", "(: $f (-> A))"],
            &["(: (f) A)", "(: f (-> A))"],
        );
        assert_eq!(st.path, Path::Leapfrog, "ground join key => fast path");
    }

    #[test]
    fn schematic_fact_admitted_when_not_at_a_join_position() {
        // (rel a $w) is schematic, but $x is in only one pattern, so nothing is a join var:
        // the schematic fact is ADMITTED to the leapfrog (the SchematicAdmit refinement).
        let st = agrees(&["(rel $x b)"], &["(rel a $w)"]);
        assert_eq!(st.path, Path::Leapfrog);
    }

    #[test]
    fn schematic_at_join_position_routes_to_coupled() {
        // $x is shared by both patterns, and (r $y $x) against a schematic fact binds $x
        // non-ground: the leapfrog would diverge, so route to the coupled path.
        let st = agrees(
            &["(r (($x $x) b) a)", "(r $y $x)"],
            &[
                "(r $m (a b))",
                "(r c b)",
                "(r $n (a))",
                "(r $p $q)",
                "(r (b (b)) (a))",
            ],
        );
        assert_eq!(st.path, Path::Coupled);
    }

    #[test]
    fn empties() {
        agrees(&["(edge $x $x)"], &["(edge a b)", "(edge b c)"]);
        agrees(&["(k $x)"], &[]);
    }

    // --- differential property test: random ground AND schematic inputs ---

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
        fn chance(&mut self, num: usize, den: usize) -> bool {
            self.below(den) < num
        }
    }

    const SYMS: &[&str] = &["a", "b", "c"];

    fn gen_term(rng: &mut Rng, depth: usize, allow_var: bool, var_pool: usize) -> Term {
        if depth == 0 || rng.chance(3, 5) {
            if allow_var && rng.chance(2, 5) {
                Term::Var(rng.below(var_pool) as u32)
            } else {
                Term::sym(SYMS[rng.below(SYMS.len())])
            }
        } else {
            let arity = 1 + rng.below(2);
            Term::App(
                (0..arity)
                    .map(|_| gen_term(rng, depth - 1, allow_var, var_pool))
                    .collect(),
            )
        }
    }

    #[test]
    fn differential_against_oracle_many_random() {
        let mut rng = Rng(0x9E3779B97F4A7C15);
        let mut leapfrog = 0u32;
        let mut coupled = 0u32;
        let mut nonempty = 0u32;
        for _ in 0..6000 {
            let npat = 1 + rng.below(3);
            let var_pool = 1 + rng.below(2);
            let patterns: Vec<Term> = (0..npat)
                .map(|_| {
                    Term::App(vec![
                        Term::sym("r"),
                        gen_term(&mut rng, 2, true, var_pool),
                        gen_term(&mut rng, 1, true, var_pool),
                    ])
                })
                .collect();
            let query_vars = {
                let mut v = Vec::new();
                for p in &patterns {
                    for id in p.var_ids() {
                        if !v.contains(&id) {
                            v.push(id);
                        }
                    }
                }
                v
            };
            let q = Conj {
                patterns,
                query_vars,
            };

            let nfacts = rng.below(6);
            let sp: Vec<Term> = (0..nfacts)
                .map(|_| {
                    let schematic = rng.chance(2, 5);
                    Term::App(vec![
                        Term::sym("r"),
                        gen_term(&mut rng, 2, schematic, 2),
                        gen_term(&mut rng, 1, schematic, 2),
                    ])
                })
                .collect();

            let (got, stats) = uni_join(&q, &sp);
            let want = naive_match(&q, &sp);
            assert_eq!(
                got,
                want,
                "MISMATCH ({:?})\n  query_vars={:?}\n  patterns={:?}\n  space={:?}",
                stats.path,
                q.query_vars,
                q.patterns.iter().map(|p| p.to_string()).collect::<Vec<_>>(),
                sp.iter().map(|f| f.to_string()).collect::<Vec<_>>(),
            );
            match stats.path {
                Path::Leapfrog => leapfrog += 1,
                Path::Coupled => coupled += 1,
            }
            if !got.is_empty() {
                nonempty += 1;
            }
        }
        // The corpus must exercise both paths and produce real answers.
        assert!(leapfrog > 1000, "too few leapfrog cases: {leapfrog}");
        assert!(coupled > 50, "too few coupled cases: {coupled}");
        assert!(nonempty > 300, "too few non-empty answers: {nonempty}");
    }
}
