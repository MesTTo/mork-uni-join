//! Leapfrog triejoin extended with unification.
//!
//! The ground leapfrog triejoin (Veldhuizen, ICDT 2014) is variable-at-a-time: it indexes
//! each relation as a trie over a shared variable order and, for each variable, intersects
//! the participating relations' domains by SEEKING in sorted tries (lead the smallest domain,
//! seek the rest), recursing with no intermediate results. The intersection is by EQUALITY of
//! the ground key.
//!
//! This module keeps that structure and makes the per-variable intersection a UNIFICATION
//! step threaded through the WAM trail in [`crate::unify::Env`]. A trie edge may carry a
//! non-ground term (a variable in the stored data). The leapfrog still leads with the smallest
//! domain and SEEKS the followers: when the lead pins the variable to a ground term, a
//! follower finds the match by binary search over its sorted ground children (the worst-case-
//! optimal path), and its few non-ground children (wildcards) are merged in by unification. On
//! ground data this is exactly the ordinary leapfrog (equality is unification); on schematic
//! data it is the genuine unification join, still variable-at-a-time, not a per-tuple fallback.
//!
//! Correctness is pinned to [`crate::oracle::naive_match`], the full nested-loop unifier, by a
//! property-based differential over random ground AND schematic inputs (see the tests).

use crate::oracle::{answer_key, Conj};
use crate::term::Term;
use crate::unify::Env;
use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

/// One trie edge: the variable's value, its canonical key (for sorted seeking), and the
/// subtrie below.
struct Child {
    key: Vec<u8>,
    val: Term,
    sub: Node,
}

/// A trie node over one relation's variables in the global order. Children are sorted so the
/// first `n_ground` are ground values ordered by key (binary-searchable); the rest carry
/// variables (wildcards), matched by unification. Ground sibling values share a child;
/// non-ground values stay distinct, because the materialized tuples already hold globally
/// unique data variables, so two tuples never alias and coreference inside a tuple is kept.
struct Node {
    children: Vec<Child>,
    n_ground: usize,
}

impl Node {
    fn leaf() -> Node {
        Node { children: Vec::new(), n_ground: 0 }
    }
}

/// One relation's trie plus the subsequence of the global variable order it constrains.
struct Trie {
    rel_vars: Vec<u32>,
    root: Node,
}

fn insert(node: &mut Node, vals: &[Term]) {
    if vals.is_empty() {
        return;
    }
    let head = &vals[0];
    let idx = match node.children.iter().position(|c| &c.val == head) {
        Some(i) => i,
        None => {
            node.children.push(Child { key: head.encode(), val: head.clone(), sub: Node::leaf() });
            node.children.len() - 1
        }
    };
    insert(&mut node.children[idx].sub, &vals[1..]);
}

/// Sort every node's children ground-first by key and record the ground count, so the
/// follower seek can binary-search the ground prefix.
fn finalize(node: &mut Node) {
    for c in &mut node.children {
        finalize(&mut c.sub);
    }
    node.children.sort_by(|a, b| match (a.val.is_ground(), b.val.is_ground()) {
        (true, false) => Ordering::Less,
        (false, true) => Ordering::Greater,
        _ => a.key.cmp(&b.key),
    });
    node.n_ground = node.children.iter().filter(|c| c.val.is_ground()).count();
}

fn build(vars: &[u32], tuples: &[BTreeMap<u32, Term>], order: &[u32]) -> Trie {
    let rel_vars: Vec<u32> = order.iter().copied().filter(|v| vars.contains(v)).collect();
    let mut root = Node::leaf();
    for tup in tuples {
        let vals: Vec<Term> = rel_vars.iter().map(|v| tup[v].clone()).collect();
        insert(&mut root, &vals);
    }
    finalize(&mut root);
    Trie { rel_vars, root }
}

/// Materialize each pattern into a relation of bindings (query var -> term) by unifying the
/// pattern against every fact. Each fact is renamed apart to a unique variable range, so all
/// data variables across all tuples are globally distinct.
fn materialize(q: &Conj, space: &[Term]) -> Option<Vec<(Vec<u32>, Vec<BTreeMap<u32, Term>>)>> {
    let mut fresh = 1_000_000u32;
    let mut rels = Vec::with_capacity(q.patterns.len());
    for p in &q.patterns {
        let vars = p.var_ids();
        let mut tuples = Vec::new();
        let mut seen = BTreeSet::new();
        for fact in space {
            let f = fact.rename_apart(fresh);
            fresh += 64;
            let mut env = Env::new();
            if env.unify(p, &f) {
                let mut tup = BTreeMap::new();
                for &v in &vars {
                    tup.insert(v, env.resolve(&Term::Var(v)));
                }
                let key = Term::App(vars.iter().map(|v| tup[v].clone()).collect()).encode();
                if seen.insert(key) {
                    tuples.push(tup);
                }
            }
        }
        if tuples.is_empty() {
            return None;
        }
        rels.push((vars, tuples));
    }
    Some(rels)
}

/// The candidate children of `node` whose value can unify with the current binding `vb` of the
/// join variable. If `vb` is unbound this is the lead (every child). If `vb` is ground, seek it
/// by binary search over the sorted ground prefix and add the wildcard children. If `vb` is a
/// non-ground compound, scan (the rare fully-schematic case).
fn candidates<'a>(node: &'a Node, vb: &Term) -> Vec<&'a Child> {
    match vb {
        Term::Var(_) => node.children.iter().collect(),
        _ if vb.is_ground() => {
            let key = vb.encode();
            let mut res: Vec<&Child> = Vec::new();
            if let Ok(idx) = node.children[..node.n_ground].binary_search_by(|c| c.key.cmp(&key)) {
                res.push(&node.children[idx]);
            }
            res.extend(node.children[node.n_ground..].iter());
            res
        }
        _ => node.children.iter().collect(),
    }
}

/// The leapfrog-unification join. Returns the set of canonical answer keys, in the exact
/// format of [`crate::oracle::naive_match`].
pub fn leapfrog_unify_join(q: &Conj, space: &[Term]) -> BTreeSet<Vec<u8>> {
    let rels = match materialize(q, space) {
        Some(r) => r,
        None => return BTreeSet::new(),
    };
    let order = &q.query_vars;
    let tries: Vec<Trie> = rels.iter().map(|(vars, tuples)| build(vars, tuples, order)).collect();

    let mut out = BTreeSet::new();
    let mut cursors: Vec<&Node> = tries.iter().map(|t| &t.root).collect();
    let mut depths = vec![0usize; tries.len()];
    let mut env = Env::new();
    descend(order, 0, &q.query_vars, &tries, &mut cursors, &mut depths, &mut env, &mut out);
    out
}

#[allow(clippy::too_many_arguments)]
fn descend<'a>(
    order: &[u32],
    k: usize,
    query_vars: &[u32],
    tries: &'a [Trie],
    cursors: &mut Vec<&'a Node>,
    depths: &mut [usize],
    env: &mut Env,
    out: &mut BTreeSet<Vec<u8>>,
) {
    if k == order.len() {
        out.insert(answer_key(env, query_vars));
        return;
    }
    let v = order[k];
    let mut parts: Vec<usize> = (0..tries.len())
        .filter(|&i| depths[i] < tries[i].rel_vars.len() && tries[i].rel_vars[depths[i]] == v)
        .collect();
    if parts.is_empty() {
        descend(order, k + 1, query_vars, tries, cursors, depths, env, out);
        return;
    }
    // Lead with the smallest domain (the leapfrog principle); the rest are seeked.
    parts.sort_by_key(|&i| cursors[i].children.len());
    intersect(order, k, &parts, 0, v, query_vars, tries, cursors, depths, env, out);
}

/// Intersect variable `v` across the participating relations under unification. The lead (the
/// first, smallest part) enumerates its children; each subsequent part SEEKS the children
/// unifiable with the binding the lead pinned. When all parts agree, recurse to the next
/// variable. Backtracking restores the trail and the cursors.
#[allow(clippy::too_many_arguments)]
fn intersect<'a>(
    order: &[u32],
    k: usize,
    parts: &[usize],
    pi: usize,
    v: u32,
    query_vars: &[u32],
    tries: &'a [Trie],
    cursors: &mut Vec<&'a Node>,
    depths: &mut [usize],
    env: &mut Env,
    out: &mut BTreeSet<Vec<u8>>,
) {
    if pi == parts.len() {
        descend(order, k + 1, query_vars, tries, cursors, depths, env, out);
        return;
    }
    let i = parts[pi];
    let saved_cursor = cursors[i];
    let saved_depth = depths[i];
    let vb = env.resolve(&Term::Var(v));
    for child in candidates(saved_cursor, &vb) {
        let m = env.mark();
        if env.unify(&Term::Var(v), &child.val) {
            cursors[i] = &child.sub;
            depths[i] = saved_depth + 1;
            intersect(order, k, parts, pi + 1, v, query_vars, tries, cursors, depths, env, out);
        }
        cursors[i] = saved_cursor;
        depths[i] = saved_depth;
        env.rollback(m);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::oracle::naive_match;
    use crate::term::parse;

    fn space(facts: &[&str]) -> Vec<Term> {
        facts.iter().map(|s| parse(s)).collect()
    }

    /// The leapfrog-unify join must equal the full unifier, exactly, on every case.
    fn agree(pats: &[&str], facts: &[&str]) {
        let q = Conj::parse(pats);
        let s = space(facts);
        let got = leapfrog_unify_join(&q, &s);
        let want = naive_match(&q, &s);
        assert_eq!(got, want, "leapfrog-unify != oracle for {pats:?} over {facts:?}");
    }

    #[test]
    fn ground_triangle() {
        agree(
            &["(e $x $y)", "(e $y $z)", "(e $x $z)"],
            &["(e a b)", "(e a c)", "(e b c)", "(e b d)"],
        );
    }

    #[test]
    fn schematic_fact_data_side_capture() {
        agree(&["(rel $x b)"], &["(rel a $w)"]);
    }

    #[test]
    fn func_type_unification() {
        agree(&["(: ($f) A)", "(: $f (-> A))"], &["(: (f) A)", "(: f (-> A))"]);
    }

    #[test]
    fn schematic_at_join_position() {
        agree(
            &["(r (($x $x) b) a)", "(r $y $x)"],
            &["(r $m (a b))", "(r c b)", "(r $n (a))", "(r $p $q)", "(r (b (b)) (a))"],
        );
    }

    #[test]
    fn polymorphic_application_typing() {
        agree(
            &["(: $fn (-> $arg $res))", "(: $x $arg)"],
            &["(: v0 t0)", "(: f0 (-> t0 t1))", "(: id (-> $a $a))"],
        );
    }

    #[test]
    fn coreferent_schematic_fact() {
        agree(&["(e $x $y)", "(e $y $z)"], &["(e $u $u)", "(e a b)", "(e b c)"]);
    }

    #[test]
    fn ground_and_wildcard_at_same_position() {
        // A relation holding both a ground and a schematic fact at the same join position, so a
        // seeked ground value matches both the ground child and the wildcard child.
        agree(&["(p $x)", "(q $x)"], &["(p a)", "(p b)", "(q a)", "(q $w)"]);
    }

    #[test]
    fn empty_relation_is_empty() {
        agree(&["(edge $x $x)"], &["(edge a b)", "(edge b c)"]);
    }

    // ---- property-based differential: random ground AND schematic inputs ----

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
            Term::App((0..arity).map(|_| gen_term(rng, depth - 1, allow_var, var_pool)).collect())
        }
    }

    #[test]
    fn differential_against_oracle_many_random() {
        let mut rng = Rng(0x9E3779B97F4A7C15);
        let mut nonempty = 0u32;
        let mut schematic_answers = 0u32;
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
            let q = Conj { patterns, query_vars };

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

            let got = leapfrog_unify_join(&q, &sp);
            let want = naive_match(&q, &sp);
            assert_eq!(
                got,
                want,
                "MISMATCH\n  patterns={:?}\n  space={:?}",
                q.patterns.iter().map(|p| p.to_string()).collect::<Vec<_>>(),
                sp.iter().map(|f| f.to_string()).collect::<Vec<_>>(),
            );
            if !got.is_empty() {
                nonempty += 1;
            }
            if got.iter().any(|key| key.iter().any(|&b| b == 0xC0)) {
                schematic_answers += 1;
            }
        }
        assert!(nonempty > 300, "too few non-empty answers: {nonempty}");
        assert!(schematic_answers > 20, "too few schematic answers exercised: {schematic_answers}");
    }
}
