//! Worst-case-optimal join (generic join / Leapfrog-Triejoin family), ported from the
//! MeTTaLingo reference `packages/core/src/wcojoin.ts` (MesTTo). Each relation is indexed
//! once into a trie over its join variables; `recurse` drives the smallest participating
//! cursor and keeps only keys present in every participating cursor (the leapfrog
//! intersection), advancing and restoring cursors on backtrack. A cyclic conjunction (a
//! triangle) is answered in AGM time (N^1.5), not the O(N^2) of a pairwise materialize,
//! which is the permutation-blowup case.
//!
//! This is the GROUND fast path. Values are keyed by the MORK encoding, so the leapfrog
//! intersection is exact equality on canonical bytes, exactly MORK's `trie_join`. The
//! schematic (non-ground) case is handled separately (see `join.rs`): a column-wise
//! leapfrog cannot match the operational unification semantics once a data variable sits
//! at a join position, so that case routes to the coupled per-tuple path.

use crate::term::Term;
use std::collections::BTreeMap;

/// A relation: its variables, and a set of tuples binding those variables to values.
pub struct Relation {
    pub vars: Vec<u32>,
    pub tuples: Vec<BTreeMap<u32, Term>>,
}

/// A node of a relation's index trie: the value at this level and the subtrie below.
struct TrieNode {
    val: Term,
    child: BTreeMap<Vec<u8>, TrieNode>,
}

struct RelInfo {
    rel_vars: Vec<u32>,
    root: BTreeMap<Vec<u8>, TrieNode>,
}

/// All variables across the relations, first-seen order (the default elimination order).
pub fn all_vars(rels: &[Relation]) -> Vec<u32> {
    let mut seen = Vec::new();
    for r in rels {
        for &v in &r.vars {
            if !seen.contains(&v) {
                seen.push(v);
            }
        }
    }
    seen
}

/// Index one relation into a trie over its variables in `order`. A tuple that does not
/// bind one of the relation's join variables cannot complete a solution, so it is dropped.
fn index_relation(r: &Relation, order: &[u32]) -> RelInfo {
    let rel_vars: Vec<u32> = order.iter().copied().filter(|v| r.vars.contains(v)).collect();
    let mut root: BTreeMap<Vec<u8>, TrieNode> = BTreeMap::new();
    'tuple: for t in &r.tuples {
        let mut node = &mut root;
        for v in &rel_vars {
            let val = match t.get(v) {
                Some(x) => x.clone(),
                None => continue 'tuple,
            };
            let k = val.encode();
            node = &mut node
                .entry(k)
                .or_insert_with(|| TrieNode {
                    val,
                    child: BTreeMap::new(),
                })
                .child;
        }
    }
    RelInfo { rel_vars, root }
}

/// The worst-case-optimal join: every binding of every variable satisfying all relations.
pub fn wco_join(rels: &[Relation], order: &[u32], visits: &mut u64) -> Vec<BTreeMap<u32, Term>> {
    let rel_infos: Vec<RelInfo> = rels.iter().map(|r| index_relation(r, order)).collect();
    // For each variable, the relations that constrain it.
    let participants: Vec<Vec<usize>> = order
        .iter()
        .map(|v| {
            rel_infos
                .iter()
                .enumerate()
                .filter(|(_, ri)| ri.rel_vars.contains(v))
                .map(|(i, _)| i)
                .collect()
        })
        .collect();

    let mut out = Vec::new();
    let mut partial: BTreeMap<u32, Term> = BTreeMap::new();
    let mut cursors: Vec<&BTreeMap<Vec<u8>, TrieNode>> =
        rel_infos.iter().map(|ri| &ri.root).collect();
    recurse(order, &participants, 0, &mut cursors, &mut partial, &mut out, visits);
    out
}

fn recurse<'a>(
    order: &[u32],
    participants: &[Vec<usize>],
    i: usize,
    cursors: &mut Vec<&'a BTreeMap<Vec<u8>, TrieNode>>,
    partial: &mut BTreeMap<u32, Term>,
    out: &mut Vec<BTreeMap<u32, Term>>,
    visits: &mut u64,
) {
    *visits += 1;
    if i == order.len() {
        out.push(partial.clone());
        return;
    }
    let parts = &participants[i];
    if parts.is_empty() {
        return; // a variable no relation constrains has no binding
    }
    // Drive the smallest participating cursor; keep keys present in every participant.
    let smallest = *parts.iter().min_by_key(|&&r| cursors[r].len()).unwrap();
    let v = order[i];
    let keys: Vec<Vec<u8>> = cursors[smallest].keys().cloned().collect();
    for k in keys {
        let mut advanced: Vec<(usize, &'a BTreeMap<Vec<u8>, TrieNode>)> = Vec::new();
        let mut val: Option<Term> = None;
        let mut ok = true;
        for &r in parts {
            match cursors[r].get(&k) {
                Some(node) => {
                    if val.is_none() {
                        val = Some(node.val.clone());
                    }
                    advanced.push((r, &node.child));
                }
                None => {
                    ok = false;
                    break;
                }
            }
        }
        if !ok {
            continue;
        }
        let saved: Vec<(usize, &'a BTreeMap<Vec<u8>, TrieNode>)> =
            advanced.iter().map(|&(r, _)| (r, cursors[r])).collect();
        for &(r, child) in &advanced {
            cursors[r] = child;
        }
        partial.insert(v, val.unwrap());
        recurse(order, participants, i + 1, cursors, partial, out, visits);
        for (r, c) in saved {
            cursors[r] = c;
        }
    }
    partial.remove(&v);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::parse;

    fn rel(vars: &[u32], tuples: &[&[(u32, &str)]]) -> Relation {
        Relation {
            vars: vars.to_vec(),
            tuples: tuples
                .iter()
                .map(|t| t.iter().map(|(v, s)| (*v, parse(s))).collect())
                .collect(),
        }
    }

    #[test]
    fn triangle_finds_only_the_triangle() {
        // edges a->b,a->c,b->c,b->d. R($x,$y),S($y,$z),T($x,$z) with the same edge set.
        let edges: &[&[(u32, &str)]] = &[
            &[(0, "a"), (1, "b")],
            &[(0, "a"), (1, "c")],
            &[(0, "b"), (1, "c")],
            &[(0, "b"), (1, "d")],
        ];
        let r = rel(&[0, 1], edges); // ($x,$y)
        let s = Relation {
            vars: vec![1, 2],
            tuples: edges
                .iter()
                .map(|t| {
                    let mut m = BTreeMap::new();
                    m.insert(1u32, parse(t[0].1)); // $y
                    m.insert(2u32, parse(t[1].1)); // $z
                    m
                })
                .collect(),
        };
        let tt = Relation {
            vars: vec![0, 2],
            tuples: edges
                .iter()
                .map(|t| {
                    let mut m = BTreeMap::new();
                    m.insert(0u32, parse(t[0].1)); // $x
                    m.insert(2u32, parse(t[1].1)); // $z
                    m
                })
                .collect(),
        };
        let res = wco_join(&[r, s, tt], &[0, 1, 2], &mut 0);
        assert_eq!(res.len(), 1);
        let sol = &res[0];
        assert_eq!(sol[&0], parse("a"));
        assert_eq!(sol[&1], parse("b"));
        assert_eq!(sol[&2], parse("c"));
    }

    #[test]
    fn cartesian_when_disjoint() {
        let a = rel(&[0], &[&[(0, "x")], &[(0, "y")]]);
        let b = rel(&[1], &[&[(1, "p")], &[(1, "q")]]);
        let res = wco_join(&[a, b], &[0, 1], &mut 0);
        assert_eq!(res.len(), 4);
    }
}
