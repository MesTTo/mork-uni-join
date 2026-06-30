//! Benchmark: the routed worst-case-optimal leapfrog against a binary (pairwise) join plan on
//! the triangle query, plus a cost-based hybrid that picks between them. Run with
//! `cargo run --release --example bench`.
//!
//! The triangle (e $x $y), (e $y $z), (e $x $z) is the textbook case for a worst-case-optimal
//! join. A binary plan joins two relations first and has to materialize every two-path before
//! the third relation can prune. On a graph with a high-degree hub the two-path intermediate
//! is quadratic in the edge count even when almost no two-path closes into a triangle. The
//! leapfrog intersects one variable at a time and never builds that intermediate, so it stays
//! near-linear (the AGM bound, N^1.5).
//!
//! The workload is that shape: a hub with `s` in-edges and `s` out-edges (2s edges, s^2
//! two-paths, zero triangles through it) plus a small complete digraph that contributes a
//! fixed set of real triangles. All three methods return the same answers (asserted on every
//! row). The two-paths and node-visit columns are a property of the query and the data, not of
//! either implementation, so they show the asymptotic separation independent of constant
//! factors.
//!
//! The leapfrog has the better asymptotics but a higher constant factor (it builds a trie
//! keyed on the MORK byte encoding), so below the crossover the pairwise plan is faster. The
//! `hybrid` estimates the two-path intermediate in one linear pass and routes to the leapfrog
//! only when that estimate is large, taking the lower envelope of the two. That is ordinary
//! cost-based plan selection: estimate the intermediate, run the cheaper plan.

use mork_uni_join::join::uni_join;
use mork_uni_join::oracle::{naive_match, Conj};
use mork_uni_join::term::Term;
use std::collections::{BTreeSet, HashMap, HashSet};
use std::time::Instant;

fn edge(src: &str, dst: &str) -> Term {
    Term::App(vec![Term::sym("e"), Term::sym(src), Term::sym(dst)])
}

/// Hub blowup of size `s` (2s edges, s^2 two-paths, no triangle through the hub) plus a
/// complete digraph on `clique` vertices (the real triangles).
fn workload(s: usize, clique: usize) -> Vec<Term> {
    let mut facts = Vec::with_capacity(2 * s + clique * clique);
    for i in 0..s {
        facts.push(edge(&format!("s{i}"), "h"));
    }
    for j in 0..s {
        facts.push(edge("h", &format!("t{j}")));
    }
    for a in 0..clique {
        for b in 0..clique {
            if a != b {
                facts.push(edge(&format!("k{a}"), &format!("k{b}")));
            }
        }
    }
    facts
}

fn as_edge(t: &Term) -> (&str, &str) {
    if let Term::App(a) = t {
        if let [Term::Sym(_), Term::Sym(s), Term::Sym(d)] = a.as_slice() {
            return (s.as_str(), d.as_str());
        }
    }
    panic!("workload fact is not (e src dst)");
}

fn intern(s: &str, ids: &mut HashMap<String, u32>, names: &mut Vec<String>) -> u32 {
    if let Some(&i) = ids.get(s) {
        return i;
    }
    let i = names.len() as u32;
    ids.insert(s.to_string(), i);
    names.push(s.to_string());
    i
}

/// The binary (pairwise) plan: build adjacency, enumerate every two-path R(x,y) join S(y,z),
/// and probe the third relation for the closing edge (x,z). Returns the answers and the count
/// of two-paths it had to materialize (the intermediate the leapfrog avoids).
fn pairwise(space: &[Term]) -> (BTreeSet<Vec<u8>>, u64) {
    let mut ids: HashMap<String, u32> = HashMap::new();
    let mut names: Vec<String> = Vec::new();
    let mut edges: Vec<(u32, u32)> = Vec::with_capacity(space.len());
    let mut out_adj: HashMap<u32, Vec<u32>> = HashMap::new();
    let mut edge_set: HashSet<(u32, u32)> = HashSet::new();
    for t in space {
        let (s, d) = as_edge(t);
        let si = intern(s, &mut ids, &mut names);
        let di = intern(d, &mut ids, &mut names);
        edges.push((si, di));
        out_adj.entry(si).or_default().push(di);
        edge_set.insert((si, di));
    }
    let mut answers = BTreeSet::new();
    let mut intermediate = 0u64;
    for &(x, y) in &edges {
        if let Some(zs) = out_adj.get(&y) {
            for &z in zs {
                intermediate += 1; // one materialized two-path x -> y -> z
                if edge_set.contains(&(x, z)) {
                    answers.insert(
                        Term::App(vec![
                            Term::sym(&names[x as usize]),
                            Term::sym(&names[y as usize]),
                            Term::sym(&names[z as usize]),
                        ])
                        .encode(),
                    );
                }
            }
        }
    }
    (answers, intermediate)
}

/// A linear-pass count of the two-paths this query would materialize: the sum over each vertex
/// of in-degree times out-degree. For the two-path count this is exact, not a guess, and it
/// costs one pass over the edges, so a planner can compute it before choosing a plan. A real
/// optimizer reads the same number off cardinality statistics it already keeps.
fn two_path_count(space: &[Term]) -> u64 {
    let mut indeg: HashMap<&str, u64> = HashMap::new();
    let mut outdeg: HashMap<&str, u64> = HashMap::new();
    for t in space {
        let (s, d) = as_edge(t);
        *outdeg.entry(s).or_default() += 1;
        *indeg.entry(d).or_default() += 1;
    }
    indeg
        .iter()
        .map(|(v, &i)| i * outdeg.get(v).copied().unwrap_or(0))
        .sum()
}

/// Cost-based dispatch: route to the leapfrog when the two-path intermediate would clear the
/// crossover, otherwise run the cheaper pairwise plan. The estimate is linear, paid once.
fn hybrid(space: &[Term], q: &Conj, crossover: u64) -> BTreeSet<Vec<u8>> {
    if two_path_count(space) > crossover {
        uni_join(q, space).0
    } else {
        pairwise(space).0
    }
}

/// Run `f` `reps` times, return the last result and the fastest wall-clock in milliseconds.
fn time_min<R>(reps: usize, mut f: impl FnMut() -> R) -> (R, f64) {
    let mut best = f64::INFINITY;
    let mut out = None;
    for _ in 0..reps {
        let t = Instant::now();
        let r = f();
        best = best.min(t.elapsed().as_secs_f64() * 1e3);
        out = Some(r);
    }
    (out.unwrap(), best)
}

fn main() {
    let q = Conj::parse(&["(e $x $y)", "(e $y $z)", "(e $x $z)"]);
    let clique = 6;
    let scales = [16usize, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192];
    let reps = 7;
    // Route to the leapfrog once the two-path intermediate clears this many tuples; set from
    // the wall-clock crossover measured on this machine (between the 542- and 1054-edge rows).
    let crossover = 150_000u64;

    println!(
        "\n  triangle  (e $x $y) , (e $y $z) , (e $x $z)  over a hub-blowup graph\n  \
         (every row returns the same {} answers; hybrid crossover = {} two-paths)\n",
        clique * (clique - 1) * (clique - 2),
        crossover
    );
    println!(
        "  {:>6}  {:>14}  {:>10}  {:>12}  {:>12}  {:>11}  {:>9}",
        "N", "2-paths", "lf_visits", "pairwise_ms", "leapfrog_ms", "hybrid_ms", "pick"
    );
    println!("  {}", "-".repeat(86));

    for &s in &scales {
        let space = workload(s, clique);
        let n = space.len();

        let ((ans_lf, stats), lf_ms) = time_min(reps, || uni_join(&q, &space));
        let ((ans_pw, intermediate), pw_ms) = time_min(reps, || pairwise(&space));
        let (ans_hy, hy_ms) = time_min(reps, || hybrid(&space, &q, crossover));

        assert_eq!(ans_lf, ans_pw, "leapfrog and pairwise disagree at N={n}");
        assert_eq!(ans_lf, ans_hy, "hybrid disagrees at N={n}");
        if n <= 200 {
            // anchor against the differential oracle on the rows it can afford.
            assert_eq!(ans_lf, naive_match(&q, &space), "oracle disagrees at N={n}");
        }
        let pick = if two_path_count(&space) > crossover {
            "leapfrog"
        } else {
            "pairwise"
        };

        println!(
            "  {:>6}  {:>14}  {:>10}  {:>12.3}  {:>12.3}  {:>11.3}  {:>9}",
            n, intermediate, stats.leapfrog_visits, pw_ms, lf_ms, hy_ms, pick
        );
    }
    println!();
}
