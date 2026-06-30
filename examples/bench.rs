//! Benchmark: the leapfrog triejoin WITH unification against the naive unifier, on SCHEMATIC
//! data. Run with `cargo run --release --example bench`.
//!
//! Both methods answer the same conjunctive query over a space that contains variables, and
//! both return identical answers (asserted every row). The naive unifier is the full
//! nested-loop matcher (the reference). The leapfrog-unify join is variable-at-a-time over
//! tries, seeking the ground join keys and unifying the schematic ones, so it inherits the
//! worst-case-optimal bound on the ground structure while still handling the variables in the
//! data. This is the case the prototype is named for: a join that is at once worst-case-optimal
//! and unification-complete.
//!
//! The workload is the AGM-blowup triangle (e $x $y), (e $y $z), (e $x $z): a hub with `s`
//! in-edges and `s` out-edges gives s^2 two-paths but no triangle, a small complete digraph
//! gives the ground triangles, and a few SCHEMATIC edges (a node related to a variable) add
//! answers that need unification, which declining schematic facts loses. The table reports how
//! many answers declining finds, how many the unification join finds, and the wall-clock of the
//! naive unifier versus the leapfrog-unify join.

use mork_uni_join::oracle::{naive_match, Conj};
use mork_uni_join::term::{parse, Term};
use mork_uni_join::unijoin::leapfrog_unify_join;
use std::time::Instant;

fn edge(src: &str, dst: &str) -> Term {
    Term::App(vec![Term::sym("e"), Term::sym(src), Term::sym(dst)])
}

/// Hub blowup of size `s`, a complete digraph on `clique` vertices, and `sch` schematic edges
/// (a clique vertex related to a fresh variable, so matching them needs unification).
fn workload(s: usize, clique: usize, sch: usize) -> Vec<Term> {
    let mut facts = Vec::new();
    for i in 0..s {
        facts.push(edge(&format!("s{i}"), "h"));
        facts.push(edge("h", &format!("t{i}")));
    }
    for a in 0..clique {
        for b in 0..clique {
            if a != b {
                facts.push(edge(&format!("k{a}"), &format!("k{b}")));
            }
        }
    }
    for j in 0..sch {
        // (e kj $w): clique vertex kj is related to anything; a stored variable on the target.
        facts.push(parse(&format!("(e k{j} $w)")));
    }
    facts
}

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
    let sch = 3;
    let scales = [16usize, 32, 64, 128, 256];
    let reps = 5;

    println!("\n  triangle  (e $x $y) , (e $y $z) , (e $x $z)  over schematic edges");
    println!("  (leapfrog-unify and the naive unifier return identical answers on every row)\n");
    println!(
        "  {:>6}  {:>6}  {:>11}  {:>9}  {:>10}  {:>12}  {:>9}",
        "N", "sch", "decline_ans", "uni_ans", "naive_ms", "leapfrog_ms", "speedup"
    );
    println!("  {}", "-".repeat(76));

    for &s in &scales {
        let space = workload(s, clique, sch);
        let n = space.len();
        let ground: Vec<Term> = space.iter().filter(|f| f.is_ground()).cloned().collect();

        let (ans_uni, lf_ms) = time_min(reps, || leapfrog_unify_join(&q, &space));
        let (ans_naive, nv_ms) = time_min(reps, || naive_match(&q, &space));
        let ans_decline = leapfrog_unify_join(&q, &ground);

        assert_eq!(ans_uni, ans_naive, "leapfrog-unify != naive unifier at N={n}");
        assert!(
            ans_decline.is_subset(&ans_uni),
            "declining schematic facts found an answer unification did not, at N={n}"
        );

        println!(
            "  {:>6}  {:>6}  {:>11}  {:>9}  {:>10.3}  {:>12.3}  {:>8.1}x",
            n,
            sch,
            ans_decline.len(),
            ans_uni.len(),
            nv_ms,
            lf_ms,
            nv_ms / lf_ms,
        );
    }
    println!();
}
