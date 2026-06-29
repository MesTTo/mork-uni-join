//! Runnable demonstration: `cargo run --example demo`.
//!
//! Shows the unification-aware conjunctive join choosing its path per query, and prints
//! the answers. The point: unification rides the worst-case-optimal leapfrog whenever it
//! resolves the join keys to ground values (the common case, including a query that needs
//! real unification); the coupled per-tuple path is used only when a schematic fact binds
//! a join variable to a non-ground term.

use mork_uni_join::join::uni_join;
use mork_uni_join::oracle::Conj;
use mork_uni_join::term::{parse, Term};

fn show(label: &str, pats: &[&str], facts: &[&str]) {
    let q = Conj::parse(pats);
    let space: Vec<Term> = facts.iter().map(|s| parse(s)).collect();
    let (ans, stats) = uni_join(&q, &space);
    let mut decoded: Vec<String> = ans.iter().map(|k| Term::decode(k).to_string()).collect();
    decoded.sort();
    println!("{label}");
    println!("  query:  {}", pats.join("  ,  "));
    println!("  space:  {}", facts.join("  "));
    println!(
        "  PATH:   {:?}   (leapfrog node-visits: {})",
        stats.path, stats.leapfrog_visits
    );
    println!(
        "  answers [{}]: {}",
        decoded.len(),
        if decoded.is_empty() {
            "(none)".to_string()
        } else {
            decoded.join("   ")
        }
    );
    println!();
}

fn main() {
    println!("\n  Each answer is the (query-variable) tuple, in De Bruijn-normal form,\n  so a free/captured variable prints as $0.\n");

    show(
        "1) Triangle, ground data -> worst-case-optimal leapfrog (the permutation/AGM win)",
        &["(e $x $y)", "(e $y $z)", "(e $x $z)"],
        &["(e a b)", "(e a c)", "(e b c)", "(e b d)"],
    );

    show(
        "2) func_type_unification: needs unification, but ($f)~(f) binds $f=f GROUND,\n   so the join key is ground and it still rides the fast leapfrog",
        &["(: ($f) A)", "(: $f (-> A))"],
        &["(: (f) A)", "(: f (-> A))"],
    );

    show(
        "3) Schematic stored fact (rel a $w), but $x is not a join variable:\n   the schematic fact is ADMITTED to the leapfrog (SchematicAdmit, not Decline)",
        &["(rel $x b)"],
        &["(rel a $w)"],
    );

    show(
        "4) Schematic fact at a JOIN position ($x shared, (q $w) binds it non-ground):\n   the column-wise leapfrog would diverge, so route to the coupled per-tuple path",
        &["(p $x)", "(q $x)"],
        &["(p a)", "(q a)", "(q $w)"],
    );
}
