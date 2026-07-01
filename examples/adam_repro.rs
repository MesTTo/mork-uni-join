//! One-command reproduction: `cargo run --release --example adam_repro`.
//!
//! Data-side capture is a completeness gap between a relational join and first-order
//! unification. This runs three engines on the same conjunctive queries and prints their
//! answers side by side:
//!
//!   equality join     the relational semantics (bind query variables to fact subterms, no
//!                     data-side capture) a Datalog-style engine, MORK's current fast path
//!                     included, computes. Here it is the SAME descent with capture switched
//!                     off, so the difference is exactly the capture step.
//!   unification join  the descent WITH data-side capture (a fact variable may bind a query
//!                     subterm), the join this prototype demonstrates.
//!   SWI-Prolog        clause resolution under `set_prolog_flag(occurs_check, true)`, sharing
//!                     no code with either join. The independent referee.
//!
//! The claim to check: the unification join equals SWI-Prolog on every case, and the equality
//! join drops exactly the data-side-capture tuples. Answers are full query-variable tuples in
//! De Bruijn-normal form, so a leftover variable prints as `_0`.

use std::collections::BTreeSet;

use mork_uni_join::corpus::{self, Case};
use mork_uni_join::oracle::Conj;
use mork_uni_join::prolog;
use mork_uni_join::term::{parse, Term};
use mork_uni_join::trie_join::{equality_join, trie_unify_join};

/// Answer keys (or Prolog lines) rendered as a sorted, comparable set of canonical strings.
fn render(set: &BTreeSet<Vec<u8>>) -> BTreeSet<String> {
    set.iter().map(|k| prolog::canon(&Term::decode(k))).collect()
}

fn show(set: &BTreeSet<String>) -> String {
    if set.is_empty() {
        "(none)".to_string()
    } else {
        set.iter().cloned().collect::<Vec<_>>().join("   ")
    }
}

fn main() {
    let swipl = prolog::available();
    println!("\n=====================================================================");
    println!(" Data-side capture: a relational join vs first-order unification,");
    println!(" refereed by SWI-Prolog (occurs_check).");
    println!("=====================================================================");
    if !swipl {
        println!(" NOTE: swipl not on PATH, so the independent Prolog column is skipped.");
        println!("       Install SWI-Prolog to see the referee. The relational-vs-unification");
        println!("       gap below stands on its own.");
    }

    let mut cases_with_drop = 0usize;
    let mut total_dropped = 0usize;
    let mut prolog_disagreements = 0usize;
    let mut prolog_checked = 0usize;

    for case in corpus::cases() {
        let Case { name, patterns, facts, .. } = case;
        let q = Conj::parse(patterns);
        let space: Vec<Term> = facts.iter().map(|f| parse(f)).collect();

        let eq = render(&equality_join(&q, &space));
        let uni = render(&trie_unify_join(&q, &space));
        let dropped: Vec<String> = uni.difference(&eq).cloned().collect();

        let pl = if swipl {
            let out = prolog::run(&prolog::program(&q, &space), &format!("repro_{name}"));
            prolog_checked += 1;
            if out != uni {
                prolog_disagreements += 1;
            }
            Some(out)
        } else {
            None
        };

        if dropped.is_empty() {
            // Agreement case: capture adds nothing here, so one compact line.
            let refereed = match &pl {
                Some(out) if *out == uni => "  = Prolog",
                Some(_) => "  != Prolog  <-- CHECK",
                None => "",
            };
            println!("\n  [{name}]  equality = unification{refereed}   ->  {}", show(&uni));
            continue;
        }

        cases_with_drop += 1;
        total_dropped += dropped.len();
        println!("\n  ----------------------------------------------------------------");
        println!("  [{name}]");
        println!("    query:  {}", patterns.join("   ,   "));
        println!("    facts:  {}", facts.join("    "));
        println!();
        println!("    equality join (no capture)   : {}", show(&eq));
        println!("    unification join (capture)   : {}", show(&uni));
        match &pl {
            Some(out) => println!("    SWI-Prolog (occurs_check)    : {}", show(out)),
            None => println!("    SWI-Prolog (occurs_check)    : (swipl not installed)"),
        }
        let confirm = match &pl {
            Some(out) if *out == uni => "  SWI-Prolog confirms every one.",
            Some(_) => "  <-- SWI-Prolog DISAGREES with the unification join; investigate.",
            None => "",
        };
        println!();
        println!("    >>> the equality join DROPS {}: {}.{confirm}", dropped.len(), dropped.join("   "));
    }

    println!("\n=====================================================================");
    println!(" SUMMARY");
    println!(
        "   {} witnesses. The equality join (MORK's relational semantics) drops",
        corpus::cases().len()
    );
    println!("   {total_dropped} tuple(s) across {cases_with_drop} of them: the data-side captures.");
    if swipl {
        println!(
            "   unification join vs SWI-Prolog (occurs_check): {}/{} identical, {prolog_disagreements} disagreement(s).",
            prolog_checked - prolog_disagreements,
            prolog_checked
        );
        println!("   Every dropped tuple is one SWI-Prolog independently confirms is correct to keep.");
    } else {
        println!("   Install SWI-Prolog and re-run to see the independent referee agree with the");
        println!("   unification join on all of them.");
    }
    println!("=====================================================================\n");

    // Fail loudly if the referee ever disagrees: the artifact must never claim agreement it
    // did not observe.
    if prolog_disagreements != 0 {
        std::process::exit(1);
    }
}
