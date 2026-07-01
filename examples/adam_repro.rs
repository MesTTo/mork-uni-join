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
//! With no arguments it runs the 16-case corpus. To throw your OWN query at it:
//!
//!   cargo run --release --example adam_repro -- \
//!       -q "(r (a $p) b)" -q "(r (b) $p)" -f "(r $d b)" -f "(r a b)"
//!
//! Each `-q`/`--query` is a conjunctive factor, each `-f`/`--fact` a stored fact (which may
//! itself contain variables). The example equals SWI-Prolog or exits non-zero: it cannot claim
//! an agreement it did not observe, on the corpus or on your query. Answers are full
//! query-variable tuples in De Bruijn-normal form, so a leftover variable prints as `_0`.

use std::collections::BTreeSet;

use mork_uni_join::corpus;
use mork_uni_join::oracle::Conj;
use mork_uni_join::prolog;
use mork_uni_join::term::{parse, Term};
use mork_uni_join::trie_join::{equality_join, trie_unify_join};

#[derive(Default)]
struct Tally {
    cases_with_drop: usize,
    total_dropped: usize,
    prolog_checked: usize,
    prolog_disagreements: usize,
}

/// Answer keys rendered as a sorted, comparable set of canonical strings.
fn render(set: &BTreeSet<Vec<u8>>) -> BTreeSet<String> {
    set.iter()
        .map(|k| prolog::canon(&Term::decode(k)))
        .collect()
}

fn show(set: &BTreeSet<String>) -> String {
    if set.is_empty() {
        "(none)".to_string()
    } else {
        set.iter().cloned().collect::<Vec<_>>().join("   ")
    }
}

/// Run one case through the three engines and print it. `force_detail` always prints the full
/// three-column block (used for a user-supplied query, even when nothing is dropped).
fn emit_case(
    name: &str,
    patterns: &[&str],
    facts: &[&str],
    swipl: bool,
    tally: &mut Tally,
    force_detail: bool,
) {
    let q = Conj::parse(patterns);
    let space: Vec<Term> = facts.iter().map(|f| parse(f)).collect();

    let eq = render(&equality_join(&q, &space));
    let uni = render(&trie_unify_join(&q, &space));
    let dropped: Vec<String> = uni.difference(&eq).cloned().collect();

    let pl = if swipl {
        let out = prolog::run(
            &prolog::program(&q, &space),
            &format!("repro_{}", name.replace(' ', "_")),
        );
        tally.prolog_checked += 1;
        if out != uni {
            tally.prolog_disagreements += 1;
        }
        Some(out)
    } else {
        None
    };

    if dropped.is_empty() && !force_detail {
        let refereed = match &pl {
            Some(out) if *out == uni => "  = Prolog",
            Some(_) => "  != Prolog  <-- CHECK",
            None => "",
        };
        println!(
            "\n  [{name}]  equality = unification{refereed}   ->  {}",
            show(&uni)
        );
        return;
    }

    if !dropped.is_empty() {
        tally.cases_with_drop += 1;
        tally.total_dropped += dropped.len();
    }
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
    println!();
    if dropped.is_empty() {
        let confirm = match &pl {
            Some(out) if *out == uni => "  SWI-Prolog agrees.",
            Some(_) => "  <-- SWI-Prolog DISAGREES; investigate.",
            None => "",
        };
        println!(
            "    >>> equality and unification agree here: no data-side capture needed.{confirm}"
        );
    } else {
        let confirm = match &pl {
            Some(out) if *out == uni => "  SWI-Prolog confirms every one.",
            Some(_) => "  <-- SWI-Prolog DISAGREES with the unification join; investigate.",
            None => "",
        };
        println!(
            "    >>> the equality join DROPS {}: {}.{confirm}",
            dropped.len(),
            dropped.join("   ")
        );
    }
}

/// Parse `-q/--query` and `-f/--fact` into (patterns, facts). Empty patterns means corpus mode.
fn parse_args() -> (Vec<String>, Vec<String>) {
    let mut queries = Vec::new();
    let mut facts = Vec::new();
    let mut it = std::env::args().skip(1);
    while let Some(a) = it.next() {
        match a.as_str() {
            "-q" | "--query" => {
                if let Some(v) = it.next() {
                    queries.push(v);
                }
            }
            "-f" | "--fact" => {
                if let Some(v) = it.next() {
                    facts.push(v);
                }
            }
            other => {
                eprintln!(
                    "ignoring unrecognised argument {other:?}; use -q <pattern> and -f <fact>"
                );
            }
        }
    }
    (queries, facts)
}

fn main() {
    let swipl = prolog::available();
    let (queries, facts) = parse_args();
    let custom = !queries.is_empty();

    println!("\n=====================================================================");
    println!(" Data-side capture: a relational join vs first-order unification,");
    println!(" refereed by SWI-Prolog (occurs_check).");
    println!("=====================================================================");
    if !swipl {
        println!(" NOTE: swipl not on PATH, so the independent Prolog column is skipped.");
        println!("       Install SWI-Prolog to see the referee. The relational-vs-unification");
        println!("       gap below stands on its own.");
    }

    let mut tally = Tally::default();

    if custom {
        let qrefs: Vec<&str> = queries.iter().map(|s| s.as_str()).collect();
        let frefs: Vec<&str> = facts.iter().map(|s| s.as_str()).collect();
        emit_case("your query", &qrefs, &frefs, swipl, &mut tally, true);
    } else {
        for case in corpus::cases() {
            emit_case(
                case.name,
                case.patterns,
                case.facts,
                swipl,
                &mut tally,
                false,
            );
        }
    }

    println!("\n=====================================================================");
    println!(" SUMMARY");
    if custom {
        println!(
            "   your query: the equality join dropped {} tuple(s).",
            tally.total_dropped
        );
    } else {
        println!(
            "   {} witnesses. The equality join (MORK's relational semantics) drops",
            corpus::cases().len()
        );
        println!(
            "   {} tuple(s) across {} of them: the data-side captures.",
            tally.total_dropped, tally.cases_with_drop
        );
    }
    if swipl {
        println!(
            "   unification join vs SWI-Prolog (occurs_check): {}/{} identical, {} disagreement(s).",
            tally.prolog_checked - tally.prolog_disagreements,
            tally.prolog_checked,
            tally.prolog_disagreements
        );
        if tally.prolog_disagreements == 0 {
            println!(
                "   Every answer the unification join gives, SWI-Prolog independently confirms."
            );
        }
    } else {
        println!("   Install SWI-Prolog and re-run to see the independent referee.");
    }
    println!("=====================================================================\n");

    // Fail loudly if the referee ever disagrees: the artifact must never claim agreement it did
    // not observe, on the corpus or on a user-supplied query.
    if tally.prolog_disagreements != 0 {
        std::process::exit(1);
    }
}
