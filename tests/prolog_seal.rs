//! Independent seal: SWI-Prolog with `occurs_check` is the gold oracle for the
//! prototype's unification join.
//!
//! The proto's `leapfrog_unify_join` and `naive_match` agree with each other, but both
//! are the same crate's code over the same `unify.rs`. This test pins them to an engine
//! that shares no code with MORK at all: standard Prolog clause resolution. A query
//! pattern becomes a goal `fact(<pattern>)`, a stored fact is `assertz(fact(<fact>))`
//! (so its variables are fresh per use, the rename-apart), shared query variables across
//! goals are the join, and `set_prolog_flag(occurs_check, true)` makes resolution sound.
//! That is exactly the prototype's `naive_match` semantics, realized by a different
//! implementation. If the proto and Prolog answer sets ever diverge, one of them is
//! wrong, and we find out before trusting either as the oracle for the trie join.
//!
//! Answers are compared as full tuples over every query variable, ground and non-ground
//! alike, each canonicalized so two answers that differ only by renaming leftover
//! variables collapse to one. The proto canonicalizes via MORK's De Bruijn encoding;
//! Prolog via `numbervars/3`. Both number variables by first occurrence in the same
//! tuple, so the rendered strings line up.

use std::collections::BTreeSet;
use std::io::Write;
use std::process::Command;

use mork_uni_join::corpus;
use mork_uni_join::oracle::Conj;
use mork_uni_join::term::{self, Term};
use mork_uni_join::unijoin::leapfrog_unify_join;

/// Render a canonical (De Bruijn) answer tuple to the shared comparison string:
/// symbols verbatim, variables as `_<level>`, expressions as `(a b ...)`.
fn canon(t: &Term) -> String {
    match t {
        Term::Sym(s) => s.clone(),
        Term::Var(n) => format!("_{n}"),
        Term::App(a) => {
            let parts: Vec<String> = a.iter().map(canon).collect();
            format!("({})", parts.join(" "))
        }
    }
}

/// Render a term to Prolog source. Symbols become quoted atoms (so any byte content is
/// legal); variables become Prolog variable names via `name`; an expression `(s0 .. sn)`
/// becomes `'$a'(s0, .., sn)` with the App marker `'$a'`, and the empty expression the
/// atom `'$nil'`. The Prolog-side renderer maps `'$a'/_` and `'$nil'` back to `(..)`.
fn to_prolog(t: &Term, name: &dyn Fn(u32) -> String, out: &mut String) {
    match t {
        Term::Sym(s) => {
            out.push('\'');
            for c in s.chars() {
                if c == '\'' || c == '\\' {
                    out.push('\\');
                }
                out.push(c);
            }
            out.push('\'');
        }
        Term::Var(id) => out.push_str(&name(*id)),
        Term::App(a) => {
            if a.is_empty() {
                out.push_str("'$nil'");
            } else {
                out.push_str("'$a'(");
                for (i, x) in a.iter().enumerate() {
                    if i > 0 {
                        out.push(',');
                    }
                    to_prolog(x, name, out);
                }
                out.push(')');
            }
        }
    }
}

/// Build the complete SWI-Prolog program for one case.
fn prolog_program(q: &Conj, space: &[Term]) -> String {
    // Dense index of each query variable, so query vars render as `_Q0.._Qn` in
    // first-occurrence order (the same order the proto encodes the answer tuple).
    let qpos = |id: u32| -> String {
        let k = q.query_vars.iter().position(|&v| v == id).expect("query var");
        format!("_Q{k}")
    };

    // assertz facts, each with its own variable namespace `_F<j>_<id>`.
    let mut asserts = String::new();
    for (j, fact) in space.iter().enumerate() {
        let fname = move |id: u32| format!("_F{j}_{id}");
        asserts.push_str("    assertz(fact(");
        to_prolog(fact, &fname, &mut asserts);
        asserts.push_str(")),\n");
    }
    asserts.push_str("    true");

    // The conjunctive goal: one fact/1 goal per pattern, sharing query-var names.
    let mut goals = String::new();
    for (i, pat) in q.patterns.iter().enumerate() {
        if i > 0 {
            goals.push_str(", ");
        }
        goals.push_str("fact(");
        to_prolog(pat, &qpos, &mut goals);
        goals.push(')');
    }

    // The output wrapper: the tuple of query-var bindings, in query_vars order.
    let mut outw = String::new();
    if q.query_vars.is_empty() {
        outw.push_str("'$nil'");
    } else {
        outw.push_str("'$a'(");
        for k in 0..q.query_vars.len() {
            if k > 0 {
                outw.push(',');
            }
            outw.push_str(&format!("_Q{k}"));
        }
        outw.push(')');
    }

    format!(
        ":- set_prolog_flag(occurs_check, true).\n\
         :- dynamic fact/1.\n\
         \n\
         render_canon(T) :- ( T = '$VAR'(N) -> format(\"_~w\", [N])\n\
         ; T == '$nil' -> ( write('('), write(')') )\n\
         ; (compound(T), functor(T, '$a', _)) -> ( T =.. [_|As], write('('), render_args(As), write(')') )\n\
         ; atom(T) -> write(T)\n\
         ; write(T) ).\n\
         render_args([]).\n\
         render_args([A]) :- !, render_canon(A).\n\
         render_args([A|As]) :- render_canon(A), write(' '), render_args(As).\n\
         \n\
         setup :-\n{asserts}.\n\
         \n\
         main :- setup,\n\
         \x20   findall(Out, ( {goals}, copy_term({outw}, Out), numbervars(Out, 0, _) ), L0),\n\
         \x20   sort(L0, L),\n\
         \x20   forall(member(M, L), (render_canon(M), nl)).\n\
         \n\
         :- ( catch(main, E, (format(user_error, \"PROLOG_ERROR: ~q~n\", [E]), true)) -> true ; true ), halt.\n",
    )
}

fn swipl_available() -> bool {
    Command::new("swipl")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Run a Prolog program and return its stdout answer lines.
fn run_swipl(program: &str, tag: &str) -> BTreeSet<String> {
    let path = std::env::temp_dir().join(format!("mork_seal_{tag}.pl"));
    let mut f = std::fs::File::create(&path).expect("write prolog");
    f.write_all(program.as_bytes()).expect("write prolog");
    drop(f);
    let out = Command::new("swipl")
        .args(["-q", "-g", "true", path.to_str().unwrap()])
        .output()
        .expect("run swipl");
    let stderr = String::from_utf8_lossy(&out.stderr);
    if stderr.contains("PROLOG_ERROR") || stderr.to_lowercase().contains("error") {
        panic!("swipl error for {tag}:\n{stderr}\n--- program ---\n{program}");
    }
    String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(|l| l.trim().to_string())
        .filter(|l| !l.is_empty())
        .collect()
}

#[test]
fn proto_join_sealed_against_swipl_occurs_check() {
    if !swipl_available() {
        eprintln!("skip proto_join_sealed_against_swipl_occurs_check: swipl not found");
        return;
    }
    let mut failures = Vec::new();
    let mut total_answers = 0usize;
    let mut nonground_cases = 0usize;
    for (idx, case) in corpus::cases().iter().enumerate() {
        let q = Conj::parse(case.patterns);
        let space: Vec<Term> = case.facts.iter().map(|f| term::parse(f)).collect();

        // Proto: full-unification answer set, each key already alpha-canonical.
        let proto: BTreeSet<String> =
            leapfrog_unify_join(&q, &space).iter().map(|k| canon(&Term::decode(k))).collect();

        // Prolog: independent occurs-checked resolution over the same structure.
        let program = prolog_program(&q, &space);
        let prolog = run_swipl(&program, &format!("case{idx}"));

        total_answers += proto.len();
        if proto.iter().any(|s| s.contains('_')) {
            nonground_cases += 1;
        }
        eprintln!(
            "case {idx:2} {:<44} proto={:2} prolog={:2} {}",
            case.name,
            proto.len(),
            prolog.len(),
            if proto == prolog { "OK" } else { "DIVERGE" }
        );

        if proto != prolog {
            failures.push(format!(
                "case {idx} {:?}:\n  proto-only  = {:?}\n  prolog-only = {:?}",
                case.name,
                proto.difference(&prolog).collect::<Vec<_>>(),
                prolog.difference(&proto).collect::<Vec<_>>()
            ));
        }
    }
    eprintln!(
        "SEAL: {} cases, {} total answers, {} cases with non-ground answers",
        corpus::cases().len(),
        total_answers,
        nonground_cases
    );
    // Guard against a vacuous pass: the corpus must actually produce answers, and some
    // must be non-ground (capture / coreference), or it is not exercising unification.
    assert!(total_answers >= corpus::cases().len(), "corpus produced too few answers to be meaningful");
    assert!(nonground_cases >= 3, "corpus has too few non-ground (capture) answer sets");
    assert!(failures.is_empty(), "proto != SWI-Prolog occurs-check:\n{}", failures.join("\n"));
}
