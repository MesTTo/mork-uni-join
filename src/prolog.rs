//! The independent oracle: SWI-Prolog with `occurs_check`, driven from Rust.
//!
//! This shares no code with the join under test. A query pattern becomes a goal
//! `fact(<pattern>)`, a stored fact becomes `assertz(fact(<fact>))` (its variables fresh per
//! use, the rename-apart), shared query variables across goals are the join, and
//! `set_prolog_flag(occurs_check, true)` makes resolution sound. Answers are full tuples over
//! the query variables, canonicalized by `numbervars/3` so two answers that differ only by
//! renaming leftover variables collapse to one, matching the proto's De Bruijn canonical form.
//!
//! `swipl` must be on PATH; [`available`] reports whether it is.

use crate::oracle::Conj;
use crate::term::Term;
use std::collections::BTreeSet;
use std::io::Write;
use std::process::Command;

/// Render a canonical (De Bruijn) answer tuple to the shared comparison string: symbols
/// verbatim, variables as `_<level>`, expressions as `(a b ...)`. The proto's answer keys
/// decode to this via `canon(&Term::decode(key))`, so both engines print the same strings.
pub fn canon(t: &Term) -> String {
    match t {
        Term::Sym(s) => s.clone(),
        Term::Var(n) => format!("_{n}"),
        Term::App(a) => {
            let parts: Vec<String> = a.iter().map(canon).collect();
            format!("({})", parts.join(" "))
        }
    }
}

/// Render a term to Prolog source. Symbols become quoted atoms (any byte content is legal);
/// variables become names via `name`; an expression `(s0 .. sn)` becomes `'$a'(s0, .., sn)`
/// and the empty expression the atom `'$nil'`. The Prolog-side renderer maps them back.
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

/// Build the complete SWI-Prolog program for one conjunctive query over one fact set.
pub fn program(q: &Conj, space: &[Term]) -> String {
    // Query vars render as `_Q0.._Qn` in first-occurrence order (the proto's answer-tuple order).
    let qpos = |id: u32| -> String {
        let k = q
            .query_vars
            .iter()
            .position(|&v| v == id)
            .expect("query var");
        format!("_Q{k}")
    };

    // assertz facts, each with its own variable namespace `_F<j>_<id>` (rename-apart per fact).
    let mut asserts = String::new();
    for (j, fact) in space.iter().enumerate() {
        let fname = move |id: u32| format!("_F{j}_{id}");
        asserts.push_str("    assertz(fact(");
        to_prolog(fact, &fname, &mut asserts);
        asserts.push_str(")),\n");
    }
    asserts.push_str("    true");

    // One fact/1 goal per pattern, sharing the query-var names: that sharing is the join.
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

/// Whether `swipl` is on PATH and runnable.
pub fn available() -> bool {
    Command::new("swipl")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Run a Prolog program and return its stdout answer lines (one canonical tuple per line).
/// Panics if swipl reports an error, so a malformed translation can never pass silently.
pub fn run(program: &str, tag: &str) -> BTreeSet<String> {
    let path = std::env::temp_dir().join(format!("mork_prolog_{tag}.pl"));
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
