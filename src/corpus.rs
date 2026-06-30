//! The genuine-unification differential corpus.
//!
//! Every case here is a conjunctive query whose answer set depends on something a
//! ground set-join cannot do: a data-side variable capturing a query subterm, a
//! coreferent data variable forcing two query positions equal, an occurs failure that
//! must yield nothing, or a non-ground answer. These are the cases the original
//! `mork_fixture.txt` lacked (Adam: "none of the items in the fixtures need
//! unification"), so this corpus is what the join is allowed to be checked against.
//!
//! One corpus, three engines: the proto's `leapfrog_unify_join` and `naive_match`
//! (in-process), and SWI-Prolog with `occurs_check` (independent, see
//! `tests/prolog_seal.rs`). The kernel's live-route contract reuses the same cases.

/// A conjunctive-query case. `patterns` share a variable scope (a repeated `$y` is the
/// same query variable, i.e. a join); each `facts` entry is parsed in its own scope
/// (its variables are renamed apart). `proj` names the variables the live-route ground
/// contract reports; the Prolog seal projects every query variable instead.
pub struct Case {
    pub name: &'static str,
    pub patterns: &'static [&'static str],
    pub facts: &'static [&'static str],
    pub proj: &'static [&'static str],
}

/// The full corpus, grouped by what it exercises.
pub fn cases() -> &'static [Case] {
    CASES
}

static CASES: &[Case] = &[
    // --- A. data-side capture: a stored variable absorbs a query subterm ---
    Case {
        name: "capture query constant",
        patterns: &["(rel $x b)"],
        facts: &["(rel a $w)"],
        proj: &["x"],
    },
    Case {
        name: "capture nonground compound, p fixed by join",
        patterns: &["(r (a $p) b)", "(r (b) $p)"],
        facts: &["(r $d b)", "(r a b)"],
        proj: &["p"],
    },
    Case {
        name: "capture (f x), x grounded by join",
        patterns: &["(r (f $x) $y)", "(s $x)"],
        facts: &["(r $d b)", "(s c)"],
        proj: &["x", "y"],
    },
    Case {
        name: "function-type unification both sides",
        patterns: &["(: ($f) A)", "(: $f (-> A))"],
        facts: &["(: (f) A)", "(: f (-> A))"],
        proj: &["f"],
    },
    // --- B. coreference: a repeated data variable forces query positions equal ---
    Case {
        name: "coreferent fact forces join equal",
        patterns: &["(e $x $y)", "(e $y $z)"],
        facts: &["(e $u $u)", "(e a b)", "(e b c)"],
        proj: &["x", "z"],
    },
    Case {
        name: "flat data coref, nonground answer",
        patterns: &["(e $x $y)"],
        facts: &["(e $u $u)"],
        proj: &["x", "y"],
    },
    Case {
        name: "ground and wildcard at same position",
        patterns: &["(p $x)", "(q $x)"],
        facts: &["(p a)", "(p b)", "(q a)", "(q $w)"],
        proj: &["x"],
    },
    // --- C. occurs failures: must yield nothing ---
    Case {
        name: "occurs via data coref yields nothing",
        patterns: &["(e $x (f $x))"],
        facts: &["(e $w $w)"],
        proj: &["x"],
    },
    Case {
        name: "indirect occurs across join yields nothing",
        patterns: &["(p $x $y)", "(p $y (s $x))"],
        facts: &["(p $u $u)"],
        proj: &["x", "y"],
    },
    // --- D. polymorphic typing / schematic at a join position ---
    Case {
        name: "polymorphic application typing",
        patterns: &["(: $fn (-> $arg $res))", "(: $x $arg)"],
        facts: &["(: v0 t0)", "(: f0 (-> t0 t1))", "(: id (-> $a $a))"],
        proj: &["fn", "arg", "res", "x"],
    },
    Case {
        name: "schematic at join position, nested",
        patterns: &["(r (($x $x) b) a)", "(r $y $x)"],
        facts: &["(r $m (a b))", "(r c b)", "(r $n (a))", "(r $p $q)", "(r (b (b)) (a))"],
        proj: &["x", "y"],
    },
    // --- E. ground controls (must agree too) ---
    Case {
        name: "ground triangle",
        patterns: &["(e $x $y)", "(e $y $z)", "(e $x $z)"],
        facts: &["(e a b)", "(e a c)", "(e b c)", "(e b d)"],
        proj: &["x", "y", "z"],
    },
    Case {
        name: "ground path of length two",
        patterns: &["(edge $x $y)", "(edge $y $z)"],
        facts: &["(edge a b)", "(edge b d)", "(edge a c)", "(edge c d)"],
        proj: &["x", "y", "z"],
    },
    // --- F. empty result ---
    Case {
        name: "empty: no fact has equal arguments",
        patterns: &["(edge $x $x)"],
        facts: &["(edge a b)", "(edge b c)"],
        proj: &["x"],
    },
];
