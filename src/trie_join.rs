//! The unification-aware join, executed LAZILY over a byte-trie with no materialized
//! per-pattern domain. This is the fusion the prototype exists to demonstrate: a
//! worst-case-optimal-style trie descent (Leapfrog Triejoin / Free Join) carrying full
//! two-sided unification, so a data-side variable in a stored fact captures a query
//! subterm (issue-29), the case the equality intersection declines.
//!
//! Each query factor is matched against the trie by the retrieval the theorem-proving
//! world settled on: descend the index unifying the query against the stored term,
//! threading ONE backtrackable substitution (Graf's substitution-tree retrieval; WAM
//! read-mode `get_structure`/`unify_variable`/`unify_value`). A stored wildcard byte is a
//! data variable that captures; occurs-check happens when the binding is applied
//! (`Env::unify`); the conjunction shares the substitution, so a capture forced at one
//! factor propagates to the others (the join-propagated case). Correctness is pinned to
//! the materialized `leapfrog_unify_join`, itself sealed against SWI-Prolog occurs-check.
//!
//! The descent is generic over [`SubtermZip`], so the very same code runs over the
//! prototype's `ByteTrie` and over MORK's live PathMap `ReadZipper`: the kernel implements
//! the four-method trait and gets this engine with no copy of the data and no second
//! implementation. All mutable state lives in one [`Descent`] threaded by `&mut`, which
//! keeps the continuation lifetimes simple under the generic zipper.
//!
//! This first cut prunes where the query is structured (it seeks that structure on the
//! trie) and branches only where a variable meets the data; a later pass adds the
//! leapfrog cross-factor seek for full worst-case optimality. Answers are byte-identical
//! to the materialized join regardless.

use crate::oracle::{answer_key, Conj};
use crate::term::Term;
use crate::trie::{ByteTrie, SubtermZip, TrieZipper};
use crate::unify::Env;
use std::collections::BTreeSet;

const TOP2: u8 = 0b1100_0000;
const TAG_ARITY: u8 = 0b0000_0000;
const TAG_VARREF: u8 = 0b1000_0000;
const TAG_SYMSIZE: u8 = 0b1100_0000;
const NEWVAR_BYTE: u8 = 0b1100_0000;
const LOW6: u8 = 0b0011_1111;

/// All mutable state of one join, threaded by a single `&mut`. `z` is the live cursor, `env`
/// the shared backtrackable substitution, `fresh` the next stored-variable id, `slots` the
/// current fact's stored variables (for coreference), `out` the canonical answer keys.
struct Descent<'a, Z> {
    factors: &'a [Term],
    query_vars: &'a [u32],
    z: Z,
    env: Env,
    fresh: u32,
    slots: Vec<u32>,
    out: BTreeSet<Vec<u8>>,
    /// When false, the data-side-capture step is skipped: a stored wildcard never binds a query
    /// compound, so the descent is a plain relational (equality) join. The ONLY difference from the
    /// full join, so the two answer sets differ by exactly the data-side-capture answers.
    capture: bool,
}

#[inline]
fn child_bytes<Z: SubtermZip>(z: &Z) -> Vec<u8> {
    let words = z.child_mask_words();
    let mut out = Vec::new();
    for hi in 0..4u8 {
        let mut w = words[hi as usize];
        while w != 0 {
            let lo = w.trailing_zeros() as u8;
            out.push((hi << 6) | lo);
            w &= w - 1;
        }
    }
    out
}

/// Read every complete stored subterm branching at `d.z`'s focus, as a `Term` whose variables
/// use the fact's stored-variable slots (a `NewVar` allocates a fresh id, a `VarRef` reads an
/// earlier one), so coreference inside the fact is preserved. `cont` runs once per subterm
/// with `d.z` advanced past it; the trie and slots are restored on return.
fn read_one_subterm<Z: SubtermZip>(
    d: &mut Descent<Z>,
    cont: &mut dyn FnMut(&mut Descent<Z>, &Term),
) {
    for b in child_bytes(&d.z) {
        d.z.descend_byte(b);
        match b & TOP2 {
            TAG_ARITY => {
                let n = (b & LOW6) as usize;
                read_n_subterms(d, n, &mut Vec::new(), &mut |d, kids| {
                    cont(d, &Term::App(kids.to_vec()));
                });
            }
            TAG_VARREF => {
                let idx = (b & LOW6) as usize;
                let v = d.slots[idx];
                cont(d, &Term::Var(v));
            }
            _ => {
                if b == NEWVAR_BYTE {
                    let id = d.fresh;
                    d.fresh += 1;
                    d.slots.push(id);
                    cont(d, &Term::Var(id));
                    d.slots.pop();
                } else {
                    let len = (b & LOW6) as usize;
                    read_payload(d, len, &mut Vec::new(), &mut |d, bytes| {
                        let s = String::from_utf8(bytes.to_vec()).expect("utf8 symbol");
                        cont(d, &Term::Sym(s));
                    });
                }
            }
        }
        d.z.ascend();
    }
}

/// Read `n` complete subterms in sequence, accumulating them, then call `cont` with the list.
fn read_n_subterms<Z: SubtermZip>(
    d: &mut Descent<Z>,
    n: usize,
    acc: &mut Vec<Term>,
    cont: &mut dyn FnMut(&mut Descent<Z>, &[Term]),
) {
    if n == 0 {
        cont(d, acc);
        return;
    }
    read_one_subterm(d, &mut |d, term| {
        acc.push(term.clone());
        read_n_subterms(d, n - 1, acc, cont);
        acc.pop();
    });
}

/// Read `len` raw payload bytes (each a trie branch), accumulating them, then call `cont`.
fn read_payload<Z: SubtermZip>(
    d: &mut Descent<Z>,
    len: usize,
    acc: &mut Vec<u8>,
    cont: &mut dyn FnMut(&mut Descent<Z>, &[u8]),
) {
    if len == 0 {
        cont(d, acc);
        return;
    }
    for b in child_bytes(&d.z) {
        d.z.descend_byte(b);
        acc.push(b);
        read_payload(d, len - 1, acc, cont);
        acc.pop();
        d.z.ascend();
    }
}

/// Match query subterm `q` against one stored subterm at `d.z`, threading the shared
/// substitution; `cont` runs for every way it unifies, with `d.z` advanced past the matched
/// stored subterm. This is the per-position WAM read-mode / substitution-tree retrieval.
fn match_subterm<Z: SubtermZip>(
    d: &mut Descent<Z>,
    q: &Term,
    cont: &mut dyn FnMut(&mut Descent<Z>),
) {
    match q {
        // A query variable unifies with whatever stored subterm sits here. WAM's read-mode split:
        // an UNBOUND variable is `unify_variable` (bind it to whatever the data holds, so enumerate
        // the stored subterms and unify); an already-BOUND variable is `unify_value` (its value is
        // fixed, so SEEK that structure on the trie instead of scanning every stored subterm and
        // filtering). The seek prunes the descent to the one matching branch, turning a per-match
        // O(domain) scan into an O(depth) descent; the answer set is unchanged (a bound variable's
        // value matches exactly the stored subterms unify would have kept), pinned byte-identical by
        // the differential against the materialized leapfrog.
        Term::Var(qv) => {
            let qv = *qv;
            let resolved = d.env.resolve(&Term::Var(qv));
            if let Term::Var(_) = resolved {
                read_one_subterm(d, &mut |d, term| {
                    let m = d.env.mark();
                    if d.env.unify(&Term::Var(qv), term) {
                        cont(d);
                    }
                    d.env.rollback(m);
                });
            } else {
                // Bound: match its resolved value as if the factor named it literally here.
                match_subterm(d, &resolved, cont);
            }
        }
        // A structured query (symbol or compound) matches the same structure in the data, OR
        // is captured by a stored wildcard variable.
        _ => {
            // (A) capture: a stored wildcard variable binds the whole query subterm. Skipped in
            // equality mode, where a stored variable never absorbs a query compound.
            if d.capture {
                for b in child_bytes(&d.z) {
                    if !(0x80..=0xC0).contains(&b) {
                        continue;
                    }
                    d.z.descend_byte(b);
                    let slots_len = d.slots.len();
                    let dv = if b == NEWVAR_BYTE {
                        let id = d.fresh;
                        d.fresh += 1;
                        d.slots.push(id);
                        id
                    } else {
                        d.slots[(b & LOW6) as usize]
                    };
                    let m = d.env.mark();
                    let qr = d.env.resolve(q);
                    if d.env.unify(&Term::Var(dv), &qr) {
                        cont(d);
                    }
                    d.env.rollback(m);
                    d.slots.truncate(slots_len);
                    d.z.ascend();
                }
            }
            // (B) structural descent into matching data structure.
            match q {
                Term::Sym(s) => {
                    let head = TAG_SYMSIZE | s.len() as u8;
                    if d.z.descend_byte(head) {
                        if descend_exact(&mut d.z, s.as_bytes()) {
                            cont(d);
                            for _ in 0..s.len() {
                                d.z.ascend();
                            }
                        }
                        d.z.ascend();
                    }
                }
                Term::App(args) => {
                    let head = TAG_ARITY | args.len() as u8;
                    if d.z.descend_byte(head) {
                        match_seq(d, args, 0, cont);
                        d.z.ascend();
                    }
                }
                Term::Var(_) => unreachable!(),
            }
        }
    }
}

/// Descend exactly the bytes of `bytes`, returning false (and restoring `z`) if any is absent.
fn descend_exact<Z: SubtermZip>(z: &mut Z, bytes: &[u8]) -> bool {
    let mut descended = 0;
    for &b in bytes {
        if z.descend_byte(b) {
            descended += 1;
        } else {
            for _ in 0..descended {
                z.ascend();
            }
            return false;
        }
    }
    true
}

/// Match `args[i..]` against successive stored subterms at `d.z`, then call `cont`.
fn match_seq<Z: SubtermZip>(
    d: &mut Descent<Z>,
    args: &[Term],
    i: usize,
    cont: &mut dyn FnMut(&mut Descent<Z>),
) {
    if i == args.len() {
        cont(d);
        return;
    }
    match_subterm(d, &args[i], &mut |d| {
        match_seq(d, args, i + 1, cont);
    });
}

/// The conjunctive driver: match factor `fi` against the whole trie, and on each full match
/// recurse to the next factor under the shared substitution; record the answer at the end.
fn solve<Z: SubtermZip>(d: &mut Descent<Z>, fi: usize) {
    if fi == d.factors.len() {
        let key = answer_key(&d.env, d.query_vars);
        d.out.insert(key);
        return;
    }
    // The cursor and the stored-variable slots are shared across factors, so a deeper factor
    // must not clobber this one's position. Snapshot both, restart this factor at the root,
    // and restore on the way out; the substitution stays shared (that is the propagation).
    let saved_path = d.z.save_path();
    let saved_slots = std::mem::take(&mut d.slots);
    d.z.restore_path(&[]);
    let factor = d.factors[fi].clone();
    match_subterm(d, &factor, &mut |d| {
        solve(d, fi + 1);
    });
    d.z.restore_path(&saved_path);
    d.slots = saved_slots;
}

/// All answers to `q` against the byte-trie rooted at `z`, under full unification, lazily over
/// the trie. `fresh_base` is the first id handed to stored (data) variables; it must be
/// disjoint from the query variable ids (the query uses small ids, so a large base is safe).
/// The return is byte-identical to `unijoin::leapfrog_unify_join` (canonical answer keys).
pub fn unify_join_z<Z: SubtermZip>(z: Z, q: &Conj, fresh_base: u32) -> BTreeSet<Vec<u8>> {
    unify_join_z_opts(z, q, fresh_base, true)
}

/// As [`unify_join_z`], with `capture` selecting the semantics: `true` is the full unification
/// join with data-side capture, `false` is the plain relational (equality) join. The two differ
/// by exactly the data-side-capture answers, so pairing them isolates the capture contribution.
pub fn unify_join_z_opts<Z: SubtermZip>(
    z: Z,
    q: &Conj,
    fresh_base: u32,
    capture: bool,
) -> BTreeSet<Vec<u8>> {
    let mut d = Descent {
        factors: &q.patterns,
        query_vars: &q.query_vars,
        z,
        env: Env::new(),
        fresh: fresh_base,
        slots: Vec::new(),
        out: BTreeSet::new(),
        capture,
    };
    solve(&mut d, 0);
    d.out
}

/// Convenience over an owned `ByteTrie` built from `facts`: the prototype's in-process entry.
pub fn trie_unify_join(q: &Conj, facts: &[Term]) -> BTreeSet<Vec<u8>> {
    let trie = ByteTrie::from_terms(facts);
    unify_join_z(TrieZipper::new(&trie), q, 1_000_000)
}

/// The same descent with data-side capture DISABLED: a stored wildcard never absorbs a query
/// compound, so a query pattern matches only by structural equality up to query-variable binding.
/// This is the relational (equality) join, the semantics a Datalog-style engine, including MORK's
/// current fast path, computes. Its answers are a subset of [`trie_unify_join`]'s; the missing
/// ones are exactly the data-side captures.
pub fn equality_join(q: &Conj, facts: &[Term]) -> BTreeSet<Vec<u8>> {
    let trie = ByteTrie::from_terms(facts);
    unify_join_z_opts(TrieZipper::new(&trie), q, 1_000_000, false)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::parse;
    use crate::unijoin::leapfrog_unify_join;

    fn space(facts: &[&str]) -> Vec<Term> {
        facts.iter().map(|s| parse(s)).collect()
    }

    /// The lazy trie join must equal the sealed materialized join, exactly.
    fn agree(pats: &[&str], facts: &[&str]) {
        let q = Conj::parse(pats);
        let sp = space(facts);
        let got = trie_unify_join(&q, &sp);
        let want = leapfrog_unify_join(&q, &sp);
        assert_eq!(
            got, want,
            "trie_unify_join != leapfrog for {pats:?} over {facts:?}"
        );
    }

    #[test]
    fn ground_path() {
        agree(
            &["(edge $x $y)", "(edge $y $z)"],
            &["(edge a b)", "(edge b d)", "(edge a c)", "(edge c d)"],
        );
    }

    #[test]
    fn data_side_capture_constant() {
        agree(&["(rel $x b)"], &["(rel a $w)"]);
    }

    #[test]
    fn capture_nonground_compound() {
        agree(&["(r (a $p) b)", "(r (b) $p)"], &["(r $d b)", "(r a b)"]);
    }

    #[test]
    fn coreferent_fact() {
        agree(
            &["(e $x $y)", "(e $y $z)"],
            &["(e $u $u)", "(e a b)", "(e b c)"],
        );
    }

    #[test]
    fn occurs_yields_nothing() {
        agree(&["(e $x (f $x))"], &["(e $w $w)"]);
    }

    #[test]
    fn join_propagated_capture() {
        agree(
            &["(e (k $x0) $x1)", "(e (k $x1) $x2)", "(h $x2 $x0)"],
            &["(e (k $s2) v0)", "(e $s1 $s1)", "(h $s0 $s0)"],
        );
    }

    /// The equality join (capture off) is exactly the capture join minus the data-side captures:
    /// a subset on every case, and strictly smaller on the genuine-capture cases. This pins the
    /// reference the reproduction uses to isolate the contribution.
    #[test]
    fn equality_join_is_capture_join_minus_capture() {
        use crate::corpus;
        let mut differ = 0usize;
        for case in corpus::cases() {
            let q = Conj::parse(case.patterns);
            let sp = space(case.facts);
            let full = trie_unify_join(&q, &sp);
            let eq = equality_join(&q, &sp);
            assert!(
                eq.is_subset(&full),
                "case {:?}: the equality join is not a subset of the capture join",
                case.name
            );
            if eq != full {
                differ += 1;
            }
        }
        assert!(
            differ >= 3,
            "the corpus must contain cases where capture adds answers: {differ}"
        );
    }
}
