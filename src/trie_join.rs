//! The unification-aware join, executed LAZILY over the byte-trie with no materialized
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
//! This first cut prunes where the query is structured (it seeks that structure on the
//! trie) and branches only where a variable meets the data; a later pass adds the
//! leapfrog cross-factor seek for full worst-case optimality. Answers are byte-identical
//! to the materialized join regardless.

use crate::oracle::{answer_key, Conj};
use crate::term::Term;
use crate::trie::{ByteTrie, TrieZipper};
use crate::unify::Env;
use std::collections::BTreeSet;

const TOP2: u8 = 0b1100_0000;
const TAG_ARITY: u8 = 0b0000_0000;
const TAG_VARREF: u8 = 0b1000_0000;
const TAG_SYMSIZE: u8 = 0b1100_0000;
const NEWVAR_BYTE: u8 = 0b1100_0000;
const LOW6: u8 = 0b0011_1111;

#[inline]
fn child_bytes(z: &TrieZipper) -> Vec<u8> {
    let mask = z.child_mask();
    let mut out = Vec::new();
    for hi in 0..4u8 {
        let mut w = mask.0[hi as usize];
        while w != 0 {
            let lo = w.trailing_zeros() as u8;
            out.push((hi << 6) | lo);
            w &= w - 1;
        }
    }
    out
}

/// Immutable context for one join: the trie, the query factors, and the head variables.
struct Ctx<'a> {
    trie: &'a ByteTrie,
    factors: &'a [Term],
    query_vars: &'a [u32],
}

/// The mutable join state: the shared substitution, the next fresh stored-variable id, and
/// the collected answers.
struct St {
    env: Env,
    fresh: u32,
    out: BTreeSet<Vec<u8>>,
}

type Cont<'a, 'c> = dyn FnMut(&Ctx<'a>, &mut St, &mut TrieZipper<'a>, &mut Vec<u32>) + 'c;
type ContTerm<'a, 'c> = dyn FnMut(&Ctx<'a>, &mut St, &mut TrieZipper<'a>, &mut Vec<u32>, &Term) + 'c;

/// Read every complete stored subterm branching at `z`'s focus, as a `Term` whose variables
/// use the fact's stored-variable slots (a `NewVar` allocates a fresh id, a `VarRef` reads an
/// earlier one), so coreference inside the fact is preserved. `cont` runs once per subterm
/// with `z` advanced past it; the trie and slots are restored on return.
fn read_one_subterm<'a>(
    ctx: &Ctx<'a>,
    st: &mut St,
    z: &mut TrieZipper<'a>,
    slots: &mut Vec<u32>,
    cont: &mut ContTerm<'a, '_>,
) {
    for b in child_bytes(z) {
        z.descend_to_byte(b);
        match b & TOP2 {
            TAG_ARITY => {
                let n = (b & LOW6) as usize;
                read_n_subterms(ctx, st, z, slots, n, &mut Vec::new(), &mut |ctx, st, z, slots, kids| {
                    cont(ctx, st, z, slots, &Term::App(kids.to_vec()));
                });
            }
            TAG_VARREF => {
                // VarRef(i): a repeat of an earlier stored variable in this fact.
                let idx = (b & LOW6) as usize;
                let v = slots[idx];
                cont(ctx, st, z, slots, &Term::Var(v));
            }
            _ => {
                if b == NEWVAR_BYTE {
                    let id = st.fresh;
                    st.fresh += 1;
                    slots.push(id);
                    cont(ctx, st, z, slots, &Term::Var(id));
                    slots.pop();
                } else {
                    // SymbolSize(len): read the payload bytes (they branch by symbol).
                    let len = (b & LOW6) as usize;
                    read_payload(ctx, st, z, slots, len, &mut Vec::new(), &mut |ctx, st, z, slots, bytes| {
                        let s = String::from_utf8(bytes.to_vec()).expect("utf8 symbol");
                        cont(ctx, st, z, slots, &Term::Sym(s));
                    });
                }
            }
        }
        z.ascend_byte();
    }
}

/// Read `n` complete subterms in sequence, accumulating them, then call `cont` with the list.
fn read_n_subterms<'a>(
    ctx: &Ctx<'a>,
    st: &mut St,
    z: &mut TrieZipper<'a>,
    slots: &mut Vec<u32>,
    n: usize,
    acc: &mut Vec<Term>,
    cont: &mut dyn FnMut(&Ctx<'a>, &mut St, &mut TrieZipper<'a>, &mut Vec<u32>, &[Term]),
) {
    if n == 0 {
        cont(ctx, st, z, slots, acc);
        return;
    }
    read_one_subterm(ctx, st, z, slots, &mut |ctx, st, z, slots, term| {
        acc.push(term.clone());
        read_n_subterms(ctx, st, z, slots, n - 1, acc, cont);
        acc.pop();
    });
}

/// Read `len` raw payload bytes (each a trie branch), accumulating them, then call `cont`.
fn read_payload<'a>(
    ctx: &Ctx<'a>,
    st: &mut St,
    z: &mut TrieZipper<'a>,
    slots: &mut Vec<u32>,
    len: usize,
    acc: &mut Vec<u8>,
    cont: &mut dyn FnMut(&Ctx<'a>, &mut St, &mut TrieZipper<'a>, &mut Vec<u32>, &[u8]),
) {
    if len == 0 {
        cont(ctx, st, z, slots, acc);
        return;
    }
    for b in child_bytes(z) {
        z.descend_to_byte(b);
        acc.push(b);
        read_payload(ctx, st, z, slots, len - 1, acc, cont);
        acc.pop();
        z.ascend_byte();
    }
}

/// Match query subterm `q` against one stored subterm at `z`, threading the shared
/// substitution; `cont` runs for every way it unifies, with `z` advanced past the matched
/// stored subterm. This is the per-position WAM read-mode / substitution-tree retrieval.
fn match_subterm<'a>(
    ctx: &Ctx<'a>,
    st: &mut St,
    q: &Term,
    z: &mut TrieZipper<'a>,
    slots: &mut Vec<u32>,
    cont: &mut Cont<'a, '_>,
) {
    match q {
        // A query variable unifies with whatever stored subterm sits here (ground, compound,
        // or another data variable). Enumerate them and unify.
        Term::Var(qv) => {
            let qv = *qv;
            read_one_subterm(ctx, st, z, slots, &mut |ctx, st, z, slots, term| {
                let m = st.env.mark();
                if st.env.unify(&Term::Var(qv), term) {
                    cont(ctx, st, z, slots);
                }
                st.env.rollback(m);
            });
        }
        // A structured query (symbol or compound) matches the same structure in the data, OR
        // is captured by a stored wildcard variable.
        _ => {
            // (A) capture: a stored wildcard variable binds the whole query subterm.
            for b in child_bytes(z) {
                if !(0x80..=0xC0).contains(&b) {
                    continue;
                }
                z.descend_to_byte(b);
                let slots_len = slots.len();
                let dv = if b == NEWVAR_BYTE {
                    let id = st.fresh;
                    st.fresh += 1;
                    slots.push(id);
                    id
                } else {
                    slots[(b & LOW6) as usize]
                };
                let m = st.env.mark();
                let qr = st.env.resolve(q);
                if st.env.unify(&Term::Var(dv), &qr) {
                    cont(ctx, st, z, slots);
                }
                st.env.rollback(m);
                slots.truncate(slots_len);
                z.ascend_byte();
            }
            // (B) structural descent into matching data structure.
            match q {
                Term::Sym(s) => {
                    let head = TAG_SYMSIZE | s.len() as u8;
                    if z.descend_to_byte(head) {
                        if descend_exact(z, s.as_bytes()) {
                            cont(ctx, st, z, slots);
                            for _ in 0..s.len() {
                                z.ascend_byte();
                            }
                        }
                        z.ascend_byte();
                    }
                }
                Term::App(args) => {
                    let head = TAG_ARITY | args.len() as u8;
                    if z.descend_to_byte(head) {
                        match_seq(ctx, st, args, 0, z, slots, cont);
                        z.ascend_byte();
                    }
                }
                Term::Var(_) => unreachable!(),
            }
        }
    }
}

/// Descend exactly the bytes of `bytes`, returning false (and leaving `z` partway) if any is
/// absent. The caller ascends on the matched path; a false return means no match here.
fn descend_exact(z: &mut TrieZipper, bytes: &[u8]) -> bool {
    let mut descended = 0;
    for &b in bytes {
        if z.descend_to_byte(b) {
            descended += 1;
        } else {
            for _ in 0..descended {
                z.ascend_byte();
            }
            return false;
        }
    }
    true
}

/// Match `args[i..]` against successive stored subterms at `z`, then call `cont`.
fn match_seq<'a>(
    ctx: &Ctx<'a>,
    st: &mut St,
    args: &[Term],
    i: usize,
    z: &mut TrieZipper<'a>,
    slots: &mut Vec<u32>,
    cont: &mut Cont<'a, '_>,
) {
    if i == args.len() {
        cont(ctx, st, z, slots);
        return;
    }
    match_subterm(ctx, st, &args[i], z, slots, &mut |ctx, st, z, slots| {
        match_seq(ctx, st, args, i + 1, z, slots, cont);
    });
}

/// The conjunctive driver: match factor `fi` against the whole trie, and on each full match
/// recurse to the next factor under the shared substitution; record the answer at the end.
fn solve(ctx: &Ctx<'_>, st: &mut St, fi: usize) {
    if fi == ctx.factors.len() {
        st.out.insert(answer_key(&st.env, ctx.query_vars));
        return;
    }
    let factor = ctx.factors[fi].clone();
    let mut z = TrieZipper::new(ctx.trie);
    let mut slots: Vec<u32> = Vec::new();
    match_subterm(ctx, st, &factor, &mut z, &mut slots, &mut |ctx, st, _z, _slots| {
        solve(ctx, st, fi + 1);
    });
}

/// All answers to `q` against `facts` under full unification, lazily over the byte-trie.
/// The return is byte-identical to `unijoin::leapfrog_unify_join` (canonical answer keys).
pub fn trie_unify_join(q: &Conj, facts: &[Term]) -> BTreeSet<Vec<u8>> {
    let trie = ByteTrie::from_terms(facts);
    let ctx = Ctx { trie: &trie, factors: &q.patterns, query_vars: &q.query_vars };
    let mut st = St { env: Env::new(), fresh: 1_000_000, out: BTreeSet::new() };
    solve(&ctx, &mut st, 0);
    st.out
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
        assert_eq!(got, want, "trie_unify_join != leapfrog for {pats:?} over {facts:?}");
    }

    #[test]
    fn ground_path() {
        agree(&["(edge $x $y)", "(edge $y $z)"], &["(edge a b)", "(edge b d)", "(edge a c)", "(edge c d)"]);
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
        agree(&["(e $x $y)", "(e $y $z)"], &["(e $u $u)", "(e a b)", "(e b c)"]);
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
}
