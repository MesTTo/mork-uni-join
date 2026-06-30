# A worst-case-optimal trie-join that unifies over schematic data

The worst-case-optimal trie-join (leapfrog triejoin) is fast, but it joins ground tuples: it
binds one variable at a time and intersects each variable's domain across relations by equality
on a sorted key. This is a small Rust prototype that replaces that equality intersection with
unification, so the same variable-at-a-time trie join works over a space whose stored facts carry
variables of their own (schematic facts).

MORK's worst-case-optimal join joins ground tuples, and its sidecar declines schematic facts
wholesale (`SidecarSchematicDecline`). This join does not decline them.
Its per-variable intersection is a unification step threaded through a WAM trail, so it stays
worst-case-optimal on the ground structure while handling the variables in the data.

## The join

`src/unijoin.rs` is the leapfrog triejoin with unification. Each pattern is matched against the
space into a relation of bindings, indexed into a trie over the shared variable order. The
descent binds one variable at a time; at each variable it leads the relation with the smallest
domain and intersects the rest, but the intersection is unification, not equality:

- when the lead pins the variable to a ground term, each follower finds the match by binary
  search over its sorted ground children (the worst-case-optimal seek), and its few non-ground
  children (the wildcards from schematic facts) are merged in by unification;
- a binding made at one cursor constrains the others through the shared trail, and backtracking
  restores it in O(1) per binding.

On ground data this is exactly the ordinary leapfrog, because there unification is equality. On
schematic data it is the genuine unification join, still variable-at-a-time, with no per-tuple
nested-loop fallback. It returns the same answers, byte for byte on the MORK encoding, as a full
nested-loop unifier, checked on 6000 random ground-and-schematic queries and against the answers
the live MORK ProductZipper produced.

## Run it

```
cargo test            # 60 unit tests, a 6000-case differential, and a check against real MORK answers
cargo run --example demo
cargo run --release --example bench   # the unification triejoin vs the naive unifier
```

## Benchmark

`cargo run --release --example bench` runs the triangle `(e $x $y), (e $y $z), (e $x $z)` over a
space that contains schematic edges, and compares the leapfrog-unify join against the naive
unifier (the full nested-loop matcher, the reference). The workload is the AGM-blowup triangle: a
hub of `s` in- and out-edges gives s^2 two-paths but no triangle, a small complete digraph gives
the ground triangles, and a few schematic edges (a node related to a variable) add answers that
need unification. Both methods return identical answers on every row.

```
   N     sch  decline_ans  uni_ans   naive_ms  leapfrog_ms   speedup
   65      3      120        270        6.767      0.267       25.3x
   97      3      120        366       21.030      0.361       58.3x
  161      3      120        558      104.117      0.521      200.0x
  289      3      120        942      683.135      0.895      763.0x
  545      3      120       1710     4831.741      1.702     2839.1x
```

Two things, both measured. The leapfrog-unify join scales near-linearly where the naive unifier
is quadratic, so the gap widens with size (2839x at 545 edges, and about 8870x at a thousand
before the example caps the slow naive rows). And unification is doing the work, not decorating
it: declining the schematic facts finds 120 answers, the unification join finds 1710, the
difference being exactly the triangles the schematic edges complete.

The honest framing of the speedup: the baseline is the naive nested-loop unifier, and the gap is
the AGM separation (worst-case-optimal versus a quadratic intermediate) now holding with
unification in the loop. It is not a number against a tuned engine; it is the cost of doing
unification the naive way versus doing it inside a worst-case-optimal join.

## When it is worst-case-optimal

The seek is worst-case-optimal exactly when the join keys come out ground. That is the common
case, and it includes queries that genuinely need unification: in `func_type_unification`, `($f)`
unifies with `(f)` to bind `$f = f`, a ground value, so the join key is ground and the seek is a
binary search. When a data variable from a schematic fact reaches a join key, that key is not
ground, equality is strictly weaker than unification, and the intersection branches by the
unification fan-out instead of seeking. The join stays correct there (it is the same trail-backed
unification), it just is not sublinear on that variable. So it is worst-case-optimal on the
ground structure and unification-complete everywhere.

## Formal verification

That condition is machine-checked. `proofs/RoutingSafe.thy` proves in Isabelle/HOL (Isabelle2025-2,
no `sorry`, no `oops`, no axioms, builds clean) that on ground terms two terms unify if and only
if they are equal (`ground_unifiable_iff_eq`), and lifts it to the join: under ground join keys
the unification-join equals the equality-join (`leapfrog_safe_join_eq`), with a witness that off
the ground case unification is strictly weaker (`nonground_unifiable_strictly_weaker`). That is
why the seek is exact on ground keys and why the schematic case must branch. The proof is of the
condition's soundness, an abstract model; it does not verify the Rust implementation, which the
6000-case differential and the ProductZipper fixture cover. Reproduce it with
`cd proofs && isabelle build -d . UniJoinRoutingSafe`.

## Checked against the real MORK matcher

The unit differential checks the join against this crate's own unifier. The other check uses
MORK's actual matcher: `tests/mork_fixture.txt` holds answers the live ProductZipper produced,
each line a body, a space, and the ground answers MORK emitted, captured by running `exec` and
`metta_calculus` through the real matcher and rendered with this crate's decoder.
`tests/against_real_mork.rs` replays each case through the join and checks that it never misses a
ground answer the matcher produced, and that where they differ it is only the join finding more.
On the captured corpus, 24 cases: 23 match the live matcher exactly. On the 24th the join returns
two extra answers, both needing a stored variable to match a compound (data-side capture); the
naive reference unifier returns them too. That case is the subtle part of the matcher semantics,
and the fixture does not try to settle it.

## What it extends

MORK's worst-case-optimal join (`generic_join`, `trie_join` in the fork) intersects by exact key
over ground tuples. This is the same trie-cursor skeleton with the intersection promoted to
unification, which is what lets it run over a space that holds variables, the case MORK's sidecar
declines.

The pieces are prior art; the combination is the new part. Worst-case-optimal joins come from
Leapfrog Triejoin (Veldhuizen, ICDT 2014), generic join (Ngo, Porat, Re, Rudra, PODS 2012), and
the AGM bound (Atserias, Grohe, Marx, FOCS 2008). Relational e-matching (Zhang, Wang, Willsey,
Tatlock, POPL 2022) makes generic join worst-case-optimal for matching but assumes ground e-class
ids; the non-ground data case is what it leaves out and what this handles. Substitution and
discrimination trees (Graf 1995; Ramakrishnan, Sekar, Voronkov, Handbook of Automated Reasoning
2001) retrieve unifiable non-ground terms, but for a single relation, not a multi-way join. The
unification and anti-unification lattice (Plotkin, Reynolds 1970) gives the algebra: unification
is the meet. The per-binding store with O(1) rollback is the WAM trail.

## Exploratory: fuzzy matching

The exact unification join is the Boolean corner of a more general engine: the same trie descent
parameterized by a semiring for cost and a lattice for types. The `semiring.rs`, `scored.rs`,
`antiunify.rs`, `quantale.rs`, and `zorder.rs` modules sketch that out (a tropical semiring scores
a near-miss by distance, anti-unification is the lattice dual, a Morton curve turns a box query
into a range scan). These are exploratory, not load-bearing for the join above.

Ahmad Mesto (MesTTo)
