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

## Wired into MORK's live flip

The join is no longer a standalone prototype. It is ported into the MORK kernel and runs on the real
flip path. When the sidecar would decline a cyclic body to the ProductZipper because a joined relation
holds a schematic fact, the templates are driven from this join instead, as long as neither the query
nor a schematic fact under a join prefix carries a non-ground compound. That is the conservative
boundary for issue-29 data-side capture (a stored variable binding a non-ground compound, the one place
unification finds more than the ProductZipper): a non-ground compound is the only thing such a capture
can latch onto, and unification never fabricates one that is not already in the syntax, so off that
case the two joins agree and the route is byte-identical to the matcher it replaces.

The port is byte-safe: symbols are raw bytes, so it consumes MORK's tag-byte encoding directly, and a
5000-case differential cross-checks it against this prototype. Only ground answer components bind for
the emit, because a ground term carries no variable identity to collide under MORK's `(n, v)` variable
scheme; a template over a non-ground variable instantiates fresh and the non-ground row the exec drops.

The correctness gate is a pair of live A/B differentials through `metta_calculus`, each running cyclic
schematic bodies twice, route on versus forced onto the ProductZipper, asserting the emitted ground
answers are byte-for-byte identical. The broad one (1500 cases) spans arity-2 edge cycles and arity-3
rotation cycles over several relations. The adversarial one (3000 cases) adds mixed relations in one
cycle, compound-wrapped endpoints, and coreferent and two-deep nested schematic facts; it is what
caught the subtle case, where a per-factor capture check missed capture propagated through the join
(`(out (k v0) (k v0))` needing three stored variables to bind the same compound), and pinned the
conservative gate above. Both never diverge. The full kernel test suite (363 tests) passes unchanged
with the route on.

The recovery, measured against the real ProductZipper rather than the naive unifier, is the AGM
separation on the live path. The same cyclic triangle over a hub-blowup space with schematic edges on a
join key, run both ways:

```
   s     unify(WCO)   decline(ProductZipper)   recovery
  128      1.8 ms            2.7 ms               1.5x
  256      2.8 ms            7.8 ms               2.8x
  512      5.8 ms           26.9 ms               4.7x
 1024     13.9 ms          100.2 ms               7.2x
 2048     33.0 ms          387.3 ms              11.7x
 4096     96.2 ms            1.503 s              15.6x
```

The ProductZipper materializes the s^2 two-paths the worst-case-optimal join prunes, so the gap widens
with the hub. This is single-to-low-double digits, not the prototype bench's thousands, because the
baseline here is the real matcher, not a quadratic nested loop.

The route reads its facts through the PathMap index, descending to each relation prefix on the same
snapshot the ProductZipper reads, not by scanning the whole space. Flooding the space with unrelated
facts leaves the route's time flat where a full scan climbed with the space size, so its cost tracks
the joined relations. It still materializes those relation facts into the join's tries; streaming the
join straight off the PathMap zipper, with no decode at all, is the next step, and the section below
builds it.

The route is on by default; `MORK_UNIFY_ROUTE=0` forces the ProductZipper for an A/B run. Its scope is
exactly the cyclic-join-over-schematic-data case: it fires only on a cyclic body with a schematic fact
under a join prefix. A two-factor linear join like process_calculus's petri rule never reaches the
cyclic path, so it neither declines nor routes and is byte-identical either way; ground cyclic benches
(clique, transitive) carry no schematic facts, so they never trip the gate.

## Streaming the join off the zipper

The route above still decodes the joined relations into the join's tries. This closes that step: a
worst-case-optimal unification join that seeks the PathMap byte-trie directly, with no materialized
domain, over MORK's variable-width terms. It lives in the fork at `kernel/src/zipper_join.rs`.

The primitive is a subterm cursor. MORK's encoding is prefix-free: an arity byte owes a fixed number
of subterms, a symbol-size byte owes its payload bytes, a variable is one byte. So a complete subterm
is self-delimiting and the trie's branches fall on subterm boundaries. The cursor enumerates and seeks
complete subterms branching from a zipper focus, the backtracking trie lower bound built from
`child_mask` and `descend_to_byte`. That variable-width seek is what the fixed-width zipper-join
prototypes could not express.

The intersection is a trail union-find, not a structural unifier. In the routed scope, the same
no-non-ground-compound gate the live route uses, every join key is a ground byte-slice or a variable,
so unification degenerates: a ground subterm is an opaque value compared by equality, a variable
unifies with anything, and nothing recurses into compound structure. `proofs/ZipperUnifySafe.thy`
machine-checks that degeneracy. On flat terms, a variable or a fully ground term, structural
unifiability equals the union-find decision (`flat_unifiable_iff_uf_agree`); it lifts to the join
intersection (`zipper_uf_join_eq_unification_join`); and a non-ground compound is the witness that
breaks it, which is the gate's boundary (`nonflat_uf_unsound`). Builds clean, no `sorry`.

The join is checked byte-identical to the real ProductZipper: five hand cases (compatible and cyclic
triangles, a schematic edge at the join, a coreferent schematic fact, a shared-key conjunction) and
250 random cases over six shapes, each run through MORK's matcher and through the join and asserted to
return the same ground answers.

The point of not materializing is that the cost tracks the answer, not the space. On a selective
two-path `(e a $y)(e $y $z)` from a fixed start, as the relation `e` fills with edges unreachable from
`a`, the join and the ProductZipper return the same 25 answers, but the ProductZipper's cost climbs
with the relation while the join stays flat:

```
  junk     ProductZipper     zipper     speedup
     0          9.1 us         4.7 us       1.9x
  1024         24.9 us         5.0 us       5.0x
 16384         49.8 us         4.8 us      10.3x
 65536          182 us         4.9 us      37.4x
```

Against the materialized unification join, the one that does decode the relation into tries, the same
query shows the cost of materializing:

```
  junk      materialized     zipper     speedup
     0          21.7 us        4.8 us       4.5x
  1024          1.11 ms        5.0 us        222x
 16384           122 ms        5.0 us      24337x
 65536          2.72 s         5.0 us     542048x
```

The lead among the join's factors is chosen by a bounded subterm count, so a selective factor drives
the join and the rest seek.

A cyclic query, the triangle the live route handles, has a factor whose columns are out of the binding
order, so the join cannot seek it forward. That factor, and only that one, is re-indexed into a fresh
map in binding order, its variables renumbered so a coreferent schematic fact stays sound; the others
stay zero-copy. That recovers worst-case optimality on the cycle, and because only the inverted factor
is materialized where the live route decodes every factor into tries, it beats that route, the gap
widening with size:

```
  s     ProductZipper   materialized   reindex-zipper
   64        589 us          304 us         111 us
  512        25.5 ms        2.47 ms         359 us
 2048         401 ms        17.7 ms        1.37 ms
```

All three return the 120 triangles. Against the materialized route the zipper is 2.7x at s=64 and
12.9x at s=2048; against the ProductZipper, 293x. The one case left at parity is an acyclic
output-bound query whose answer is itself s^2, where every join method must enumerate the output.

It is now the default kernel in MORK's unification route, gated by `SIDECAR_ZIPPER_JOIN_ENABLED`, with
the materialized join as the fallback for a body outside the factor model (a non-leading constant or a
compound column). A direct kernel A/B over 1500 cyclic bodies, the zipper kernel exercised on 930 of
them, asserts byte-identical emit to the materialized join; the live ProductZipper differentials, 1500
broad and 3000 adversarial, still hold with it on; the full kernel suite passes.

End to end through `metta_calculus` the win is smaller than the isolated join's, because the join is a
fraction of a flip step: the parse, the rewrite, and the emit are shared. On the hub-blowup cycle the
route is at parity at 64 edges and 2.1x at 2048, the gap widening with the relation:

```
  s     materialized-route   zipper-route   speedup
   64          598 us             619 us       0.97x
 1024         9.73 ms            6.02 ms        1.62x
 2048         21.0 ms            10.1 ms        2.09x
```

The join numbers earlier are the algorithm's merit; this is the deployed benefit.

## What it extends

MORK's worst-case-optimal join (`generic_join`, `trie_join` in the fork) intersects by exact key
over ground tuples. This is the same trie-cursor skeleton with the intersection promoted to
unification, which is what lets it run over a space that holds variables, the case MORK's sidecar
declines.

The pieces are prior art; the combination is the new part. Worst-case-optimal joins come from
Leapfrog Triejoin (Veldhuizen, ICDT 2014), generic join (Ngo, Porat, Re, Rudra, PODS 2012), and
the AGM bound (Atserias, Grohe, Marx, FOCS 2008). The byte-level form, intersecting on the trie of
the key encoding rather than an interned-integer domain, is radix triejoin (Fekete, Franks, Jordan,
Scholz, 2019); the new part in `zipper_join.rs` is running it over MORK's variable-width prefix-free
terms with no interning and with the intersection promoted to unification. Variable-length keys are
the known hard case for these joins (Freitag, Bandle, Schmidt, Kemper, Neumann, VLDB 2020), usually
met with hash tries; MORK's prefix-free encoding makes the subterm boundaries self-delimiting, so the
byte-trie reads them directly with a parse stack. Relational e-matching (Zhang, Wang, Willsey,
Tatlock, POPL 2022) makes generic join worst-case-optimal for matching but assumes ground e-class
ids; the non-ground data case is what it leaves out and what this handles. The unification side is
older still: substitution-tree indexing (Graf 1995, 1996; Ramakrishnan, Sekar, Voronkov, Handbook
of Automated Reasoning 2001) retrieves unifiable terms with variables on both sides, and Graf's
simultaneous-unification operations handle whole sets of query substitutions at once. What that
line does not carry is the worst-case-optimal, variable-at-a-time AGM guarantee. So the new part
is narrow and specific: the combination, a leapfrog whose intersection is substitution-tree-style
unification, not either piece alone. The unification and anti-unification lattice (Plotkin,
Reynolds 1970) gives the algebra: unification is the meet. The per-binding store with O(1)
rollback is the WAM trail.

## Exploratory: fuzzy matching

The exact unification join is the Boolean corner of a more general engine: the same trie descent
parameterized by a semiring for cost and a lattice for types. The `semiring.rs`, `scored.rs`,
`antiunify.rs`, `quantale.rs`, and `zorder.rs` modules sketch that out (a tropical semiring scores
a near-miss by distance, anti-unification is the lattice dual, a Morton curve turns a box query
into a range scan). These are exploratory, not load-bearing for the join above.

Ahmad Mesto (MesTTo)
