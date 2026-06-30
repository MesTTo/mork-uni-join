# A worst-case-optimal trie-join that unifies over schematic data

The worst-case-optimal trie-join is fast, but it joins ground tuples. This is a small Rust
prototype for the case it cannot do on its own: a space whose stored facts carry variables
of their own (schematic facts), so the join has to agree with unification. MORK's sidecar
declines that case wholesale (`SidecarSchematicDecline`). The prototype shows the join does
not need to change; it needs a routing condition. The same condition is implemented and
validated in a working branch of the fork, not yet in the public release.

Everything it builds on already exists: the leapfrog triejoin, the conjunction lowering, and
the WAM trail (`trie_join`, `generic_join`, `BindingSidecarPlan` in the fork; `wcojoin.ts`
and `trail.ts` in MeTTaLingo). This is the layer on top.

## The result

The leapfrog's per-variable intersection is exact and worst-case-optimal whenever
unification pins every join-position variable to a ground term. That is the common case, and
it includes queries that genuinely need unification. When a schematic stored fact would bind
a join variable to a non-ground term, the prototype takes a coupled per-tuple path instead.
Both paths return the same answer set, byte for byte, as a naive reference unifier.

So the rule is short:

- every join-position binding is ground, take the worst-case-optimal leapfrog (fast),
- a data variable reaches a join position, take the coupled per-tuple path (correct).

A query that needs unification still rides the fast path, as long as the unification pins the
join keys to ground values. Take `func_type_unification`: `($f)` unifies with `(f)` to bind
`$f = f`, a ground value, so the join runs on the leapfrog. That is demo case 2.

This is the per-position refinement of `SidecarSchematicDecline`. The fork's gate declines a
whole body the moment any joined relation holds a schematic fact. The prototype admits a
schematic fact whenever its variables stay off the join positions, and declines only the
rest. Demo case 3 admits a schematic fact, case 4 declines one.

## Run it

```
cargo test            # 51 unit tests plus a zero-fork check against real MORK answers
cargo run --example demo
```

The unit differential makes random conjunctive queries over random spaces (about 40% of the
facts schematic) and checks that the join's answer set equals a naive nested-loop unifier,
byte for byte on the MORK encoding, on every case. It runs both paths thousands of times with
no mismatch.

## Checked against the real MORK matcher, no fork checkout

The unit differential checks the join against this crate's own unifier. To check it against
MORK's actual matcher without building the fork, `tests/mork_fixture.txt` holds answers the
live ProductZipper produced. Each line is a body, a space, and the ground answers MORK
emitted, captured by running `exec` and `metta_calculus` through the real matcher in the fork
and rendered with this crate's decoder. `tests/against_real_mork.rs` replays each case through
the join and checks two things: the join never misses a ground answer the matcher produced,
and where they differ it is only the join finding more.

On the captured corpus, 24 cases: 23 match the live matcher exactly. On the 24th the join
returns two extra answers, both needing a stored variable to match a compound (data-side
capture); the naive reference unifier returns them too. That case is the subtle part of the
matcher semantics, and this fixture does not try to settle it. What the check pins down is the
direction that matters: the join never misses an answer the matcher produced. A larger random
version (500 cases) runs in a working branch of the fork, 499 identical, same direction held.

## What the coarse decline costs

The worst-case-optimal join is already fast in the fork. What the routing adds is keeping
that fast path available when the space holds schematic facts. The cost it removes is
concrete. The fork's sidecar declines a whole body to the slower ProductZipper the moment any
joined relation holds a schematic fact (`any_schematic_fact_under_prefixes`). This benchmark
isolates that cost. The same triangle body and hub-graph
`(, (edge $x $y) (edge $y $z) (edge $z $x))` run two ways: all facts ground (the join takes
it), then the same data plus one isolated schematic fact `(edge zzdead (qq $w))` that matches
no real edge, emits nothing, and exists only to trip the gate. The output is byte-identical
both ways (the test asserts it) and a counter confirms the path flipped, so the gap is the
coarse per-relation decline and nothing else.

| n   | join     | declined to ProductZipper | penalty |
|-----|----------|---------------------------|---------|
| 100 | 1.83 ms  | 6.45 ms                   | 3.5x    |
| 200 | 3.31 ms  | 20.9 ms                   | 6.3x    |
| 400 | 6.27 ms  | 74.6 ms                   | 11.9x   |

The penalty grows with n because the ProductZipper materializes the roughly n^2 two-paths
while the join intersects instead, so the gap widens as the intermediate blows up. That is the
AGM bound in wall-clock. One inert schematic fact forfeits all of it. Per-position routing
recovers it: a schematic fact whose variables never reach a join position stays on the fast
join. Measured by `bench_decline_penalty_metta` in a working branch of the fork; the
wholesale decline it isolates is the public fork's behavior today.

## How it maps to the fork

| prototype           | the MORK fork                                                     |
|---------------------|-------------------------------------------------------------------|
| `term.rs`           | `mork_expr` tag bytes (Arity/SymbolSize/NewVar/VarRef), De Bruijn  |
| `unify.rs` (trail)  | the WAM `unify_value` plus `TrailRollback`                         |
| `wcojoin.rs`        | `trie_join` / `generic_join`, the leapfrog primitive              |
| `oracle.rs`         | a naive nested-loop unifier, the reference                        |
| `join.rs` (routing) | `schematic_facts_safe_to_admit` (working branch), the admission gate |

The public fork today has the sidecar (`transform_via_sidecar`) and the all-or-nothing
schematic decline (`any_schematic_fact_under_prefixes`), the behavior this routing refines. A
working branch turns that decline into a per-position check (`schematic_facts_safe_to_admit`),
not yet in the public release. A schematic stored fact stays on the fast join when each of its
variables sits only on an output-only position, never on a constant (which would need capture)
and never on a join key (which another factor would ground). Otherwise the body keeps the
ProductZipper, the same as before. The emit did not change, because it already drops the
non-ground rows such a fact produces. The check handles nesting on either side: a fact with
nested structure, and a query factor that decomposes a column.

In that branch the check is sound by an adversarial test: 600 random schematic bodies, nesting
on both sides, and no admission whose join output differs from the ProductZipper. A benchmark
shows the payoff: a partial-information fact, a value left unknown, keeps the triangle on the
worst-case-optimal join instead of declining the whole body, 3.4 to 8.8 times faster, with
byte-identical output. The `join.rs` here states the same condition against materialized
relations.

## What this combines

The pieces are all prior art. The combination is the new part.

Worst-case-optimal joins come from Leapfrog Triejoin (Veldhuizen, ICDT 2014), generic join
(Ngo, Porat, Re, Rudra, PODS 2012), and the AGM bound (Atserias, Grohe, Marx, FOCS 2008).
Relational e-matching (Zhang, Wang, Willsey, Tatlock, POPL 2022) compiles a pattern to a
conjunctive query and solves it with generic join, but it assumes ground e-class ids. The
non-ground data case is exactly what it leaves out and what this handles. Substitution and
discrimination trees (Graf 1995; Ramakrishnan, Sekar, Voronkov, Handbook of Automated
Reasoning 2001) index and retrieve non-ground terms; their normalized variables are MORK's De
Bruijn levels. The per-binding store with O(1) rollback is the WAM trail. The unification and
anti-unification lattice (Plotkin, Reynolds 1970) gives the algebra: unification is the meet,
anti-unification the join, and the subsumption lattice embeds in the set lattice. The scored
extension is the same join over a tropical semiring (the FAQ framework, Abo Khamis, Ngo,
Rudra, PODS 2016), with exact unification as the Boolean corner.

## The two paths

Column-wise leapfrog intersection and per-tuple unification agree on ground data. They can
come apart when a schematic fact puts a data variable on a join position. The routing sends
exactly that case to the coupled path, so both paths match the reference. The smallest case
the property test found, which routes to the coupled path:

```
query:  (r (($x $x) b) a) ,  (r $y $x)        ($x is the join variable)
space:  (r $m (a b)) (r c b) (r $n (a)) (r $p $q) (r (b (b)) (a))
```

The reference is a naive nested-loop unifier, clear and obviously correct, not a model of the
live matcher. The two paths agree with it on 6000 random cases, and the join is separately
checked against MORK's actual ProductZipper (see above): 499 of 500 identical, and the join
never misses. The same routing is implemented in a working branch of the fork, with its own
adversarial test, not yet in the public release.

## Formal verification

Sketched, not done. The fork verifies code in Verus (`VarRefRecheck.rs`,
`SidecarSchematicDecline.rs`) and abstract laws in Lean. The statement here is that the routed
join's answer set equals the `complete_match` semantics, both soundness and completeness, with
the leapfrog-safe condition as the precondition for the fast path. It is the dual of what
`SidecarSchematicDecline` already proves. It is a small Isabelle/HOL target on the AFP
`First_Order_Terms` entry, scoped to the core lemma, not a full end-to-end proof.

## Connections to the measured bottlenecks

The permutation benchmark is the leapfrog's home ground: it wins the AGM bound over the O(N^2)
pairwise materialize, which is the permutation blowup. Deep unary Peano terms benefit from the
trie's prefix sharing and the zero-allocation trail, and the single-pattern case stays on the
fast path. Counting without materializing is the COUNT and EXISTS aggregates, already in the
fork, the factorized-database direction, and it composes with this routing unchanged.

## Extending to fuzzy matching

The exact unification join is the Boolean corner of a more general engine: one trie descent,
parameterized by a semiring for cost and a lattice for types. The modules in `src/` build that
out.

`semiring.rs` is the per-step combine, parameterized over Reach (exact), Tropical (best-cost),
and Count. `scored.rs` runs the matcher over it: the Reach instance recovers the exact oracle,
and the Tropical instance makes a shared variable match approximately by distance, so one pass
can mix a symbol that must match exactly with a number scored by how close it is. `antiunify.rs`
is anti-unification, the lattice join dual to unification's meet. `quantale.rs` makes a fuzzy
type a bitset lattice (meet is unification, join is anti-unification, top is a variable) paired
with a cost monoid; a type or arity filter is one more meet, so it composes for free, and a
bounded lattice with a cost monoid is a quantale, which by Lawvere is what a metric space is
enriched over. `zorder.rs` lays a Morton curve over the trie so a box query becomes a range
scan, checked against brute force. `string_fuzzy.rs` is the edit-distance source, kept separate
because strings reindex on insert and do not ride the trie's prefix structure.

Ahmad Mesto (MesTTo)
