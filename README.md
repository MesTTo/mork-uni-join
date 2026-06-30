# Integrating the worst-case-optimal trie-join with unification

A standalone, differentially-validated prototype of a piece the MORK fork was missing:
making the worst-case-optimal trie-join answer conjunctive queries against a space whose
stored facts may themselves carry variables (schematic facts), the case the sidecar
declined wholesale (`SidecarSchematicDecline`) and the thing Adam asked to build ("this is
sound... let's try and integrate this with unification"). The per-position admission this
prototype demonstrates is now wired into the fork's sidecar gate (see "How it maps to the
fork").

The leapfrog triejoin, the COUNT/EXISTS aggregates, the multi-pattern conjunction
lowering, the WAM trail, and the matcher already exist (the MORK fork's `trie_join` /
`generic_join` / `BindingSidecarPlan`, and MeTTaLingo's `wcojoin.ts` / `trail.ts` /
`match.ts`). This prototype is the layer that sits on top of them.

## The result

Unification does not need a new join. It needs a routing condition.

> The leapfrog triejoin's per-variable intersection is exact and worst-case-optimal when
> unification resolves every **join-position** variable to a **ground** term. That is the
> common case, and it includes queries that genuinely need unification. When a schematic
> stored fact binds a join variable to a **non-ground** term, the prototype takes a coupled
> per-tuple path instead. Both paths are validated, byte-for-byte, against a naive reference
> matcher.

So the integration is:

- every join-position binding ground  ->  the existing worst-case-optimal leapfrog (fast),
- a data variable reaches a join position  ->  the coupled per-tuple path (correct).

Two consequences that matter:

1. A query that genuinely needs unification still rides the fast path, as long as the
   unification pins the join keys to ground values. `func_type_unification` is exactly
   this: `($f)` unifies `(f)` to bind `$f = f`, a ground value, so the join runs on the
   leapfrog. See demo case 2.
2. This refines the fork's all-or-nothing `SidecarSchematicDecline` (decline the whole
   join if any fact is schematic) into a **per-position** admission: a schematic fact is
   admitted to the worst-case-optimal join whenever its variables do not land on a join
   position. See demo case 3 (a schematic fact admitted) versus case 4 (one declined).

## Run it

```
cargo test            # 51 unit tests + a zero-fork check against REAL MORK answers
cargo run --example demo
```

The unit differential generates random conjunctive queries over random spaces (about 40%
of facts schematic) and asserts the join's answer set equals a naive nested-loop
unification matcher, byte-for-byte on the MORK encoding, on every case. It exercises both
paths (leapfrog and coupled) thousands of times with zero mismatch.

## Validated against the real MORK matcher (zero fork)

The unit differential checks the routed join against *this crate's own* unification oracle.
To check it against MORK's *actual* matcher without a fork checkout, `tests/mork_fixture.txt`
holds answers the live ProductZipper produced. Each line is a body, a space, and the ground
answers MORK emitted, captured by running `exec` + `metta_calculus` through the real matcher
in the fork and rendered with this crate's own decoder. `tests/against_real_mork.rs` replays
each case through the routed join and checks two things:

- the routed join never misses a ground answer the real matcher produced (`fork ⊆ routed`),
  the soundness/completeness floor, and
- where they differ, it is only the routed join finding *more*.

Result on the captured corpus: 24 cases, 23 exact, 1 superset. The one superset is the
data-side variable capture case (`(r (a $x) b) , (r (b) $x)` against a schematic `(r $d b)`):
the routed join's full unification returns the two spec-correct answers, while the live
ProductZipper currently emits nothing there. That is MORK's known data-side-capture gap, not
a flaw in the join. The fixture is real matcher output, not a model of it, so this is the
strongest in-repo evidence short of rebuilding the fork. The full 500-case random version of
this cross-validation lives in the fork's own test suite, run against the live matcher
directly: 499/500 byte-identical, zero misses.

## Measured: what the coarse decline costs (same body, identical output)

The worst-case-optimal join is already fast in the fork. What this routing adds is keeping
that fast path available to schematic data. The cost it removes is concrete: the fork's
sidecar declines a *whole body* to the slower ProductZipper the moment *any* joined relation
holds a schematic fact (`any_schematic_fact_under_prefixes`). This benchmark isolates that
cost. The same triangle body and hub-graph
`(, (edge $x $y) (edge $y $z) (edge $z $x))` run two ways: all facts ground (admitted to the
WCO join), versus the same data plus *one* isolated schematic fact `(edge zzdead (qq $w))`
that unifies with no real edge, emits nothing, and exists only to trip the gate. Output is
byte-identical both ways (asserted), and a decline counter confirms the path actually flips,
so the gap is purely the coarse per-relation decline:

| n   | admit (WCO join) | decline (ProductZipper) | penalty |
|-----|------------------|-------------------------|---------|
| 100 | 1.83 ms          | 6.45 ms                 | 3.5x    |
| 200 | 3.31 ms          | 20.9 ms                 | 6.3x    |
| 400 | 6.27 ms          | 74.6 ms                 | 11.9x   |

The penalty grows with n because the ProductZipper materializes the ~n^2 two-paths while the
join intersects instead, so the gap widens as the intermediate blows up (the AGM bound in
wall-clock). One inert schematic fact forfeits all of it. That penalty is exactly what
per-position routing recovers: a schematic fact whose variables never reach a join position
can stay on the fast join. Measured in the fork test `bench_decline_penalty_metta`.

## How it maps to the fork

| prototype            | the MORK fork                                                |
|----------------------|--------------------------------------------------------------|
| `term.rs`            | `mork_expr` tag bytes (Arity/SymbolSize/NewVar/VarRef), De Bruijn |
| `unify.rs` (trail)   | the WAM `unify_value` + `TrailRollback`                      |
| `wcojoin.rs`         | `trie_join` / `generic_join` (the leapfrog primitive)        |
| `oracle.rs`          | a naive nested-loop unification matcher (the reference oracle) |
| `join.rs` (routing)  | `schematic_facts_safe_to_admit`, the per-position sidecar admission gate |

The per-position admission this prototype demonstrates is now wired into the fork. It lands
where the worst-case-optimal sidecar decides whether to take a body: `transform_via_sidecar`'s
all-or-nothing schematic decline becomes a per-position check. A schematic stored fact stays
on the fast join when each of its variables sits only on an output-only position (never a
constant, which would capture, nor a join key, which another factor would ground); otherwise
the body keeps the ProductZipper, as before. The emit needed no change: it already drops the
non-ground rows such a fact produces, and the check handles nesting on either side (a fact
with nested structure, or a query factor that decomposes a column).

Soundness is gated by a random adversarial differential in the fork's test suite: 600 random
schematic bodies, nesting on both sides, zero admissions whose join output differs from the
ProductZipper. The payoff, benchmarked: a partial-information schematic fact (an unknown
value) keeps the triangle on the worst-case-optimal join instead of declining the whole body,
3.4-8.8x faster with byte-identical output. The standalone `join.rs` here states the same
condition against materialized relations; the fork wires it into the live sidecar.

## What this combines (prior art, not reinvented)

- Worst-case-optimal joins: Leapfrog Triejoin (Veldhuizen, ICDT 2014), generic join
  (Ngo-Porat-Re-Rudra, PODS 2012), the AGM bound (Atserias-Grohe-Marx, FOCS 2008).
- Relational e-matching (Zhang-Wang-Willsey-Tatlock, POPL 2022): compile a pattern to a
  conjunctive query solved by generic join. It assumes ground e-class ids; the non-ground
  *data* case is exactly what it does not cover, and what this handles.
- Substitution / discrimination trees (Graf 1995; Ramakrishnan-Sekar-Voronkov, Handbook of
  Automated Reasoning 2001): indexing and retrieving non-ground terms; normalized
  variables = MORK's De Bruijn levels.
- The WAM trail (`unify_value`, read mode) for the per-binding store with O(1) rollback.
- The unification / anti-unification lattice (Plotkin, Reynolds 1970): unification is the
  meet, anti-unification the join, and the subsumption lattice embeds in the set lattice,
  which is the rigorous form of Adam's "unification = intersection of fuzzy types". The
  scored/fuzzy extension is the same join over a tropical semiring (FAQ, Abo
  Khamis-Ngo-Rudra, PODS 2016); exact unification is the Boolean semiring instance.

## The two paths

Column-wise leapfrog intersection and per-tuple unification agree on ground data, and they
can come apart when a schematic fact puts a data variable on a join position. The routing
sends exactly that case to the coupled per-tuple path, so both paths match the reference
matcher. The smallest case the property test surfaced, which routes to the coupled path:

```
query:  (r (($x $x) b) a) ,  (r $y $x)        ($x is the join variable)
space:  (r $m (a b)) (r c b) (r $n (a)) (r $p $q) (r (b (b)) (a))
```

The oracle here is a naive nested-loop unifier: a clear, obviously-correct reference, not a
verified model of the live `coreferential_transition`. The two paths agree with it on 6000
random cases, and the routed join is separately cross-validated against MORK's actual
ProductZipper (see "Validated against the real MORK matcher"): 499/500 byte-identical, zero
misses. The per-position admission is now wired into the fork's sidecar gate (see "How it
maps to the fork"), gated by its own adversarial differential.

## Formal verification (planned)

The fork verifies code in Verus (`VarRefRecheck.rs`, `SidecarSchematicDecline.rs`) and
abstract laws in Lean. The meta-theorem here (the routed join's answer set equals the
`complete_match` semantics, soundness + completeness, with the leapfrog-safe condition as
the precondition for the fast path) is the dual of `SidecarSchematicDecline`'s "incomplete
on schematic" property. It is a clean Isabelle/HOL target built on the AFP
`First_Order_Terms` entry; scoped to the core lemma, not a full machine-checked end-to-end
proof.

## Connections to the measured bottlenecks

- Permutations: the leapfrog is the AGM-bound win over the O(N^2) pairwise materialize,
  which is the permutation blowup.
- Peano: deep unary terms benefit from the trie's prefix sharing and the zero-allocation
  trail; the single-pattern case stays on the fast path.
- Counting without materializing: the COUNT/EXISTS aggregates (already in the fork) are the
  FAQ / factorized-database direction, and compose with this routing unchanged.

## Extending to fuzzy matching (the lattice + semiring layer)

The exact unification join above is the Boolean corner of a more general engine. These
modules generalize it along the algebra the design converged on (one engine, the trie
descent, parameterized by a semiring for cost and a lattice for types):

- `semiring.rs` — the matcher's per-step combine, parameterized by a semiring (mirrors the
  fork's own `semiring.rs`): Reach (exact), Tropical (best-cost / fuzzy), Count.
- `scored.rs` — the matcher over that semiring. The Reach instance provably recovers the
  exact oracle; the Tropical instance makes the join key fuzzy (a shared variable can match
  approximately, scored by distance), and a query can mix crisp symbolic structure (cost 0
  or infinity) with a fuzzy number (scored by distance) in one pass.
- `antiunify.rs` — anti-unification (Plotkin/Reynolds lgg), the lattice join dual to
  unification's meet (the "union" in a fuzzy descent, and WILLIAM's generalization).
- `quantale.rs` — fuzzy types as a bitset lattice (meet = unification = AND, join =
  anti-unification = OR, top = a variable) paired with a cost monoid. A type/arity filter
  is a meet, so it composes with the join. A bounded lattice plus a cost monoid is a
  quantale, and by Lawvere a metric space is enrichment over one, so an arbitrary metric is
  just the cost monoid.
- `zorder.rs` — a Z-order (Morton) space-filling curve over the trie (the UB-tree idea):
  multidimensional points become trie paths and a box query a range scan (validated against
  brute force). The orthogonal-finite-dimension fuzzy case, native to the trie.
- `string_fuzzy.rs` — the string / edit-distance source (separate, since strings are
  non-orthogonal): fuzzy-match keys within an edit distance, then aggregate the matched
  values with the semiring `add` (set-union / min / count).

Ahmad Mesto (MesTTo)
