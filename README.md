# Integrating the worst-case-optimal trie-join with unification

A standalone, differentially-validated prototype of the one open piece in the MORK fork:
making the worst-case-optimal trie-join answer conjunctive queries against a space whose
stored facts may themselves carry variables (schematic facts), the case the sidecar
currently declines (`SidecarSchematicDecline`) and the thing Adam asked to build ("this is
sound... let's try and integrate this with unification").

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
cargo test            # 27 tests, incl. a 6000-case differential oracle (ground + schematic)
cargo run --example demo
```

The differential test generates random conjunctive queries over random spaces (about 40%
of facts schematic) and asserts the join's answer set equals a naive nested-loop
unification matcher, byte-for-byte on the MORK encoding, on every case. It exercises both
paths (leapfrog and coupled) thousands of times with zero mismatch.

## Measured (same query, identical output)

On the intermediate-bound hub-graph triangle
`(, (edge $x $y) (edge $y $z) (edge $z $x))` (n peripheral nodes around 3 hubs: many
two-paths, few triangles), run once with the factor-at-a-time matcher and once with the
worst-case-optimal join, identical results both ways:

| n   | factor-at-a-time | worst-case-optimal join | speedup |
|-----|------------------|-------------------------|---------|
| 100 | 6.75 ms          | 1.96 ms                 | 3.4x    |
| 200 | 21.6 ms          | 3.22 ms                 | 6.7x    |
| 400 | 76.8 ms          | 7.64 ms                 | 10.0x   |

The speedup grows with n (3.4x -> 6.7x -> 10x): the factor-at-a-time path materializes the
~n^2 two-paths, the worst-case-optimal join intersects instead, so the gap widens as the
intermediate blows up. That is the AGM bound in wall-clock. The output is identical on both
paths, so it is the same answer computed faster. The unification routing above is what lets
this join answer queries with variables, not only ground tuples.

## How it maps to the fork

| prototype            | the MORK fork                                                |
|----------------------|--------------------------------------------------------------|
| `term.rs`            | `mork_expr` tag bytes (Arity/SymbolSize/NewVar/VarRef), De Bruijn |
| `unify.rs` (trail)   | the WAM `unify_value` + `TrailRollback`                      |
| `wcojoin.rs`         | `trie_join` / `generic_join` (the leapfrog primitive)        |
| `oracle.rs`          | a naive nested-loop unification matcher (the reference oracle) |
| `join.rs` (routing)  | the new bit: a route that would sit at `query_multi`         |

None of this is wired into the fork yet; the prototype is standalone. Wiring it would route
at `query_multi`: the leapfrog-safe branch to `trie_join`, the coupled branch to the
existing matcher. The routing test (a non-ground binding at a join position) is computable
from the lowered pattern factors at plan time.

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
verified model of the live `coreferential_transition`. So the validated claim is "the two
paths agree with this reference on 6000 random cases", and validating against MORK's actual
matcher is the next step before wiring into the fork.

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

Ahmad Mesto (MesTTo)
