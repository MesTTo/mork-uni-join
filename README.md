# A worst-case-optimal trie-join that unifies over schematic data

The worst-case-optimal trie-join is fast, but it joins ground tuples. This is a small Rust
prototype for the case it cannot do on its own: a space whose stored facts carry variables
of their own (schematic facts), so the join has to agree with unification. MORK's sidecar
declines that case wholesale (`SidecarSchematicDecline`). The prototype shows the join does
not need to change; it needs a routing condition.

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

This is the per-position view of `SidecarSchematicDecline`. That proof declines a whole body
the moment any joined relation holds a schematic fact. The prototype admits a schematic fact
whenever its variables stay off the join positions, and declines only the rest. Demo case 3
admits a schematic fact, case 4 declines one.

## Run it

```
cargo test            # 51 unit tests plus a check against real MORK answers
cargo run --example demo
cargo run --release --example bench   # worst-case-optimal join vs a pairwise plan, and a hybrid
```

The unit differential makes random conjunctive queries over random spaces (about 40% of the
facts schematic) and checks that the join's answer set equals a naive nested-loop unifier,
byte for byte on the MORK encoding, on every case. It runs both paths thousands of times with
no mismatch.

## Benchmark

The reason to route to the leapfrog is that it is worst-case-optimal. `cargo run --release
--example bench` measures it against a binary (pairwise) join plan on the triangle
(e $x $y), (e $y $z), (e $x $z), and against a hybrid that picks between the two.

The workload is the shape that separates them. A hub with `s` in-edges and `s` out-edges has
s^2 two-paths through it but closes no triangle, so it sits next to a small complete digraph
that contributes a fixed 120 real triangles. A pairwise plan joins two relations first and has
to materialize every two-path before the third relation rules it out. The leapfrog intersects
one variable at a time and never builds that intermediate. All three methods return the same
120 answers, asserted on every row, and the small rows are also checked against the naive
oracle.

```
       N         2-paths   lf_visits   pairwise_ms   leapfrog_ms    hybrid_ms       pick
  --------------------------------------------------------------------------------------
      62             406         190         0.022         0.135        0.024   pairwise
      94            1174         222         0.033         0.185        0.037   pairwise
     158            4246         286         0.066         0.291        0.073   pairwise
     286           16534         414         0.177         0.511        0.188   pairwise
     542           65686         670         0.565         0.944        0.592   pairwise
    1054          262294        1182         2.093         1.843        1.911   leapfrog
    2078         1048726        2206         7.989         3.706        3.865   leapfrog
    4126         4194454        4254        31.464         7.918        7.991   leapfrog
    8222        16777366        8350       123.818        19.534       20.217   leapfrog
   16414        67109014       16542       491.764        44.470       45.265   leapfrog
```

The two middle columns are the result and they do not depend on either implementation. The
two-paths a pairwise plan materializes grow with the square of the edge count, 406 up to 67
million. The leapfrog's node-visits grow linearly, 190 up to 16,542. Their ratio is the AGM
separation and it widens without bound.

The wall-clock is honest about the constant factor. The leapfrog builds a trie keyed on the
MORK byte encoding, so below about a thousand edges it is slower than the pairwise plan while
the intermediate is still small. Past the crossover the quadratic intermediate takes over and
the leapfrog pulls away, from parity at a thousand edges to 11x at sixteen thousand and
widening.

So which plan wins is data-dependent, and the right move is to choose per query. The `hybrid`
column does exactly that: it counts the two-path intermediate in one linear pass (the sum of
in-degree times out-degree) and routes to the leapfrog only when that count is large, so it
tracks the lower envelope. That is the toy version of cost-based plan selection.

## Choosing the plan: the fork already does this

The size threshold in the benchmark is a stand-in. The public fork picks a physical join
kernel per query from a real cost model, and it reads straight from the source in `MesTTo/MORK`:

- `binding_plan.rs`: `BindingSidecarPlan::choose_execution` returns a
  `BindingSidecarExecutionChoice`, picking one of four `BindingSidecarExecutionKernel`s
  (`GenericJoin`, `TrieJoinSuggested`, `AcyclicYannakakis`, `GhdYannakakis`) and recording why
  in a `BindingSidecarExecutionReason`. `BindingSidecarPlan::body_is_acyclic` and
  `BindingSidecarRoutingCost` gate the decision.
- `binding_space.rs`: the cost model that choice reads, `agm_size_bound` (the integral AGM
  output bound), `ghd_size_cost`, `min_edge_cover`, `selectivity_variable_order`, and the
  precomputed `cover_cost_table`.
- `space.rs`: `body_is_cyclic` gates the cyclic flip, and `bench_triangle_join_metta` /
  `bench_triangle_sparse_join_metta` run the same triangle-with-a-hub workload as the table
  above, end to end through `metta_calculus`.

So the structure-aware, cost-aware form of the size switch is already there: an acyclic body
goes to a Yannakakis full reducer, a bare cyclic core stays on the trie leapfrog, and the AGM
and GHD size bounds decide between a global worst-case-optimal join and a hypertree
decomposition.

## Checked against the real MORK matcher

The unit differential checks the join against this crate's own unifier. The other check uses
MORK's actual matcher: `tests/mork_fixture.txt` holds answers the live ProductZipper
produced. Each line is a body, a space, and the ground answers MORK
emitted, captured by running `exec` and `metta_calculus` through the real matcher and rendered
with this crate's decoder. `tests/against_real_mork.rs` replays each case through the join and
checks two things: the join never misses a ground answer the matcher produced, and where they
differ it is only the join finding more.

On the captured corpus, 24 cases: 23 match the live matcher exactly. On the 24th the join
returns two extra answers, both needing a stored variable to match a compound (data-side
capture); the naive reference unifier returns them too. That case is the subtle part of the
matcher semantics, and this fixture does not try to settle it. What it pins down is the
direction that matters: the join never misses an answer the matcher produced.

## How it maps to the fork

| prototype           | the MORK fork                                                     |
|---------------------|-------------------------------------------------------------------|
| `term.rs`           | `mork_expr` tag bytes (Arity/SymbolSize/NewVar/VarRef), De Bruijn  |
| `unify.rs` (trail)  | the WAM `unify_value` plus `TrailRollback`                         |
| `wcojoin.rs`        | `trie_join` / `generic_join`, the leapfrog primitive              |
| `oracle.rs`         | a naive nested-loop unifier, the reference                        |
| `join.rs` (routing) | the routing condition over the `any_schematic_fact_under_prefixes` decline |

The fork's sidecar runs a conjunctive body on the worst-case-optimal join, and declines the
whole body to the ProductZipper the moment any joined relation holds a schematic fact
(`any_schematic_fact_under_prefixes`). This prototype is the routing that refines that decline
per position: a schematic fact would stay on the fast join when each of its variables sits
only on an output-only position, never on a constant (which would need capture) and never on a
join key (which another factor would ground). It runs against materialized relations here, and
the condition is computable from the lowered factors at plan time.

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
checked against MORK's actual ProductZipper (the fixture above): 23 of 24 identical, and the
join never misses.

## Formal verification

Sketched, not done. The fork verifies code in Verus (`VarRefRecheck.rs`,
`SidecarSchematicDecline.rs`) and abstract laws in Lean. The statement here is that the routed
join's answer set equals the `complete_match` semantics, both soundness and completeness, with
the leapfrog-safe condition as the precondition for the fast path. It is the dual of what
`SidecarSchematicDecline` already proves. It is a small Isabelle/HOL target on the AFP
`First_Order_Terms` entry, scoped to the core lemma, not a full end-to-end proof.

## Connections to the measured bottlenecks

The triangle in the benchmark above is the leapfrog's home ground, the permutation blowup where
a pairwise materialize pays the quadratic intermediate. The same routing touches the other
shapes too. Deep unary Peano terms lean on the trie's prefix sharing and the zero-allocation
trail, and a single-pattern query stays on the fast path. Counting without materializing is the
COUNT and EXISTS aggregates already in the fork (`GenericJoinCount`, `GenericJoinExistence` in
`binding_space.rs`), the factorized-database direction, and it composes with this routing
unchanged.

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
