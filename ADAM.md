# Data-side capture: a completeness gap, and the unification join that closes it

## The finding

A conjunctive query over a space whose facts may themselves contain variables can require a
fact variable to bind a query subterm. Call it data-side capture. Relational matching binds
query variables to fact subterms but not the reverse, so it silently drops those answers.

The smallest witness:

    query:  (r (a $p) b)  ,  (r (b) $p)
    facts:  (r $d b)      (r a b)

In the first goal `$d` absorbs `(a $p)`; in the second `(b)` forces `$p = b`. A relational join
returns nothing. Full first-order unification returns `$p = b`, and so does SWI-Prolog under
`occurs_check`.

## Reproduce it

    swipl --version          # SWI-Prolog on PATH (optional but recommended)
    ./reproduce.sh           # or: cargo run --release --example adam_repro

You get three columns per query: the equality join (relational semantics), the unification join
(the same descent with data-side capture enabled), and SWI-Prolog with
`set_prolog_flag(occurs_check, true)`. Across the 16 witnesses the equality join drops 15 tuples,
and the unification join equals SWI-Prolog on every one. If the join and Prolog ever disagree the
example exits non-zero, so it cannot claim an agreement it did not observe.

The Prolog bridge shares no code with the join under test. A pattern becomes a goal `fact(P)`, a
stored fact becomes `assertz(fact(F))` with its variables fresh per use (the rename-apart),
shared query variables across goals are the join, and `numbervars/3` canonicalises the output so
the two engines' answer strings line up. That independence is the point: the referee is not MORK
and not this crate.

## Throw your own query at it

The corpus is fixed, but the harness is not. Supply your own conjunctive query and facts and it
runs the same three engines on them:

    cargo run --release --example adam_repro -- \
        -q "(r (a $p) b)" -q "(r (b) $p)" -f "(r $d b)" -f "(r a b)"

Each `-q` is a factor, each `-f` a stored fact (which may contain variables). Try to find a case
where the unification join and SWI-Prolog disagree. If you do, the example exits non-zero and
prints both answer sets, so a divergence surfaces immediately rather than hiding.

## The join

This is the trie-join combined with unification. It is a worst-case-optimal-style trie descent
(Leapfrog Triejoin / Free Join) carrying two-sided unification: each query factor is matched
against the byte-trie by descending it and unifying against the stored term, where a stored
wildcard byte is a data variable that captures the aligned query subterm. The per-factor
retrieval is Graf's substitution-tree idea and WAM read-mode (`get_structure`, `unify_variable`,
`unify_value`); the store is one backtrackable trail (triangular substitution, Hoder and
Voronkov); occurs-check happens at binding. None of those pieces is new on its own. The
combination is: a worst-case-optimal join meeting two-sided unification retrieval over one shared
byte-trie.

The descent is generic over a four-method zipper trait, so the identical code runs over this
crate's own `ByteTrie` and over MORK's live PathMap, with no copy of the data and no second
implementation.

## How the equality column is defined

The equality join in the example is the *same descent with the capture step switched off* (see
`equality_join` in `src/trie_join.rs`, and the test `equality_join_is_capture_join_minus_capture`
asserting it is a strict subset of the full join, differing only on capture cases). So the gap
you see is exactly the capture contribution, isolated inside one engine, not an accident of
comparing two different codebases. It is the relational semantics a Datalog-style matcher
computes; MORK's current fast path is such a matcher and exhibits the same gap.

## Validation

- `cargo test --release --test prolog_seal -- --nocapture` : the join equals SWI-Prolog
  occurs-check on the corpus, printed case by case.
- `cargo test --release trie_join` : the lazy trie join equals a materialized leapfrog join on
  the corpus and 20000 random schematic cases, byte for byte, so the lazy descent is pinned to
  the reference, which is pinned to Prolog.

## Honest limits

- Performance is not claimed here. This prototype is about which answers, not how fast. Any speed
  comparison belongs in its own artifact and, for MORK, on upstream PathMap, so a divergent
  perf branch cannot confound the number.
- The scope is the plain conjunctive query. Where MORK's exec forms carry grounded operators
  rather than relational joins over schematic facts, data-side capture does not arise.
- In the MORK integration this is wired behind a flag, default off. Whether data-side capture
  becomes the default MeTTa semantics is a language decision, not the engine's.
