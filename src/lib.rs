//! Prototype: a worst-case-optimal join that unifies over non-ground (schematic) data.
//!
//! The point it demonstrates: a plain worst-case-optimal trie-join intersects ground `TermId`s
//! by equality. Replace that per-variable equality with a *unification meet* and feed it
//! domains retrieved with substitution-tree awareness of variables in the *data*, and
//! you get a join that is simultaneously worst-case-optimal and does data-side capture,
//! i.e. it answers conjunctive queries against a space whose facts may themselves contain
//! variables. Upstream MORK's ProductZipper already does that capture; this prototype's
//! contribution is the correctness oracle (sealed against SWI-Prolog) and the scaling study.
//! An earlier version cited a fork route `SidecarSchematicDecline` as MORK refusing capture;
//! that reflected a fork regression, since fixed. See the README correction.
//!
//! Combines, does not reinvent:
//!   - relational e-matching (pattern -> conjunctive query -> generic join),
//!   - substitution/discrimination-tree retrieval of unifiable terms over non-ground data,
//!   - WAM `unify_value` + trail for the binding store,
//!   - the leapfrog skeleton of Leapfrog Triejoin.

pub mod antiunify;
pub mod corpus;
pub mod join;
pub mod oracle;
pub mod prolog;
pub mod quantale;
pub mod randgen;
pub mod scored;
pub mod semiring;
pub mod string_fuzzy;
pub mod term;
pub mod trie;
pub mod trie_join;
pub mod unify;
pub mod unijoin;
pub mod wcojoin;
pub mod zorder;
