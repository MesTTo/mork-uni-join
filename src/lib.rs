//! Prototype: a worst-case-optimal join that unifies over non-ground (schematic) data.
//!
//! The point it demonstrates: MORK's WCO trie-join intersects ground `TermId`s by
//! equality. Replace that per-variable equality with a *unification meet* and feed it
//! domains retrieved with substitution-tree awareness of variables in the *data*, and
//! you get a join that is simultaneously worst-case-optimal and unification-complete,
//! i.e. it answers conjunctive queries against a space whose facts may themselves
//! contain variables. That is the case MORK's `SidecarSchematicDecline` proof currently
//! refuses.
//!
//! Combines, does not reinvent:
//!   - relational e-matching (pattern -> conjunctive query -> generic join),
//!   - substitution/discrimination-tree retrieval of unifiable terms over non-ground data,
//!   - WAM `unify_value` + trail for the binding store,
//!   - the leapfrog skeleton of Leapfrog Triejoin.

pub mod antiunify;
pub mod corpus;
pub mod join;
pub mod randgen;
pub mod oracle;
pub mod prolog;
pub mod quantale;
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
