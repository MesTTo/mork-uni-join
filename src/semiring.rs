//! Semirings, mirroring the fork's `kernel/src/semiring.rs` (commit 7aef787, "the
//! semiring generalization: one closure, many analyses"). The same matching machinery
//! run over a different semiring gives exact, fuzzy, or counting answers (the FAQ idea,
//! Abo Khamis-Ngo-Rudra). `mul` (the product) combines ALONG a match (a conjunction);
//! `add` (the sum) chooses the best ACROSS alternatives.
//!
//!   Reach    = exact matching            (and / or)
//!   Tropical = fuzzy best-cost matching  (+ / min),  None = infinity
//!   Count    = number of derivations     (* / +)
//!
//! Exact matching is just the Reach corner of the same engine, which is the meeting's
//! whole point: fuzzy is not a separate matcher, it is this matcher over a cost semiring.

pub trait Semiring: Clone + PartialEq + std::fmt::Debug {
    /// `add`-identity and `mul`-annihilator: "no match / impossible".
    fn zero() -> Self;
    /// `mul`-identity: "exact, free".
    fn one() -> Self;
    /// The sum: keep the best across alternatives.
    fn add(&self, other: &Self) -> Self;
    /// The product: combine along a match.
    fn mul(&self, other: &Self) -> Self;
    fn is_zero(&self) -> bool {
        *self == Self::zero()
    }
}

/// Reachability / Boolean: exact matching. product = and, sum = or.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Reach(pub bool);
impl Semiring for Reach {
    fn zero() -> Self {
        Reach(false)
    }
    fn one() -> Self {
        Reach(true)
    }
    fn add(&self, o: &Self) -> Self {
        Reach(self.0 || o.0)
    }
    fn mul(&self, o: &Self) -> Self {
        Reach(self.0 && o.0)
    }
}

/// Tropical (min, +): a cost. `None` is infinity (no match). product = +, sum = min.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Tropical(pub Option<i64>);
impl Semiring for Tropical {
    fn zero() -> Self {
        Tropical(None)
    }
    fn one() -> Self {
        Tropical(Some(0))
    }
    fn add(&self, o: &Self) -> Self {
        Tropical(match (self.0, o.0) {
            (None, x) | (x, None) => x,
            (Some(a), Some(b)) => Some(a.min(b)),
        })
    }
    fn mul(&self, o: &Self) -> Self {
        Tropical(match (self.0, o.0) {
            (Some(a), Some(b)) => Some(a + b),
            _ => None,
        })
    }
}

/// Counting: how many ways a match succeeds. product = *, sum = +. This is the semiring
/// FuzzyMultiMap aggregates over (union/count of the fuzzy-matched set).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Count(pub u64);
impl Semiring for Count {
    fn zero() -> Self {
        Count(0)
    }
    fn one() -> Self {
        Count(1)
    }
    fn add(&self, o: &Self) -> Self {
        Count(self.0 + o.0)
    }
    fn mul(&self, o: &Self) -> Self {
        Count(self.0 * o.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reach_is_exact() {
        assert_eq!(Reach::one().mul(&Reach::one()), Reach(true));
        assert_eq!(Reach::one().mul(&Reach::zero()), Reach(false));
        assert_eq!(Reach::zero().add(&Reach::one()), Reach(true));
        assert!(Reach::zero().is_zero());
    }

    #[test]
    fn tropical_sums_along_mins_across() {
        assert_eq!(Tropical(Some(3)).mul(&Tropical(Some(4))), Tropical(Some(7)));
        assert_eq!(Tropical(Some(3)).add(&Tropical(Some(4))), Tropical(Some(3)));
        assert_eq!(Tropical::one().mul(&Tropical(Some(5))), Tropical(Some(5)));
        assert_eq!(Tropical::zero().add(&Tropical(Some(5))), Tropical(Some(5)));
        assert_eq!(Tropical::zero().mul(&Tropical(Some(5))), Tropical(None)); // inf annihilates
        assert!(Tropical::zero().is_zero());
    }

    #[test]
    fn count_multiplies_along_adds_across() {
        assert_eq!(Count(2).mul(&Count(3)), Count(6));
        assert_eq!(Count(2).add(&Count(3)), Count(5));
        assert!(Count::zero().is_zero());
    }
}
