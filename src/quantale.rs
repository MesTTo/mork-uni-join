//! The quantale: a bounded lattice plus a cost monoid (improvement #4), the structure the
//! fuzzy-type design converges on.
//!
//! A fuzzy type is a bitset over a small universe of options (for example two bits, a
//! four-valued logic, generalized). The lattice operations are the unification algebra at
//! the type level:
//!   - meet = bitwise AND = unification = intersection of allowed options,
//!   - join = bitwise OR  = anti-unification = union of options,
//!   - top  = all bits set = a variable (matches anything, the meet identity),
//!   - bottom = no bits     = a contradiction (the join identity).
//! A type or arity filter is just a meet, one more AND, so it composes with the join's
//! per-variable intersection for free.
//!
//! A cost (the tropical semiring, or any semiring) rides alongside as the metric. A
//! bounded lattice with a monoid that distributes over joins is a quantale, and Lawvere's
//! theorem (a metric space is a category enriched over such a quantale) is why an
//! arbitrary metric drops in as the cost monoid rather than being bolted on.

use crate::semiring::Semiring;

/// A fuzzy type: a bitset over a small universe of options.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct FuzzyType(pub u64);

impl FuzzyType {
    /// The top element: every option allowed (a variable, matches anything).
    pub fn top(universe_bits: u32) -> Self {
        FuzzyType(if universe_bits >= 64 {
            u64::MAX
        } else {
            (1u64 << universe_bits) - 1
        })
    }
    /// The bottom element: no option (a contradiction).
    pub fn bottom() -> Self {
        FuzzyType(0)
    }
    /// A single option.
    pub fn singleton(i: u32) -> Self {
        FuzzyType(1u64 << i)
    }
    /// Meet = unification = intersection of allowed options.
    pub fn meet(self, o: Self) -> Self {
        FuzzyType(self.0 & o.0)
    }
    /// Join = anti-unification = union of options.
    pub fn join(self, o: Self) -> Self {
        FuzzyType(self.0 | o.0)
    }
    pub fn is_bottom(self) -> bool {
        self.0 == 0
    }
}

/// A quantale element: a lattice value (the type/region) and a cost (the metric). The
/// product of a lattice and a cost monoid is a quantale.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Q<S: Semiring> {
    pub ty: FuzzyType,
    pub cost: S,
}

impl<S: Semiring> Q<S> {
    pub fn new(ty: FuzzyType, cost: S) -> Self {
        Q { ty, cost }
    }
    /// The identity for meet: a variable (top type) at no cost.
    pub fn top(universe_bits: u32) -> Self {
        Q {
            ty: FuzzyType::top(universe_bits),
            cost: S::one(),
        }
    }
    /// Combine ALONG a match: meet the types, multiply the costs.
    pub fn meet(&self, o: &Self) -> Self {
        Q {
            ty: self.ty.meet(o.ty),
            cost: self.cost.mul(&o.cost),
        }
    }
    /// Combine ACROSS alternatives: join the types, add (best-of) the costs.
    pub fn join(&self, o: &Self) -> Self {
        Q {
            ty: self.ty.join(o.ty),
            cost: self.cost.add(&o.cost),
        }
    }
    /// Impossible if the type bottomed out or the cost is the annihilator.
    pub fn is_impossible(&self) -> bool {
        self.ty.is_bottom() || self.cost.is_zero()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semiring::Tropical;

    // A four-option universe.
    const SYMBOL: u32 = 0;
    const NUMBER: u32 = 1;
    const EXPR: u32 = 2;
    const VARIABLE: u32 = 3;
    const BITS: u32 = 4;

    #[test]
    fn lattice_laws() {
        let x = FuzzyType(0b0110);
        let y = FuzzyType(0b1100);
        let z = FuzzyType(0b1010);
        // idempotent, commutative
        assert_eq!(x.meet(x), x);
        assert_eq!(x.join(x), x);
        assert_eq!(x.meet(y), y.meet(x));
        assert_eq!(x.join(y), y.join(x));
        // identities: top for meet, bottom for join
        assert_eq!(FuzzyType::top(BITS).meet(x), x);
        assert_eq!(FuzzyType::bottom().join(x), x);
        // absorption
        assert_eq!(x.meet(x.join(y)), x);
        assert_eq!(x.join(x.meet(y)), x);
        // distributive (bitsets are a distributive lattice)
        assert_eq!(x.meet(y.join(z)), x.meet(y).join(x.meet(z)));
    }

    #[test]
    fn variable_is_top_and_neutral() {
        // A variable allows every option; unifying (meet) with it returns the other side.
        let var = FuzzyType::top(BITS);
        let num = FuzzyType::singleton(NUMBER);
        assert_eq!(var.meet(num), num);
        // anti-unifying (join) toward top: number with symbol generalizes to {sym,num}.
        let sym = FuzzyType::singleton(SYMBOL);
        assert_eq!(num.join(sym), FuzzyType(0b0011));
    }

    #[test]
    fn type_filter_is_a_meet() {
        // Candidates allow symbol, number, or expression; "filter on Number" is a meet.
        let candidates = FuzzyType(0b0111); // sym | num | expr
        let only_numbers = FuzzyType::singleton(NUMBER);
        assert_eq!(candidates.meet(only_numbers), only_numbers);
        // "accept variables or expressions but not strings" (Ben's example) is also a meet.
        let not_symbol = FuzzyType::singleton(EXPR).join(FuzzyType::singleton(VARIABLE));
        assert_eq!(FuzzyType::top(BITS).meet(not_symbol), not_symbol);
    }

    #[test]
    fn quantale_pairs_type_with_cost() {
        // A crisp constraint (type = Number, cost 0) met with a fuzzy one (any type,
        // cost 3) keeps the type constraint and carries the cost: crisp + fuzzy in one.
        let crisp: Q<Tropical> = Q::new(FuzzyType::singleton(NUMBER), Tropical(Some(0)));
        let fuzzy: Q<Tropical> = Q::new(FuzzyType::top(BITS), Tropical(Some(3)));
        let combined = crisp.meet(&fuzzy);
        assert_eq!(combined.ty, FuzzyType::singleton(NUMBER));
        assert_eq!(combined.cost, Tropical(Some(3)));
        assert!(!combined.is_impossible());
        // Q::top is the meet identity (a variable at no cost).
        assert_eq!(Q::<Tropical>::top(BITS).meet(&crisp), crisp);
    }

    #[test]
    fn contradiction_is_impossible() {
        let q: Q<Tropical> = Q::new(
            FuzzyType::singleton(SYMBOL).meet(FuzzyType::singleton(NUMBER)),
            Tropical(Some(0)),
        );
        assert!(q.is_impossible(), "symbol AND number is bottom");
    }
}
