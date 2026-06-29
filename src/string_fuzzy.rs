//! The string / edit-distance fuzzy source. The meeting scoped this as a SEPARATE source:
//! strings are non-orthogonal (an insert reindexes every later position), so they do not
//! ride the trie's prefix structure and need their own edit-distance machinery rather than
//! the lattice/semiring descent.
//!
//! The point of this module is to show that such a source still plugs into the SAME
//! semiring aggregation as the rest of the prototype: fuzzy-match the keys within an edit
//! distance, then aggregate the matched values with the semiring `add` (set-union, or min
//! distance, or a count). A production version would walk the trie with a Levenshtein
//! automaton instead of the brute-force edit-distance scan used here.

use crate::semiring::Semiring;
use std::collections::HashSet;

/// Standard Levenshtein edit distance (insert / delete / substitute), Wagner-Fischer DP.
/// A Levenshtein automaton would scale this; the DP is the obvious reference.
pub fn edit_distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let mut prev: Vec<usize> = (0..=b.len()).collect();
    let mut cur = vec![0usize; b.len() + 1];
    for i in 1..=a.len() {
        cur[0] = i;
        for j in 1..=b.len() {
            let sub = prev[j - 1] + usize::from(a[i - 1] != b[j - 1]);
            cur[j] = sub.min(prev[j] + 1).min(cur[j - 1] + 1);
        }
        std::mem::swap(&mut prev, &mut cur);
    }
    prev[b.len()]
}

/// A fuzzy multimap: keys carry values, a query fuzzy-matches the key within an edit
/// distance and aggregates the matched values.
#[derive(Default)]
pub struct FuzzyMap<V> {
    entries: Vec<(String, V)>,
}

impl<V> FuzzyMap<V> {
    pub fn new() -> Self {
        FuzzyMap { entries: Vec::new() }
    }

    pub fn insert(&mut self, key: &str, value: V) {
        self.entries.push((key.to_string(), value));
    }

    /// Aggregate, via the semiring `add`, the score of every key within `max_distance`.
    /// `score(key, value, distance)` maps a matched entry into the semiring. With Tropical
    /// and `score = distance` this returns the best (min) edit distance; with Count and
    /// `score = one` it returns how many keys matched.
    pub fn query<S: Semiring>(
        &self,
        term: &str,
        max_distance: usize,
        score: impl Fn(&str, &V, usize) -> S,
    ) -> S {
        let mut acc = S::zero();
        for (k, v) in &self.entries {
            let d = edit_distance(term, k);
            if d <= max_distance {
                acc = acc.add(&score(k, v, d));
            }
        }
        acc
    }
}

impl FuzzyMap<HashSet<i32>> {
    /// Union the value sets of every key within `max_distance`. Set union is the `add` of a
    /// set-union semiring, so this is the same aggregation the generic `query` performs,
    /// specialized to sets.
    pub fn query_union(&self, term: &str, max_distance: usize) -> HashSet<i32> {
        let mut out = HashSet::new();
        for (k, v) in &self.entries {
            if edit_distance(term, k) <= max_distance {
                out.extend(v.iter().copied());
            }
        }
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::semiring::{Count, Tropical};

    #[test]
    fn edit_distance_is_correct() {
        assert_eq!(edit_distance("kitten", "sitting"), 3);
        assert_eq!(edit_distance("foo", "foo"), 0);
        assert_eq!(edit_distance("bat", "bar"), 1);
        assert_eq!(edit_distance("bat", "baz"), 1);
        assert_eq!(edit_distance("bat", "foo"), 3);
        assert_eq!(edit_distance("", "abc"), 3);
    }

    #[test]
    fn fuzzy_multimap_unions_matched_values() {
        // foo->{1,2}, bar->{3}, baz->{4,5}; query "bat" within distance 1 matches bar and
        // baz (not foo), and unions their values.
        let mut m: FuzzyMap<HashSet<i32>> = FuzzyMap::new();
        m.insert("foo", HashSet::from([1, 2]));
        m.insert("bar", HashSet::from([3]));
        m.insert("baz", HashSet::from([4, 5]));
        assert_eq!(m.query_union("bat", 1), HashSet::from([3, 4, 5]));
    }

    #[test]
    fn the_same_source_aggregates_in_any_semiring() {
        // The string source feeding the prototype's semirings: Count = number of fuzzy
        // matches, Tropical = best (min) edit distance.
        let mut m: FuzzyMap<()> = FuzzyMap::new();
        for k in ["foo", "bar", "baz", "bat"] {
            m.insert(k, ());
        }
        // within distance 1 of "bat": bar, baz, bat -> 3 matches.
        let n = m.query::<Count>("bat", 1, |_, _, _| Count(1));
        assert_eq!(n, Count(3));
        // best edit distance to "bat": bat itself, distance 0.
        let best = m.query::<Tropical>("bat", 2, |_, _, d| Tropical(Some(d as i64)));
        assert_eq!(best, Tropical(Some(0)));
        // best distance when "bat" itself is absent (within 1 of "far"): bar at distance 1.
        let mut m2: FuzzyMap<()> = FuzzyMap::new();
        for k in ["foo", "bar", "baz"] {
            m2.insert(k, ());
        }
        let best2 = m2.query::<Tropical>("far", 1, |_, _, d| Tropical(Some(d as i64)));
        assert_eq!(best2, Tropical(Some(1)));
    }
}
