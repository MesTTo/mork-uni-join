//! Z-order (Morton) space-filling curve: the MORK-native spatial index from the meeting
//! (the UB-tree idea). Interleave the bits of each coordinate, most-significant first,
//! into one key, so a multidimensional point becomes a single trie path and a box query
//! becomes a contiguous range scan. "Good mixing" is the interleaving: one prefix narrows
//! every dimension at once, which is exactly the `proj_i_c` bisection Adam drew, with the
//! "big to small" ordering being most-significant-bit first.
//!
//! Orthogonal finite dimensions make the curve factorize, which is what keeps the descent
//! worst-case-optimal. A box range over-covers on the curve (the curve leaves and re-enters
//! the box); we scan the Z-interval and filter, and note where BIGMIN/LITMAX would skip the
//! dead sub-ranges.

use std::collections::BTreeMap;

/// Interleave `coords` (each `bits` wide), MSB first, into a Morton code. `dims * bits`
/// must be <= 128.
pub fn morton_encode(coords: &[u32], bits: u32) -> u128 {
    assert!(coords.len() as u32 * bits <= 128, "morton code wider than 128 bits");
    let mut code: u128 = 0;
    for b in (0..bits).rev() {
        for &c in coords {
            code = (code << 1) | u128::from((c >> b) & 1);
        }
    }
    code
}

/// Invert [`morton_encode`].
pub fn morton_decode(code: u128, dims: usize, bits: u32) -> Vec<u32> {
    let mut coords = vec![0u32; dims];
    let total = dims as u32 * bits;
    for p in 0..total {
        let bit = ((code >> (total - 1 - p)) & 1) as u32;
        let round = p / dims as u32; // 0 = highest bit level
        let dim = (p % dims as u32) as usize;
        let shift = bits - 1 - round;
        coords[dim] |= bit << shift;
    }
    coords
}

/// A Z-order index: points keyed by their Morton code, so `BTreeMap` order is curve order.
pub struct ZIndex {
    dims: usize,
    bits: u32,
    points: BTreeMap<u128, Vec<Vec<u32>>>,
}

/// Counters to show the over-coverage a Z-interval scan pays (and that BIGMIN would skip).
#[derive(Default, Debug, Clone, Copy)]
pub struct RangeStats {
    pub scanned: u64,
    pub returned: u64,
}

impl ZIndex {
    pub fn new(dims: usize, bits: u32) -> Self {
        ZIndex {
            dims,
            bits,
            points: BTreeMap::new(),
        }
    }

    pub fn insert(&mut self, coords: &[u32]) {
        assert_eq!(coords.len(), self.dims);
        let code = morton_encode(coords, self.bits);
        self.points.entry(code).or_default().push(coords.to_vec());
    }

    fn in_box(p: &[u32], lo: &[u32], hi: &[u32]) -> bool {
        p.iter().zip(lo).zip(hi).all(|((&v, &l), &h)| l <= v && v <= h)
    }

    /// All points inside the box `[lo, hi]` (inclusive per dimension), found by scanning
    /// the Z-interval `[morton(lo), morton(hi)]` and filtering. The scan is one contiguous
    /// trie range; the filter drops the points the curve passed through outside the box.
    pub fn range(&self, lo: &[u32], hi: &[u32]) -> (Vec<Vec<u32>>, RangeStats) {
        let zlo = morton_encode(lo, self.bits);
        let zhi = morton_encode(hi, self.bits);
        let (zlo, zhi) = (zlo.min(zhi), zlo.max(zhi));
        let mut out = Vec::new();
        let mut stats = RangeStats::default();
        for (_code, pts) in self.points.range(zlo..=zhi) {
            for p in pts {
                stats.scanned += 1;
                if Self::in_box(p, lo, hi) {
                    stats.returned += 1;
                    out.push(p.clone());
                }
            }
        }
        out.sort();
        (out, stats)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn morton_roundtrips() {
        for (coords, bits) in [
            (vec![5u32, 3], 4u32),
            (vec![0, 0, 0], 3),
            (vec![15, 15], 4),
            (vec![100, 200, 50], 8),
            (vec![1, 2, 3, 4], 5),
        ] {
            let code = morton_encode(&coords, bits);
            assert_eq!(morton_decode(code, coords.len(), bits), coords);
        }
    }

    #[test]
    fn nearby_points_share_a_prefix() {
        // (4,4) and (4,5) differ in one low bit, so their Morton codes are close; (4,4)
        // and (12,4) differ in a high bit, so they are far. That locality is what makes
        // the range a contiguous trie scan.
        let near = morton_encode(&[4, 4], 4) ^ morton_encode(&[4, 5], 4);
        let far = morton_encode(&[4, 4], 4) ^ morton_encode(&[12, 4], 4);
        assert!(near < far);
    }

    // --- differential: the Z-order range query equals a brute-force box scan ---

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            self.0 = x;
            x.wrapping_mul(0x2545F4914F6CDD1D)
        }
        fn below(&mut self, n: u32) -> u32 {
            (self.next() % n as u64) as u32
        }
    }

    #[test]
    fn range_query_matches_brute_force() {
        let mut rng = Rng(0x5EED);
        let bits = 5u32;
        let max = 1u32 << bits; // coords in 0..32
        for dims in [2usize, 3] {
            for _ in 0..400 {
                // random point set
                let pts: Vec<Vec<u32>> = (0..40)
                    .map(|_| (0..dims).map(|_| rng.below(max)).collect())
                    .collect();
                let mut idx = ZIndex::new(dims, bits);
                for p in &pts {
                    idx.insert(p);
                }
                // random box
                let mut lo = vec![0u32; dims];
                let mut hi = vec![0u32; dims];
                for d in 0..dims {
                    let a = rng.below(max);
                    let b = rng.below(max);
                    lo[d] = a.min(b);
                    hi[d] = a.max(b);
                }
                let (got, _stats) = idx.range(&lo, &hi);
                let mut want: Vec<Vec<u32>> = pts
                    .iter()
                    .filter(|p| ZIndex::in_box(p, &lo, &hi))
                    .cloned()
                    .collect();
                want.sort();
                assert_eq!(got, want, "Z-order range != brute force for box {lo:?}..{hi:?}");
            }
        }
    }
}
