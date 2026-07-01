//! Anti-unification: the least general generalization (Plotkin 1970, Reynolds 1970),
//! the lattice JOIN dual to unification's meet. This is the "union" in a fuzzy descent, and
//! the operation that forms generalization templates.
//!
//! `anti_unify(s, t)` is the most specific term that both `s` and `t` are instances of.
//! Where the two terms agree it keeps the structure; where they disagree it puts a
//! variable, and the SAME disagreement pair gets the SAME variable, so `(f a a)` and
//! `(f b b)` generalize to `(f $0 $0)`, not `(f $0 $1)`. That consistency is what makes
//! it the *least* general generalization rather than just *a* generalization.
//!
//! Lattice picture: order terms by "is an instance of". Unification is the meet (the most
//! general common instance, the mgu); anti-unification is the join (the least general
//! common generalization, the lgg). A variable is the top element.

use crate::term::Term;
use std::collections::HashMap;

/// The least general generalization of `a` and `b`.
pub fn anti_unify(a: &Term, b: &Term) -> Term {
    // Disagreement pairs, keyed by the canonical encoding of each side (so the same pair
    // up to variable renaming reuses the same generalization variable).
    let mut subs: HashMap<(Vec<u8>, Vec<u8>), u32> = HashMap::new();
    let mut next = 0u32;
    lgg(a, b, &mut subs, &mut next)
}

fn lgg(a: &Term, b: &Term, subs: &mut HashMap<(Vec<u8>, Vec<u8>), u32>, next: &mut u32) -> Term {
    match (a, b) {
        (Term::Sym(x), Term::Sym(y)) if x == y => Term::Sym(x.clone()),
        (Term::App(xs), Term::App(ys)) if xs.len() == ys.len() => Term::App(
            xs.iter()
                .zip(ys)
                .map(|(x, y)| lgg(x, y, subs, next))
                .collect(),
        ),
        // A disagreement (different symbols, different arity, or a variable on a side):
        // a fresh variable, but the same one for the same disagreement pair.
        _ => {
            let key = (a.encode(), b.encode());
            let v = *subs.entry(key).or_insert_with(|| {
                let v = *next;
                *next += 1;
                v
            });
            Term::Var(v)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::parse;
    use crate::unify::Env;

    fn au(a: &str, b: &str) -> Term {
        anti_unify(&parse(a), &parse(b))
    }

    #[test]
    fn shared_disagreement_shares_a_variable() {
        // (f a a) and (f b b) generalize to (f $x $x), not (f $x $y).
        assert_eq!(
            au("(f a a)", "(f b b)").encode(),
            parse("(f $x $x)").encode()
        );
        // distinct disagreements get distinct variables.
        assert_eq!(
            au("(f a c)", "(f b d)").encode(),
            parse("(f $x $y)").encode()
        );
    }

    #[test]
    fn keeps_the_common_part() {
        assert_eq!(
            au("(f a b)", "(f a c)").encode(),
            parse("(f a $x)").encode()
        );
        assert_eq!(
            au("(f a b)", "(f c b)").encode(),
            parse("(f $x b)").encode()
        );
        assert_eq!(
            au("(g (h a) b)", "(g (h a) c)").encode(),
            parse("(g (h a) $x)").encode()
        );
    }

    #[test]
    fn idempotent_and_top() {
        // lgg(a, a) = a.
        assert_eq!(
            au("(f a (g b))", "(f a (g b))").encode(),
            parse("(f a (g b))").encode()
        );
        // Same arity, different head: the structure is kept with a variable in the head.
        assert_eq!(au("(f a)", "(g a)").encode(), parse("($h a)").encode());
        // Incompatible shapes (symbol vs expression, or different arity) generalize to a
        // bare variable, the top element.
        assert!(matches!(au("a", "(f a)"), Term::Var(_)));
        assert!(matches!(au("(f a)", "(f a b)"), Term::Var(_)));
    }

    /// Both inputs must be instances of the generalization (the defining property).
    fn is_instance_of(general: &Term, specific: &Term) -> bool {
        // Rename the generalization apart, then it should unify with the (ground) specific
        // term and resolve back to it.
        let g = general.rename_apart(5_000_000);
        let mut env = Env::new();
        env.unify(&g, specific) && env.resolve(&g) == *specific
    }

    #[test]
    fn both_inputs_are_instances() {
        for (a, b) in [
            ("(f a a)", "(f b b)"),
            ("(f a b)", "(f a c)"),
            ("(g (h a) b)", "(g (h c) d)"),
            ("(cons 1 (cons 2 nil))", "(cons 3 (cons 4 nil))"),
        ] {
            let g = au(a, b);
            assert!(is_instance_of(&g, &parse(a)), "{a} not an instance of lgg");
            assert!(is_instance_of(&g, &parse(b)), "{b} not an instance of lgg");
        }
    }

    // --- property test: the generalization property holds on random ground terms ---

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
        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    fn gen_ground(rng: &mut Rng, depth: usize) -> Term {
        const SYMS: &[&str] = &["a", "b", "c", "f", "g"];
        if depth == 0 || rng.below(3) == 0 {
            Term::sym(SYMS[rng.below(SYMS.len())])
        } else {
            let arity = 1 + rng.below(2);
            Term::App((0..arity).map(|_| gen_ground(rng, depth - 1)).collect())
        }
    }

    #[test]
    fn generalization_property_random() {
        let mut rng = Rng(0xC0FFEE123);
        for _ in 0..3000 {
            let a = gen_ground(&mut rng, 3);
            let b = gen_ground(&mut rng, 3);
            let g = anti_unify(&a, &b);
            assert!(is_instance_of(&g, &a), "lgg not a generalization of a={a}");
            assert!(is_instance_of(&g, &b), "lgg not a generalization of b={b}");
        }
    }
}
