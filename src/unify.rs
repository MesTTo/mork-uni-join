//! Unification with an explicit trail (the WAM idea), occurs check included.
//!
//! This is the *meet* of the term lattice: `unify(a, b)` finds the most general
//! substitution making `a` and `b` equal, or fails. It is both the per-variable
//! operation the join performs and the core of the differential oracle.
//!
//! The trail records every binding so the join can `mark()` a point, try a branch, and
//! `rollback(mark)` in O(1) per binding when it backtracks. This is exactly MORK's
//! `TrailRollback` / WAM `unify_value` machinery, kept tiny here.

use crate::term::Term;
use std::collections::HashMap;

/// A substitution environment with a trail for backtracking.
#[derive(Default)]
pub struct Env {
    bindings: HashMap<u32, Term>,
    trail: Vec<u32>,
}

impl Env {
    pub fn new() -> Self {
        Env::default()
    }

    /// A point to roll back to later.
    pub fn mark(&self) -> usize {
        self.trail.len()
    }

    /// Undo every binding made since `mark`. O(1) per undone binding.
    pub fn rollback(&mut self, mark: usize) {
        while self.trail.len() > mark {
            let v = self.trail.pop().unwrap();
            self.bindings.remove(&v);
        }
    }

    fn bind(&mut self, v: u32, t: Term) {
        self.bindings.insert(v, t);
        self.trail.push(v);
    }

    /// Bind an (assumed-unbound) variable to a term, recorded on the trail. Public entry
    /// point for the scored matcher, which binds structurally rather than full-unifying.
    pub fn bind_var(&mut self, v: u32, t: Term) {
        self.bind(v, t);
    }

    /// Follow the binding chain at the head of `t` (var -> its binding -> ...), returning
    /// the first non-bound-variable / non-variable term. Shallow (head only).
    pub fn walk<'a>(&'a self, t: &'a Term) -> &'a Term {
        let mut cur = t;
        while let Term::Var(x) = cur {
            match self.bindings.get(x) {
                Some(next) => cur = next,
                None => break,
            }
        }
        cur
    }

    /// Apply the substitution fully (deep), producing a term with all bound variables
    /// replaced. Unbound variables are left as-is.
    pub fn resolve(&self, t: &Term) -> Term {
        match self.walk(t) {
            Term::Sym(s) => Term::Sym(s.clone()),
            Term::Var(x) => Term::Var(*x),
            Term::App(a) => Term::App(a.iter().map(|x| self.resolve(x)).collect()),
        }
    }

    /// Unify `a` and `b`. On success, the binding is left in place and `true` returned.
    /// On failure, any partial bindings are rolled back and `false` returned, so a failed
    /// unify never leaves the environment dirty.
    pub fn unify(&mut self, a: &Term, b: &Term) -> bool {
        let m = self.mark();
        if self.unify_rec(a, b) {
            true
        } else {
            self.rollback(m);
            false
        }
    }

    fn unify_rec(&mut self, a: &Term, b: &Term) -> bool {
        // Clone the walked heads so we can mutate `self` freely below.
        let a = self.walk(a).clone();
        let b = self.walk(b).clone();
        match (&a, &b) {
            (Term::Var(x), Term::Var(y)) if x == y => true,
            (Term::Var(x), _) => {
                if self.occurs(*x, &b) {
                    false
                } else {
                    self.bind(*x, b);
                    true
                }
            }
            (_, Term::Var(y)) => {
                if self.occurs(*y, &a) {
                    false
                } else {
                    self.bind(*y, a);
                    true
                }
            }
            (Term::Sym(p), Term::Sym(q)) => p == q,
            (Term::App(xs), Term::App(ys)) => {
                if xs.len() != ys.len() {
                    return false;
                }
                for (x, y) in xs.iter().zip(ys.iter()) {
                    if !self.unify_rec(x, y) {
                        return false;
                    }
                }
                true
            }
            _ => false,
        }
    }

    /// Does variable `x` occur in `t` (under the current substitution)? Prevents binding
    /// `x` to a term containing `x`, which would build an infinite term.
    fn occurs(&self, x: u32, t: &Term) -> bool {
        match self.walk(t) {
            Term::Var(y) => x == *y,
            Term::Sym(_) => false,
            Term::App(a) => a.iter().any(|s| self.occurs(x, s)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::parse;

    // Parse two patterns with disjoint variables (rename the second apart).
    fn two(a: &str, b: &str) -> (Term, Term) {
        (parse(a), parse(b).rename_apart(1000))
    }

    #[test]
    fn unifies_both_sides() {
        let (a, b) = two("(f $x b)", "(f a $y)");
        let mut e = Env::new();
        assert!(e.unify(&a, &b));
        // $x (id 0) = a, $y (id 1000) = b
        assert_eq!(e.resolve(&Term::Var(0)), parse("a"));
        assert_eq!(e.resolve(&Term::Var(1000)), parse("b"));
    }

    #[test]
    fn different_heads_fail() {
        let (a, b) = two("(f $x)", "(g a)");
        let mut e = Env::new();
        assert!(!e.unify(&a, &b));
    }

    #[test]
    fn coreference_contradiction_fails() {
        // (f $x $x) vs (f a b): $x cannot be both a and b.
        let (a, b) = two("(f $x $x)", "(f a b)");
        let mut e = Env::new();
        assert!(!e.unify(&a, &b));
    }

    #[test]
    fn occurs_check_fails_not_loops() {
        // $x vs (f $x): would build f(f(f(...))). Must fail.
        let x = Term::Var(0);
        let fx = parse("(f $x)"); // also Var(0)
        let mut e = Env::new();
        assert!(!e.unify(&x, &fx));
    }

    #[test]
    fn variable_bound_to_structure() {
        let (a, b) = two("(f $x)", "(f (g $y))");
        let mut e = Env::new();
        assert!(e.unify(&a, &b));
        assert_eq!(e.resolve(&Term::Var(0)), parse("(g $y)").rename_apart(1000));
    }

    #[test]
    fn rollback_restores_environment() {
        let mut e = Env::new();
        let m = e.mark();
        assert!(e.unify(&Term::Var(0), &parse("a")));
        assert_eq!(e.resolve(&Term::Var(0)), parse("a"));
        e.rollback(m);
        // After rollback, $0 is unbound again.
        assert_eq!(e.resolve(&Term::Var(0)), Term::Var(0));
    }

    #[test]
    fn func_type_unification_pieces() {
        // The two patterns from MORK's func_type_unification test, sharing $f.
        // (: ($f) A) ~ (: (f) A)   and   (: $f (-> A)) ~ (: f (-> A))
        // Together they force $f = f.
        let p1 = parse("(: ($f) A)");
        let d1 = parse("(: (f) A)");
        let p2 = parse("(: $f (-> A))");
        let d2 = parse("(: f (-> A))");
        let mut e = Env::new();
        assert!(e.unify(&p1, &d1));
        assert!(e.unify(&p2, &d2));
        assert_eq!(e.resolve(&Term::Var(0)), parse("f"), "$f must unify to f");
    }
}
