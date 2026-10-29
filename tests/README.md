Regression exports beyond the arena's suite, run by tools/regress.sh BIN.

- soundness/: exports Lean REJECTS; a checker must not accept them.
  - proj_fst_any: `∀ p q : ℕ × ℕ, p.1 = q.1 := fun p q => Eq.refl p.1`
    (hand-built; the official kernel rejects it). Accepted before 2026-10-28:
    the catch-all's same-head test read every non-constant head as one name.
- accept/: miniatures Lean accepts that once failed here.
  - eqndrec_quot_sound(_nat): an Eq.ndrec over Quot.sound against its
    Sym2-style unfolding (cslib Sym2.pmap._proof_1; rejected, then declined).
  - indexed_rec_universe_ih: `isAx.eq_def` for a universe-polymorphic
    indexed family `Pf (α : Type u) : List α → Type u` with a recursive
    constructor; the iota rule's inductive hypothesis kept the
    constructor's own universe `u` (cslib's CLL.Proof equations).
  - inductive_type_behind_def(2): an inductive whose declared type hides
    its indices behind a definition (`inductive CompClo .. : HomRel C`,
    `inductive RC .. : Rel2 α`); Lean peels the type through whnf. The first
    was REJECTED (mathlib's CategoryTheory.HomRel.CompClosure), the second
    declined.
