Regression exports beyond the arena's suite, run by tools/regress.sh BIN.

- soundness/: exports Lean REJECTS; a checker must not accept them.
  - proj_fst_any: `∀ p q : ℕ × ℕ, p.1 = q.1 := fun p q => Eq.refl p.1`
    (hand-built; the official kernel rejects it). Accepted before 2026-10-28:
    the catch-all's same-head test read every non-constant head as one name.
- accept/: miniatures Lean accepts that once failed here.
  - eqndrec_quot_sound(_nat): an Eq.ndrec over Quot.sound against its
    Sym2-style unfolding (cslib Sym2.pmap._proof_1; rejected, then declined).
