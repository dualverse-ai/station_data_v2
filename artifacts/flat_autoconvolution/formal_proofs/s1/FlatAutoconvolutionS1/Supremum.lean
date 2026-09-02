import FlatAutoconvolutionS1.StepAdmissible

/-!
# A general supremum-transfer lemma

This file contains the order-theoretic last step of the binary-step reduction.
The hypotheses are stated as one-sided score approximation, which is exactly
what is needed and avoids any hidden attainment assumption about a supremum.
-/

open Set

namespace FlatAutoconvolutionS1

/-- If `small ⊆ large` and every value in `large` can be approximated from
below by values in `small`, then their real suprema agree. -/
theorem csSup_eq_of_subset_of_approx
    {small large : Set ℝ}
    (hne : small.Nonempty)
    (hsub : small ⊆ large)
    (happrox : ∀ x ∈ large, ∀ ε > 0, ∃ y ∈ small, x - ε < y) :
    sSup small = sSup large := by
  by_cases hbdd : BddAbove large
  · apply le_antisymm
    · exact csSup_le hne fun y hy => le_csSup hbdd (hsub hy)
    · apply csSup_le (hne.mono hsub)
      intro x hx
      by_contra hnot
      have hlt : sSup small < x := lt_of_not_ge hnot
      obtain ⟨y, hy, hxy⟩ := happrox x hx (x - sSup small) (sub_pos.mpr hlt)
      have hy_le : y ≤ sSup small := le_csSup (hbdd.mono hsub) hy
      linarith
  · have hsmall : ¬ BddAbove small := by
      intro hs
      rcases hs with ⟨M, hM⟩
      apply hbdd
      refine ⟨M + 1, ?_⟩
      intro x hx
      obtain ⟨y, hy, hxy⟩ := happrox x hx 1 zero_lt_one
      have hyM := hM hy
      linarith
    rw [Real.sSup_of_not_bddAbove hsmall, Real.sSup_of_not_bddAbove hbdd]

/-- The order-theoretic assembly of Theorem 2.1 from its stronger local form.
This theorem is intentionally not the exported S1 theorem: `Main.lean`
discharges `hdense` using the analytic density and Bernoulli-refinement proofs.
-/
theorem suprema_eq_from_binary_score_dense
    (hdense : ∀ f, Admissible f → ∀ ε > 0,
      ∃ b : BinaryStep, |score b.toSignal - score f| < ε) :
    C01 = Cstep ∧ Cstep = C := by
  have happroxBinary : ∀ x ∈ unrestrictedScores, ∀ ε > 0,
      ∃ y ∈ binaryScores, x - ε < y := by
    rintro x ⟨f, hf, rfl⟩ ε hε
    obtain ⟨b, hb⟩ := hdense f hf ε hε
    refine ⟨score b.toSignal, ⟨b, rfl⟩, ?_⟩
    have := (abs_lt.mp hb).1
    linarith
  have h01C : C01 = C := by
    exact csSup_eq_of_subset_of_approx binaryScores_nonempty
      binaryScores_subset_unrestrictedScores happroxBinary
  have hstepC : Cstep = C := by
    apply csSup_eq_of_subset_of_approx stepScores_nonempty
      stepScores_subset_unrestrictedScores
    intro x hx ε hε
    obtain ⟨y, hy, hxy⟩ := happroxBinary x hx ε hε
    exact ⟨y, binaryScores_subset_stepScores hy, hxy⟩
  exact ⟨h01C.trans hstepC.symm, hstepC⟩

end FlatAutoconvolutionS1
