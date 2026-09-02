import Mathlib.Tactic

/-!
# Phase-coupled Fourier support inequality

This is the algebraic core of Lemma 2.2 in the verification notebook.  It is
stated without Fourier-analysis infrastructure: substituting the real and
imaginary Fourier identities gives precisely the two inequalities below.
-/

namespace ErdosMinimum

/-- Phase support inequality for the correlation orientation in which
`Q = 2*s*b`.  The proof remains valid when `s = 0`. -/
theorem phase_support_add (s a b α β : ℝ) (hα : 0 < α) :
    α * (2 * s * a - a ^ 2 - b ^ 2) + β * (2 * s * b) ≤
      s ^ 2 * (α + β ^ 2 / α) := by
  have h₁ : 0 ≤ α * (a - s) ^ 2 := mul_nonneg hα.le (sq_nonneg _)
  have h₂ : 0 ≤ (α * b - β * s) ^ 2 / α := div_nonneg (sq_nonneg _) hα.le
  have hid :
      s ^ 2 * (α + β ^ 2 / α) -
          (α * (2 * s * a - a ^ 2 - b ^ 2) + β * (2 * s * b)) =
        α * (a - s) ^ 2 + (α * b - β * s) ^ 2 / α := by
    field_simp
    ring
  linarith

/-- The same support inequality for the opposite sine-transform convention,
where `Q = -2*s*b`. -/
theorem phase_support_sub (s a b α β : ℝ) (hα : 0 < α) :
    α * (2 * s * a - a ^ 2 - b ^ 2) + β * (-2 * s * b) ≤
      s ^ 2 * (α + β ^ 2 / α) := by
  simpa [sq] using phase_support_add s a b α (-β) hα

/-- The parabolic form quoted in the paper, away from a zero of `s`. -/
theorem phase_parabola (s a b Q : ℝ) (hs : s ≠ 0) (hQ : Q ^ 2 = 4 * s ^ 2 * b ^ 2) :
    2 * s * a - a ^ 2 - b ^ 2 ≤ s ^ 2 - Q ^ 2 / (4 * s ^ 2) := by
  have hs2 : 4 * s ^ 2 ≠ 0 := by positivity
  rw [hQ]
  field_simp
  nlinarith [sq_nonneg (a - s)]

end ErdosMinimum
