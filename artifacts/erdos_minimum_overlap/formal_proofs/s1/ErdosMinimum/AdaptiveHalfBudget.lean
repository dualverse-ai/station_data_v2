import ErdosMinimum.AdaptiveBudget
import ErdosMinimum.UniformHalfBudget

/-!
# Adaptive positive-half budgets for even rows

This is the symmetry wrapper for adaptive certificates on `[0,2]`.  The
generic adaptive checker proves the positive-half estimate; evenness turns it
into the required estimate on `[-2,2]`.
-/

namespace ErdosMinimum

/-- Full `[-2,2]` budget obtained by doubling an adaptive positive-half
budget. -/
def positivePartAdaptivePreparedEvenBudget (row : RatRow) (fixed : FixedRow)
    (curvature : FixedInterval) (segments : List AdaptiveSegment) : ℚ :=
  2 * positivePartAdaptivePreparedBudget row fixed curvature segments

/-- Soundness of a prepared adaptive partition of `[0,2]` for an even row. -/
theorem positivePartAdaptivePreparedEvenBudget_interval_le
    (row : RatRow) (fixed : FixedRow) (curvature : FixedInterval)
    (segments : List AdaptiveSegment)
    (hfixed : fixed = FixedRow.ofRatRow row)
    (hcurvature : curvature = FixedInterval.ofRat (rowCurvatureBound row))
    (hchain : AdaptiveChain 0 2 segments)
    (hsymmetric : RatRowSymmetric row)
    (hfreq : RowFrequenciesNonzero row) :
    (∫ x in (-2 : ℝ)..2, positivePart (ratRowFunction row) x) ≤
      (positivePartAdaptivePreparedEvenBudget row fixed curvature segments : ℝ) := by
  let g : ℝ → ℝ := positivePart (ratRowFunction row)
  have hg_even (x : ℝ) : g (-x) = g x := by
    simp only [g, positivePart, ratRowFunction_neg_of_symmetric row hsymmetric]
  have hg_cont : Continuous g := by
    simpa [g, positivePart] using
      (contDiff_ratRowFunction row).continuous.max continuous_const
  have hneg : (∫ x in (-2 : ℝ)..0, g x) = ∫ x in (0 : ℝ)..2, g x := by
    calc
      (∫ x in (-2 : ℝ)..0, g x) = ∫ x in (0 : ℝ)..2, g (-x) := by
        symm
        simpa using (intervalIntegral.integral_comp_neg (f := g)
          (a := (0 : ℝ)) (b := 2))
      _ = ∫ x in (0 : ℝ)..2, g x := by
        apply intervalIntegral.integral_congr
        intro x _
        exact hg_even x
  have hsplit : (∫ x in (-2 : ℝ)..2, g x) =
      (∫ x in (-2 : ℝ)..0, g x) + ∫ x in (0 : ℝ)..2, g x := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hg_cont.intervalIntegrable (-2) 0)
      (hg_cont.intervalIntegrable 0 2)]
  have hhalf := positivePartAdaptivePreparedBudget_interval_le_of_chain
    row fixed curvature hfixed hcurvature hchain hfreq
  rw [hsplit, hneg]
  calc
    (∫ x in (0 : ℝ)..2, g x) + ∫ x in (0 : ℝ)..2, g x ≤
        2 * (positivePartAdaptivePreparedBudget row fixed curvature segments : ℝ) := by
      norm_num at hhalf
      change (∫ x in (0 : ℝ)..2, g x) ≤ _ at hhalf
      simpa [two_mul] using add_le_add hhalf hhalf
    _ = (positivePartAdaptivePreparedEvenBudget row fixed curvature segments : ℝ) := by
      simp [positivePartAdaptivePreparedEvenBudget]

end ErdosMinimum
