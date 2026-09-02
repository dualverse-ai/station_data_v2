import FlatAutoconvolutionS1.BinaryApproximation
import FlatAutoconvolutionS1.BinaryRefinement

/-!
# Binary approximation of equal-grid steps

This module joins the Bernoulli--Hoeffding coefficient refinement to the
analytic output-continuity theorem.  The result is the local, stronger form
of the binary-step reduction: every nonnegative equal-grid step score is a
limit of scores of nonempty binary steps on arbitrarily fine grids.
-/

namespace FlatAutoconvolutionS1

/-- The probability theorem supplies exactly the `NNReal` refinement
interface consumed by `BinaryApproximation`. -/
theorem normalizedProfile_hasNNRealCoefficientRefinements (g : EqualGridStep) :
    HasNNRealCoefficientRefinements
      (fun i ↦ ⟨g.normalizedProfile i,
        g.normalizedProfile_nonnegative i⟩) := by
  intro δ hδ T₀
  have hv : ∀ i,
      (⟨g.normalizedProfile i,
        g.normalizedProfile_nonnegative i⟩ : NNReal) ≤ 1 := by
    intro i
    exact_mod_cast g.normalizedProfile_le_one i
  obtain ⟨T, hT₀, hT, ξ, hsupp, hclose⟩ :=
    BinaryRefinement.binaryRefinementProperty g.cells g.cells_pos
      (fun i ↦ ⟨g.normalizedProfile i,
        g.normalizedProfile_nonnegative i⟩) hv δ hδ T₀
  refine ⟨T, hT₀, hT, ξ, hsupp, ?_⟩
  have hbool :
      (fun i ↦ BinaryRefinement.boolReal (ξ i)) =
        fun i ↦ natBoolReal (ξ i) := by
    funext i
    cases ξ i <;> rfl
  have hblock :
      (fun i ↦ (BinaryRefinement.blockProb g.cells T
        (fun j ↦ ⟨g.normalizedProfile j,
          g.normalizedProfile_nonnegative j⟩) i).toReal) =
        fun i ↦ (nnBlockProfile T
          (fun j ↦ ⟨g.normalizedProfile j,
            g.normalizedProfile_nonnegative j⟩) i : ℝ) := by
    funext i
    unfold BinaryRefinement.blockProb nnBlockProfile
    split_ifs <;> rfl
  rw [hbool, hblock] at hclose
  simpa only [BinaryRefinement.coeff, rangeCoeff] using hclose

/-- Every nonzero nonnegative equal-grid step has binary-step scores
arbitrarily close to its score. -/
theorem EqualGridStep.exists_binaryStep_score_approx
    (g : EqualGridStep) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : BinaryStep, |score b.toSignal - score g.toSignal| < ε := by
  exact exists_binaryStep_score_approx_of_nnreal_rounding g
    (normalizedProfile_hasNNRealCoefficientRefinements g) hε

end FlatAutoconvolutionS1
