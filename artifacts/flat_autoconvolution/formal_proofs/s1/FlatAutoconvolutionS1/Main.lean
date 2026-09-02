import FlatAutoconvolutionS1.StepAdmissible
import FlatAutoconvolutionS1.ConvolutionL1
import FlatAutoconvolutionS1.ConvolutionL2
import FlatAutoconvolutionS1.ScoreLimit
import FlatAutoconvolutionS1.ConvolutionMass
import FlatAutoconvolutionS1.AdmissibleBounds
import FlatAutoconvolutionS1.OutputContinuity
import FlatAutoconvolutionS1.StepDensity
import FlatAutoconvolutionS1.StepScoreDensity
import FlatAutoconvolutionS1.FiniteProfile
import FlatAutoconvolutionS1.GridBridge
import FlatAutoconvolutionS1.AffineScore
import FlatAutoconvolutionS1.CoefficientBridge
import FlatAutoconvolutionS1.StepProfileBridge
import FlatAutoconvolutionS1.BinaryRefinement
import FlatAutoconvolutionS1.BinaryApproximation
import FlatAutoconvolutionS1.BinaryStepDensity
import FlatAutoconvolutionS1.Supremum
import FlatAutoconvolutionS1.StepSupremum

namespace FlatAutoconvolutionS1

/-! # Flat autoconvolution, Spotlight 1 -/

/-- Strong local form: every admissible score is approximated by the score of
a genuine nonempty binary equal-grid step.  The grid resolution is unbounded
along the construction used in `BinaryApproximation`. -/
theorem Admissible.exists_binaryStep_score_approx
    {f : Signal} (hf : Admissible f) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : BinaryStep, |score b.toSignal - score f| < ε := by
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨g, hg⟩ := hf.exists_equalGridStep_score_approx hhalf
  obtain ⟨b, hb⟩ := g.exists_binaryStep_score_approx hhalf
  refine ⟨b, lt_of_le_of_lt (abs_sub_le _ (score g.toSignal) _) ?_⟩
  linarith

/-- Complete three-class formulation of Spotlight 1. -/
theorem flat_autoconvolution_spotlight_one_full :
    C01 = Cstep ∧ Cstep = C := by
  exact suprema_eq_from_binary_score_dense fun f hf ε hε ↦
    hf.exists_binaryStep_score_approx hε

/-- Spotlight 1 as stated in the paper: binary equal-grid step functions
preserve the unrestricted supremum of the flat-autoconvolution score. -/
theorem flat_autoconvolution_spotlight_one : C01 = C := by
  exact flat_autoconvolution_spotlight_one_full.1.trans
    flat_autoconvolution_spotlight_one_full.2

end FlatAutoconvolutionS1
