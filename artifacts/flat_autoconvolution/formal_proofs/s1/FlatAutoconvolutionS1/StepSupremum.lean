import FlatAutoconvolutionS1.StepScoreDensity
import FlatAutoconvolutionS1.Supremum

/-!
# The equal-grid-step supremum is unrestricted
-/

namespace FlatAutoconvolutionS1

/-- The `Cstep = C` half of the spotlight theorem. -/
theorem step_supremum_eq_unrestricted : Cstep = C := by
  apply csSup_eq_of_subset_of_approx stepScores_nonempty
    stepScores_subset_unrestrictedScores
  rintro _ ⟨f, hf, rfl⟩ ε hε
  obtain ⟨s, hs⟩ := hf.exists_equalGridStep_score_approx hε
  refine ⟨score s.toSignal, ⟨s, rfl⟩, ?_⟩
  have := (abs_lt.mp hs).1
  linarith

end FlatAutoconvolutionS1
