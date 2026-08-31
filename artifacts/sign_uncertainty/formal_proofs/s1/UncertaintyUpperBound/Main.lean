import UncertaintyUpperBound.Witness

namespace UncertaintyUpperBound

/-- The certified upper bound from the paper: the one-dimensional sign uncertainty
constant is at most `0.3089`. -/
theorem C_SU_le_03089 : C_SU ≤ (3089 / 10000 : ℝ) := by
  calc
    signUncertaintyConstant ≤ uncertaintyWitness.score :=
      signUncertaintyConstant_le_score uncertaintyWitness
    _ ≤ certifiedRadius ^ 2 :=
      selfFourier_score_le_sq uncertaintyWitness rfl witness_tail
    _ = (1213 / 625 : ℝ) / (2 * Real.pi) := certifiedRadius_sq
    _ ≤ 3089 / 10000 := le_of_lt certified_ratio_lt

end UncertaintyUpperBound
