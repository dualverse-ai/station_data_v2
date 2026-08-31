import UncertaintyS2.LowerCertificate
import UncertaintyS2.UpperBound

namespace UncertaintyS2

open Set

theorem witness_score_mem :
    tailThreshold witnessR / (2 * Real.pi) ∈ DR20Scores :=
  ⟨witnessR, ⟨witness_is_DR20⟩, rfl⟩

theorem scores_nonempty : DR20Scores.Nonempty := ⟨_, witness_score_mem⟩

theorem scores_bddBelow : BddBelow DR20Scores := by
  refine ⟨0, ?_⟩
  intro a ha
  obtain ⟨P, ⟨hP⟩, rfl⟩ := ha
  exact div_nonneg (tailThreshold_nonneg hP.tail_nonempty) (by positivity)

theorem C_DR_20_lower : (63061 / 200000 : ℝ) < C_DR_20 := by
  apply lt_of_lt_of_le rational_lower_lt_node_score
  apply le_csInf scores_nonempty
  intro a ha
  obtain ⟨P, ⟨hP⟩, rfl⟩ := ha
  exact div_le_div_of_nonneg_right (first_node_le_tailThreshold hP) (by positivity)

theorem C_DR_20_upper :
    C_DR_20 < (3153090099692479 / 10000000000000000 : ℝ) := by
  exact (csInf_le scores_bddBelow witness_score_mem).trans_lt witness_score_lt_upper

/-- Spotlight 2: the double-root Laguerre family with at most twenty prescribed
positive double roots is exhausted near `0.3153`. -/
theorem spotlight_two :
    (63061 / 200000 : ℝ) < C_DR_20 ∧
      C_DR_20 < (3153090099692479 / 10000000000000000 : ℝ) :=
  ⟨C_DR_20_lower, C_DR_20_upper⟩

end UncertaintyS2
