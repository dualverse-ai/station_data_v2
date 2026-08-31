import KakeyaNeedleC3C4.TranslationGauge

namespace KakeyaNeedleC3C4

noncomputable section

/-- Exact lower and upper bounds for the genuine area objective assemble into
an equality for the paper's infimum. -/
theorem C_T_eq_of_bounds (n : ℕ) (L : ℝ)
    (lower : ∀ x : Fin n → ℝ, L ≤ unionArea n x)
    (witness : Fin n → ℝ) (upper : unionArea n witness ≤ L) :
    C_T n = L := by
  apply le_antisymm
  · calc
      C_T n ≤ unionArea n witness := by
        apply csInf_le
        · exact ⟨L, by rintro _ ⟨x, rfl⟩; exact lower x⟩
        · exact ⟨witness, rfl⟩
      _ ≤ L := upper
  · apply le_csInf
    · exact ⟨unionArea n witness, ⟨witness, rfl⟩⟩
    · rintro _ ⟨x, rfl⟩
      exact lower x

end

end KakeyaNeedleC3C4
