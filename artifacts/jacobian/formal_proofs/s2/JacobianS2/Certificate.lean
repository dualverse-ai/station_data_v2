import JacobianS2.DenseFiber

/-!
# Non-vacuity: the paper's displayed three-point fiber

This specialization shows that the hypotheses of `three_sheeted_fiber` really
hold at the target and points printed in the paper.
-/

namespace JacobianS2

def paperTarget : Point ℚ := ⟨1, 7 / 3, 0⟩
def paperPoint₁ : Point ℚ := ⟨-6 / 7, -7 / 6, -4753 / 216⟩
def paperPoint₂ : Point ℚ := ⟨3 / 4, 7 / 3, -980 / 27⟩
def paperPoint₃ : Point ℚ := ⟨3 / 28, 7 / 3, 2548 / 27⟩

theorem recover_paper_roots :
    recover 6 paperTarget 0 = paperPoint₁ ∧
    recover 6 paperTarget 1 = paperPoint₂ ∧
    recover 6 paperTarget (-7) = paperPoint₃ := by
  norm_num [recover, cubicDeriv, paperTarget, paperPoint₁, paperPoint₂, paperPoint₃]

/-- The displayed target has exactly the three displayed rational preimages. -/
theorem paper_target_exactly_three :
    map 6 paperPoint₁ = paperTarget ∧
    map 6 paperPoint₂ = paperTarget ∧
    map 6 paperPoint₃ = paperTarget ∧
    paperPoint₁ ≠ paperPoint₂ ∧ paperPoint₁ ≠ paperPoint₃ ∧ paperPoint₂ ≠ paperPoint₃ ∧
    ∀ p : Point ℚ, map 6 p = paperTarget →
      p = paperPoint₁ ∨ p = paperPoint₂ ∨ p = paperPoint₃ := by
  have h := three_sheeted_fiber (K := ℚ) (a := 6) (q := paperTarget)
    (r₁ := 0) (r₂ := 1) (r₃ := -7)
    (by norm_num) (by norm_num [paperTarget])
    (by
      intro s
      norm_num [cubic, paperTarget]
      ring)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [cubicDeriv, paperTarget])
    (by norm_num [cubicDeriv, paperTarget])
    (by norm_num [cubicDeriv, paperTarget])
  rw [recover_paper_roots.1, recover_paper_roots.2.1, recover_paper_roots.2.2] at h
  exact h

end JacobianS2
