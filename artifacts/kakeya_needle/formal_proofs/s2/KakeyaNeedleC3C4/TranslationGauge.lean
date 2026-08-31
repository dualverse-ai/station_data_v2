import KakeyaNeedleC3C4.Slices

namespace KakeyaNeedleC3C4

open Set MeasureTheory
open scoped Pointwise

noncomputable section

theorem sliceUnion_add_const (n : ℕ) (x : Fin n → ℝ) (c y : ℝ) :
    sliceUnion n (fun j => x j + c) y = c +ᵥ sliceUnion n x y := by
  ext u
  simp only [sliceUnion, mem_iUnion, mem_Icc, mem_vadd_set]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨u - c, ?_, ?_⟩
    · refine ⟨j, ?_⟩
      constructor <;> dsimp [leftEndpoint, rightEndpoint] at hj ⊢ <;> linarith
    · dsimp
      abel
  · rintro ⟨v, ⟨j, hj⟩, rfl⟩
    refine ⟨j, ?_⟩
    constructor <;> dsimp [leftEndpoint, rightEndpoint] at hj ⊢ <;> linarith

theorem sliceLength_add_const (n : ℕ) (x : Fin n → ℝ) (c y : ℝ) :
    sliceLength n (fun j => x j + c) y = sliceLength n x y := by
  rw [sliceLength, sliceUnion_add_const, sliceLength, measureReal_def,
    measure_vadd, measureReal_def]

theorem sliceArea_add_const (n : ℕ) (x : Fin n → ℝ) (c : ℝ) :
    sliceArea n (fun j => x j + c) = sliceArea n x := by
  unfold sliceArea
  apply setIntegral_congr_fun measurableSet_Icc
  intro y hy
  exact sliceLength_add_const n x c y

/-- The common-translation gauge used by the paper's arrangement certificate
does not change the genuine planar union area. -/
theorem unionArea_add_const (n : ℕ) (x : Fin n → ℝ) (c : ℝ) :
    unionArea n (fun j => x j + c) = unionArea n x := by
  rw [unionArea_eq_sliceArea, unionArea_eq_sliceArea, sliceArea_add_const]

end

end KakeyaNeedleC3C4
