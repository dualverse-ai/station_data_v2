import FiniteKakeyaInf.Definitions

namespace FiniteKakeyaInf

open Finset

theorem onePoleKakeya_isKakeya
    (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    IsKakeya (onePoleKakeya F) := by
  intro v hv
  classical
  by_cases hx : v.1 = 0
  · by_cases hy : v.2.1 = 0
    · have hz : v.2.2 ≠ 0 := by
        intro hz
        apply hv
        ext <;> simp [hx, hy, hz]
      refine ⟨0, ?_⟩
      intro q hq
      simp only [affineLine, mem_image, mem_univ, true_and] at hq
      rcases hq with ⟨t, rfl⟩
      apply mem_union_right
      apply mem_union_right
      simp [verticalBoundary, hx, hy]
    · let c : F := v.2.2 / v.2.1
      by_cases hc : c = 1
      · refine ⟨0, ?_⟩
        intro q hq
        simp only [affineLine, mem_image, mem_univ, true_and] at hq
        rcases hq with ⟨t, rfl⟩
        apply mem_union_right
        apply mem_union_left
        apply mem_union_right
        simp only [diagonalBoundary, mem_filter, mem_univ, true_and]
        constructor
        · simp [hx]
        · simp only [Prod.smul_fst, Prod.smul_snd, zero_add, smul_eq_mul]
          have hcv : v.2.2 = v.2.1 := by
            calc
              v.2.2 = c * v.2.1 := (div_mul_cancel₀ v.2.2 hy).symm
              _ = 1 * v.2.1 := by rw [hc]
              _ = v.2.1 := one_mul _
          rw [hcv]
      · let w : Point F := (0, 0, c / (c - 1))
        refine ⟨w, ?_⟩
        intro q hq
        simp only [affineLine, mem_image, mem_univ, true_and] at hq
        rcases hq with ⟨t, rfl⟩
        apply mem_union_right
        apply mem_union_left
        apply mem_union_left
        simp only [finiteBoundary, mem_filter, mem_univ, true_and]
        refine ⟨?_, c, hc, ?_⟩
        · simp [w, hx]
        · dsimp [w]
          change c / (c - 1) + t * v.2.2 = c * (0 + t * v.2.1) + c / (c - 1)
          have hcv : c * v.2.1 = v.2.2 := div_mul_cancel₀ v.2.2 hy
          rw [← hcv]
          ring
  · let a : F := v.2.1 / v.1
    let b : F := v.2.2 / v.1
    let w : Point F := (0, a ^ 2, b ^ 2)
    refine ⟨w, ?_⟩
    intro q hq
    simp only [affineLine, mem_image, mem_univ, true_and] at hq
    rcases hq with ⟨t, rfl⟩
    apply mem_union_left
    simp only [body, mem_filter, mem_univ, true_and]
    constructor
    · apply mem_image.mpr
      refine ⟨t * v.1 + 2 * a, mem_univ _, ?_⟩
      have hav : a * v.1 = v.2.1 := div_mul_cancel₀ v.2.1 hx
      dsimp [w]
      change (t * v.1 + 2 * a) ^ 2 = (0 + t * v.1) ^ 2 + 4 * (a ^ 2 + t * v.2.1)
      rw [← hav]
      ring
    · apply mem_image.mpr
      refine ⟨t * v.1 + 2 * b, mem_univ _, ?_⟩
      have hbv : b * v.1 = v.2.2 := div_mul_cancel₀ v.2.2 hx
      dsimp [w]
      change (t * v.1 + 2 * b) ^ 2 = (0 + t * v.1) ^ 2 + 4 * (b ^ 2 + t * v.2.2)
      rw [← hbv]
      ring

end FiniteKakeyaInf
