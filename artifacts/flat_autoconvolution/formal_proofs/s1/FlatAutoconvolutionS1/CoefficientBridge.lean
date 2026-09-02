import FlatAutoconvolutionS1.FiniteProfile

/-! Identification of the two finite anti-diagonal coefficient conventions. -/

open scoped BigOperators

namespace FlatAutoconvolutionS1
open Finite

/-- Extend a finite profile by zero to all natural indices. -/
def profileGetZero {n : ℕ} (w : Profile n) (i : ℕ) : ℝ :=
  if h : i < n then w ⟨i, h⟩ else 0

/-- Ordered anti-diagonal coefficient written as a sum over `0 ≤ a ≤ t`. -/
def rangeCoeff (x : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (t + 1), x a * x (t - a)

theorem convCoeff_eq_sum_fin_getZero {n : ℕ} (w : Profile n) (t : ℕ) :
    convCoeff w t =
      ∑ a : Fin n, if (a : ℕ) ≤ t then w a * profileGetZero w (t - a) else 0 := by
  classical
  rw [convCoeff, Fintype.sum_prod_type]
  change (∑ a : Fin n, ∑ j : Fin n,
      if (a : ℕ) + (j : ℕ) = t then w a * w j else 0) = _
  apply Finset.sum_congr rfl
  intro a _
  by_cases hat : (a : ℕ) ≤ t
  · rw [if_pos hat]
    by_cases hd : t - (a : ℕ) < n
    · let b : Fin n := ⟨t - (a : ℕ), hd⟩
      rw [Finset.sum_eq_single b]
      · simp [b, profileGetZero, hat, hd]
      · intro j _ hj
        have hne : (a : ℕ) + (j : ℕ) ≠ t := by
          intro heq
          apply hj
          apply Fin.ext
          dsimp [b]
          omega
        simp [hne]
      · simp
    · have hzero : profileGetZero w (t - (a : ℕ)) = 0 := by
        simp [profileGetZero, hd]
      rw [hzero, mul_zero]
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      intro heq
      have : (j : ℕ) = t - (a : ℕ) := by omega
      omega
  · rw [if_neg hat]
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    omega

/-- The range-sum convention used by the Bernoulli rounding proof is exactly
the ordered-pair convention used by `Finite.convCoeff`. -/
theorem rangeCoeff_profileGetZero_eq_convCoeff {n : ℕ} (w : Profile n) (t : ℕ) :
    rangeCoeff (profileGetZero w) t = convCoeff w t := by
  rw [convCoeff_eq_sum_fin_getZero]
  unfold rangeCoeff
  classical
  let F : ℕ → ℝ := fun a ↦ profileGetZero w a * profileGetZero w (t - a)
  calc
    (∑ a ∈ Finset.range (t + 1), F a) =
        ∑ a ∈ Finset.range (min (t + 1) n), F a := by
      symm
      apply Finset.sum_subset (Finset.range_mono (min_le_left _ _))
      intro a hat hamin
      have han : ¬a < n := by
        simp only [Finset.mem_range] at hat hamin
        omega
      simp [F, profileGetZero, han]
    _ = ∑ a ∈ Finset.range (min (t + 1) n),
        if a ≤ t then profileGetZero w a * profileGetZero w (t - a) else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      have hat : a ≤ t := by simp only [Finset.mem_range] at ha; omega
      simp [F, hat]
    _ = ∑ a ∈ Finset.range n,
        if a ≤ t then profileGetZero w a * profileGetZero w (t - a) else 0 := by
      apply Finset.sum_subset (Finset.range_mono (min_le_right _ _))
      intro a han hamin
      have hat : ¬a ≤ t := by
        simp only [Finset.mem_range] at han hamin
        omega
      simp [hat]
    _ = ∑ a : Fin n,
        if (a : ℕ) ≤ t then w a * profileGetZero w (t - a) else 0 := by
      rw [← Fin.sum_univ_eq_sum_range (fun a : ℕ ↦
        if a ≤ t then profileGetZero w a * profileGetZero w (t - a) else 0) n]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hat : (a : ℕ) ≤ t
      · simp only [hat, if_true]
        have ha : profileGetZero w (a : ℕ) = w a := by
          simp [profileGetZero, a.isLt]
        rw [ha]
      · simp only [hat, if_false]

end FlatAutoconvolutionS1
