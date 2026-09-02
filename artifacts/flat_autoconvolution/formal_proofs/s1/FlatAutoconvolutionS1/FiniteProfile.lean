import Mathlib

/-!
# Finite coefficient layer for flat autoconvolution

This module formalizes the finite algebra behind the equal-grid score formula.
The convolution coefficient at `k` is an ordered anti-diagonal sum over all
pairs of input cells whose indices add to `k`.
-/

open scoped BigOperators

namespace FlatAutoconvolutionS1.Finite

/-- A finite real-valued weight profile. -/
abbrev Profile (n : ℕ) := Fin n → ℝ

/-- Pointwise nonnegativity of a finite profile. -/
def Nonnegative {n : ℕ} (w : Profile n) : Prop := ∀ i, 0 ≤ w i

/-- A binary profile has only zero-one weights. -/
def Binary {n : ℕ} (w : Profile n) : Prop := ∀ i, w i = 0 ∨ w i = 1

/-- Total mass of a finite profile. -/
def mass {n : ℕ} (w : Profile n) : ℝ := ∑ i, w i

/-- Ordered anti-diagonal convolution coefficient. -/
def convCoeff {n : ℕ} (w : Profile n) (k : ℕ) : ℝ :=
  ∑ p : Fin n × Fin n,
    if (p.1 : ℕ) + (p.2 : ℕ) = k then w p.1 * w p.2 else 0

/-- A padded range containing the complete coefficient support. -/
def outputRange (n : ℕ) : Finset ℕ := Finset.range (2 * n)

/-- Numerator in the exact equal-grid score formula. -/
def scoreNumerator {n : ℕ} (w : Profile n) : ℝ :=
  2 * (∑ k ∈ outputRange n, convCoeff w k ^ 2) +
    ∑ k ∈ Finset.range (2 * n - 1), convCoeff w k * convCoeff w (k + 1)

/-- Maximum coefficient, expressed as the supremum of a finite image. -/
noncomputable def peak {n : ℕ} (w : Profile n) : ℝ :=
  sSup (convCoeff w '' (outputRange n : Set ℕ))

/-- The exact expression from notebook Lemma 1.1. -/
noncomputable def gridScore {n : ℕ} (w : Profile n) : ℝ :=
  scoreNumerator w / (3 * mass w ^ 2 * peak w)

@[simp] theorem mass_zero (n : ℕ) : mass (fun _ : Fin n ↦ (0 : ℝ)) = 0 := by
  simp [mass]

theorem mass_nonneg {n : ℕ} {w : Profile n} (hw : Nonnegative w) : 0 ≤ mass w := by
  exact Finset.sum_nonneg fun i _ ↦ hw i

theorem Binary.nonnegative {n : ℕ} {w : Profile n} (hw : Binary w) : Nonnegative w := by
  intro i
  rcases hw i with hi | hi <;> simp [hi]

theorem convCoeff_nonneg {n : ℕ} {w : Profile n} (hw : Nonnegative w) (k : ℕ) :
    0 ≤ convCoeff w k := by
  apply Finset.sum_nonneg
  intro p _
  split_ifs
  · exact mul_nonneg (hw p.1) (hw p.2)
  · exact le_rfl

theorem convCoeff_eq_zero_of_ge_two_mul {n : ℕ} (w : Profile n) {k : ℕ}
    (hk : 2 * n ≤ k) : convCoeff w k = 0 := by
  classical
  simp only [convCoeff]
  apply Finset.sum_eq_zero
  intro p _
  rw [if_neg]
  intro hsum
  have hi : (p.1 : ℕ) < n := p.1.isLt
  have hj : (p.2 : ℕ) < n := p.2.isLt
  omega

@[simp] theorem convCoeff_last_eq_zero {n : ℕ} (w : Profile n) :
    convCoeff w (2 * n - 1) = 0 := by
  by_cases hn : n = 0
  · subst n
    simp [convCoeff]
  · classical
    simp only [convCoeff]
    apply Finset.sum_eq_zero
    intro p _
    rw [if_neg]
    intro hsum
    have hi : (p.1 : ℕ) < n := p.1.isLt
    have hj : (p.2 : ℕ) < n := p.2.isLt
    omega

/-- Scaling weights by `a` scales every coefficient by `a²`. -/
theorem convCoeff_smul {n : ℕ} (a : ℝ) (w : Profile n) (k : ℕ) :
    convCoeff (fun i ↦ a * w i) k = a ^ 2 * convCoeff w k := by
  classical
  simp only [convCoeff]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> ring

/-- Total convolution mass equals the square of total input mass. -/
theorem sum_convCoeff_eq_mass_sq {n : ℕ} (w : Profile n) :
    (∑ k ∈ outputRange n, convCoeff w k) = mass w ^ 2 := by
  classical
  have hpair (p : Fin n × Fin n) : (p.1 : ℕ) + (p.2 : ℕ) < 2 * n := by
    have hi : (p.1 : ℕ) < n := p.1.isLt
    have hj : (p.2 : ℕ) < n := p.2.isLt
    omega
  simp only [outputRange, convCoeff]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_range, hpair, if_true]
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  simp [mass, pow_two]

/-- The exact numerator is homogeneous of degree four. -/
theorem scoreNumerator_smul {n : ℕ} (a : ℝ) (w : Profile n) :
    scoreNumerator (fun i ↦ a * w i) = a ^ 4 * scoreNumerator w := by
  classical
  have hsq :
      (∑ k ∈ outputRange n, (a ^ 2 * convCoeff w k) ^ 2) =
        a ^ 4 * ∑ k ∈ outputRange n, convCoeff w k ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hadj :
      (∑ k ∈ Finset.range (2 * n - 1),
          (a ^ 2 * convCoeff w k) * (a ^ 2 * convCoeff w (k + 1))) =
        a ^ 4 * ∑ k ∈ Finset.range (2 * n - 1),
          convCoeff w k * convCoeff w (k + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp only [scoreNumerator, convCoeff_smul]
  rw [hsq, hadj]
  ring

theorem mass_smul {n : ℕ} (a : ℝ) (w : Profile n) :
    mass (fun i ↦ a * w i) = a * mass w := by
  simp [mass, Finset.mul_sum]

theorem peak_smul {n : ℕ} (a : ℝ) (w : Profile n) :
    peak (fun i ↦ a * w i) = a ^ 2 * peak w := by
  unfold peak
  simp only [convCoeff_smul]
  rw [show
    (fun k : ℕ ↦ a ^ 2 * convCoeff w k) '' (outputRange n : Set ℕ) =
      (fun x : ℝ ↦ a ^ 2 * x) ''
        (convCoeff w '' (outputRange n : Set ℕ)) by
      rw [Set.image_image]]
  simpa [smul_eq_mul] using
    Real.sSup_smul_of_nonneg (sq_nonneg a)
      (convCoeff w '' (outputRange n : Set ℕ))

/-- Positive-amplitude normalization does not alter the grid score. -/
theorem gridScore_smul {n : ℕ} {a : ℝ} (ha : a ≠ 0) (w : Profile n) :
    gridScore (fun i ↦ a * w i) = gridScore w := by
  rw [gridScore, scoreNumerator_smul, mass_smul, peak_smul, gridScore]
  have hden :
      3 * (a * mass w) ^ 2 * (a ^ 2 * peak w) =
        a ^ 4 * (3 * mass w ^ 2 * peak w) := by ring
  rw [hden]
  exact mul_div_mul_left _ _ (pow_ne_zero 4 ha)

end FlatAutoconvolutionS1.Finite
