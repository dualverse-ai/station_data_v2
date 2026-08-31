import BookS1.ConferenceSource
import Mathlib.Tactic

/-!
# The four-chamber conference lift

This is the exact block construction in the paper/notebook.  The entries are
integer Seidel signs; `+1` is red and `-1` is blue.
-/

namespace BookS1

open scoped BigOperators Matrix
open Finset

universe u

variable {V : Type u}

private def delta [DecidableEq V] (x y : V) : ℤ := if x = y then 1 else 0

/-- The `4 × 4` bulk block `H` of the conference lift. -/
def bulkSign [DecidableEq V] (C : V → V → ℤ) (x y : Fin 4 × V) : ℤ :=
  let c := C x.2 y.2
  let d := delta x.2 y.2
  ![![c,       d - c,   d + c,  -d - c],
    ![d - c,   -c,      -d - c, -d - c],
    ![d + c,   -d - c,  -c,     -d + c],
    ![-d - c,  -d - c,  -d + c, c      ]] x.1 y.1

private def endpointA (i : Fin 4) : ℤ := ![-1, -1, 1, 1] i
private def endpointB (i : Fin 4) : ℤ := ![-1, 1, -1, 1] i

/-- The complete `(4q+2) × (4q+2)` Seidel sign matrix of the lift. -/
def liftSign [DecidableEq V] (C : V → V → ℤ) :
    LiftVertex V → LiftVertex V → ℤ
  | .inl x, .inl y => bulkSign C x y
  | .inl x, .inr e => if e = 0 then endpointA x.1 else endpointB x.1
  | .inr e, .inl x => if e = 0 then endpointA x.1 else endpointB x.1
  | .inr e, .inr f => if e = f then 0 else -1

theorem bulkSign_symm [DecidableEq V] {C : V → V → ℤ}
    (hC : ∀ x y, C x y = C y x) (x y : Fin 4 × V) :
    bulkSign C x y = bulkSign C y x := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  fin_cases i <;> fin_cases j <;>
    simp [bulkSign, delta, hC, eq_comm]

theorem liftSign_symm [DecidableEq V] {C : V → V → ℤ}
    (hC : ∀ x y, C x y = C y x) (x y : LiftVertex V) :
    liftSign C x y = liftSign C y x := by
  rcases x with x | e <;> rcases y with y | f
  · exact bulkSign_symm hC x y
  · rfl
  · rfl
  · simp [liftSign, eq_comm]

theorem bulkSign_diag [DecidableEq V] {C : V → V → ℤ}
    (hC : ∀ x, C x x = 0) (x : Fin 4 × V) : bulkSign C x x = 0 := by
  rcases x with ⟨i, x⟩
  fin_cases i <;> simp [bulkSign, delta, hC]

theorem liftSign_diag [DecidableEq V] {C : V → V → ℤ}
    (hC : ∀ x, C x x = 0) (x : LiftVertex V) : liftSign C x x = 0 := by
  rcases x with x | e
  · exact bulkSign_diag hC x
  · simp [liftSign]

theorem bulkSign_offdiag [DecidableEq V] {C : V → V → ℤ}
    (hdiag : ∀ x, C x x = 0)
    (hoff : ∀ ⦃x y⦄, x ≠ y → C x y = 1 ∨ C x y = -1)
    {x y : Fin 4 × V} (hxy : x ≠ y) :
    bulkSign C x y = 1 ∨ bulkSign C x y = -1 := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  by_cases hv : x = y
  · subst y
    have hij : i ≠ j := by simpa using hxy
    fin_cases i <;> fin_cases j <;> simp_all [bulkSign, delta]
  · rcases hoff hv with hc | hc
    · fin_cases i <;> fin_cases j <;> simp [bulkSign, delta, hv, hc]
    · fin_cases i <;> fin_cases j <;> simp [bulkSign, delta, hv, hc]

theorem liftSign_offdiag [DecidableEq V] {C : V → V → ℤ}
    (hdiag : ∀ x, C x x = 0)
    (hoff : ∀ ⦃x y⦄, x ≠ y → C x y = 1 ∨ C x y = -1)
    {x y : LiftVertex V} (hxy : x ≠ y) :
    liftSign C x y = 1 ∨ liftSign C x y = -1 := by
  rcases x with x | e <;> rcases y with y | f
  · apply bulkSign_offdiag hdiag hoff
    intro h
    exact hxy (congrArg Sum.inl h)
  · rcases x with ⟨i, x⟩
    fin_cases i <;> fin_cases f <;> simp [liftSign, endpointA, endpointB]
  · rcases y with ⟨i, y⟩
    fin_cases i <;> fin_cases e <;> simp [liftSign, endpointA, endpointB]
  · have hef : e ≠ f := by simpa using hxy
    simp [liftSign, hef]

/-- The red graph of the conference lift. -/
def conferenceLift [DecidableEq V] (C : V → V → ℤ)
    (hsymm : ∀ x y, C x y = C y x) (hdiag : ∀ x, C x x = 0) :
    SimpleGraph (LiftVertex V) where
  Adj x y := liftSign C x y = 1
  symm x y h := by
    change liftSign C y x = 1
    change liftSign C x y = 1 at h
    rw [liftSign_symm hsymm y x]
    exact h
  loopless x := by simp [liftSign_diag hdiag]

@[simp] theorem conferenceLift_adj [DecidableEq V] (C : V → V → ℤ)
    (hsymm : ∀ x y, C x y = C y x) (hdiag : ∀ x, C x x = 0)
    (x y : LiftVertex V) :
    (conferenceLift C hsymm hdiag).Adj x y ↔ liftSign C x y = 1 := Iff.rfl

theorem liftSign_rowSum [Fintype V] [DecidableEq V]
    {C : V → V → ℤ} {q : ℕ} (h : IsConferenceSign C q)
    (x : LiftVertex V) : ∑ y, liftSign C x y = -1 := by
  rcases x with ⟨i, x⟩ | e
  · rw [Fintype.sum_sum_type]
    simp only [Fintype.sum_prod_type]
    fin_cases i <;>
      simp [liftSign, bulkSign, endpointA, endpointB, delta, h.rowSum,
        Fin.sum_univ_four, sum_add_distrib, sum_sub_distrib]
  · fin_cases e
    · rw [Fintype.sum_sum_type]
      simp only [Fintype.sum_prod_type]
      simp [liftSign, endpointA, Fin.sum_univ_four]
    · rw [Fintype.sum_sum_type]
      simp only [Fintype.sum_prod_type]
      simp [liftSign, endpointB, Fin.sum_univ_four]

private theorem sum_delta [Fintype V] [DecidableEq V] (x : V) :
    ∑ z, delta x z = 1 := by simp [delta]

private theorem sum_delta_mul [Fintype V] [DecidableEq V]
    (C : V → V → ℤ) (x y : V) :
    ∑ z, delta x z * C z y = C x y := by simp [delta]

private theorem sum_mul_delta [Fintype V] [DecidableEq V]
    (C : V → V → ℤ) (x y : V) :
    ∑ z, C x z * delta z y = C x y := by simp [delta]

private theorem sum_delta_mul_delta [Fintype V] [DecidableEq V] (x y : V) :
    ∑ z, delta x z * delta z y = delta x y := by
  by_cases hxy : x = y <;> simp [delta, hxy]

private def bulkDeltaCoeff : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![0, 1, 1, -1], ![1, 0, -1, -1],
    ![1, -1, 0, -1], ![-1, -1, -1, 0]]

private def bulkCcoeff : Matrix (Fin 4) (Fin 4) ℤ :=
  ![![1, -1, 1, -1], ![-1, -1, -1, -1],
    ![1, -1, -1, 1], ![-1, -1, 1, 1]]

private theorem bulkSign_eq_coeff [DecidableEq V] (C : V → V → ℤ)
    (i j : Fin 4) (x y : V) :
    bulkSign C (i, x) (j, y) =
      bulkDeltaCoeff i j * delta x y + bulkCcoeff i j * C x y := by
  fin_cases i <;> fin_cases j <;>
    simp [bulkSign, bulkDeltaCoeff, bulkCcoeff] <;> ring

private theorem mulSum_eq_delta [Fintype V] [DecidableEq V]
    {C : V → V → ℤ} {q : ℕ} (h : IsConferenceSign C q) (x y : V) :
    ∑ z, C x z * C z y = (q : ℤ) * delta x y - 1 := by
  rw [h.mulSum]
  by_cases hxy : x = y <;> simp [delta, hxy]

private theorem sum_linear_mul_linear [Fintype V] [DecidableEq V]
    {C : V → V → ℤ} {q : ℕ} (h : IsConferenceSign C q)
    (a b c d : ℤ) (x y : V) :
    ∑ z, (a * delta x z + b * C x z) * (c * delta z y + d * C z y) =
      a * c * delta x y + (a * d + b * c) * C x y +
        b * d * ((q : ℤ) * delta x y - 1) := by
  calc
    _ = a * c * (∑ z, delta x z * delta z y) +
          a * d * (∑ z, delta x z * C z y) +
          b * c * (∑ z, C x z * delta z y) +
          b * d * (∑ z, C x z * C z y) := by
        simp only [mul_sum, ← sum_add_distrib]
        apply sum_congr rfl
        intro z hz
        ring
    _ = _ := by
      rw [sum_delta_mul_delta, sum_delta_mul, sum_mul_delta, mulSum_eq_delta h]
      ring

/-- Exact block-square calculation for two chamber vertices.  This is equation
(2) of the verification notebook, restricted to its `4 × 4` bulk. -/
theorem liftSign_mulSum_inl [Fintype V] [DecidableEq V]
    {C : V → V → ℤ} {q : ℕ} (h : IsConferenceSign C q)
    (i j : Fin 4) (x y : V) :
    ∑ z, liftSign C (.inl (i, x)) z * liftSign C z (.inl (j, y)) =
      ![![(4 * (q : ℤ) + 3) * delta x y - 2 + 2 * C x y, 0, 0,
            -2 * (delta x y + 1 + C x y)],
        ![0, (4 * (q : ℤ) + 3) * delta x y - 2 + 2 * C x y,
            2 * (delta x y - 1 + C x y), 0],
        ![0, 2 * (delta x y - 1 + C x y),
            (4 * (q : ℤ) + 3) * delta x y - 2 + 2 * C x y, 0],
        ![-2 * (delta x y + 1 + C x y), 0, 0,
            (4 * (q : ℤ) + 3) * delta x y - 2 + 2 * C x y]] i j := by
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type]
  simp only [liftSign]
  simp_rw [bulkSign_eq_coeff]
  rw [Fin.sum_univ_four]
  simp_rw [sum_linear_mul_linear h]
  fin_cases i <;> fin_cases j <;>
    simp [endpointA, endpointB, bulkDeltaCoeff, bulkCcoeff,
      Fin.sum_univ_two] <;> ring

private theorem sum_linear [Fintype V] [DecidableEq V]
    {C : V → V → ℤ} {q : ℕ} (h : IsConferenceSign C q)
    (a b : ℤ) (x : V) : ∑ z, (a * delta x z + b * C x z) = a := by
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, sum_delta, h.rowSum]
  ring

theorem liftSign_mulSum_inl_inr [Fintype V] [DecidableEq V]
    {C : V → V → ℤ} {q : ℕ} (h : IsConferenceSign C q)
    (i : Fin 4) (x : V) (e : Fin 2) :
    ∑ z, liftSign C (.inl (i, x)) z * liftSign C z (.inr e) =
      if e = 0 then ![0, -4, 0, 0] i else ![0, 0, -4, 0] i := by
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, liftSign]
  simp_rw [bulkSign_eq_coeff]
  rw [Fin.sum_univ_four]
  simp_rw [← Finset.sum_mul]
  simp_rw [sum_linear h]
  fin_cases i <;> fin_cases e <;>
    simp [endpointA, endpointB, bulkDeltaCoeff, Fin.sum_univ_two]

theorem liftSign_mulSum_inr_inl [Fintype V] [DecidableEq V]
    {C : V → V → ℤ} {q : ℕ} (h : IsConferenceSign C q)
    (e : Fin 2) (i : Fin 4) (x : V) :
    ∑ z, liftSign C (.inr e) z * liftSign C z (.inl (i, x)) =
      if e = 0 then ![0, -4, 0, 0] i else ![0, 0, -4, 0] i := by
  simpa only [liftSign_symm h.symm, mul_comm] using liftSign_mulSum_inl_inr h i x e

theorem liftSign_mulSum_inr [Fintype V] [DecidableEq V]
    {C : V → V → ℤ} {q : ℕ} (h : IsConferenceSign C q)
    (e f : Fin 2) :
    ∑ z, liftSign C (.inr e) z * liftSign C z (.inr f) =
      if e = f then 4 * (q : ℤ) + 1 else 0 := by
  rw [Fintype.sum_sum_type]
  simp only [Fintype.sum_prod_type, liftSign]
  fin_cases e <;> fin_cases f <;>
    simp [endpointA, endpointB, Fin.sum_univ_four, Fin.sum_univ_two, h.card] <;> ring

/-- Every off-diagonal entry of the square of the lifted Seidel matrix is
nonpositive (in fact it is either `0` or `-4`). -/
theorem liftSign_mulSum_nonpos [Fintype V] [DecidableEq V]
    {C : V → V → ℤ} {q : ℕ} (h : IsConferenceSign C q)
    {x y : LiftVertex V} (hxy : x ≠ y) :
    ∑ z, liftSign C x z * liftSign C z y ≤ 0 := by
  rcases x with ⟨i, x⟩ | e <;> rcases y with ⟨j, y⟩ | f
  · rw [liftSign_mulSum_inl h]
    by_cases hv : x = y
    · subst y
      have hij : i ≠ j := by
        intro hij
        subst j
        exact hxy rfl
      fin_cases i <;> fin_cases j <;>
        simp_all [delta, h.diag]
    · rcases h.offdiag hv with hc | hc
      · fin_cases i <;> fin_cases j <;> simp [delta, hv, hc]
      · fin_cases i <;> fin_cases j <;> simp [delta, hv, hc]
  · rw [liftSign_mulSum_inl_inr h]
    fin_cases i <;> fin_cases f <;> simp
  · rw [liftSign_mulSum_inr_inl h]
    fin_cases j <;> fin_cases e <;> simp
  · have hef : e ≠ f := by
      intro hef
      subst f
      exact hxy rfl
    rw [liftSign_mulSum_inr h]
    simp [hef]

end BookS1
