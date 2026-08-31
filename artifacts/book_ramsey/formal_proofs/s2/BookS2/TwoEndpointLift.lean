import BookS2.PeriodicSource
import Mathlib

/-!
# The abstract two-endpoint lift

This file formalizes the matrix construction in Theorem 3.2 of the paper.  It
uses only the axioms of a `PeriodicLegendreSource`; the finite-field source is
supplied separately.
-/

namespace BookS2

open scoped BigOperators
open Matrix

abbrev SourceVertex (K : Type*) := Fin 2 × K
abbrev BulkVertex (K : Type*) := Fin 2 × SourceVertex K
abbrev LiftVertex (K : Type*) := Sum (BulkVertex K) (Fin 2)

section

variable {K : Type*} [Fintype K] [CommGroup K] [DecidableEq K]

private lemma sign_sq {z : ℤ} (h : z = 1 ∨ z = -1) : z * z = 1 := by
  rcases h with rfl | rfl <;> norm_num

/-- The grading matrix `R` is diagonal with this grading vector. -/
def grade (p : SourceVertex K) : ℤ := if p.1 = 0 then 1 else -1

@[simp] lemma grade_zero (s : K) : grade (0, s) = 1 := by simp [grade]
@[simp] lemma grade_one (s : K) : grade (1, s) = -1 := by simp [grade]

private lemma grade_sign (p : SourceVertex K) : grade p = 1 ∨ grade p = -1 := by
  by_cases h : p.1 = 0 <;> simp [grade, h]

/-- A group-developed matrix. -/
def developed (f : K → ℤ) (s t : K) : ℤ := f (t * s⁻¹)

variable (src : PeriodicLegendreSource K)

def sourceA (s t : K) : ℤ :=
  developed src.x s t - if s = t then 1 else 0

def sourceB (s t : K) : ℤ := developed src.y s t

/-- The `2q × 2q` signed source matrix `T`. -/
def sourceT (p q : SourceVertex K) : ℤ :=
  if p.1 = 0 then
    if q.1 = 0 then sourceA src p.2 q.2 else sourceB src p.2 q.2
  else
    if q.1 = 0 then sourceB src q.2 p.2 else -sourceA src p.2 q.2

private def sourceTMatrix : Matrix (SourceVertex K) (SourceVertex K) ℤ :=
  Matrix.of (sourceT src)

/-- The `4q × 4q` bulk matrix `M`. -/
def bulkM (p q : BulkVertex K) : ℤ :=
  if p.1 = q.1 then
    if p.1 = 0 then sourceT src p.2 q.2 else -sourceT src p.2 q.2
  else
    sourceT src p.2 q.2 + if p.2 = q.2 then grade p.2 else 0

/-- The complete two-endpoint Seidel matrix. -/
def twoEndpointSeidel : Matrix (LiftVertex K) (LiftVertex K) ℤ
  | .inl p, .inl q => bulkM src p q
  | .inl p, .inr e => if e = 0 then -grade p.2 else if p.1 = 0 then 1 else -1
  | .inr e, .inl p => if e = 0 then -grade p.2 else if p.1 = 0 then 1 else -1
  | .inr e, .inr f => if e = f then 0 else -1

private lemma developed_sum (f : K → ℤ) (s : K) :
    ∑ t, developed f s t = ∑ t, f t := by
  simpa [developed] using (Equiv.sum_comp (Equiv.mulRight s⁻¹) f)

private lemma sourceA_sum (s : K) : ∑ t, sourceA src s t = 0 := by
  classical
  simp only [sourceA, Finset.sum_sub_distrib, developed_sum]
  rw [src.sum_x]
  simp

private lemma sourceB_sum (s : K) : ∑ t, sourceB src s t = -1 := by
  simp only [sourceB, developed_sum, src.sum_y]

private lemma sourceB_col_sum (t : K) : ∑ s, sourceB src s t = -1 := by
  classical
  let e : K ≃ K := Equiv.inv K |>.trans (Equiv.mulRight t)
  calc
    ∑ s, sourceB src s t = ∑ s, sourceB src (e s) t :=
      (Equiv.sum_comp e (fun s => sourceB src s t)).symm
    _ = ∑ s, src.y s := by
      apply Finset.sum_congr rfl
      intro s _
      simp [sourceB, developed, e, mul_comm]
    _ = -1 := src.sum_y

private lemma sourceA_symm (s t : K) : sourceA src s t = sourceA src t s := by
  classical
  simp only [sourceA, developed]
  rw [← src.x_inv (t * s⁻¹)]
  simp [mul_comm, eq_comm]

private lemma sourceT_symm (p q : SourceVertex K) : sourceT src p q = sourceT src q p := by
  rcases p with ⟨i, s⟩
  rcases q with ⟨j, t⟩
  fin_cases i <;> fin_cases j <;> simp [sourceT, sourceA_symm src]

private lemma sourceT_diag (p : SourceVertex K) : sourceT src p p = 0 := by
  rcases p with ⟨i, s⟩
  fin_cases i <;> simp [sourceT, sourceA, developed, src.x_one]

private lemma sourceA_sign {s t : K} (h : s ≠ t) :
    sourceA src s t = 1 ∨ sourceA src s t = -1 := by
  simpa [sourceA, h] using src.x_sign (t * s⁻¹)

private lemma sourceT_sign {p q : SourceVertex K} (h : p ≠ q) :
    sourceT src p q = 1 ∨ sourceT src p q = -1 := by
  rcases p with ⟨i, s⟩
  rcases q with ⟨j, t⟩
  fin_cases i <;> fin_cases j
  · exact sourceA_sign src (by simpa using h)
  · simpa [sourceT, sourceB] using src.y_sign (t * s⁻¹)
  · simpa [sourceT, sourceB] using src.y_sign (s * t⁻¹)
  · rcases sourceA_sign src (by simpa using h) with hA | hA
    · right; simp [sourceT, hA]
    · left; simp [sourceT, hA]

private lemma sourceT_row_sum (p : SourceVertex K) : ∑ q, sourceT src p q = -1 := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  rcases p with ⟨i, s⟩
  fin_cases i
  · simp only [sourceT, Fin.zero_eta, Fin.isValue, ↓reduceIte]
    simp only [one_ne_zero, if_false]
    rw [sourceA_sum, sourceB_sum]
    norm_num
  · simp only [sourceT, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    rw [sourceB_col_sum]
    simp only [Finset.sum_neg_distrib, sourceA_sum]
    norm_num

private lemma x_reverse (s t : K) : src.x (t * s⁻¹) = src.x (s * t⁻¹) := by
  rw [← src.x_inv (t * s⁻¹)]
  simp [mul_comm]

private lemma shifted_correlation (s t : K) :
    ∑ u, (src.x (u * s⁻¹) * src.x (u * t⁻¹) +
      src.y (u * s⁻¹) * src.y (u * t⁻¹)) =
      if s = t then 2 * (Fintype.card K : ℤ) else -2 := by
  classical
  by_cases hst : s = t
  · subst t
    simp only [if_pos rfl]
    calc
      ∑ u, (src.x (u * s⁻¹) * src.x (u * s⁻¹) +
          src.y (u * s⁻¹) * src.y (u * s⁻¹)) = ∑ _u : K, (2 : ℤ) := by
            apply Finset.sum_congr rfl
            intro u _
            rw [sign_sq (src.x_sign _), sign_sq (src.y_sign _)]
            norm_num
      _ = 2 * (Fintype.card K : ℤ) := by simp [mul_comm]
  · rw [if_neg hst]
    have hδ : t * s⁻¹ ≠ 1 := by
      intro h
      have : t = s := by
        calc t = (t * s⁻¹) * s := by simp
             _ = s := by rw [h]; simp
      exact hst this.symm
    let e : K ≃ K := Equiv.mulRight t
    calc
      ∑ u, (src.x (u * s⁻¹) * src.x (u * t⁻¹) +
          src.y (u * s⁻¹) * src.y (u * t⁻¹)) =
          ∑ z, (src.x ((e z) * s⁻¹) * src.x ((e z) * t⁻¹) +
            src.y ((e z) * s⁻¹) * src.y ((e z) * t⁻¹)) :=
              (Equiv.sum_comp e _).symm
      _ = ∑ z, (src.x z * src.x ((t * s⁻¹) * z) +
          src.y z * src.y ((t * s⁻¹) * z)) := by
            apply Finset.sum_congr rfl
            intro z _
            simp [e, mul_assoc, mul_comm, mul_left_comm]
      _ = -2 := src.correlation (t * s⁻¹) hδ

private lemma source_block_product (s t : K) :
    ∑ u, (sourceA src s u * sourceA src u t +
      sourceB src s u * sourceB src t u) =
      (if s = t then 2 * (Fintype.card K : ℤ) else -2) -
        2 * developed src.x s t + (if s = t then 1 else 0) := by
  classical
  have hx (u : K) : src.x (t * u⁻¹) = src.x (u * t⁻¹) := x_reverse src u t
  simp only [sourceA, sourceB, developed]
  calc
    ∑ u, ((src.x (u * s⁻¹) - if s = u then 1 else 0) *
          (src.x (t * u⁻¹) - if u = t then 1 else 0) +
          src.y (u * s⁻¹) * src.y (u * t⁻¹)) =
        ∑ u, ((src.x (u * s⁻¹) * src.x (u * t⁻¹) +
          src.y (u * s⁻¹) * src.y (u * t⁻¹)) -
          (if u = t then src.x (u * s⁻¹) else 0) -
          (if s = u then src.x (u * t⁻¹) else 0) +
          (if s = u ∧ u = t then (1 : ℤ) else 0)) := by
            apply Finset.sum_congr rfl
            intro u _
            rw [hx]
            by_cases hsu : s = u <;> by_cases hut : u = t <;>
              simp_all [src.x_one] <;> ring
    _ = (∑ u, (src.x (u * s⁻¹) * src.x (u * t⁻¹) +
          src.y (u * s⁻¹) * src.y (u * t⁻¹))) -
          src.x (t * s⁻¹) - src.x (s * t⁻¹) + (if s = t then 1 else 0) := by
            have h₁ : (∑ u, if u = t then src.x (u * s⁻¹) else 0) =
                src.x (t * s⁻¹) := by simp
            have h₂ : (∑ u, if s = u then src.x (u * t⁻¹) else 0) =
                src.x (s * t⁻¹) := by simp
            have h₃ : (∑ u : K, if s = u ∧ u = t then (1 : ℤ) else 0) =
                if s = t then 1 else 0 := by
              calc
                (∑ u : K, if s = u ∧ u = t then (1 : ℤ) else 0) =
                    (if s = s ∧ s = t then (1 : ℤ) else 0) := by
                      apply Finset.sum_eq_single s
                      · intro u _ hus
                        simp [Ne.symm hus]
                      · simp
                _ = if s = t then 1 else 0 := by simp
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            rw [h₁, h₂, h₃]
    _ = (if s = t then 2 * (Fintype.card K : ℤ) else -2) -
          2 * src.x (t * s⁻¹) + (if s = t then 1 else 0) := by
            rw [shifted_correlation src, ← x_reverse src s t]
            ring

private lemma developed_comm (f g : K → ℤ) (s t : K) :
    ∑ u, developed f s u * developed g u t =
      ∑ u, developed g s u * developed f u t := by
  let d := t * s⁻¹
  let e : K ≃ K := (Equiv.inv K).trans (Equiv.mulLeft d)
  have hfg : (∑ u, developed f s u * developed g u t) =
      ∑ z, f z * g (d * z⁻¹) := by
    calc
      ∑ u, developed f s u * developed g u t =
          ∑ z, developed f s ((Equiv.mulRight s) z) *
            developed g ((Equiv.mulRight s) z) t :=
              (Equiv.sum_comp (Equiv.mulRight s) _).symm
      _ = ∑ z, f z * g (d * z⁻¹) := by
        apply Finset.sum_congr rfl
        intro z _
        simp [developed, d, mul_assoc, mul_comm, mul_left_comm]
  have hgf : (∑ u, developed g s u * developed f u t) =
      ∑ z, g z * f (d * z⁻¹) := by
    calc
      ∑ u, developed g s u * developed f u t =
          ∑ z, developed g s ((Equiv.mulRight s) z) *
            developed f ((Equiv.mulRight s) z) t :=
              (Equiv.sum_comp (Equiv.mulRight s) _).symm
      _ = ∑ z, g z * f (d * z⁻¹) := by
        apply Finset.sum_congr rfl
        intro z _
        simp [developed, d, mul_assoc, mul_comm, mul_left_comm]
  rw [hfg, hgf]
  calc
    ∑ z, f z * g (d * z⁻¹) = ∑ z, f (e z) * g (d * (e z)⁻¹) :=
      (Equiv.sum_comp e _).symm
    _ = ∑ z, g z * f (d * z⁻¹) := by
      apply Finset.sum_congr rfl
      intro z _
      simp [d, e, mul_assoc, mul_comm, mul_left_comm]

private lemma developed_transpose_product (f : K → ℤ) (s t : K) :
    ∑ u, developed f u s * developed f u t =
      ∑ u, developed f s u * developed f t u := by
  let fi : K → ℤ := fun z ↦ f z⁻¹
  calc
    ∑ u, developed f u s * developed f u t =
        ∑ u, developed fi s u * developed f u t := by
          apply Finset.sum_congr rfl
          intro u _
          simp [developed, fi, mul_comm]
    _ = ∑ u, developed f s u * developed fi u t := developed_comm fi f s t
    _ = ∑ u, developed f s u * developed f t u := by
          apply Finset.sum_congr rfl
          intro u _
          simp [developed, fi, mul_comm]

private lemma source_block_product_rev (s t : K) :
    ∑ u, (sourceB src u s * sourceB src u t +
      sourceA src s u * sourceA src u t) =
      (if s = t then 2 * (Fintype.card K : ℤ) else -2) -
        2 * developed src.x s t + (if s = t then 1 else 0) := by
  simp only [sourceB]
  rw [Finset.sum_add_distrib, developed_transpose_product src.y s t]
  rw [← Finset.sum_add_distrib]
  simpa [sourceB, add_comm] using source_block_product src s t

private lemma source_cross_zero (s t : K) :
    ∑ u, (sourceA src s u * sourceB src u t -
      sourceB src s u * sourceA src u t) = 0 := by
  classical
  have h₁ : (∑ u : K, (if s = u then 1 else 0) * sourceB src u t) =
      sourceB src s t := by simp
  have h₂ : (∑ u : K, sourceB src s u * (if u = t then 1 else 0)) =
      sourceB src s t := by simp
  simp only [sourceA]
  calc
    ∑ u, ((developed src.x s u - if s = u then 1 else 0) * sourceB src u t -
      sourceB src s u * (developed src.x u t - if u = t then 1 else 0)) =
      (∑ u, developed src.x s u * developed src.y u t) - sourceB src s t -
        ((∑ u, developed src.y s u * developed src.x u t) - sourceB src s t) := by
          simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
          rw [h₁, h₂]
          simp only [sourceB]
    _ = 0 := by rw [developed_comm]; ring

/-- The exact square of the source matrix.  Its off-diagonal source-block
entries vanish, and its diagonal source blocks are controlled by `x`. -/
private lemma sourceT_square (p q : SourceVertex K) :
    (sourceTMatrix src * sourceTMatrix src) p q =
      if p.1 = q.1 then
        (if p.2 = q.2 then 2 * (Fintype.card K : ℤ) - 1
          else -2 - 2 * developed src.x p.2 q.2)
      else 0 := by
  classical
  rcases p with ⟨i, s⟩
  rcases q with ⟨j, t⟩
  rw [Matrix.mul_apply]
  change (∑ r : SourceVertex K, sourceT src (i, s) r * sourceT src r (j, t)) = _
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j
  · simp only [sourceT, Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.mk_one, one_ne_zero]
    rw [← Finset.sum_add_distrib, source_block_product]
    by_cases hst : s = t
    · subst t
      simp [sourceT, sourceA, developed, src.x_one]
      ring
    · simp [sourceT, hst]
  · simp only [sourceT, Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.mk_one, one_ne_zero,
      Fin.zero_ne_one, if_false]
    calc
      (∑ x, sourceA src s x * sourceB src x t) +
          ∑ x, sourceB src s x * -sourceA src x t =
          ∑ x, (sourceA src s x * sourceB src x t -
            sourceB src s x * sourceA src x t) := by
              rw [Finset.sum_sub_distrib]
              simp only [mul_neg, Finset.sum_neg_distrib]
              abel
      _ = 0 := source_cross_zero src s t
  · simp only [sourceT, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, Fin.zero_eta,
      if_false]
    calc
      (∑ x, sourceB src x s * sourceA src x t) +
          ∑ x, -sourceA src s x * sourceB src t x =
          ∑ x, (sourceA src t x * sourceB src x s -
            sourceB src t x * sourceA src x s) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro x _
              rw [sourceA_symm src x t, sourceA_symm src s x]
              ring
      _ = 0 := source_cross_zero src t s
  · simp only [sourceT, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, Fin.zero_eta,
      neg_mul, mul_neg, neg_neg]
    rw [← Finset.sum_add_distrib, source_block_product_rev]
    by_cases hst : s = t
    · subst t
      simp [sourceT, sourceA, developed, src.x_one]
      ring
    · simp [sourceT, hst]

private lemma sourceT_product (p q : SourceVertex K) :
    ∑ r, sourceT src p r * sourceT src r q =
      if p.1 = q.1 then
        (if p.2 = q.2 then 2 * (Fintype.card K : ℤ) - 1
          else -2 - 2 * developed src.x p.2 q.2)
      else 0 := by
  simpa [sourceTMatrix, Matrix.mul_apply] using sourceT_square src p q

private lemma sourceT_grade_right (p q : SourceVertex K) :
    ∑ r, sourceT src p r * (if r = q then grade r else 0) =
      sourceT src p q * grade q := by
  classical
  simp

private lemma sourceT_grade_left (p q : SourceVertex K) :
    ∑ r, (if p = r then grade p else 0) * sourceT src r q =
      grade p * sourceT src p q := by
  classical
  simp

private lemma grade_product (p q : SourceVertex K) :
    ∑ r, (if p = r then grade p else 0) *
        (if r = q then grade r else 0) =
      if p = q then 1 else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    simp [sign_sq (grade_sign p)]
  · simp [hpq]

private lemma grade_sum : ∑ p : SourceVertex K, grade p = 0 := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp

private lemma bulkM_symm (p q : BulkVertex K) : bulkM src p q = bulkM src q p := by
  classical
  rcases p with ⟨i, p⟩
  rcases q with ⟨j, q⟩
  fin_cases i <;> fin_cases j
  · simp [bulkM, sourceT_symm src]
  · by_cases hpq : p = q
    · simp [bulkM, hpq, sourceT_symm src]
    · have hqp : q ≠ p := Ne.symm hpq
      simp [bulkM, hpq, hqp, sourceT_symm src]
  · by_cases hpq : p = q
    · simp [bulkM, hpq, sourceT_symm src]
    · have hqp : q ≠ p := Ne.symm hpq
      simp [bulkM, hpq, hqp, sourceT_symm src]
  · simp [bulkM, sourceT_symm src]

private lemma bulkM_diag (p : BulkVertex K) : bulkM src p p = 0 := by
  simp [bulkM, sourceT_diag]

private lemma bulkM_sign {p q : BulkVertex K} (h : p ≠ q) :
    bulkM src p q = 1 ∨ bulkM src p q = -1 := by
  classical
  rcases p with ⟨i, p⟩
  rcases q with ⟨j, q⟩
  fin_cases i <;> fin_cases j
  · have hpq : p ≠ q := by simpa using h
    simpa [bulkM] using sourceT_sign src hpq
  · by_cases hpq : p = q
    · subst q
      rw [bulkM]
      simpa [sourceT_diag] using grade_sign p
    · simpa [bulkM, hpq] using sourceT_sign src hpq
  · by_cases hpq : p = q
    · subst q
      rw [bulkM]
      simpa [sourceT_diag] using grade_sign p
    · simpa [bulkM, hpq] using sourceT_sign src hpq
  · have hpq : p ≠ q := by simpa using h
    rcases sourceT_sign src hpq with hT | hT
    · right; simp [bulkM, hT]
    · left; simp [bulkM, hT]

private lemma bulkM_row_sum (p : BulkVertex K) : ∑ q, bulkM src p q =
    if p.1 = 0 then -2 + grade p.2 else grade p.2 := by
  classical
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  rcases p with ⟨i, p⟩
  fin_cases i
  · simp only [bulkM, Fin.zero_eta, Fin.isValue, ↓reduceIte, zero_ne_one]
    simp [Finset.sum_add_distrib, sourceT_row_sum]
    ring
  · simp only [bulkM, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, ne_eq]
    simp [Finset.sum_add_distrib, sourceT_row_sum]

private lemma bulk_endpoint_sum (p : BulkVertex K) :
    ∑ e : Fin 2, twoEndpointSeidel src (.inl p) (.inr e) =
      if p.1 = 0 then -grade p.2 + 1 else -grade p.2 - 1 := by
  rw [Fin.sum_univ_two]
  rcases p with ⟨i, p⟩
  fin_cases i <;> simp [twoEndpointSeidel] <;> ring

private lemma endpoint_product (p q : BulkVertex K) :
    ∑ e : Fin 2, twoEndpointSeidel src (.inl p) (.inr e) *
        twoEndpointSeidel src (.inr e) (.inl q) =
      grade p.2 * grade q.2 + if p.1 = q.1 then 1 else -1 := by
  rw [Fin.sum_univ_two]
  rcases p with ⟨i, p⟩
  rcases q with ⟨j, q⟩
  fin_cases i <;> fin_cases j <;> simp [twoEndpointSeidel] <;> ring

private lemma bulk_product (p q : BulkVertex K) :
    ∑ r, bulkM src p r * bulkM src r q =
      if p.1 = q.1 then
        2 * (∑ r, sourceT src p.2 r * sourceT src r q.2) +
          sourceT src p.2 q.2 * (grade p.2 + grade q.2) +
          (if p.2 = q.2 then 1 else 0)
      else if p.1 = 0 then
        sourceT src p.2 q.2 * (grade q.2 - grade p.2)
      else
        sourceT src p.2 q.2 * (grade p.2 - grade q.2) := by
  classical
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  rcases p with ⟨i, p⟩
  rcases q with ⟨j, q⟩
  fin_cases i <;> fin_cases j <;>
    simp only [bulkM, Fin.zero_eta, Fin.mk_one, Fin.isValue, zero_ne_one,
      one_ne_zero, ↓reduceIte, add_mul, mul_add, neg_mul, mul_neg,
      neg_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib] <;>
    simp only [sourceT_product, sourceT_grade_right, sourceT_grade_left,
      grade_product] <;>
    ring

/-- The two-endpoint matrix is symmetric. -/
theorem twoEndpointSeidel_symm : (twoEndpointSeidel src).IsSymm := by
  apply Matrix.IsSymm.ext
  intro p q
  rcases p with p | e <;> rcases q with q | f
  · exact bulkM_symm src q p
  · rfl
  · rfl
  · simp [twoEndpointSeidel, eq_comm]

/-- The two-endpoint matrix has zero diagonal. -/
theorem twoEndpointSeidel_diag (p : LiftVertex K) : twoEndpointSeidel src p p = 0 := by
  rcases p with p | e
  · exact bulkM_diag src p
  · simp [twoEndpointSeidel]

/-- Every off-diagonal entry is a sign. -/
theorem twoEndpointSeidel_sign {p q : LiftVertex K} (h : p ≠ q) :
    twoEndpointSeidel src p q = 1 ∨ twoEndpointSeidel src p q = -1 := by
  rcases p with p | e <;> rcases q with q | f
  · exact bulkM_sign src (by simpa using h)
  · rcases p with ⟨i, ⟨j, s⟩⟩
    fin_cases f <;> fin_cases i <;> fin_cases j <;> simp [twoEndpointSeidel, grade]
  · rcases q with ⟨i, ⟨j, s⟩⟩
    fin_cases e <;> fin_cases i <;> fin_cases j <;> simp [twoEndpointSeidel, grade]
  · have hef : e ≠ f := by simpa using h
    right
    simp [twoEndpointSeidel, hef]

/-- Every row sum of the two-endpoint matrix is `-1`. -/
theorem twoEndpointSeidel_row_sum (p : LiftVertex K) :
    ∑ q, twoEndpointSeidel src p q = -1 := by
  rw [Fintype.sum_sum_type]
  rcases p with p | e
  · change (∑ q, bulkM src p q) +
        ∑ e, twoEndpointSeidel src (.inl p) (.inr e) = -1
    rw [bulkM_row_sum, bulk_endpoint_sum]
    split_ifs <;> ring
  · fin_cases e
    · rw [Fintype.sum_prod_type, Fin.sum_univ_two]
      simp only [twoEndpointSeidel, Fin.zero_eta, Fin.isValue, ↓reduceIte,
        Finset.sum_neg_distrib]
      rw [grade_sum]
      simp
    · rw [Fintype.sum_prod_type, Fin.sum_univ_two]
      simp [twoEndpointSeidel]

set_option maxHeartbeats 800000 in
private lemma square_bulk_nonpos {p q : BulkVertex K} (hpq : p ≠ q) :
    (twoEndpointSeidel src * twoEndpointSeidel src) (.inl p) (.inl q) ≤ 0 := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  change (∑ r, bulkM src p r * bulkM src r q) +
      ∑ e, twoEndpointSeidel src (.inl p) (.inr e) *
        twoEndpointSeidel src (.inr e) (.inl q) ≤ 0
  rw [bulk_product, endpoint_product, sourceT_product]
  rcases p with ⟨a, ⟨i, s⟩⟩
  rcases q with ⟨b, ⟨j, t⟩⟩
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j
  all_goals
    simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, zero_ne_one, one_ne_zero,
      ↓reduceIte, grade_zero, grade_one, sourceT]
  all_goals
    by_cases hst : s = t
    · subst t
      rcases src.x_sign 1 with hx | hx <;>
        rcases src.y_sign 1 with hy | hy <;>
        simp_all [developed, sourceA, sourceB]
    · rcases src.x_sign (t * s⁻¹) with hx | hx <;>
        rcases src.x_sign (s * t⁻¹) with hx' | hx' <;>
        rcases src.y_sign (t * s⁻¹) with hy | hy <;>
        rcases src.y_sign (s * t⁻¹) with hy' | hy' <;>
        simp [developed, sourceA, sourceB, hx, hx', hy, hy', hst]

private lemma sourceT_grade_sum (p : SourceVertex K) :
    ∑ q, sourceT src p q * grade q = grade p := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  rcases p with ⟨i, s⟩
  fin_cases i
  · simp only [sourceT, grade_zero, grade_one, mul_one, mul_neg,
      Fin.zero_eta, Fin.isValue, ↓reduceIte, one_ne_zero, if_false,
      Finset.sum_neg_distrib]
    rw [sourceA_sum, sourceB_sum]
    norm_num
  · simp only [sourceT, grade_zero, grade_one, mul_one, mul_neg,
      Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte, neg_neg,
      Finset.sum_neg_distrib]
    rw [sourceB_col_sum, sourceA_sum]
    norm_num

private lemma grade_weight_sum (p : SourceVertex K) :
    ∑ q, (if p = q then grade p else 0) * grade q = 1 := by
  classical
  simp [sign_sq (grade_sign p)]

private lemma bulk_grade_weighted (p : BulkVertex K) :
    ∑ q, bulkM src p q * grade q.2 =
      if p.1 = 0 then 2 * grade p.2 + 1 else 1 := by
  classical
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  rcases p with ⟨i, p⟩
  fin_cases i
  · simp only [bulkM, Fin.zero_eta, Fin.isValue, ↓reduceIte, zero_ne_one,
      add_mul, Finset.sum_add_distrib]
    simp only [sourceT_grade_sum, grade_weight_sum]
    ring
  · simp only [bulkM, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte,
      add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    simp only [sourceT_grade_sum, grade_weight_sum]
    ring

private lemma bulk_outer_weighted (p : BulkVertex K) :
    ∑ q, bulkM src p q * (if q.1 = 0 then 1 else -1) =
      if p.1 = 0 then -grade p.2 else -2 + grade p.2 := by
  classical
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  rcases p with ⟨i, p⟩
  fin_cases i
  · simp only [bulkM, Fin.zero_eta, Fin.isValue, ↓reduceIte, zero_ne_one,
      one_ne_zero,
      mul_one, mul_neg, Finset.sum_neg_distrib, Finset.sum_add_distrib]
    simp only [sourceT_row_sum]
    simp <;> ring
  · simp only [bulkM, Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte,
      mul_one, mul_neg, neg_neg, Finset.sum_add_distrib]
    simp only [sourceT_row_sum]
    simp <;> ring

private lemma square_bulk_endpoint_nonpos (p : BulkVertex K) (e : Fin 2) :
    (twoEndpointSeidel src * twoEndpointSeidel src) (.inl p) (.inr e) ≤ 0 := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  fin_cases e
  · change (∑ q, bulkM src p q * -grade q.2) +
        ∑ f : Fin 2, twoEndpointSeidel src (.inl p) (.inr f) *
          twoEndpointSeidel src (.inr f) (.inr 0) ≤ 0
    have hneg : (∑ q, bulkM src p q * -grade q.2) =
        -(∑ q, bulkM src p q * grade q.2) := by
      simp [Finset.sum_neg_distrib]
    rw [hneg, bulk_grade_weighted, Fin.sum_univ_two]
    rcases p with ⟨i, p⟩
    fin_cases i <;> simp [twoEndpointSeidel] <;>
      rcases grade_sign p with hp | hp <;> simp [hp]
  · change (∑ q, bulkM src p q * (if q.1 = 0 then 1 else -1)) +
        ∑ f : Fin 2, twoEndpointSeidel src (.inl p) (.inr f) *
          twoEndpointSeidel src (.inr f) (.inr 1) ≤ 0
    rw [bulk_outer_weighted, Fin.sum_univ_two]
    rcases p with ⟨i, p⟩
    fin_cases i <;> simp [twoEndpointSeidel] <;>
      rcases grade_sign p with hp | hp <;> simp [hp]

private lemma square_endpoint_endpoint_nonpos {e f : Fin 2} (hef : e ≠ f) :
    (twoEndpointSeidel src * twoEndpointSeidel src) (.inr e) (.inr f) ≤ 0 := by
  classical
  fin_cases e <;> fin_cases f
  · exact (hef rfl).elim
  · rw [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_two]
    simp [twoEndpointSeidel, grade_sum]
  · rw [Matrix.mul_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fin.sum_univ_two, Fin.sum_univ_two]
    simp [twoEndpointSeidel, grade_sum]
  · exact (hef rfl).elim

/-- Every off-diagonal entry of the square is nonpositive. -/
theorem twoEndpointSeidel_square_nonpos {p q : LiftVertex K} (hpq : p ≠ q) :
    (twoEndpointSeidel src * twoEndpointSeidel src) p q ≤ 0 := by
  rcases p with p | e <;> rcases q with q | f
  · exact square_bulk_nonpos src (by simpa using hpq)
  · exact square_bulk_endpoint_nonpos src p f
  · have hsquare : (twoEndpointSeidel src * twoEndpointSeidel src).IsSymm := by
      simpa [twoEndpointSeidel_symm src |>.eq] using
        (Matrix.isSymm_transpose_mul_self (twoEndpointSeidel src))
    rw [hsquare.apply (.inl q) (.inr e)]
    exact square_bulk_endpoint_nonpos src q e
  · exact square_endpoint_endpoint_nonpos src (by simpa using hpq)

/-- The lifted matrix has exactly `4 * |K| + 2` vertices. -/
theorem card_liftVertex : Fintype.card (LiftVertex K) = 4 * Fintype.card K + 2 := by
  simp [LiftVertex, BulkVertex, SourceVertex]
  ring

/-- A self-contained certificate exposing all properties needed by the
graph/Seidel conversion. -/
structure TwoEndpointLiftCertificate (K : Type*) [Fintype K] where
  matrix : Matrix (LiftVertex K) (LiftVertex K) ℤ
  symmetric : matrix.IsSymm
  diagonal_zero : ∀ p, matrix p p = 0
  offDiagonal_sign : ∀ {p q}, p ≠ q → matrix p q = 1 ∨ matrix p q = -1
  row_sum_neg_one : ∀ p, ∑ q, matrix p q = -1
  square_offDiagonal_nonpos : ∀ {p q}, p ≠ q → (matrix * matrix) p q ≤ 0

/-- The certificate furnished by a periodic Legendre source. -/
def twoEndpointLiftCertificate : TwoEndpointLiftCertificate K where
  matrix := twoEndpointSeidel src
  symmetric := twoEndpointSeidel_symm src
  diagonal_zero := twoEndpointSeidel_diag src
  offDiagonal_sign := twoEndpointSeidel_sign src
  row_sum_neg_one := twoEndpointSeidel_row_sum src
  square_offDiagonal_nonpos := twoEndpointSeidel_square_nonpos src

end

end BookS2
