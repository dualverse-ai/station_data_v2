import Mathlib

/-!
# Positive-part budget lemma

This is the order/integration step at the start of Lemma 2.3 in the notebook.
It is independent of the particular Fourier atoms.  Later certificate work
only has to provide the three routine integrability facts and the directed
budget inequality.
-/

open MeasureTheory Set

namespace ErdosMinimum

theorem integral_mul_le_of_positive_part_budget
    (s : Set ℝ) (C G : ℝ → ℝ) (M : ℝ)
    (hs : MeasurableSet s)
    (hC0 : ∀ x ∈ s, 0 ≤ C x)
    (hCM : ∀ x ∈ s, C x ≤ M)
    (hM0 : 0 ≤ M)
    (hbudget : ∫ x in s, max (G x) 0 ≤ 1)
    (hCG : IntegrableOn (fun x => C x * G x) s)
    (hCGp : IntegrableOn (fun x => C x * max (G x) 0) s)
    (hMGp : IntegrableOn (fun x => M * max (G x) 0) s) :
    ∫ x in s, C x * G x ≤ M := by
  have h1 : (∫ x in s, C x * G x) ≤ ∫ x in s, C x * max (G x) 0 := by
    apply setIntegral_mono_on hCG hCGp hs
    intro x hx
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (hC0 x hx)
  have h2 : (∫ x in s, C x * max (G x) 0) ≤
      ∫ x in s, M * max (G x) 0 := by
    apply setIntegral_mono_on hCGp hMGp hs
    intro x hx
    exact mul_le_mul_of_nonneg_right (hCM x hx) (le_max_right _ _)
  have h3 : (∫ x in s, M * max (G x) 0) =
      M * ∫ x in s, max (G x) 0 := by
    rw [MeasureTheory.integral_const_mul]
  have hbudget0 : 0 ≤ ∫ x in s, max (G x) 0 := by
    apply integral_nonneg_of_ae
    filter_upwards with x
    exact le_max_right _ _
  rw [h3] at h2
  nlinarith

end ErdosMinimum
