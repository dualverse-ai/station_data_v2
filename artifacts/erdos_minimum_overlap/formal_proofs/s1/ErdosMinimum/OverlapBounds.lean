import ErdosMinimum.Problem
import Mathlib.MeasureTheory.Group.Integral

/-!
# Pointwise bounds for the continuum overlap

This file proves that the overlap of an admissible profile is nonnegative,
bounded above by one, and supported on `[-2,2]`.  In particular, the range
used in `overlapMaximum` is nonempty and bounded above, so its conditionally
complete supremum has the expected order properties.
-/

open MeasureTheory Set Function

namespace ErdosMinimum

noncomputable section

theorem activeInterval_nonneg (x : ℝ) : 0 ≤ activeInterval x := by
  by_cases hx : x ∈ Icc (-1 : ℝ) 1 <;> simp [activeInterval, hx]

theorem activeInterval_le_one (x : ℝ) : activeInterval x ≤ 1 := by
  by_cases hx : x ∈ Icc (-1 : ℝ) 1 <;> simp [activeInterval, hx]

theorem integrable_activeInterval : Integrable activeInterval := by
  rw [show activeInterval =
      (Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) by rfl]
  exact (integrableOn_const (C := (1 : ℝ)) (hs := measure_Icc_lt_top.ne)).integrable_indicator
    measurableSet_Icc

theorem Admissible.integrable {f : ℝ → ℝ} (hf : Admissible f) : Integrable f := by
  apply integrable_activeInterval.mono hf.1.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (hf.2.1 x).1,
    Real.norm_eq_abs, abs_of_nonneg (activeInterval_nonneg x)]
  exact (hf.2.1 x).2

theorem Admissible.eq_zero_of_not_mem {f : ℝ → ℝ} (hf : Admissible f)
    {x : ℝ} (hx : x ∉ Icc (-1 : ℝ) 1) : f x = 0 := by
  have h := hf.2.1 x
  simp [activeInterval, hx] at h
  exact le_antisymm h.2 h.1

theorem Admissible.complement_nonneg {f : ℝ → ℝ} (hf : Admissible f) (x : ℝ) :
    0 ≤ complementProfile f x := by
  exact sub_nonneg.mpr (hf.2.1 x).2

theorem Admissible.complement_le_one {f : ℝ → ℝ} (hf : Admissible f) (x : ℝ) :
    complementProfile f x ≤ 1 := by
  dsimp [complementProfile]
  linarith [activeInterval_le_one x, (hf.2.1 x).1]

theorem Admissible.complement_eq_zero_of_not_mem {f : ℝ → ℝ} (hf : Admissible f)
    {x : ℝ} (hx : x ∉ Icc (-1 : ℝ) 1) : complementProfile f x = 0 := by
  simp [complementProfile, activeInterval, hx, hf.eq_zero_of_not_mem hx]

theorem Admissible.complement_integrable {f : ℝ → ℝ} (hf : Admissible f) :
    Integrable (complementProfile f) := by
  have hsub := integrable_activeInterval.sub hf.integrable
  simpa only [Pi.sub_apply, complementProfile] using hsub

theorem Admissible.overlap_integrable_integrand {f : ℝ → ℝ} (hf : Admissible f)
    (x : ℝ) : Integrable (fun t => f t * complementProfile f (t + x)) := by
  apply (Admissible.integrable hf).mul_bdd
    ((Admissible.complement_integrable hf).comp_add_right x).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_of_nonneg (hf.complement_nonneg (t + x))]
  exact hf.complement_le_one (t + x)

theorem overlap_nonneg {f : ℝ → ℝ} (hf : Admissible f) (x : ℝ) :
    0 ≤ overlap f x := by
  rw [overlap]
  apply integral_nonneg
  intro t
  exact mul_nonneg (hf.2.1 t).1 (hf.complement_nonneg (t + x))

theorem overlap_le_one {f : ℝ → ℝ} (hf : Admissible f) (x : ℝ) :
    overlap f x ≤ 1 := by
  rw [overlap, ← hf.2.2]
  apply integral_mono (hf.overlap_integrable_integrand x) hf.integrable
  intro t
  exact mul_le_of_le_one_right (hf.2.1 t).1 (hf.complement_le_one (t + x))

theorem overlap_eq_zero_of_not_mem {f : ℝ → ℝ} (hf : Admissible f)
    {x : ℝ} (hx : x ∉ Icc (-2 : ℝ) 2) : overlap f x = 0 := by
  rw [overlap]
  apply integral_eq_zero_of_ae
  filter_upwards with t
  by_cases ht : t ∈ Icc (-1 : ℝ) 1
  · have hx' : x < -2 ∨ 2 < x := by
      by_cases hleft : -2 ≤ x
      · exact Or.inr (lt_of_not_ge fun hright => hx ⟨hleft, hright⟩)
      · exact Or.inl (lt_of_not_ge hleft)
    rcases hx' with hx' | hx'
    · have htx : t + x ∉ Icc (-1 : ℝ) 1 := by
        intro h
        linarith [ht.1, ht.2, h.1, h.2]
      rw [hf.complement_eq_zero_of_not_mem htx, mul_zero]
      simp
    · have htx : t + x ∉ Icc (-1 : ℝ) 1 := by
        intro h
        linarith [ht.1, ht.2, h.1, h.2]
      rw [hf.complement_eq_zero_of_not_mem htx, mul_zero]
      simp
  · rw [hf.eq_zero_of_not_mem ht, zero_mul]
    simp

theorem overlap_hasCompactSupport {f : ℝ → ℝ} (hf : Admissible f) :
    HasCompactSupport (overlap f) := by
  apply HasCompactSupport.of_support_subset_isCompact isCompact_Icc
  intro x hx
  by_contra hmem
  exact hx (overlap_eq_zero_of_not_mem hf hmem)

theorem overlap_range_bddAbove {f : ℝ → ℝ} (hf : Admissible f) :
    BddAbove (range (overlap f)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact overlap_le_one hf x

theorem overlap_le_overlapMaximum {f : ℝ → ℝ} (hf : Admissible f) (x : ℝ) :
    overlap f x ≤ overlapMaximum f := by
  exact le_csSup (overlap_range_bddAbove hf) ⟨x, rfl⟩

theorem overlapMaximum_le_iff {f : ℝ → ℝ} (hf : Admissible f) (a : ℝ) :
    overlapMaximum f ≤ a ↔ ∀ x, overlap f x ≤ a := by
  constructor
  · intro h x
    exact (overlap_le_overlapMaximum hf x).trans h
  · intro h
    rw [overlapMaximum]
    exact csSup_le (range_nonempty (overlap f)) (by rintro _ ⟨x, rfl⟩; exact h x)

theorem overlapMaximum_nonneg {f : ℝ → ℝ} (hf : Admissible f) :
    0 ≤ overlapMaximum f := by
  exact (overlap_nonneg hf 0).trans (overlap_le_overlapMaximum hf 0)

theorem overlapMaximum_le_one {f : ℝ → ℝ} (hf : Admissible f) :
    overlapMaximum f ≤ 1 := by
  exact (overlapMaximum_le_iff hf 1).2 (overlap_le_one hf)

theorem overlapMaximum_mem_Icc {f : ℝ → ℝ} (hf : Admissible f) :
    overlapMaximum f ∈ Icc (0 : ℝ) 1 :=
  ⟨overlapMaximum_nonneg hf, overlapMaximum_le_one hf⟩

end

end ErdosMinimum
