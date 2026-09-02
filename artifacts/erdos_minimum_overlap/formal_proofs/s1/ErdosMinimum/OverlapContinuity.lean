import ErdosMinimum.OverlapBounds
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Topology.UniformSpace.UniformApproximation

/-!
# Continuity and the `L∞` interpretation of overlap

The overlap of two bounded, compactly supported measurable profiles is a
continuous function even though neither profile need be continuous.  We prove
this by approximating the complementary profile in `L¹` by compactly
supported continuous functions.  Since an admissible `f` satisfies
`|f| ≤ 1`, the resulting correlations approximate the overlap uniformly.

As a consequence, the pointwise supremum `overlapMaximum` is exactly the
measure-theoretic `L∞` seminorm.  Positivity of Lebesgue measure on nonempty
open sets is the key fact that upgrades an almost-everywhere bound on the
continuous overlap to an everywhere bound.
-/

open MeasureTheory Set Filter
open scoped Convolution ENNReal

namespace ErdosMinimum

noncomputable section

private def correlationApprox (f h : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t, f t * h (t + x)

private theorem correlationApprox_eq_convolution (f h : ℝ → ℝ) :
    correlationApprox f h =
      convolution (fun t : ℝ => f (-t)) h (ContinuousLinearMap.mul ℝ ℝ) volume := by
  letI : Measure.IsNegInvariant (volume : Measure ℝ) :=
    ⟨Measure.map_neg_eq_self volume⟩
  funext x
  rw [correlationApprox, convolution_def]
  have hn := integral_neg_eq_self (fun t : ℝ ↦ f (-t) * h (x - t)) volume
  simpa only [neg_neg, sub_neg_eq_add, add_comm, ContinuousLinearMap.mul_apply] using hn

private theorem correlationApprox_continuous {f h : ℝ → ℝ}
    (hf : Integrable f) (hhc : Continuous h) (hhs : HasCompactSupport h) :
    Continuous (correlationApprox f h) := by
  letI : Measure.IsNegInvariant (volume : Measure ℝ) :=
    ⟨Measure.map_neg_eq_self volume⟩
  rw [correlationApprox_eq_convolution]
  apply
    (hhc.norm.bddAbove_range_of_hasCompactSupport hhs.norm).continuous_convolution_right_of_integrable
  · exact hf.comp_neg
  · exact hhc

private theorem overlap_sub_correlationApprox_le {f h : ℝ → ℝ}
    (hf : Admissible f) (hh : Integrable h) (x : ℝ) :
    |overlap f x - correlationApprox f h x| ≤
      ∫ t, |complementProfile f t - h t| := by
  rw [overlap, correlationApprox, ← integral_sub]
  · refine (norm_integral_le_of_norm_le (G := ℝ)
      ((hf.complement_integrable.sub hh).norm.comp_add_right x) ?_).trans_eq ?_
    · filter_upwards with t
      rw [← mul_sub]
      simp only [Real.norm_eq_abs, abs_mul]
      apply mul_le_of_le_one_left (abs_nonneg _)
      apply abs_le.2
      constructor
      · linarith [(hf.2.1 t).1]
      · exact (hf.2.1 t).2.trans (activeInterval_le_one t)
    · change (∫ t : ℝ, |complementProfile f (t + x) - h (t + x)|) = _
      exact integral_add_right_eq_self
        (fun t : ℝ ↦ |complementProfile f t - h t|) x
  · exact hf.overlap_integrable_integrand x
  · have hfi : Integrable (fun t ↦ h (t + x) * f t) := by
      apply (hh.comp_add_right x).mul_bdd (c := 1) hf.integrable.aestronglyMeasurable
      filter_upwards with t
      simp only [Real.norm_eq_abs]
      apply abs_le.2
      exact
        ⟨by linarith [(hf.2.1 t).1],
          (hf.2.1 t).2.trans (activeInterval_le_one t)⟩
    simpa only [mul_comm] using hfi

/-- The overlap of every admissible profile is continuous. -/
theorem overlap_continuous {f : ℝ → ℝ} (hf : Admissible f) :
    Continuous (overlap f) := by
  apply continuous_of_uniform_approx_of_continuous
  intro u hu
  rcases Metric.mem_uniformity_dist.mp hu with ⟨ε, hε, hεu⟩
  have hεhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨h, hhs, hhapprox, hhc, hhi⟩ :=
    hf.complement_integrable.exists_hasCompactSupport_integral_sub_le hεhalf
  refine ⟨correlationApprox f h, correlationApprox_continuous hf.integrable hhc hhs, ?_⟩
  intro x
  apply hεu
  simp only [Real.dist_eq]
  exact (overlap_sub_correlationApprox_le hf hhi x).trans_lt
    (hhapprox.trans_lt (half_lt_self hε))

/-- For an admissible profile, the pointwise supremum used by
`overlapMaximum` is exactly the measure-theoretic `L∞` seminorm of its
overlap. -/
theorem eLpNorm_top_overlap_eq_overlapMaximum {f : ℝ → ℝ} (hf : Admissible f) :
    eLpNorm (overlap f) ⊤ volume = ENNReal.ofReal (overlapMaximum f) := by
  rw [eLpNorm_exponent_top]
  let E : ℝ≥0∞ := eLpNormEssSup (overlap f) volume
  have hupper : E ≤ ENNReal.ofReal (overlapMaximum f) := by
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (overlap_nonneg hf x)]
    exact overlap_le_overlapMaximum hf x
  have hEtop : E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hupper
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), ‖overlap f x‖ₑ ≤ E := by
    simpa only [E, eLpNormEssSup_eq_essSup_enorm] using
      (ENNReal.ae_le_essSup (fun x : ℝ ↦ ‖overlap f x‖ₑ))
  have hopen : IsOpen {x : ℝ | E < ‖overlap f x‖ₑ} :=
    isOpen_lt continuous_const (continuous_enorm.comp (overlap_continuous hf))
  have hnull : volume {x : ℝ | E < ‖overlap f x‖ₑ} = 0 := by
    simpa only [not_le] using (MeasureTheory.ae_iff.mp hae)
  have hempty : {x : ℝ | E < ‖overlap f x‖ₑ} = ∅ :=
    hopen.eq_empty_of_measure_zero hnull
  have hall : ∀ x : ℝ, ‖overlap f x‖ₑ ≤ E := by
    intro x
    by_contra hx
    have hxmem : x ∈ {x : ℝ | E < ‖overlap f x‖ₑ} := by
      simpa only [Set.mem_setOf_eq, not_le] using hx
    rw [hempty] at hxmem
    exact hxmem
  have hmaximum : overlapMaximum f ≤ E.toReal := by
    apply (overlapMaximum_le_iff hf E.toReal).2
    intro x
    apply (ENNReal.ofReal_le_iff_le_toReal hEtop).mp
    calc
      ENNReal.ofReal (overlap f x) = ENNReal.ofReal ‖overlap f x‖ := by
        rw [Real.norm_of_nonneg (overlap_nonneg hf x)]
      _ = ‖overlap f x‖ₑ := ofReal_norm_eq_enorm _
      _ ≤ E := hall x
  exact le_antisymm hupper ((ENNReal.ofReal_le_iff_le_toReal hEtop).2 hmaximum)

end

end ErdosMinimum
