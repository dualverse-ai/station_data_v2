import ErdosMinimum.AnalyticBridge
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The first overlap-moment identity

This file proves, for the genuine measurable admissible class, the Fubini and
translation identity which identifies the first moment of the overlap with
the algebraic moment used by the certificate argument.
-/

open MeasureTheory

namespace ErdosMinimum

noncomputable section

private theorem activeInterval_firstMoment_integrable :
    Integrable (fun x : ℝ ↦ x * activeInterval x) := by
  let hI : Integrable (Set.Icc (-1 : ℝ) 1 |>.indicator fun x ↦ x) :=
    continuousOn_id.integrableOn_Icc.integrable_indicator measurableSet_Icc
  convert hI using 1
  funext x
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1 <;> simp [activeInterval, hx]

private theorem integral_activeInterval_firstMoment :
    (∫ x : ℝ, x * activeInterval x) = 0 := by
  have hfun : (fun x : ℝ ↦ x * activeInterval x) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun x ↦ x) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1 <;> simp [activeInterval, hx]
  rw [hfun]
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]
  norm_num [integral_id]

private theorem complementProfile_firstMoment_integrable {f : ℝ → ℝ}
    (hf : Admissible f) :
    Integrable (fun x ↦ x * complementProfile f x) := by
  have hsub := activeInterval_firstMoment_integrable.sub
    (profileFirstMoment_integrable hf)
  convert hsub using 1
  ext x
  simp only [Pi.sub_apply]
  simp [complementProfile, mul_sub]

private theorem integral_complementProfile_firstMoment {f : ℝ → ℝ}
    (hf : Admissible f) :
    (∫ x, x * complementProfile f x) = -profileFirstMoment f := by
  rw [show (fun x ↦ x * complementProfile f x) =
      (fun x ↦ x * activeInterval x) - fun x ↦ x * f x by
        funext x
        simp [complementProfile, mul_sub]]
  change (∫ x, x * activeInterval x - x * f x) = _
  rw [integral_sub activeInterval_firstMoment_integrable
    (profileFirstMoment_integrable hf), integral_activeInterval_firstMoment]
  simp [profileFirstMoment]

private theorem translated_complement_firstMoment {f : ℝ → ℝ}
    (hf : Admissible f) (t : ℝ) :
    (∫ x, x * complementProfile f (t + x)) =
      -profileFirstMoment f - t := by
  let g := complementProfile f
  have hg : Integrable g := complementProfile_integrable hf
  have hmg : Integrable (fun u ↦ u * g u) :=
    complementProfile_firstMoment_integrable hf
  have hshiftBase : Integrable (fun u ↦ (u - t) * g u) := by
    have ht : Integrable (fun u ↦ t * g u) := hg.const_mul t
    convert hmg.sub ht using 1
    ext u
    simp only [Pi.sub_apply]
    ring
  have htranslate := integral_add_right_eq_self (μ := volume)
    (fun u : ℝ ↦ (u - t) * g u) t
  have hsplit : (∫ u, (u - t) * g u) =
      (∫ u, u * g u) - t * (∫ u, g u) := by
    rw [show (fun u ↦ (u - t) * g u) =
        (fun u ↦ u * g u) - fun u ↦ t * g u by
          funext u
          simp only [Pi.sub_apply]
          ring]
    change (∫ u, u * g u - t * g u) = _
    rw [integral_sub hmg (hg.const_mul t), integral_const_mul]
  have hleft : (∫ x, ((x + t) - t) * g (x + t)) =
      ∫ x, x * complementProfile f (t + x) := by
    congr 1
    funext x
    simp [g, add_comm]
  rw [hleft, hsplit, integral_complementProfile_firstMoment hf,
    integral_complementProfile hf] at htranslate
  simpa using htranslate

private theorem overlap_firstMoment_kernel_integrable {f : ℝ → ℝ}
    (hf : Admissible f) :
    Integrable (Function.uncurry fun t x : ℝ ↦
      x * (f t * complementProfile f (t + x))) := by
  let box : Set (ℝ × ℝ) := Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-2 : ℝ) 2
  have hbox : MeasurableSet box := measurableSet_Icc.prod measurableSet_Icc
  have hmajor : Integrable (box.indicator fun _ : ℝ × ℝ ↦ (2 : ℝ)) := by
    rw [integrable_indicator_iff hbox]
    exact integrableOn_const (ne_of_lt ((isCompact_Icc.prod isCompact_Icc).measure_lt_top))
  have hmeas : Measurable (Function.uncurry fun t x : ℝ ↦
      x * (f t * complementProfile f (t + x))) := by
    exact measurable_snd.mul ((hf.1.comp measurable_fst).mul
      ((complementProfile_measurable hf).comp (measurable_fst.add measurable_snd)))
  apply hmajor.mono hmeas.aestronglyMeasurable
  filter_upwards [] with z
  rcases z with ⟨t, x⟩
  simp only [Function.uncurry_apply_pair]
  by_cases ht : t ∈ Set.Icc (-1 : ℝ) 1
  · by_cases hx : x ∈ Set.Icc (-2 : ℝ) 2
    · rw [Set.indicator_of_mem (show (t, x) ∈ box from ⟨ht, hx⟩)]
      simp only [Real.norm_eq_abs, abs_mul]
      rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num),
        abs_of_nonneg (admissible_nonnegative hf t),
        abs_of_nonneg (complementProfile_nonnegative hf (t + x))]
      have hft : f t ≤ 1 := by
        simpa [activeInterval, ht] using admissible_le_activeInterval hf t
      have htx : complementProfile f (t + x) ≤ 1 := by
        exact (complementProfile_le_activeInterval hf (t + x)).trans (by
          by_cases hmem : t + x ∈ Set.Icc (-1 : ℝ) 1 <;>
            simp [activeInterval, hmem])
      have hax : |x| ≤ 2 := abs_le.mpr hx
      have hfg : f t * complementProfile f (t + x) ≤ 1 := calc
        f t * complementProfile f (t + x) ≤
            1 * complementProfile f (t + x) :=
          mul_le_mul_of_nonneg_right hft
            (complementProfile_nonnegative hf (t + x))
        _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left htx (by norm_num)
        _ = 1 := by norm_num
      calc
        |x| * (f t * complementProfile f (t + x)) ≤
            2 * (f t * complementProfile f (t + x)) :=
          mul_le_mul_of_nonneg_right hax
            (mul_nonneg (admissible_nonnegative hf t)
              (complementProfile_nonnegative hf (t + x)))
        _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hfg (by norm_num)
        _ = 2 := by norm_num
    · rw [Set.indicator_of_notMem (show (t, x) ∉ box by
          intro hz
          exact hx hz.2)]
      have htx : t + x ∉ Set.Icc (-1 : ℝ) 1 := by
        intro hmem
        apply hx
        constructor <;> linarith [ht.1, ht.2, hmem.1, hmem.2]
      rw [complementProfile_eq_zero_of_not_mem hf htx]
      simp
  · rw [Set.indicator_of_notMem (show (t, x) ∉ box by
        intro hz
        exact ht hz.1)]
    rw [admissible_eq_zero_of_not_mem hf ht]
    simp

/-- The genuine Fubini/correlation identity for the first overlap moment. -/
theorem overlapFirstMoment_eq_algebraicOverlapFirstMoment {f : ℝ → ℝ}
    (hf : Admissible f) :
    overlapFirstMoment f = algebraicOverlapFirstMoment f := by
  have hkernel := overlap_firstMoment_kernel_integrable hf
  have hswap := integral_integral_swap hkernel
  have hoverlap : overlapFirstMoment f =
      ∫ x, ∫ t, x * (f t * complementProfile f (t + x)) := by
    simp only [overlapFirstMoment, overlap]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [integral_const_mul]
  rw [hoverlap, ← hswap]
  have hinner : ∀ t : ℝ,
      (∫ x, x * (f t * complementProfile f (t + x))) =
        f t * (-profileFirstMoment f - t) := by
    intro t
    rw [show (fun x ↦ x * (f t * complementProfile f (t + x))) =
        fun x ↦ f t * (x * complementProfile f (t + x)) by
          funext x
          ring]
    rw [integral_const_mul, translated_complement_firstMoment hf t]
  simp_rw [hinner]
  rw [show (fun t ↦ f t * (-profileFirstMoment f - t)) =
      (fun t ↦ (-profileFirstMoment f) * f t) - fun t ↦ t * f t by
        funext t
        simp only [Pi.sub_apply]
        ring]
  change (∫ t, (-profileFirstMoment f) * f t - t * f t) = _
  rw [integral_sub ((admissible_integrable hf).const_mul _)
      (profileFirstMoment_integrable hf),
    integral_const_mul, hf.2.2]
  unfold algebraicOverlapFirstMoment profileFirstMoment
  ring

end

end ErdosMinimum
