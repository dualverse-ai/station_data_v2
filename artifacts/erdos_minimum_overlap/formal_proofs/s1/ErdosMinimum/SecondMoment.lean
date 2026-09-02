import ErdosMinimum.AnalyticBridge
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The second moment of the overlap

This module proves the exact correlation-moment identity used in the paper.
All integrals are Lebesgue integrals on `ℝ`.  In particular, the proof records
the integrability needed for Fubini and uses translation invariance explicitly.
-/

open MeasureTheory Set

namespace ErdosMinimum

noncomputable section

/-- The ordinary second moment of a profile. -/
noncomputable def profileSecondMoment (f : ℝ → ℝ) : ℝ :=
  ∫ x, x ^ 2 * f x

/-- The second moment of the overlap density. -/
noncomputable def overlapSecondMoment (f : ℝ → ℝ) : ℝ :=
  ∫ x, x ^ 2 * overlap f x

private theorem active_first_moment_integrable :
    Integrable (fun x : ℝ ↦ x * activeInterval x) := by
  apply integrable_activeInterval.mono
    (measurable_id.mul measurable_activeInterval).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · have hax : |x| ≤ 1 := abs_le.mpr hx
    simp [activeInterval, hx, hax]
  · simp [activeInterval, hx]

private theorem active_second_moment_integrable :
    Integrable (fun x : ℝ ↦ x ^ 2 * activeInterval x) := by
  apply integrable_activeInterval.mono
    ((measurable_id.pow_const 2).mul measurable_activeInterval).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · have hax : |x| ≤ 1 := abs_le.mpr hx
    have hx2 : x ^ 2 ≤ 1 := (sq_le_one_iff_abs_le_one x).2 hax
    simp [activeInterval, hx, abs_of_nonneg (sq_nonneg x), hx2]
  · simp [activeInterval, hx]

theorem profileSecondMoment_integrable {f : ℝ → ℝ} (hf : Admissible f) :
    Integrable (fun x ↦ x ^ 2 * f x) := by
  apply active_second_moment_integrable.mono
    ((measurable_id.pow_const 2).mul hf.1).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · have hfx := admissible_le_activeInterval hf x
    have hfn := admissible_nonnegative hf x
    simp only [activeInterval, Set.indicator_of_mem hx] at hfx
    rw [abs_mul, abs_mul, abs_of_nonneg hfn]
    simp only [activeInterval, Set.indicator_of_mem hx, abs_one, mul_one]
    simpa [abs_pow] using
      (mul_le_mul_of_nonneg_left hfx (pow_nonneg (abs_nonneg x) 2))
  · simp [activeInterval, hx, admissible_eq_zero_of_not_mem hf hx]

theorem complementSecondMoment_integrable {f : ℝ → ℝ} (hf : Admissible f) :
    Integrable (fun x ↦ x ^ 2 * complementProfile f x) := by
  apply active_second_moment_integrable.mono
    ((measurable_id.pow_const 2).mul (complementProfile_measurable hf)).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · have hg := complementProfile_le_activeInterval hf x
    have hgn := complementProfile_nonnegative hf x
    simp only [activeInterval, Set.indicator_of_mem hx] at hg
    rw [abs_mul, abs_mul, abs_of_nonneg hgn]
    simp only [activeInterval, Set.indicator_of_mem hx, abs_one, mul_one]
    simpa [abs_pow] using
      (mul_le_mul_of_nonneg_left hg (pow_nonneg (abs_nonneg x) 2))
  · simp [activeInterval, hx, complementProfile_eq_zero_of_not_mem hf hx]

private theorem active_first_moment :
    (∫ x : ℝ, x * activeInterval x) = 0 := by
  calc
    (∫ x : ℝ, x * activeInterval x) =
        ∫ x, (Icc (-1 : ℝ) 1).indicator (fun x ↦ x) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ Icc (-1 : ℝ) 1 <;> simp [activeInterval, hx]
    _ = ∫ x in Icc (-1 : ℝ) 1, x := integral_indicator measurableSet_Icc
    _ = 0 := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num)]
      norm_num [integral_id]

private theorem active_second_moment :
    (∫ x : ℝ, x ^ 2 * activeInterval x) = (2 : ℝ) / 3 := by
  calc
    (∫ x : ℝ, x ^ 2 * activeInterval x) =
        ∫ x, (Icc (-1 : ℝ) 1).indicator (fun x ↦ x ^ 2) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      by_cases hx : x ∈ Icc (-1 : ℝ) 1 <;> simp [activeInterval, hx]
    _ = ∫ x in Icc (-1 : ℝ) 1, x ^ 2 := integral_indicator measurableSet_Icc
    _ = (2 : ℝ) / 3 := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num)]
      norm_num [integral_pow]

theorem complement_first_moment {f : ℝ → ℝ} (hf : Admissible f) :
    (∫ x, x * complementProfile f x) = -profileFirstMoment f := by
  rw [show (fun x : ℝ ↦ x * complementProfile f x) =
      fun x ↦ x * activeInterval x - x * f x by
    funext x
    simp [complementProfile, mul_sub]]
  rw [integral_sub active_first_moment_integrable (profileFirstMoment_integrable hf),
    active_first_moment]
  simp [profileFirstMoment]

theorem complement_second_moment {f : ℝ → ℝ} (hf : Admissible f) :
    profileSecondMoment (complementProfile f) = (2 : ℝ) / 3 - profileSecondMoment f := by
  rw [profileSecondMoment]
  rw [show (fun x : ℝ ↦ x ^ 2 * complementProfile f x) =
      fun x ↦ x ^ 2 * activeInterval x - x ^ 2 * f x by
    funext x
    simp [complementProfile, mul_sub]]
  rw [integral_sub active_second_moment_integrable (profileSecondMoment_integrable hf),
    active_second_moment, profileSecondMoment]

private theorem integral_shift_first
    (g : ℝ → ℝ) (t : ℝ) :
    (∫ x, x * g (t + x)) = ∫ u, (u - t) * g u := by
  have h := integral_add_right_eq_self (μ := volume)
    (fun u : ℝ ↦ (u - t) * g u) t
  simpa [add_comm, add_left_comm, add_assoc] using h

private theorem integral_shift_second
    (g : ℝ → ℝ) (t : ℝ) :
    (∫ x, x ^ 2 * g (t + x)) = ∫ u, (u - t) ^ 2 * g u := by
  have h := integral_add_right_eq_self (μ := volume)
    (fun u : ℝ ↦ (u - t) ^ 2 * g u) t
  simpa [add_comm, add_left_comm, add_assoc] using h

theorem overlap_product_integrable {f : ℝ → ℝ} (hf : Admissible f) :
    Integrable
      (fun p : ℝ × ℝ ↦ f p.1 * complementProfile f (p.1 + p.2)) := by
  let g := complementProfile f
  have hmeas : Measurable (fun p : ℝ × ℝ ↦ f p.1 * g (p.1 + p.2)) :=
    (hf.1.comp measurable_fst).mul
      ((complementProfile_measurable hf).comp (measurable_fst.add measurable_snd))
  change Integrable (fun p : ℝ × ℝ ↦ f p.1 * g (p.1 + p.2))
    (volume.prod volume)
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  constructor
  · filter_upwards [] with t
    simpa [g, add_comm] using
      ((complementProfile_integrable hf).comp_add_right t).const_mul (f t)
  · have hgNorm : Integrable (fun t : ℝ ↦
        (∫ x, ‖g x‖) * ‖f t‖) :=
      (admissible_integrable hf).norm.const_mul (∫ x, ‖g x‖)
    convert hgNorm using 1
    funext t
    rw [show (∫ x, ‖f t * g (t + x)‖) =
        ‖f t‖ * ∫ x, ‖g (x + t)‖ by
      simp_rw [norm_mul, add_comm t]
      rw [integral_const_mul]]
    have hshift : (∫ x : ℝ, ‖g (x + t)‖) = ∫ x, ‖g x‖ :=
      integral_add_right_eq_self (μ := volume) (fun x : ℝ ↦ ‖g x‖) t
    rw [hshift]
    ring

private theorem overlap_first_product_integrable {f : ℝ → ℝ} (hf : Admissible f) :
    Integrable
      (fun p : ℝ × ℝ ↦ p.2 * (f p.1 * complementProfile f (p.1 + p.2))) := by
  apply (overlap_product_integrable hf).const_mul 2 |>.mono
    ((measurable_snd.mul
      ((hf.1.comp measurable_fst).mul
        ((complementProfile_measurable hf).comp
          (measurable_fst.add measurable_snd)))).aestronglyMeasurable)
  filter_upwards [] with p
  by_cases hp : f p.1 * complementProfile f (p.1 + p.2) = 0
  · simp [hp]
  · have hft : f p.1 ≠ 0 := left_ne_zero_of_mul hp
    have hgu : complementProfile f (p.1 + p.2) ≠ 0 := right_ne_zero_of_mul hp
    have ht : p.1 ∈ Icc (-1 : ℝ) 1 := by
      by_contra h
      exact hft (admissible_eq_zero_of_not_mem hf h)
    have hu : p.1 + p.2 ∈ Icc (-1 : ℝ) 1 := by
      by_contra h
      exact hgu (complementProfile_eq_zero_of_not_mem hf h)
    rcases ht with ⟨htl, htr⟩
    rcases hu with ⟨hul, hur⟩
    have hx : |p.2| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    convert mul_le_mul_of_nonneg_right hx
      (norm_nonneg (f p.1 * complementProfile f (p.1 + p.2))) using 1 <;>
      simp [norm_mul]

private theorem overlap_second_product_integrable {f : ℝ → ℝ} (hf : Admissible f) :
    Integrable
      (fun p : ℝ × ℝ ↦ p.2 ^ 2 *
        (f p.1 * complementProfile f (p.1 + p.2))) := by
  apply (overlap_product_integrable hf).const_mul 4 |>.mono
    (((measurable_snd.pow_const 2).mul
      ((hf.1.comp measurable_fst).mul
        ((complementProfile_measurable hf).comp
          (measurable_fst.add measurable_snd)))).aestronglyMeasurable)
  filter_upwards [] with p
  by_cases hp : f p.1 * complementProfile f (p.1 + p.2) = 0
  · simp [hp]
  · have hft : f p.1 ≠ 0 := left_ne_zero_of_mul hp
    have hgu : complementProfile f (p.1 + p.2) ≠ 0 := right_ne_zero_of_mul hp
    have ht : p.1 ∈ Icc (-1 : ℝ) 1 := by
      by_contra h
      exact hft (admissible_eq_zero_of_not_mem hf h)
    have hu : p.1 + p.2 ∈ Icc (-1 : ℝ) 1 := by
      by_contra h
      exact hgu (complementProfile_eq_zero_of_not_mem hf h)
    rcases ht with ⟨htl, htr⟩
    rcases hu with ⟨hul, hur⟩
    have habs : |p.2| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have hx : p.2 ^ 2 ≤ 4 := by
      have := (sq_le_sq (a := p.2) (b := (2 : ℝ))).2 (by simpa using habs)
      norm_num at this ⊢
      exact this
    convert mul_le_mul_of_nonneg_right hx
      (norm_nonneg (f p.1 * complementProfile f (p.1 + p.2))) using 1 <;>
      simp [norm_mul]

private theorem shifted_first_moment_complement {f : ℝ → ℝ}
    (hf : Admissible f) (t : ℝ) :
    (∫ x, x * complementProfile f (t + x)) =
      -profileFirstMoment f - t := by
  rw [integral_shift_first]
  rw [show (fun u : ℝ ↦ (u - t) * complementProfile f u) =
      fun u ↦ u * complementProfile f u - t * complementProfile f u by
    funext u
    ring]
  rw [integral_sub (profileFirstMoment_integrable
      ⟨complementProfile_measurable hf,
        fun x ↦ ⟨complementProfile_nonnegative hf x,
          complementProfile_le_activeInterval hf x⟩,
        integral_complementProfile hf⟩)
      ((complementProfile_integrable hf).const_mul t),
    integral_const_mul, complement_first_moment hf, integral_complementProfile hf]
  ring

private theorem shifted_second_moment_complement {f : ℝ → ℝ}
    (hf : Admissible f) (t : ℝ) :
    (∫ x, x ^ 2 * complementProfile f (t + x)) =
      profileSecondMoment (complementProfile f) +
        2 * t * profileFirstMoment f + t ^ 2 := by
  rw [integral_shift_second]
  rw [show (fun u : ℝ ↦ (u - t) ^ 2 * complementProfile f u) =
      fun u ↦ u ^ 2 * complementProfile f u -
        (2 * t) * (u * complementProfile f u) +
        t ^ 2 * complementProfile f u by
    funext u
    ring]
  have hgAdmissible : Admissible (complementProfile f) :=
    ⟨complementProfile_measurable hf,
      fun x ↦ ⟨complementProfile_nonnegative hf x,
        complementProfile_le_activeInterval hf x⟩,
      integral_complementProfile hf⟩
  have hfirst := profileFirstMoment_integrable hgAdmissible
  have hsub : Integrable (fun u : ℝ ↦
      u ^ 2 * complementProfile f u -
        (2 * t) * (u * complementProfile f u)) :=
    (complementSecondMoment_integrable hf).sub (hfirst.const_mul (2 * t))
  have hlast : Integrable (fun u : ℝ ↦ t ^ 2 * complementProfile f u) :=
    (complementProfile_integrable hf).const_mul (t ^ 2)
  calc
    (∫ u, u ^ 2 * complementProfile f u -
        2 * t * (u * complementProfile f u) +
        t ^ 2 * complementProfile f u) =
        (∫ u, u ^ 2 * complementProfile f u -
          2 * t * (u * complementProfile f u)) +
          ∫ u, t ^ 2 * complementProfile f u := by
      exact integral_add hsub hlast
    _ = profileSecondMoment (complementProfile f) +
        2 * t * profileFirstMoment f + t ^ 2 := by
      rw [integral_sub (complementSecondMoment_integrable hf)
          (hfirst.const_mul (2 * t)),
    integral_const_mul, integral_const_mul, complement_first_moment hf,
    integral_complementProfile hf, profileSecondMoment]
      ring

/-- The overlap itself is integrable. -/
theorem overlap_integrable {f : ℝ → ℝ} (hf : Admissible f) :
    Integrable (overlap f) := by
  have h := (overlap_product_integrable hf).integral_prod_right
  apply h.congr
  filter_upwards [] with x
  rfl

/-- The overlap has total mass one. -/
theorem integral_overlap {f : ℝ → ℝ} (hf : Admissible f) :
    ∫ x, overlap f x = 1 := by
  change (∫ x, ∫ t, f t * complementProfile f (t + x)) = 1
  rw [← integral_integral_swap (overlap_product_integrable hf)]
  simp_rw [integral_const_mul]
  have hshift : ∀ t : ℝ, (∫ x, complementProfile f (t + x)) = 1 := by
    intro t
    rw [show (fun x : ℝ ↦ complementProfile f (t + x)) =
        fun x ↦ complementProfile f (x + t) by
      funext x
      rw [add_comm]]
    rw [integral_add_right_eq_self, integral_complementProfile hf]
  simp_rw [hshift, mul_one, hf.2.2]

/-- The actual overlap first moment equals the algebraic expression used elsewhere. -/
theorem secondMoment_overlapFirstMoment_eq_algebraic {f : ℝ → ℝ}
    (hf : Admissible f) :
    overlapFirstMoment f = algebraicOverlapFirstMoment f := by
  rw [overlapFirstMoment]
  simp_rw [overlap]
  simp_rw [← integral_const_mul]
  rw [← integral_integral_swap (overlap_first_product_integrable hf)]
  rw [show (fun t : ℝ ↦ ∫ x, x *
      (f t * complementProfile f (t + x))) =
      fun t ↦ ∫ x, f t * (x * complementProfile f (t + x)) by
    funext t
    apply integral_congr_ae
    filter_upwards [] with x
    ring]
  simp_rw [integral_const_mul, shifted_first_moment_complement hf]
  rw [show (fun t : ℝ ↦ f t * (-profileFirstMoment f - t)) =
      fun t ↦ (-profileFirstMoment f) * f t - t * f t by
    funext t
    ring]
  rw [integral_sub ((admissible_integrable hf).const_mul (-profileFirstMoment f))
      (profileFirstMoment_integrable hf),
    integral_const_mul, hf.2.2]
  simp [algebraicOverlapFirstMoment, profileFirstMoment]
  ring

/-- Exact second-overlap moment identity for every admissible measurable profile. -/
theorem overlap_second_moment_identity {f : ℝ → ℝ} (hf : Admissible f) :
    overlapSecondMoment f =
      (2 : ℝ) / 3 + (overlapFirstMoment f) ^ 2 / 2 := by
  have hraw : overlapSecondMoment f =
      profileSecondMoment (complementProfile f) +
        2 * (profileFirstMoment f) ^ 2 + profileSecondMoment f := by
    rw [overlapSecondMoment]
    simp_rw [overlap]
    simp_rw [← integral_const_mul]
    rw [← integral_integral_swap (overlap_second_product_integrable hf)]
    rw [show (fun t : ℝ ↦ ∫ x, x ^ 2 *
        (f t * complementProfile f (t + x))) =
        fun t ↦ ∫ x, f t * (x ^ 2 * complementProfile f (t + x)) by
      funext t
      apply integral_congr_ae
      filter_upwards [] with x
      ring]
    simp_rw [integral_const_mul, shifted_second_moment_complement hf]
    rw [show (fun t : ℝ ↦ f t *
        (profileSecondMoment (complementProfile f) +
          2 * t * profileFirstMoment f + t ^ 2)) =
        fun t ↦ profileSecondMoment (complementProfile f) * f t +
          (2 * profileFirstMoment f) * (t * f t) + t ^ 2 * f t by
      funext t
      ring]
    have hsum : Integrable (fun t : ℝ ↦
        profileSecondMoment (complementProfile f) * f t +
          (2 * profileFirstMoment f) * (t * f t)) :=
      ((admissible_integrable hf).const_mul
        (profileSecondMoment (complementProfile f))).add
        ((profileFirstMoment_integrable hf).const_mul (2 * profileFirstMoment f))
    calc
      (∫ t, profileSecondMoment (complementProfile f) * f t +
          2 * profileFirstMoment f * (t * f t) + t ^ 2 * f t) =
          (∫ t, profileSecondMoment (complementProfile f) * f t +
            2 * profileFirstMoment f * (t * f t)) +
            ∫ t, t ^ 2 * f t := by
        exact integral_add hsum (profileSecondMoment_integrable hf)
      _ = profileSecondMoment (complementProfile f) +
          2 * (profileFirstMoment f) ^ 2 + profileSecondMoment f := by
        rw [integral_add
            ((admissible_integrable hf).const_mul
              (profileSecondMoment (complementProfile f)))
            ((profileFirstMoment_integrable hf).const_mul (2 * profileFirstMoment f)),
          integral_const_mul, integral_const_mul, hf.2.2, profileFirstMoment,
          profileSecondMoment]
        simp only [profileSecondMoment]
        ring
  rw [hraw, complement_second_moment hf,
    secondMoment_overlapFirstMoment_eq_algebraic hf]
  simp [algebraicOverlapFirstMoment]
  ring

theorem overlap_second_moment_integrable {f : ℝ → ℝ} (hf : Admissible f) :
    Integrable (fun x ↦ x ^ 2 * overlap f x) := by
  have h := overlap_second_product_integrable hf
  have hi := h.integral_prod_right
  apply hi.congr
  filter_upwards [] with x
  rw [overlap, ← integral_const_mul]

theorem overlap_first_moment_integrable {f : ℝ → ℝ} (hf : Admissible f) :
    Integrable (fun x ↦ x * overlap f x) := by
  have h := overlap_first_product_integrable hf
  have hi := h.integral_prod_right
  apply hi.congr
  filter_upwards [] with x
  rw [overlap, ← integral_const_mul]

end

end ErdosMinimum
