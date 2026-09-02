import ErdosMinimum.AnalyticBridge
import ErdosMinimum.PhaseSupport
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Fourier transforms of the overlap correlation

This module supplies the analytic input to `PhaseSupport.lean`.  We use real
cosine and sine transforms, with no normalization factor.  If

* `a` and `b` are the cosine and sine transforms of an admissible profile,
* `s` is half the cosine transform of `1_[−1,1]`,

then the transforms of its overlap are respectively
`2*s*a - a^2 - b^2` and `-2*s*b`.  Consequently the phase-support inequality
holds at every real frequency.
-/

open MeasureTheory

namespace ErdosMinimum

noncomputable section

/-- Unnormalized real cosine transform. -/
def cosineTransform (h : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ x, h x * Real.cos (ξ * x)

/-- Unnormalized real sine transform. -/
def sineTransform (h : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  ∫ x, h x * Real.sin (ξ * x)

/-- Half the cosine transform of the active interval.  This is the `s`
appearing in the phase-support parabola. -/
def intervalHalfCosineTransform (ξ : ℝ) : ℝ :=
  cosineTransform activeInterval ξ / 2

/-- The interval factor has the paper's closed form `sin ξ / ξ`, continuously
extended to one at the origin. -/
theorem intervalHalfCosineTransform_eq_sinc (ξ : ℝ) :
    intervalHalfCosineTransform ξ = Real.sinc ξ := by
  have hfun : (fun x : ℝ ↦ activeInterval x * Real.cos (ξ * x)) =
      (Set.Icc (-1 : ℝ) 1).indicator (fun x ↦ Real.cos (ξ * x)) := by
    funext x
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1 <;> simp [activeInterval, hx]
  rw [intervalHalfCosineTransform, cosineTransform, hfun,
    integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
  by_cases hξ : ξ = 0
  · subst ξ
    norm_num
  · rw [intervalIntegral.integral_comp_mul_left Real.cos hξ, integral_cos,
      Real.sinc_of_ne_zero hξ]
    simp
    field_simp
    ring

private theorem integrable_mul_cos {h : ℝ → ℝ} (hh : Integrable h) (ξ : ℝ) :
    Integrable (fun x ↦ h x * Real.cos (ξ * x)) := by
  apply hh.mul_bdd
  · exact (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards with x
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (ξ * x)

private theorem integrable_mul_sin {h : ℝ → ℝ} (hh : Integrable h) (ξ : ℝ) :
    Integrable (fun x ↦ h x * Real.sin (ξ * x)) := by
  apply hh.mul_bdd
  · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · filter_upwards with x
    simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (ξ * x)

/-- The sine transform of the symmetric active interval vanishes. -/
theorem activeInterval_sineTransform (ξ : ℝ) :
    sineTransform activeInterval ξ = 0 := by
  letI : Measure.IsNegInvariant (volume : Measure ℝ) :=
    ⟨Measure.map_neg_eq_self volume⟩
  have hneg := integral_neg_eq_self
    (fun x : ℝ ↦ activeInterval x * Real.sin (ξ * x)) volume
  rw [sineTransform]
  have hodd : (fun x : ℝ ↦ activeInterval (-x) * Real.sin (ξ * (-x))) =
      fun x : ℝ ↦ -(activeInterval x * Real.sin (ξ * x)) := by
    funext x
    rw [activeInterval_neg]
    simp
  rw [hodd, integral_neg] at hneg
  linarith

private theorem integrable_correlation_kernel
    {f g : ℝ → ℝ} (hmf : Measurable f) (hmg : Measurable g)
    (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun p : ℝ × ℝ ↦ f p.1 * g (p.1 + p.2))
      ((volume : Measure ℝ).prod volume) := by
  have hmeas : Measurable (fun p : ℝ × ℝ ↦ f p.1 * g (p.1 + p.2)) :=
    (hmf.comp measurable_fst).mul (hmg.comp (measurable_fst.add measurable_snd))
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  constructor
  · filter_upwards with t
    exact (hg.comp_add_left t).const_mul (f t)
  · have heq : (fun t : ℝ ↦ ∫ x, ‖f t * g (t + x)‖) =
        fun t ↦ ‖f t‖ * ∫ u, ‖g u‖ := by
      funext t
      rw [show (fun x : ℝ ↦ ‖f t * g (t + x)‖) =
          fun x ↦ ‖f t‖ * ‖g (t + x)‖ by
            funext x
            rw [norm_mul]]
      rw [integral_const_mul]
      rw [show (fun x : ℝ ↦ ‖g (t + x)‖) = fun x ↦ ‖g (x + t)‖ by
        funext x; rw [add_comm]]
      congr 1
      exact integral_add_right_eq_self (fun u : ℝ ↦ ‖g u‖) t
    rw [heq]
    exact hf.norm.mul_const _

private theorem integrable_correlation_cos_kernel
    {f g : ℝ → ℝ} (hmf : Measurable f) (hmg : Measurable g)
    (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦
      (f p.1 * g (p.1 + p.2)) * Real.cos (ξ * p.2)) := by
  apply (integrable_correlation_kernel hmf hmg hf hg).mul_bdd
  · exact (Real.continuous_cos.comp
      (continuous_const.mul continuous_snd)).aestronglyMeasurable
  · filter_upwards with p
    simpa [Real.norm_eq_abs] using Real.abs_cos_le_one (ξ * p.2)

private theorem integrable_correlation_sin_kernel
    {f g : ℝ → ℝ} (hmf : Measurable f) (hmg : Measurable g)
    (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    Integrable (fun p : ℝ × ℝ ↦
      (f p.1 * g (p.1 + p.2)) * Real.sin (ξ * p.2)) := by
  apply (integrable_correlation_kernel hmf hmg hf hg).mul_bdd
  · exact (Real.continuous_sin.comp
      (continuous_const.mul continuous_snd)).aestronglyMeasurable
  · filter_upwards with p
    simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (ξ * p.2)

private theorem integral_shift_cos {g : ℝ → ℝ} (hg : Integrable g) (t ξ : ℝ) :
    (∫ x, g (t + x) * Real.cos (ξ * x)) =
      cosineTransform g ξ * Real.cos (ξ * t) +
        sineTransform g ξ * Real.sin (ξ * t) := by
  have htranslate := integral_add_right_eq_self (μ := volume)
    (fun u : ℝ ↦ g u * Real.cos (ξ * (u - t))) t
  have hleft :
      (fun x : ℝ ↦ g (x + t) * Real.cos (ξ * ((x + t) - t))) =
        fun x ↦ g (t + x) * Real.cos (ξ * x) := by
    funext x
    simp [add_comm]
  rw [hleft] at htranslate
  rw [htranslate]
  have hsplit : (fun u : ℝ ↦ g u * Real.cos (ξ * (u - t))) =
      fun u ↦ (g u * Real.cos (ξ * u)) * Real.cos (ξ * t) +
        (g u * Real.sin (ξ * u)) * Real.sin (ξ * t) := by
    funext u
    rw [mul_sub, Real.cos_sub]
    ring
  rw [hsplit, integral_add
    ((integrable_mul_cos hg ξ).mul_const _)
    ((integrable_mul_sin hg ξ).mul_const _),
    integral_mul_const, integral_mul_const]
  rfl

private theorem integral_shift_sin {g : ℝ → ℝ} (hg : Integrable g) (t ξ : ℝ) :
    (∫ x, g (t + x) * Real.sin (ξ * x)) =
      sineTransform g ξ * Real.cos (ξ * t) -
        cosineTransform g ξ * Real.sin (ξ * t) := by
  have htranslate := integral_add_right_eq_self (μ := volume)
    (fun u : ℝ ↦ g u * Real.sin (ξ * (u - t))) t
  have hleft :
      (fun x : ℝ ↦ g (x + t) * Real.sin (ξ * ((x + t) - t))) =
        fun x ↦ g (t + x) * Real.sin (ξ * x) := by
    funext x
    simp [add_comm]
  rw [hleft] at htranslate
  rw [htranslate]
  have hsplit : (fun u : ℝ ↦ g u * Real.sin (ξ * (u - t))) =
      fun u ↦ (g u * Real.sin (ξ * u)) * Real.cos (ξ * t) -
        (g u * Real.cos (ξ * u)) * Real.sin (ξ * t) := by
    funext u
    rw [mul_sub, Real.sin_sub]
    ring
  rw [hsplit, integral_sub
    ((integrable_mul_sin hg ξ).mul_const _)
    ((integrable_mul_cos hg ξ).mul_const _),
    integral_mul_const, integral_mul_const]
  rfl

/-- Fubini/translation identity for the cosine transform of a correlation in
the orientation `g (t + x)`. -/
theorem cosineTransform_correlation
    {f g : ℝ → ℝ} (hmf : Measurable f) (hmg : Measurable g)
    (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    cosineTransform (fun x ↦ ∫ t, f t * g (t + x)) ξ =
      cosineTransform f ξ * cosineTransform g ξ +
        sineTransform f ξ * sineTransform g ξ := by
  rw [cosineTransform]
  simp_rw [← integral_mul_const]
  rw [← integral_integral_swap
    (integrable_correlation_cos_kernel hmf hmg hf hg ξ)]
  have hinner : ∀ t : ℝ,
      (∫ x, (f t * g (t + x)) * Real.cos (ξ * x)) =
        f t * (cosineTransform g ξ * Real.cos (ξ * t) +
          sineTransform g ξ * Real.sin (ξ * t)) := by
    intro t
    rw [show (fun x : ℝ ↦ (f t * g (t + x)) * Real.cos (ξ * x)) =
        fun x ↦ f t * (g (t + x) * Real.cos (ξ * x)) by
          funext x
          ring,
      integral_const_mul, integral_shift_cos hg t ξ]
  simp_rw [hinner]
  have hsplit : (fun t : ℝ ↦ f t *
      (cosineTransform g ξ * Real.cos (ξ * t) +
        sineTransform g ξ * Real.sin (ξ * t))) =
      fun t ↦ cosineTransform g ξ * (f t * Real.cos (ξ * t)) +
        sineTransform g ξ * (f t * Real.sin (ξ * t)) := by
    funext t
    ring
  rw [hsplit, integral_add
    ((integrable_mul_cos hf ξ).const_mul _)
    ((integrable_mul_sin hf ξ).const_mul _),
    integral_const_mul, integral_const_mul]
  simp only [cosineTransform, sineTransform]
  ring

/-- Fubini/translation identity for the sine transform of a correlation in
the orientation `g (t + x)`. -/
theorem sineTransform_correlation
    {f g : ℝ → ℝ} (hmf : Measurable f) (hmg : Measurable g)
    (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    sineTransform (fun x ↦ ∫ t, f t * g (t + x)) ξ =
      cosineTransform f ξ * sineTransform g ξ -
        sineTransform f ξ * cosineTransform g ξ := by
  rw [sineTransform]
  simp_rw [← integral_mul_const]
  rw [← integral_integral_swap
    (integrable_correlation_sin_kernel hmf hmg hf hg ξ)]
  have hinner : ∀ t : ℝ,
      (∫ x, (f t * g (t + x)) * Real.sin (ξ * x)) =
        f t * (sineTransform g ξ * Real.cos (ξ * t) -
          cosineTransform g ξ * Real.sin (ξ * t)) := by
    intro t
    rw [show (fun x : ℝ ↦ (f t * g (t + x)) * Real.sin (ξ * x)) =
        fun x ↦ f t * (g (t + x) * Real.sin (ξ * x)) by
          funext x
          ring,
      integral_const_mul, integral_shift_sin hg t ξ]
  simp_rw [hinner]
  have hsplit : (fun t : ℝ ↦ f t *
      (sineTransform g ξ * Real.cos (ξ * t) -
        cosineTransform g ξ * Real.sin (ξ * t))) =
      fun t ↦ sineTransform g ξ * (f t * Real.cos (ξ * t)) -
        cosineTransform g ξ * (f t * Real.sin (ξ * t)) := by
    funext t
    ring
  rw [hsplit, integral_sub
    ((integrable_mul_cos hf ξ).const_mul _)
    ((integrable_mul_sin hf ξ).const_mul _),
    integral_const_mul, integral_const_mul]
  simp only [cosineTransform, sineTransform]
  ring

theorem complement_cosineTransform {f : ℝ → ℝ} (hf : Admissible f) (ξ : ℝ) :
    cosineTransform (complementProfile f) ξ =
      2 * intervalHalfCosineTransform ξ - cosineTransform f ξ := by
  rw [cosineTransform, show (fun x ↦ complementProfile f x * Real.cos (ξ * x)) =
      fun x ↦ activeInterval x * Real.cos (ξ * x) - f x * Real.cos (ξ * x) by
        funext x
        simp [complementProfile]
        ring]
  rw [integral_sub (integrable_mul_cos integrable_activeInterval ξ)
    (integrable_mul_cos (admissible_integrable hf) ξ)]
  simp [intervalHalfCosineTransform, cosineTransform]
  ring

theorem complement_sineTransform {f : ℝ → ℝ} (hf : Admissible f) (ξ : ℝ) :
    sineTransform (complementProfile f) ξ = -sineTransform f ξ := by
  rw [sineTransform, show (fun x ↦ complementProfile f x * Real.sin (ξ * x)) =
      fun x ↦ activeInterval x * Real.sin (ξ * x) - f x * Real.sin (ξ * x) by
        funext x
        simp [complementProfile]
        ring]
  rw [integral_sub (integrable_mul_sin integrable_activeInterval ξ)
    (integrable_mul_sin (admissible_integrable hf) ξ)]
  change (∫ x, activeInterval x * Real.sin (ξ * x)) -
      (∫ x, f x * Real.sin (ξ * x)) = -sineTransform f ξ
  rw [← sineTransform, activeInterval_sineTransform]
  simp [sineTransform]

/-- Exact cosine-transform identity for the overlap. -/
theorem overlap_cosineTransform {f : ℝ → ℝ} (hf : Admissible f) (ξ : ℝ) :
    cosineTransform (overlap f) ξ =
      2 * intervalHalfCosineTransform ξ * cosineTransform f ξ -
        cosineTransform f ξ ^ 2 - sineTransform f ξ ^ 2 := by
  change cosineTransform (fun x ↦ ∫ t, f t * complementProfile f (t + x)) ξ = _
  rw [cosineTransform_correlation hf.1 (complementProfile_measurable hf)
    (admissible_integrable hf) (complementProfile_integrable hf) ξ,
    complement_cosineTransform hf ξ, complement_sineTransform hf ξ]
  ring

/-- Exact sine-transform identity for the overlap. -/
theorem overlap_sineTransform {f : ℝ → ℝ} (hf : Admissible f) (ξ : ℝ) :
    sineTransform (overlap f) ξ =
      -2 * intervalHalfCosineTransform ξ * sineTransform f ξ := by
  change sineTransform (fun x ↦ ∫ t, f t * complementProfile f (t + x)) ξ = _
  rw [sineTransform_correlation hf.1 (complementProfile_measurable hf)
    (admissible_integrable hf) (complementProfile_integrable hf) ξ,
    complement_cosineTransform hf ξ, complement_sineTransform hf ξ]
  ring

/-- Certificate-facing form of the cosine identity, with the interval factor
written as the unnormalized real sinc. -/
theorem overlap_cosineTransform_sinc {f : ℝ → ℝ} (hf : Admissible f) (ξ : ℝ) :
    cosineTransform (overlap f) ξ =
      2 * Real.sinc ξ * cosineTransform f ξ - cosineTransform f ξ ^ 2 -
        sineTransform f ξ ^ 2 := by
  simpa only [intervalHalfCosineTransform_eq_sinc] using overlap_cosineTransform hf ξ

/-- Certificate-facing form of the sine identity. -/
theorem overlap_sineTransform_sinc {f : ℝ → ℝ} (hf : Admissible f) (ξ : ℝ) :
    sineTransform (overlap f) ξ = -2 * Real.sinc ξ * sineTransform f ξ := by
  simpa only [intervalHalfCosineTransform_eq_sinc] using overlap_sineTransform hf ξ

/-- The analytic transforms instantiate the phase-support inequality at every
real frequency. -/
theorem overlap_phaseSupport {f : ℝ → ℝ} (hf : Admissible f)
    (ξ α β : ℝ) (hα : 0 < α) :
    α * cosineTransform (overlap f) ξ + β * sineTransform (overlap f) ξ ≤
      intervalHalfCosineTransform ξ ^ 2 * (α + β ^ 2 / α) := by
  rw [overlap_cosineTransform hf ξ, overlap_sineTransform hf ξ]
  exact phase_support_sub (intervalHalfCosineTransform ξ)
    (cosineTransform f ξ) (sineTransform f ξ) α β hα

/-- The exact support inequality used by each certificate atom, valid also at
zeros of sinc and at frequency zero. -/
theorem overlap_phaseSupport_sinc {f : ℝ → ℝ} (hf : Admissible f)
    (ξ α β : ℝ) (hα : 0 < α) :
    α * cosineTransform (overlap f) ξ + β * sineTransform (overlap f) ξ ≤
      Real.sinc ξ ^ 2 * (α + β ^ 2 / α) := by
  simpa only [intervalHalfCosineTransform_eq_sinc] using
    overlap_phaseSupport hf ξ α β hα

end

end ErdosMinimum
