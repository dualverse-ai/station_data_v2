import ErdosMinimum.OverlapBounds
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Elementary analytic bridge for minimum overlap

This file records consequences of the genuine continuum definition in
`ErdosMinimum.Problem`.  In particular, admissible profiles and their
complements are measurable, integrable, supported on `[-1,1]`, and have
controlled first moments.  Reflection is treated pointwise, so these results
do not restrict the paper's measurable class to continuous or even profiles.
-/

open MeasureTheory

namespace ErdosMinimum

noncomputable section

/-- Reflection in the origin. -/
def reflectProfile (f : ℝ → ℝ) (x : ℝ) : ℝ := f (-x)

/-- The ordinary first moment of a profile. -/
noncomputable def profileFirstMoment (f : ℝ → ℝ) : ℝ :=
  ∫ x, x * f x

/-- The first moment of the overlap density appearing in the paper. -/
noncomputable def overlapFirstMoment (f : ℝ → ℝ) : ℝ :=
  ∫ x, x * overlap f x

theorem activeInterval_eq_zero_of_not_mem {x : ℝ}
    (hx : x ∉ Set.Icc (-1 : ℝ) 1) : activeInterval x = 0 := by
  simp [activeInterval, hx]

theorem activeInterval_neg (x : ℝ) : activeInterval (-x) = activeInterval x := by
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · have hnx : -x ∈ Set.Icc (-1 : ℝ) 1 := by
      constructor <;> linarith [hx.1, hx.2]
    simp [activeInterval, hx, hnx]
  · have hnx : -x ∉ Set.Icc (-1 : ℝ) 1 := by
      intro h
      apply hx
      constructor <;> linarith [h.1, h.2]
    simp [activeInterval, hx, hnx]

theorem admissible_nonnegative {f : ℝ → ℝ} (hf : Admissible f) (x : ℝ) : 0 ≤ f x :=
  (hf.2.1 x).1

theorem admissible_le_activeInterval {f : ℝ → ℝ} (hf : Admissible f) (x : ℝ) :
    f x ≤ activeInterval x :=
  (hf.2.1 x).2

theorem admissible_eq_zero_of_not_mem {f : ℝ → ℝ} (hf : Admissible f)
    {x : ℝ} (hx : x ∉ Set.Icc (-1 : ℝ) 1) : f x = 0 := by
  have hle : f x ≤ 0 := by
    simpa [activeInterval_eq_zero_of_not_mem hx] using admissible_le_activeInterval hf x
  exact le_antisymm hle (admissible_nonnegative hf x)

theorem measurable_activeInterval : Measurable activeInterval := by
  exact measurable_const.indicator measurableSet_Icc

theorem admissible_integrable {f : ℝ → ℝ} (hf : Admissible f) : Integrable f := by
  apply integrable_activeInterval.mono hf.1.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (admissible_nonnegative hf x),
    abs_of_nonneg]
  · exact admissible_le_activeInterval hf x
  · by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1 <;> simp [activeInterval, hx]

theorem complementProfile_nonnegative {f : ℝ → ℝ} (hf : Admissible f) (x : ℝ) :
    0 ≤ complementProfile f x := by
  exact sub_nonneg.mpr (admissible_le_activeInterval hf x)

theorem complementProfile_le_activeInterval {f : ℝ → ℝ} (hf : Admissible f) (x : ℝ) :
    complementProfile f x ≤ activeInterval x := by
  dsimp [complementProfile]
  linarith [admissible_nonnegative hf x]

theorem complementProfile_eq_zero_of_not_mem {f : ℝ → ℝ} (hf : Admissible f)
    {x : ℝ} (hx : x ∉ Set.Icc (-1 : ℝ) 1) : complementProfile f x = 0 := by
  rw [complementProfile, activeInterval_eq_zero_of_not_mem hx,
    admissible_eq_zero_of_not_mem hf hx, sub_zero]

theorem complementProfile_measurable {f : ℝ → ℝ} (hf : Admissible f) :
    Measurable (complementProfile f) := by
  exact measurable_activeInterval.sub hf.1

theorem complementProfile_integrable {f : ℝ → ℝ} (hf : Admissible f) :
    Integrable (complementProfile f) := by
  apply integrable_activeInterval.mono (complementProfile_measurable hf).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (complementProfile_nonnegative hf x),
    abs_of_nonneg]
  · exact complementProfile_le_activeInterval hf x
  · by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1 <;> simp [activeInterval, hx]

theorem integral_complementProfile {f : ℝ → ℝ} (hf : Admissible f) :
    ∫ x, complementProfile f x = 1 := by
  rw [show (fun x ↦ complementProfile f x) = fun x ↦ activeInterval x - f x by rfl,
    integral_sub integrable_activeInterval (admissible_integrable hf),
    hf.2.2]
  have hactive : ∫ x : ℝ, activeInterval x = 2 := by
    rw [show (fun x : ℝ ↦ activeInterval x) =
        (Set.Icc (-1 : ℝ) 1).indicator (fun _ ↦ (1 : ℝ)) by rfl]
    rw [integral_indicator_const (1 : ℝ) measurableSet_Icc]
    norm_num [Measure.real, Real.volume_Icc]
  linarith

theorem profileFirstMoment_integrable {f : ℝ → ℝ} (hf : Admissible f) :
    Integrable (fun x ↦ x * f x) := by
  apply integrable_activeInterval.mono (measurable_id.mul hf.1).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
  · simp only [id_eq, abs_mul, abs_of_nonneg (admissible_nonnegative hf x)]
    have hax : |x| ≤ 1 := abs_le.mpr hx
    have hfa : f x ≤ 1 := by
      simpa [activeInterval, hx] using admissible_le_activeInterval hf x
    norm_num [activeInterval, hx]
    calc
      |x| * f x ≤ 1 * f x := mul_le_mul_of_nonneg_right hax (admissible_nonnegative hf x)
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hfa (by norm_num)
      _ = 1 := by norm_num
  · rw [admissible_eq_zero_of_not_mem hf hx]
    simp [activeInterval, hx]

/-- The elementary bathtub estimate in this normalization. -/
theorem abs_profileFirstMoment_le_half {f : ℝ → ℝ} (hf : Admissible f) :
    |profileFirstMoment f| ≤ (1 : ℝ) / 2 := by
  let upper : ℝ → ℝ := Set.Icc (0 : ℝ) 1 |>.indicator (fun x ↦ x)
  let lower : ℝ → ℝ := Set.Icc (-1 : ℝ) 0 |>.indicator (fun x ↦ x)
  have hiUpper : Integrable upper := by
    exact continuousOn_id.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hiLower : Integrable lower := by
    exact continuousOn_id.integrableOn_Icc.integrable_indicator measurableSet_Icc
  have hpointUpper : ∀ x : ℝ, x * f x ≤ upper x := by
    intro x
    by_cases hxneg : x < 0
    · have hxout : x ∉ Set.Icc (0 : ℝ) 1 := by simp [hxneg]
      simp [upper, hxout]
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_lt hxneg) (admissible_nonnegative hf x)
    · by_cases hxone : x ≤ 1
      · have hxmem : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_not_gt hxneg, hxone⟩
        have hxi : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, hxone⟩
        have hfa : f x ≤ 1 := by
          simpa [activeInterval, hxi] using admissible_le_activeInterval hf x
        simp only [upper, Set.indicator_of_mem hxmem]
        nlinarith [admissible_nonnegative hf x]
      · have hxout : x ∉ Set.Icc (-1 : ℝ) 1 := by simp [not_le.mp hxone]
        have hxu : x ∉ Set.Icc (0 : ℝ) 1 := by simp [not_le.mp hxone]
        simp [upper, hxu, admissible_eq_zero_of_not_mem hf hxout]
  have hpointLower : ∀ x : ℝ, lower x ≤ x * f x := by
    intro x
    by_cases hxlt : x < -1
    · have hxout : x ∉ Set.Icc (-1 : ℝ) 1 := by simp [hxlt]
      simp [lower, hxlt, admissible_eq_zero_of_not_mem hf hxout]
    · by_cases hxnonpos : x ≤ 0
      · have hxmem : x ∈ Set.Icc (-1 : ℝ) 0 := ⟨le_of_not_gt hxlt, hxnonpos⟩
        have hxi : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨hxmem.1, by linarith⟩
        have hfa : f x ≤ 1 := by
          simpa [activeInterval, hxi] using admissible_le_activeInterval hf x
        simp only [lower, Set.indicator_of_mem hxmem]
        nlinarith [admissible_nonnegative hf x]
      · have hxout : x ∉ Set.Icc (-1 : ℝ) 0 := by simp [not_le.mp hxnonpos]
        simp [lower, hxout]
        exact mul_nonneg (by linarith) (admissible_nonnegative hf x)
  have hpos0 : profileFirstMoment f ≤ ∫ x, upper x := by
    exact integral_mono (profileFirstMoment_integrable hf) hiUpper hpointUpper
  have hneg0 : (∫ x, lower x) ≤ profileFirstMoment f := by
    exact integral_mono hiLower (profileFirstMoment_integrable hf) hpointLower
  have hUpper : (∫ x, upper x) = (1 : ℝ) / 2 := by
    rw [show (∫ x, upper x) = ∫ x in Set.Icc (0 : ℝ) 1, x by
      simp [upper, integral_indicator measurableSet_Icc]]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    norm_num [integral_id]
  have hLower : (∫ x, lower x) = -((1 : ℝ) / 2) := by
    rw [show (∫ x, lower x) = ∫ x in Set.Icc (-1 : ℝ) 0, x by
      simp [lower, integral_indicator measurableSet_Icc]]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    norm_num [integral_id]
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- The algebraic overlap moment used after the correlation-moment identity. -/
noncomputable def algebraicOverlapFirstMoment (f : ℝ → ℝ) : ℝ :=
  -2 * profileFirstMoment f

theorem abs_algebraicOverlapFirstMoment_le_one {f : ℝ → ℝ} (hf : Admissible f) :
    |algebraicOverlapFirstMoment f| ≤ 1 := by
  rw [algebraicOverlapFirstMoment, abs_mul]
  norm_num
  nlinarith [abs_profileFirstMoment_le_half hf]

theorem reflectProfile_measurable {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (reflectProfile f) := by
  exact hf.comp measurable_neg

theorem reflectProfile_admissible {f : ℝ → ℝ} (hf : Admissible f) :
    Admissible (reflectProfile f) := by
  letI : Measure.IsNegInvariant (volume : Measure ℝ) :=
    ⟨Measure.map_neg_eq_self volume⟩
  refine ⟨reflectProfile_measurable hf.1, ?_, ?_⟩
  · intro x
    constructor
    · exact admissible_nonnegative hf (-x)
    · simpa [reflectProfile, activeInterval_neg] using admissible_le_activeInterval hf (-x)
  · simpa [reflectProfile] using (integral_neg_eq_self f volume).trans hf.2.2

theorem complementProfile_reflect (f : ℝ → ℝ) (x : ℝ) :
    complementProfile (reflectProfile f) x = complementProfile f (-x) := by
  simp [complementProfile, reflectProfile, activeInterval_neg]

theorem profileFirstMoment_reflect {f : ℝ → ℝ} (_hf : Admissible f) :
    profileFirstMoment (reflectProfile f) = -profileFirstMoment f := by
  letI : Measure.IsNegInvariant (volume : Measure ℝ) :=
    ⟨Measure.map_neg_eq_self volume⟩
  have h := integral_neg_eq_self (fun x : ℝ ↦ (-x) * f x) volume
  simpa [profileFirstMoment, reflectProfile, integral_neg] using h

theorem algebraicOverlapFirstMoment_reflect {f : ℝ → ℝ} (hf : Admissible f) :
    algebraicOverlapFirstMoment (reflectProfile f) = -algebraicOverlapFirstMoment f := by
  simp [algebraicOverlapFirstMoment, profileFirstMoment_reflect hf]

theorem overlap_reflect (f : ℝ → ℝ) (x : ℝ) :
    overlap (reflectProfile f) x = overlap f (-x) := by
  letI : Measure.IsNegInvariant (volume : Measure ℝ) :=
    ⟨Measure.map_neg_eq_self volume⟩
  have h := integral_neg_eq_self
    (fun t : ℝ ↦ f t * complementProfile f (t - x)) volume
  simpa [overlap, reflectProfile, complementProfile_reflect, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using h

theorem overlapFirstMoment_reflect (f : ℝ → ℝ) :
    overlapFirstMoment (reflectProfile f) = -overlapFirstMoment f := by
  letI : Measure.IsNegInvariant (volume : Measure ℝ) :=
    ⟨Measure.map_neg_eq_self volume⟩
  have h := integral_neg_eq_self (fun x : ℝ ↦ (-x) * overlap f x) volume
  simpa [overlapFirstMoment, overlap_reflect, integral_neg] using h

theorem overlapMaximum_reflect (f : ℝ → ℝ) :
    overlapMaximum (reflectProfile f) = overlapMaximum f := by
  unfold overlapMaximum
  apply congrArg sSup
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨-x, by simp [overlap_reflect]⟩
  · rintro ⟨x, rfl⟩
    exact ⟨-x, by simp [overlap_reflect]⟩

end

end ErdosMinimum
