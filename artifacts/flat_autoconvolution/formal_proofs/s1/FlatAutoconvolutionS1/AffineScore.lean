import FlatAutoconvolutionS1.Definitions
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Exact affine covariance of autoconvolution and invariance of the score. -/

open scoped Convolution ENNReal
open MeasureTheory

namespace FlatAutoconvolutionS1

/-- Amplitude scaling followed by translation and positive spatial dilation. -/
noncomputable def affineSignal (a origin mesh : ℝ) (f : Signal) : Signal :=
  fun x ↦ a * f ((x - origin) / mesh)

theorem autoconvolution_affineSignal (a origin mesh : ℝ) (hmesh : 0 < mesh)
    (f : Signal) (x : ℝ) :
    autoconvolution (affineSignal a origin mesh f) x =
      a ^ 2 * mesh * autoconvolution f ((x - 2 * origin) / mesh) := by
  let K : ℝ → ℝ := fun y ↦ f y * f ((x - 2 * origin) / mesh - y)
  rw [autoconvolution, MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, affineSignal]
  calc
    (∫ t, (a * f ((t - origin) / mesh)) *
        (a * f ((x - t - origin) / mesh))) =
        a ^ 2 * ∫ t, K ((t - origin) / mesh) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      dsimp [K]
      have harg : (x - t - origin) / mesh =
          (x - 2 * origin) / mesh - (t - origin) / mesh := by
        field_simp [hmesh.ne']
        ring
      rw [harg]
      ring
    _ = a ^ 2 * ∫ t, K (t / mesh) := by
      rw [show (fun t ↦ K ((t - origin) / mesh)) =
          fun t ↦ (fun u ↦ K (u / mesh)) (t - origin) by rfl]
      congr 1
      exact integral_sub_right_eq_self (fun u ↦ K (u / mesh)) origin
    _ = a ^ 2 * (|mesh| * ∫ y, K y) := by
      rw [Measure.integral_comp_div]
      rfl
    _ = a ^ 2 * mesh * autoconvolution f ((x - 2 * origin) / mesh) := by
      rw [abs_of_pos hmesh]
      rw [autoconvolution, MeasureTheory.convolution_def]
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      dsimp [K]
      ring

theorem convolutionEnergy_affineSignal (a origin mesh : ℝ) (hmesh : 0 < mesh)
    (f : Signal) :
    convolutionEnergy (affineSignal a origin mesh f) =
      a ^ 4 * mesh ^ 3 * convolutionEnergy f := by
  unfold convolutionEnergy
  simp_rw [autoconvolution_affineSignal a origin mesh hmesh f]
  let K : ℝ → ℝ := fun y ↦ (autoconvolution f y) ^ 2
  calc
    (∫ x, (a ^ 2 * mesh * autoconvolution f ((x - 2 * origin) / mesh)) ^ 2) =
        (a ^ 2 * mesh) ^ 2 * ∫ x, K ((x - 2 * origin) / mesh) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [K]
      ring
    _ = (a ^ 2 * mesh) ^ 2 * ∫ x, K (x / mesh) := by
      rw [show (fun x ↦ K ((x - 2 * origin) / mesh)) =
          fun x ↦ (fun u ↦ K (u / mesh)) (x - 2 * origin) by rfl]
      congr 1
      exact integral_sub_right_eq_self (fun u ↦ K (u / mesh)) (2 * origin)
    _ = (a ^ 2 * mesh) ^ 2 * (|mesh| * ∫ y, K y) := by
      rw [Measure.integral_comp_div]
      rfl
    _ = a ^ 4 * mesh ^ 3 * ∫ y, (autoconvolution f y) ^ 2 := by
      rw [abs_of_pos hmesh]
      dsimp [K]
      ring

theorem convolutionMass_affineSignal (a origin mesh : ℝ) (hmesh : 0 < mesh)
    (f : Signal) :
    convolutionMass (affineSignal a origin mesh f) =
      a ^ 2 * mesh ^ 2 * convolutionMass f := by
  unfold convolutionMass
  simp_rw [autoconvolution_affineSignal a origin mesh hmesh f]
  let K : ℝ → ℝ := fun y ↦ |autoconvolution f y|
  have hfactor : 0 ≤ a ^ 2 * mesh := mul_nonneg (sq_nonneg a) hmesh.le
  calc
    (∫ x, |a ^ 2 * mesh * autoconvolution f ((x - 2 * origin) / mesh)|) =
        (a ^ 2 * mesh) * ∫ x, K ((x - 2 * origin) / mesh) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      dsimp [K]
      rw [abs_mul, abs_of_nonneg hfactor]
    _ = (a ^ 2 * mesh) * ∫ x, K (x / mesh) := by
      rw [show (fun x ↦ K ((x - 2 * origin) / mesh)) =
          fun x ↦ (fun u ↦ K (u / mesh)) (x - 2 * origin) by rfl]
      congr 1
      exact integral_sub_right_eq_self (fun u ↦ K (u / mesh)) (2 * origin)
    _ = (a ^ 2 * mesh) * (|mesh| * ∫ y, K y) := by
      rw [Measure.integral_comp_div]
      rfl
    _ = a ^ 2 * mesh ^ 2 * ∫ y, |autoconvolution f y| := by
      rw [abs_of_pos hmesh]
      dsimp [K]
      ring

theorem eLpNormEssSup_comp_sub_right (f : Signal) (d : ℝ) :
    eLpNormEssSup (fun x ↦ f (x - d)) volume = eLpNormEssSup f volume := by
  have hmap := (MeasurableEquiv.subRight d).measurableEmbedding.eLpNormEssSup_map_measure
      (g := f) (μ := volume)
  change eLpNormEssSup f (Measure.map (fun x : ℝ ↦ x - d) volume) =
      eLpNormEssSup (fun x : ℝ ↦ f (x - d)) volume at hmap
  rw [(measurePreserving_sub_right volume d).map_eq] at hmap
  exact hmap.symm

theorem eLpNormEssSup_comp_div (f : Signal) (mesh : ℝ) (hmesh : 0 < mesh) :
    eLpNormEssSup (fun x ↦ f (x / mesh)) volume = eLpNormEssSup f volume := by
  let e : ℝ ≃ᵐ ℝ :=
    (Homeomorph.mulRight₀ mesh⁻¹ (inv_ne_zero hmesh.ne')).toMeasurableEquiv
  have hemb : MeasurableEmbedding (fun x : ℝ ↦ x / mesh) := by
    simpa [e, div_eq_mul_inv] using e.measurableEmbedding
  calc
    eLpNormEssSup (fun x ↦ f (x / mesh)) volume =
        eLpNormEssSup f (Measure.map (fun x : ℝ ↦ x / mesh) volume) :=
      (hemb.eLpNormEssSup_map_measure (g := f) (μ := volume)).symm
    _ = eLpNormEssSup f (ENNReal.ofReal |mesh| • volume) := by
      rw [show (fun x : ℝ ↦ x / mesh) = fun x ↦ x * mesh⁻¹ by funext x; rfl]
      rw [Real.map_volume_mul_right (inv_ne_zero hmesh.ne')]
      congr 2
      rw [inv_inv, abs_of_pos hmesh]
    _ = eLpNormEssSup f volume := by
      rw [eLpNormEssSup_smul_measure]
      simp [hmesh.ne']

theorem eLpNorm_top_comp_affine (f : Signal) (origin mesh : ℝ) (hmesh : 0 < mesh) :
    eLpNorm (fun x ↦ f ((x - origin) / mesh)) ⊤ volume = eLpNorm f ⊤ volume := by
  simp only [eLpNorm_exponent_top]
  calc
    eLpNormEssSup (fun x ↦ f ((x - origin) / mesh)) volume =
        eLpNormEssSup (fun x ↦ f (x / mesh)) volume :=
      eLpNormEssSup_comp_sub_right (fun x ↦ f (x / mesh)) origin
    _ = eLpNormEssSup f volume := eLpNormEssSup_comp_div f mesh hmesh

theorem convolutionPeak_affineSignal (a origin mesh : ℝ) (hmesh : 0 < mesh)
    (f : Signal) :
    convolutionPeak (affineSignal a origin mesh f) =
      a ^ 2 * mesh * convolutionPeak f := by
  unfold convolutionPeak
  have hfactor : 0 ≤ a ^ 2 * mesh := mul_nonneg (sq_nonneg a) hmesh.le
  rw [show autoconvolution (affineSignal a origin mesh f) =
      fun x ↦ (a ^ 2 * mesh) * autoconvolution f ((x - 2 * origin) / mesh) by
    funext x
    exact autoconvolution_affineSignal a origin mesh hmesh f x]
  rw [show (fun x ↦ (a ^ 2 * mesh) * autoconvolution f ((x - 2 * origin) / mesh)) =
      (a ^ 2 * mesh) • (fun x ↦ autoconvolution f ((x - 2 * origin) / mesh)) by rfl]
  rw [eLpNorm_const_smul]
  rw [eLpNorm_top_comp_affine (autoconvolution f) (2 * origin) mesh hmesh]
  rw [ENNReal.toReal_mul]
  simp only [Real.enorm_eq_ofReal_abs, abs_of_nonneg hfactor]
  rw [ENNReal.toReal_ofReal hfactor]

/-- The score is invariant under a nonzero amplitude, translation, and positive
spatial dilation. -/
theorem score_affineSignal (a origin mesh : ℝ) (ha : a ≠ 0) (hmesh : 0 < mesh)
    (f : Signal) : score (affineSignal a origin mesh f) = score f := by
  rw [score, convolutionEnergy_affineSignal a origin mesh hmesh,
    convolutionMass_affineSignal a origin mesh hmesh,
    convolutionPeak_affineSignal a origin mesh hmesh, score]
  have ham : a ^ 4 * mesh ^ 3 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 4 ha) (pow_ne_zero 3 hmesh.ne')
  field_simp

end FlatAutoconvolutionS1
