import FlatAutoconvolutionS1.Definitions

/-!
# Positivity and mass of a nonnegative autoconvolution
-/

open scoped Convolution ENNReal
open MeasureTheory Filter

namespace FlatAutoconvolutionS1

theorem autoconvolution_nonneg
    {f : Signal} (hf : 0 ≤ᵐ[volume] f) (t : ℝ) :
    0 ≤ autoconvolution f t := by
  rw [autoconvolution, convolution_def]
  apply MeasureTheory.integral_nonneg_of_ae
  have htranslated : 0 ≤ᵐ[volume] (fun x : ℝ => f (t - x)) :=
    (quasiMeasurePreserving_sub_left_of_right_invariant volume t).ae hf
  filter_upwards [hf, htranslated] with x hx htx
  simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using mul_nonneg hx htx

theorem autoconvolution_integrable {f : Signal} (hf : Integrable f) :
    Integrable (autoconvolution f) := by
  exact hf.integrable_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf

theorem integral_eq_integral_abs_of_ae_nonneg
    {f : Signal} (hf : 0 ≤ᵐ[volume] f) :
    (∫ x, f x) = ∫ x, |f x| := by
  apply integral_congr_ae
  filter_upwards [hf] with x hx
  exact (abs_of_nonneg hx).symm

theorem convolutionMass_eq_integral_sq
    {f : Signal} (hf_nonneg : 0 ≤ᵐ[volume] f) (hf_int : Integrable f) :
    convolutionMass f = (∫ x, f x) ^ 2 := by
  rw [convolutionMass]
  have hc_nonneg : 0 ≤ᵐ[volume] autoconvolution f :=
    Filter.Eventually.of_forall (autoconvolution_nonneg hf_nonneg)
  rw [integral_congr_ae (hc_nonneg.mono fun x hx => abs_of_nonneg hx)]
  rw [autoconvolution]
  simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, pow_two] using
    (integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) hf_int hf_int)

theorem Admissible.convolutionMass_pos {f : Signal} (hf : Admissible f) :
    0 < convolutionMass f := by
  rcases hf with ⟨hf_nonneg, hf_int, _hf_two, hf_ne⟩
  rw [convolutionMass_eq_integral_sq hf_nonneg hf_int]
  have hfi : 0 < ∫ x, f x := by
    rw [integral_eq_integral_abs_of_ae_nonneg hf_nonneg]
    exact hf_ne
  positivity

end FlatAutoconvolutionS1
