import UncertaintyUpperBound.SelfFourierCertificate
import UncertaintyUpperBound.TailCertificate
import UncertaintyUpperBound.SignUncertainty
import Mathlib.Analysis.Real.Pi.Bounds

namespace UncertaintyUpperBound

open MeasureTheory Polynomial
open scoped FourierTransform

noncomputable def adjustedWitnessQ : ℚ[X] :=
  polynomialOfArray selfFourierCoefficients

lemma selfFourierCoefficients_size : selfFourierCoefficients.size = 227 := by
  native_decide

lemma adjustedWitnessQ_eq :
    adjustedWitnessQ = -witnessPolynomialQ - C (1 / 1000000 : ℚ) := by
  ext k
  rw [adjustedWitnessQ, coeff_polynomialOfArray, coeff_sub, coeff_neg,
    witnessPolynomialQ, coeff_polynomialOfArray, coeff_C]
  by_cases hk : k < selfFourierCoefficients.size
  · have hkPower : k < CertificateData.powerCoefficients.size := by
      rw [power_coefficients_size]
      simpa [selfFourierCoefficients_size] using hk
    rw [if_pos hk, if_pos hkPower]
    rw [getElem!_pos selfFourierCoefficients k hk]
    simp only [selfFourierCoefficients, Array.getElem_map, Array.getElem_range]
  · have hkPower : ¬ k < CertificateData.powerCoefficients.size := by
      rw [power_coefficients_size]
      simpa [selfFourierCoefficients_size] using hk
    rw [if_neg hk, if_neg hkPower]
    have hk0 : k ≠ 0 := by
      intro h
      subst k
      have : 0 < selfFourierCoefficients.size := by native_decide
      exact hk this
    simp [hk0]

noncomputable def adjustedEval (t : ℝ) : ℝ :=
  adjustedWitnessQ.eval₂ (algebraMap ℚ ℝ) t

lemma adjustedEval_eq (t : ℝ) :
    adjustedEval t = -evalWitness t - 1 / 1000000 := by
  change adjustedWitnessQ.eval₂ (algebraMap ℚ ℝ) t =
    -witnessPolynomialQ.eval₂ (algebraMap ℚ ℝ) t - 1 / 1000000
  rw [adjustedWitnessQ_eq]
  simp only [eval₂_sub, eval₂_neg, eval₂_C]
  norm_num

lemma ofReal_eval₂ (p : ℚ[X]) (t : ℝ) :
    ((p.eval₂ (algebraMap ℚ ℝ) t : ℝ) : ℂ) =
      p.eval₂ (algebraMap ℚ ℂ) (t : ℂ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n c =>
      simp [eval₂_monomial]

noncomputable def witnessFunction (x : ℝ) : ℝ :=
  adjustedEval (2 * Real.pi * x ^ 2) * Real.exp (-Real.pi * x ^ 2)

lemma complex_witness_shape :
    (fun x : ℝ => (witnessFunction x : ℂ)) =
      polyGaussian (radialEmbed (adjustedWitnessQ.map (algebraMap ℚ ℂ))) := by
  funext x
  simp only [witnessFunction, adjustedEval, polyGaussian, radialEmbed, gaussian, eval_comp, eval_mul,
    eval_C, eval_pow, eval_X, Complex.ofReal_mul, Complex.ofReal_exp]
  rw [eval_map]
  rw [ofReal_eval₂]
  congr 2 <;> push_cast <;> ring

theorem witness_integrable : Integrable witnessFunction := by
  have hc : Integrable (fun x : ℝ => (witnessFunction x : ℂ)) := by
    rw [complex_witness_shape]
    exact integrable_polyGaussian _
  have hr := Complex.reCLM.integrable_comp hc
  simpa using hr

theorem witness_self_fourier :
    𝓕 (fun x : ℝ => (witnessFunction x : ℂ)) =
      fun x : ℝ => (witnessFunction x : ℂ) := by
  rw [complex_witness_shape, fourier_radialTransform]
  have hfixQ : radialTransform adjustedWitnessQ = adjustedWitnessQ := by
    exact exact_self_fourier_polynomial
  have hfixC : radialTransform (adjustedWitnessQ.map (algebraMap ℚ ℂ)) =
      adjustedWitnessQ.map (algebraMap ℚ ℂ) := by
    rw [← radialTransform_map, hfixQ]
  rw [hfixC, ← complex_witness_shape]

theorem witness_even : IsEvenFunction witnessFunction := by
  intro x
  simp [witnessFunction]

lemma evalWitness_zero : evalWitness 0 = 0 := by
  unfold evalWitness
  rw [show (0 : ℝ) = Rat.castHom ℝ 0 by simp, eval₂_at_apply, witness_at_zero]

theorem witness_origin_negative : witnessFunction 0 < 0 := by
  rw [witnessFunction, adjustedEval_eq]
  simp [evalWitness_zero]

noncomputable def certifiedRadius : ℝ :=
  Real.sqrt ((1213 / 625 : ℝ) / (2 * Real.pi))

lemma certifiedRadius_nonneg : 0 ≤ certifiedRadius := Real.sqrt_nonneg _

lemma certifiedRadius_pos : 0 < certifiedRadius := by
  apply Real.sqrt_pos.2
  positivity

lemma certifiedRadius_sq :
    certifiedRadius ^ 2 = (1213 / 625 : ℝ) / (2 * Real.pi) := by
  apply Real.sq_sqrt
  positivity

theorem witness_tail : IsTailRadius witnessFunction certifiedRadius := by
  refine ⟨certifiedRadius_pos, ?_⟩
  intro x hx
  have hsquares : certifiedRadius ^ 2 ≤ |x| ^ 2 :=
    (sq_le_sq₀ certifiedRadius_nonneg (abs_nonneg x)).2 hx
  rw [certifiedRadius_sq, sq_abs] at hsquares
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hT : (1213 / 625 : ℝ) ≤ 2 * Real.pi * x ^ 2 := by
    have hm := mul_le_mul_of_nonneg_left hsquares hpi.le
    field_simp [Real.pi_ne_zero] at hm ⊢
    nlinarith
  have hpoly := witness_polynomial_whole_tail hT
  rw [witnessFunction, adjustedEval_eq]
  have hexp : 0 < Real.exp (-Real.pi * x ^ 2) := Real.exp_pos _
  have hadj : 0 < -evalWitness (2 * Real.pi * x ^ 2) - 1 / 1000000 := by
    linarith
  exact mul_nonneg hadj.le hexp.le

noncomputable def uncertaintyWitness : AdmissiblePair where
  f := witnessFunction
  fourier := witnessFunction
  f_integrable := witness_integrable
  fourier_integrable := witness_integrable
  f_even := witness_even
  fourier_even := witness_even
  f_nonzero := by
    intro hzero
    have hnegative := witness_origin_negative
    rw [hzero] at hnegative
    simp at hnegative
  transform_eq := witness_self_fourier
  f_origin_negative := witness_origin_negative
  fourier_origin_negative := witness_origin_negative
  f_eventually_nonnegative := ⟨certifiedRadius, witness_tail⟩
  fourier_eventually_nonnegative := ⟨certifiedRadius, witness_tail⟩

theorem certified_ratio_lt :
    (1213 / 625 : ℝ) / (2 * Real.pi) < 3089 / 10000 := by
  apply (div_lt_iff₀ (mul_pos (by norm_num) Real.pi_pos)).2
  have hpi := Real.pi_gt_d4
  norm_num at hpi ⊢
  nlinarith

end UncertaintyUpperBound
