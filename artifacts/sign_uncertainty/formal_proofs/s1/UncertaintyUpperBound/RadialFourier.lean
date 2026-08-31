import UncertaintyUpperBound.FourierPolynomial

namespace UncertaintyUpperBound

open MeasureTheory Polynomial
open scoped FourierTransform

noncomputable def spatialDerivativePolynomial (p : ℂ[X]) : ℂ[X] :=
  p.derivative - C (2 * (Real.pi : ℂ)) * X * p

noncomputable def radialEmbed (p : ℂ[X]) : ℂ[X] :=
  p.comp (C (2 * (Real.pi : ℂ)) * X ^ 2)

noncomputable def radialOperator {R : Type*} [CommRing R] (p : R[X]) : R[X] :=
  (1 - X) * p + (4 * X - 2) * p.derivative - 4 * X * p.derivative.derivative

noncomputable def radialBasis {R : Type*} [CommRing R] : ℕ → R[X]
  | 0 => 1
  | n + 1 => radialOperator (radialBasis n)

noncomputable def radialTransform {R : Type*} [CommRing R] (p : R[X]) : R[X] :=
  p.sum fun n c => C c * radialBasis n

lemma deriv_const_mul_polyGaussian (c : ℂ) (p : ℂ[X]) :
    deriv (fun x : ℝ => c * polyGaussian p x) =
      fun x => c * polyGaussian (spatialDerivativePolynomial p) x := by
  funext x
  have h := (hasDerivAt_polyGaussian p x).const_mul c
  simpa [spatialDerivativePolynomial] using h.deriv

lemma fourier_X_mul_polyGaussian (p : ℂ[X]) :
    𝓕 (polyGaussian (X * p)) =
      fun x => Complex.I / (2 * Real.pi) * deriv (𝓕 (polyGaussian p)) x := by
  have hfun : polyGaussian (X * p) =
      fun x : ℝ => (x : ℂ) * polyGaussian p x := by
    funext x
    simp [polyGaussian]
    ring
  rw [hfun]
  exact fourier_mul_x p

lemma radialEmbed_X_mul (p : ℂ[X]) :
    radialEmbed (X * p) = C (2 * (Real.pi : ℂ)) * X ^ 2 * radialEmbed p := by
  simp only [radialEmbed, mul_comp, X_comp, C_mul, pow_two]

lemma derivative_radialEmbed (p : ℂ[X]) :
    (radialEmbed p).derivative =
      C (4 * (Real.pi : ℂ)) * X * radialEmbed p.derivative := by
  simp only [radialEmbed, derivative_comp, derivative_mul, derivative_C, derivative_pow,
    derivative_X, zero_mul, zero_add, one_mul]
  have hc : C (4 * (Real.pi : ℂ)) = C (2 * (Real.pi : ℂ)) * C 2 := by
    rw [← C_mul]
    congr 1
    ring
  rw [hc]
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, C_ofNat]
  ring

lemma spatialDerivative_radial (p : ℂ[X]) :
    spatialDerivativePolynomial (radialEmbed p) =
      C (2 * (Real.pi : ℂ)) * X * radialEmbed (2 * p.derivative - p) := by
  rw [spatialDerivativePolynomial, derivative_radialEmbed]
  simp only [radialEmbed, sub_comp, mul_comp, ofNat_comp]
  have hc : C (4 * (Real.pi : ℂ)) = C (2 * (Real.pi : ℂ)) * C 2 := by
    rw [← C_mul]
    congr 1
    ring
  rw [hc]
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, C_ofNat]
  ring

lemma spatialDerivative_radial_aux (p : ℂ[X]) :
    spatialDerivativePolynomial
        (C (2 * (Real.pi : ℂ)) * X * radialEmbed p) =
      C (2 * (Real.pi : ℂ)) *
        radialEmbed (p + 2 * X * p.derivative - X * p) := by
  rw [spatialDerivativePolynomial]
  simp only [derivative_mul, derivative_C, derivative_X, zero_mul, zero_add, one_mul,
    ]
  rw [derivative_radialEmbed]
  simp only [
    radialEmbed, add_comp, sub_comp, mul_comp, ofNat_comp, X_comp]
  have hc : C (4 * (Real.pi : ℂ)) = C (2 * (Real.pi : ℂ)) * C 2 := by
    rw [← C_mul]
    congr 1
    ring
  rw [hc]
  simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, C_ofNat]
  ring

lemma radialOperator_identity (p : ℂ[X]) :
    C (-(1 / (2 * (Real.pi : ℂ)))) *
        spatialDerivativePolynomial (spatialDerivativePolynomial (radialEmbed p)) =
      radialEmbed (radialOperator p) := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [spatialDerivative_radial, spatialDerivative_radial_aux]
  have hcancel : C (-(1 / (2 * (Real.pi : ℂ)))) * C (2 * (Real.pi : ℂ)) = -1 := by
    rw [← C_mul]
    have hs : -(1 / (2 * (Real.pi : ℂ))) * (2 * Real.pi) = -1 := by
      field_simp [hpi]
    rw [hs]
    simp
  rw [← mul_assoc, hcancel, neg_one_mul]
  simp only [radialEmbed]
  rw [← neg_comp]
  apply congrArg (fun q : ℂ[X] => q.comp (C (2 * (Real.pi : ℂ)) * X ^ 2))
  simp only [radialOperator, derivative_sub, derivative_mul, derivative_ofNat, derivative_X,
    zero_mul, zero_add, one_mul]
  ring

theorem fourier_radial_mul {p q : ℂ[X]}
    (h : 𝓕 (polyGaussian (radialEmbed p)) = polyGaussian (radialEmbed q)) :
    𝓕 (polyGaussian (radialEmbed (X * p))) =
      polyGaussian (radialEmbed (radialOperator q)) := by
  have hX :
      𝓕 (polyGaussian (X * radialEmbed p)) =
        fun x => Complex.I / (2 * Real.pi) *
          polyGaussian (spatialDerivativePolynomial (radialEmbed q)) x := by
    rw [fourier_X_mul_polyGaussian, h, deriv_polyGaussian]
    rfl
  have hXX :
      𝓕 (polyGaussian (X * (X * radialEmbed p))) =
        fun x => (Complex.I / (2 * Real.pi)) ^ 2 *
          polyGaussian
            (spatialDerivativePolynomial (spatialDerivativePolynomial (radialEmbed q))) x := by
    rw [fourier_X_mul_polyGaussian, hX, deriv_const_mul_polyGaussian]
    funext x
    ring
  rw [radialEmbed_X_mul]
  have hsource :
      polyGaussian (C (2 * (Real.pi : ℂ)) * X ^ 2 * radialEmbed p) =
        fun x => (2 * (Real.pi : ℂ)) *
          polyGaussian (X * (X * radialEmbed p)) x := by
    funext x
    simp only [polyGaussian, eval_mul, eval_C, eval_pow, eval_X]
    ring
  rw [hsource, fourier_const_mul, hXX]
  funext x
  rw [← radialOperator_identity q]
  simp only [polyGaussian, eval_mul, eval_C]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  rw [Complex.I_sq]
  ring

theorem fourier_radialBasis (n : ℕ) :
    𝓕 (polyGaussian (radialEmbed (X ^ n))) =
      polyGaussian (radialEmbed (radialBasis n : ℂ[X])) := by
  induction n with
  | zero =>
      have hembed : radialEmbed (1 : ℂ[X]) = 1 := by simp [radialEmbed]
      simp only [radialBasis]
      rw [pow_zero, hembed]
      have hpg : polyGaussian 1 = gaussian := by
        funext x
        simp [polyGaussian]
      rw [hpg]
      exact fourier_gaussian
  | succ n ih =>
      simpa [pow_succ, radialBasis, mul_comm] using fourier_radial_mul ih

lemma radialTransform_add {R : Type*} [CommRing R] (p q : R[X]) :
    radialTransform (p + q) = radialTransform p + radialTransform q := by
  apply sum_add_index
  · intro n
    simp
  · intro n a b
    simp only [C_add]
    ring

lemma radialTransform_monomial {R : Type*} [CommRing R] (n : ℕ) (c : R) :
    radialTransform (monomial n c) = C c * radialBasis n := by
  simp [radialTransform]

lemma radialBasis_map (n : ℕ) :
    (radialBasis n : ℚ[X]).map (algebraMap ℚ ℂ) = (radialBasis n : ℂ[X]) := by
  induction n with
  | zero => simp [radialBasis]
  | succ n ih =>
      simp only [radialBasis]
      simp [radialOperator, ih, ← derivative_map]

lemma radialTransform_map (p : ℚ[X]) :
    (radialTransform p).map (algebraMap ℚ ℂ) =
      radialTransform (p.map (algebraMap ℚ ℂ)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      calc
        (radialTransform (p + q)).map (algebraMap ℚ ℂ) =
            (radialTransform p + radialTransform q).map (algebraMap ℚ ℂ) := by
              rw [radialTransform_add]
        _ = (radialTransform p).map (algebraMap ℚ ℂ) +
            (radialTransform q).map (algebraMap ℚ ℂ) := by rw [Polynomial.map_add]
        _ = radialTransform (p.map (algebraMap ℚ ℂ)) +
            radialTransform (q.map (algebraMap ℚ ℂ)) := by rw [hp, hq]
        _ = radialTransform (p.map (algebraMap ℚ ℂ) +
            q.map (algebraMap ℚ ℂ)) := (radialTransform_add _ _).symm
        _ = radialTransform ((p + q).map (algebraMap ℚ ℂ)) := by
          rw [Polynomial.map_add]
  | monomial n c => simp [radialTransform_monomial, radialBasis_map]

theorem fourier_radialTransform (p : ℂ[X]) :
    𝓕 (polyGaussian (radialEmbed p)) =
      polyGaussian (radialEmbed (radialTransform p)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      have hsource : polyGaussian (radialEmbed (p + q)) =
          fun x => polyGaussian (radialEmbed p) x + polyGaussian (radialEmbed q) x := by
        funext x
        simp [polyGaussian, radialEmbed, add_mul]
      rw [hsource, fourier_add (integrable_polyGaussian _) (integrable_polyGaussian _), hp, hq,
        radialTransform_add]
      funext x
      simp [polyGaussian, radialEmbed, add_mul]
  | monomial n c =>
      have hsource : polyGaussian (radialEmbed (monomial n c)) =
          fun x => c * polyGaussian (radialEmbed (X ^ n)) x := by
        funext x
        simp [polyGaussian, radialEmbed, mul_assoc]
      rw [hsource, fourier_const_mul, fourier_radialBasis, radialTransform_monomial]
      funext x
      simp [polyGaussian, radialEmbed, mul_assoc]

end UncertaintyUpperBound
