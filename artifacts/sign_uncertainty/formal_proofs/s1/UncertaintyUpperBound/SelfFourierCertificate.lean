import UncertaintyUpperBound.PolynomialWitness
import UncertaintyUpperBound.RadialFourier

namespace UncertaintyUpperBound

open Polynomial

def radialStepCoefficient (p : Array ℚ) (k : ℕ) : ℚ :=
  coeffAt p k - (if k = 0 then 0 else coeffAt p (k - 1)) +
    4 * k * coeffAt p k - 2 * (k + 1) * coeffAt p (k + 1) -
    4 * k * (k + 1) * coeffAt p (k + 1)

def radialStepCoefficients (p : Array ℚ) : Array ℚ :=
  (Array.range (p.size + 1)).map fun k => radialStepCoefficient p k

def radialBasisCoefficients : ℕ → Array ℚ
  | 0 => #[1]
  | n + 1 => radialStepCoefficients (radialBasisCoefficients n)

def selfFourierCoefficients : Array ℚ :=
  (Array.range CertificateData.powerCoefficients.size).map fun i =>
    -CertificateData.powerCoefficients[i]! - if i = 0 then 1 / 1000000 else 0

def radialCombinationState (p : Array ℚ) : ℕ → Array ℚ × Array ℚ
  | 0 => (#[1], #[])
  | n + 1 =>
      let state := radialCombinationState p n
      (radialStepCoefficients state.1,
        addCoeffs state.2 (scaleCoeffs p[n]! state.1))

def radialCombinationCoefficients (p : Array ℚ) : Array ℚ :=
  (radialCombinationState p p.size).2

def selfFourierCertificateValid : Bool :=
  radialCombinationCoefficients selfFourierCoefficients == selfFourierCoefficients

theorem self_fourier_certificate_valid : selfFourierCertificateValid = true := by
  native_decide

lemma coeff_radialOperator (p : ℚ[X]) (k : ℕ) :
    (radialOperator p).coeff k =
      p.coeff k - (if k = 0 then 0 else p.coeff (k - 1)) +
        4 * k * p.coeff k - 2 * (k + 1) * p.coeff (k + 1) -
        4 * k * (k + 1) * p.coeff (k + 1) := by
  cases k with
  | zero =>
      simp [radialOperator, coeff_derivative]
      ring
  | succ k =>
      rw [show radialOperator p =
          p - X * p + (X * p.derivative) * 4 - p.derivative * 2 -
            (X * p.derivative.derivative) * 4 from by
        simp only [radialOperator]
        ring]
      simp [coeff_sub, coeff_add, coeff_mul_natCast, coeff_X_mul,
        coeff_derivative, Nat.succ_eq_add_one]
      push_cast
      ring

lemma radialStepCoefficients_size (p : Array ℚ) :
    (radialStepCoefficients p).size = p.size + 1 := by
  simp [radialStepCoefficients]

lemma coeffAt_eq (p : Array ℚ) (k : ℕ) :
    coeffAt p k = if h : k < p.size then p[k] else 0 := by
  by_cases h : k < p.size <;> simp [coeffAt, h]

lemma coeff_polynomialOfArray_eq_coeffAt (p : Array ℚ) (k : ℕ) :
    (polynomialOfArray p).coeff k = coeffAt p k := by
  rw [coeff_polynomialOfArray]
  by_cases h : k < p.size <;> simp [coeffAt, h]

lemma coeffAt_radialStepCoefficients (p : Array ℚ) (k : ℕ) :
    coeffAt (radialStepCoefficients p) k =
      if k < p.size + 1 then radialStepCoefficient p k else 0 := by
  rw [coeffAt_eq]
  simp only [radialStepCoefficients_size]
  split_ifs with h
  · simp [radialStepCoefficients, h]
  · rfl

lemma coeffAt_addCoeffs (p q : Array ℚ) (k : ℕ) :
    coeffAt (addCoeffs p q) k = coeffAt p k + coeffAt q k := by
  rw [coeffAt_eq]
  simp only [addCoeffs, Array.size_map, Array.size_range]
  split_ifs with hk
  · simp [addCoeffs, hk, coeffAt]
  · have hp : ¬ k < p.size := by omega
    have hq : ¬ k < q.size := by omega
    simp [coeffAt, hp, hq]

lemma coeffAt_scaleCoeffs (c : ℚ) (p : Array ℚ) (k : ℕ) :
    coeffAt (scaleCoeffs c p) k = c * coeffAt p k := by
  rw [coeffAt_eq]
  by_cases hk : k < p.size
  · simp [scaleCoeffs, hk, coeffAt]
  · simp [scaleCoeffs, hk, coeffAt]

lemma polynomialOfArray_addCoeffs (p q : Array ℚ) :
    polynomialOfArray (addCoeffs p q) = polynomialOfArray p + polynomialOfArray q := by
  ext k
  simp [coeff_polynomialOfArray_eq_coeffAt, coeffAt_addCoeffs]

lemma polynomialOfArray_scaleCoeffs (c : ℚ) (p : Array ℚ) :
    polynomialOfArray (scaleCoeffs c p) = C c * polynomialOfArray p := by
  ext k
  simp [coeff_polynomialOfArray_eq_coeffAt, coeffAt_scaleCoeffs]

lemma polynomialOfArray_radialStep (p : Array ℚ) :
    polynomialOfArray (radialStepCoefficients p) =
      radialOperator (polynomialOfArray p) := by
  ext k
  rw [coeff_radialOperator]
  simp_rw [coeff_polynomialOfArray_eq_coeffAt]
  rw [coeffAt_radialStepCoefficients]
  by_cases hk : k < p.size + 1
  · rw [if_pos hk]
    simp only [radialStepCoefficient]
  · rw [if_neg hk]
    have hklarge : p.size ≤ k := by omega
    have hkm : ¬ k < p.size := by omega
    have hkpos : k ≠ 0 := by omega
    have hprev : ¬ k - 1 < p.size := by omega
    have hnext : ¬ k + 1 < p.size := by omega
    simp [coeffAt_eq, hkpos, hkm, hprev, hnext]

lemma radialBasisCoefficients_size (n : ℕ) :
    (radialBasisCoefficients n).size = n + 1 := by
  induction n with
  | zero => simp [radialBasisCoefficients]
  | succ n ih => simp [radialBasisCoefficients, radialStepCoefficients_size, ih]

lemma polynomialOfArray_radialBasis (n : ℕ) :
    polynomialOfArray (radialBasisCoefficients n) = (radialBasis n : ℚ[X]) := by
  induction n with
  | zero =>
      ext k
      rw [coeff_polynomialOfArray_eq_coeffAt]
      cases k <;> simp [radialBasisCoefficients, radialBasis, coeffAt, coeff_one]
  | succ n ih =>
      rw [radialBasisCoefficients, polynomialOfArray_radialStep, ih, radialBasis]

lemma polynomialOfArray_combination_current (p : Array ℚ) (n : ℕ) :
    polynomialOfArray (radialCombinationState p n).1 = (radialBasis n : ℚ[X]) := by
  induction n with
  | zero =>
      ext k
      cases k <;> simp [radialCombinationState, radialBasis,
        coeff_polynomialOfArray_eq_coeffAt, coeffAt, coeff_one]
  | succ n ih =>
      simp only [radialCombinationState]
      rw [polynomialOfArray_radialStep, ih, radialBasis]

lemma polynomialOfArray_combination_accumulator (p : Array ℚ) (n : ℕ) :
    polynomialOfArray (radialCombinationState p n).2 =
      ∑ i ∈ Finset.range n, C p[i]! * (radialBasis i : ℚ[X]) := by
  induction n with
  | zero => simp [radialCombinationState, polynomialOfArray]
  | succ n ih =>
      simp only [radialCombinationState]
      rw [polynomialOfArray_addCoeffs, polynomialOfArray_scaleCoeffs, ih,
        polynomialOfArray_combination_current, Finset.sum_range_succ]

lemma radialTransform_finset_sum {R : Type*} [CommRing R] {s : Finset ℕ}
    (f : ℕ → R[X]) :
    radialTransform (∑ i ∈ s, f i) = ∑ i ∈ s, radialTransform (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [radialTransform]
  | insert a s ha ih => simp [ha, radialTransform_add, ih]

lemma radialTransform_polynomialOfArray (p : Array ℚ) :
    radialTransform (polynomialOfArray p) =
      polynomialOfArray (radialCombinationCoefficients p) := by
  rw [polynomialOfArray, radialTransform_finset_sum]
  simp_rw [C_mul_X_pow_eq_monomial, radialTransform_monomial]
  rw [radialCombinationCoefficients, polynomialOfArray_combination_accumulator]

theorem exact_self_fourier_polynomial :
    radialTransform (polynomialOfArray selfFourierCoefficients) =
      polynomialOfArray selfFourierCoefficients := by
  rw [radialTransform_polynomialOfArray]
  exact congrArg polynomialOfArray (beq_iff_eq.mp self_fourier_certificate_valid)

end UncertaintyUpperBound
