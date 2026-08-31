import UncertaintyUpperBound.CertificateData
import Mathlib.Algebra.Polynomial.Derivative

namespace UncertaintyUpperBound

open Polynomial

noncomputable def polynomialOfArray {R : Type*} [Semiring R] [Inhabited R]
    (coeffs : Array R) : Polynomial R :=
  ∑ i ∈ Finset.range coeffs.size, C coeffs[i]! * X ^ i

theorem coeff_polynomialOfArray {R : Type*} [Semiring R] [Inhabited R]
    (coeffs : Array R) (n : ℕ) :
    (polynomialOfArray coeffs).coeff n = if n < coeffs.size then coeffs[n]! else 0 := by
  simp only [polynomialOfArray]
  by_cases h : n < coeffs.size
  · rw [if_pos h]
    simp [h]
  · rw [if_neg h]
    simp [h]

noncomputable def witnessPolynomialQ : Polynomial ℚ :=
  polynomialOfArray CertificateData.powerCoefficients

def coeffAt (p : Array ℚ) (i : ℕ) : ℚ :=
  (p[i]?).getD 0

def addCoeffs (p q : Array ℚ) : Array ℚ :=
  (Array.range (max p.size q.size)).map fun i => coeffAt p i + coeffAt q i

def scaleCoeffs (c : ℚ) (p : Array ℚ) : Array ℚ :=
  p.map fun x => c * x

def shiftCoeffs (p : Array ℚ) : Array ℚ :=
  #[0] ++ p

def laguerreStep (state : Array ℚ × Array ℚ) (n : ℕ) : Array ℚ × Array ℚ :=
  let previous := state.1
  let current := state.2
  let next := scaleCoeffs (1 / (n + 1 : ℚ)) <|
    addCoeffs
      (addCoeffs
        (scaleCoeffs (2 * (n : ℚ) + 1 / 2) current)
        (scaleCoeffs (-1) (shiftCoeffs current)))
      (scaleCoeffs (-((n : ℚ) - 1 / 2)) previous)
  (current, next)

def laguerreHalfCoeffs (degree : ℕ) : Array ℚ :=
  if degree = 0 then #[1]
  else
    ((Array.range (degree - 1)).foldl
      (fun state k => laguerreStep state (k + 1)) (#[1], #[1 / 2, -1])).2

def laguerreExpansionCoeffs : Array ℚ :=
  (Array.range CertificateData.laguerreCoefficients.size).foldl
    (fun acc j => addCoeffs acc <|
      scaleCoeffs CertificateData.laguerreCoefficients[j]! (laguerreHalfCoeffs (2 * j))) #[0]

noncomputable def laguerreHalf (n : ℕ) : Polynomial ℚ :=
  polynomialOfArray (laguerreHalfCoeffs n)

noncomputable def laguerreExpansionQ : Polynomial ℚ :=
  polynomialOfArray laguerreExpansionCoeffs

theorem power_coefficients_size : CertificateData.powerCoefficients.size = 227 := by
  native_decide

theorem laguerre_coefficients_size : CertificateData.laguerreCoefficients.size = 114 := by
  native_decide

theorem exact_laguerre_recomposition : laguerreExpansionQ = witnessPolynomialQ := by
  unfold laguerreExpansionQ witnessPolynomialQ
  rw [show laguerreExpansionCoeffs = CertificateData.powerCoefficients by native_decide]

theorem witness_at_zero : witnessPolynomialQ.eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, witnessPolynomialQ, coeff_polynomialOfArray]
  have hsize : 0 < CertificateData.powerCoefficients.size := by native_decide
  rw [if_pos hsize]
  native_decide

theorem witness_derivative_at_zero : witnessPolynomialQ.derivative.eval 0 = 1 := by
  rw [← coeff_zero_eq_eval_zero, coeff_derivative, witnessPolynomialQ,
    coeff_polynomialOfArray]
  have hsize : 1 < CertificateData.powerCoefficients.size := by native_decide
  rw [if_pos hsize]
  native_decide

end UncertaintyUpperBound
