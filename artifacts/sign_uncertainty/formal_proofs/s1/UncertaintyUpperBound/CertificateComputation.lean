import UncertaintyUpperBound.PolynomialWitness
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Algebra.Polynomial.Taylor

namespace UncertaintyUpperBound

open Polynomial

abbrev certificateDegree : ℕ := 226

def qPowerCoefficient (a b : ℚ) (ell : ℕ) : ℚ :=
  (b - a) ^ ell *
    ∑ k ∈ Finset.range (certificateDegree + 1 - ell),
      CertificateData.powerCoefficients[ell + k]! * Nat.choose (ell + k) ell * a ^ k

def qPowerCoefficients (a b : ℚ) : Array ℚ :=
  (Array.range (certificateDegree + 1)).map (qPowerCoefficient a b)

def bernsteinCoefficientFrom (q : Array ℚ) (j : ℕ) : ℚ :=
  ∑ ell ∈ Finset.range (j + 1),
    q[ell]! * Nat.choose j ell / Nat.choose certificateDegree ell

def bernsteinCoefficients (a b : ℚ) : Array ℚ :=
  let q := qPowerCoefficients a b
  (Array.range (certificateDegree + 1)).map (bernsteinCoefficientFrom q)

def bernsteinCoefficient (a b : ℚ) (j : ℕ) : ℚ :=
  (bernsteinCoefficients a b)[j]!

noncomputable def bernsteinPolynomialQ (a b : ℚ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (certificateDegree + 1),
    C (bernsteinCoefficient a b j) * _root_.bernsteinPolynomial ℚ certificateDegree j

noncomputable def affineWitnessQ (a b : ℚ) : Polynomial ℚ :=
  witnessPolynomialQ.comp (C a + C (b - a) * X)

def bernsteinPowerCoefficientFrom (beta : Array ℚ) (r : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (r + 1),
    beta[j]! * Nat.choose certificateDegree j *
      Nat.choose (certificateDegree - j) (r - j) * (-1 : ℚ) ^ (r - j)

def bernsteinPowerCoefficientsFrom (beta : Array ℚ) : Array ℚ :=
  (Array.range (certificateDegree + 1)).map (bernsteinPowerCoefficientFrom beta)

def intervalCertificateValid (ab : ℚ × ℚ) : Bool :=
  let q := qPowerCoefficients ab.1 ab.2
  let beta := bernsteinCoefficients ab.1 ab.2
  (q == bernsteinPowerCoefficientsFrom beta) &&
    beta.all fun value => decide (value < -(1 / 100000 : ℚ))

def boundedCertificateValid : Bool :=
  CertificateData.intervals.all intervalCertificateValid

theorem bounded_certificate_valid : boundedCertificateValid = true := by
  native_decide

def shiftedCoefficient (r : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (certificateDegree + 1 - r),
    CertificateData.powerCoefficients[r + k]! * Nat.choose (r + k) r * 1000 ^ k

theorem exact_shifted_coefficients_negative :
    ∀ r ∈ Finset.range (certificateDegree + 1), shiftedCoefficient r < 0 := by
  native_decide

theorem exact_shifted_constant_margin :
    shiftedCoefficient 0 + 1 / 1000000 < 0 := by
  native_decide

end UncertaintyUpperBound
