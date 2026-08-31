import UncertaintyS2.UpperWitness

namespace UncertaintyS2

open Polynomial

abbrev residualDegree : ℕ := 41

def qPowerCoefficient (a b : ℚ) (ell : ℕ) : ℚ :=
  (b - a) ^ ell *
    ∑ k ∈ Finset.range (residualDegree + 1 - ell),
      CertificateData.residualCoefficients[ell + k]! * Nat.choose (ell + k) ell * a ^ k

def qPowerCoefficients (a b : ℚ) : Array ℚ :=
  (Array.range (residualDegree + 1)).map (qPowerCoefficient a b)

def bernsteinCoefficientFrom (q : Array ℚ) (j : ℕ) : ℚ :=
  ∑ ell ∈ Finset.range (j + 1),
    q[ell]! * Nat.choose j ell / Nat.choose residualDegree ell

def bernsteinCoefficients (a b : ℚ) : Array ℚ :=
  let q := qPowerCoefficients a b
  (Array.range (residualDegree + 1)).map (bernsteinCoefficientFrom q)

def bernsteinPowerCoefficientFrom (beta : Array ℚ) (r : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (r + 1),
    beta[j]! * Nat.choose residualDegree j *
      Nat.choose (residualDegree - j) (r - j) * (-1 : ℚ) ^ (r - j)

def bernsteinPowerCoefficientsFrom (beta : Array ℚ) : Array ℚ :=
  (Array.range (residualDegree + 1)).map (bernsteinPowerCoefficientFrom beta)

def intervalCertificateValid (ab : ℚ × ℚ) : Bool :=
  let q := qPowerCoefficients ab.1 ab.2
  let beta := bernsteinCoefficients ab.1 ab.2
  (q == bernsteinPowerCoefficientsFrom beta) &&
    beta.all fun value => decide (value < 0)

def boundedCertificateValid : Bool :=
  CertificateData.tailIntervals.all intervalCertificateValid

set_option maxHeartbeats 0 in
theorem bounded_certificate_valid : boundedCertificateValid = true := by
  native_decide

theorem interval_count : CertificateData.tailIntervals.size = 33 := by native_decide

theorem interval_endpoints :
    CertificateData.tailIntervals[0]!.1 = CertificateData.isolatingRight ∧
      CertificateData.tailIntervals[32]!.2 = 500 := by native_decide

theorem interval_chain :
    ∀ i ∈ Finset.range 32,
      CertificateData.tailIntervals[i]!.2 = CertificateData.tailIntervals[i + 1]!.1 := by
  native_decide

theorem interval_strict :
    ∀ ab ∈ CertificateData.tailIntervals.toList, ab.1 < ab.2 := by native_decide

set_option maxHeartbeats 0 in
theorem exact_bernstein_negative :
    ∀ i (hi : i < CertificateData.tailIntervals.size),
      ∀ j (hj : j < residualDegree + 1),
        (bernsteinCoefficients CertificateData.tailIntervals[i].1
          CertificateData.tailIntervals[i].2)[j]! < 0 := by
  intro i hi j hj
  have hvalid := Array.all_eq_true.mp bounded_certificate_valid i hi
  dsimp only [intervalCertificateValid] at hvalid
  rw [Bool.and_eq_true] at hvalid
  have hjsize : j < (bernsteinCoefficients CertificateData.tailIntervals[i].1
      CertificateData.tailIntervals[i].2).size := by
    simpa [bernsteinCoefficients] using hj
  rw [getElem!_pos _ j hjsize]
  exact of_decide_eq_true (Array.all_eq_true.mp hvalid.2 j hjsize)

set_option maxHeartbeats 0 in
theorem exact_bernstein_power_identity :
    ∀ i (hi : i < CertificateData.tailIntervals.size),
      qPowerCoefficients CertificateData.tailIntervals[i].1
          CertificateData.tailIntervals[i].2 =
        bernsteinPowerCoefficientsFrom
          (bernsteinCoefficients CertificateData.tailIntervals[i].1
            CertificateData.tailIntervals[i].2) := by
  intro i hi
  have hvalid := Array.all_eq_true.mp bounded_certificate_valid i hi
  dsimp only [intervalCertificateValid] at hvalid
  rw [Bool.and_eq_true] at hvalid
  exact beq_iff_eq.mp hvalid.1

def shiftedCoefficient500 (r : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (residualDegree + 1 - r),
    CertificateData.residualCoefficients[r + k]! * Nat.choose (r + k) r * 500 ^ k

set_option maxHeartbeats 0 in
theorem exact_shifted_coefficients_negative :
    ∀ r ∈ Finset.range (residualDegree + 1), shiftedCoefficient500 r < 0 := by
  native_decide

end UncertaintyS2
