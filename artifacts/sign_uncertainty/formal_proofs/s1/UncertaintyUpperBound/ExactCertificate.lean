import UncertaintyUpperBound.CertificateComputation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace UncertaintyUpperBound

theorem interval_count : CertificateData.intervals.size = 27 := by native_decide

theorem interval_endpoints :
    CertificateData.intervals[0]!.1 = 1213 / 625 ∧
      CertificateData.intervals[26]!.2 = 1000 := by native_decide

theorem interval_chain :
    ∀ i ∈ Finset.range 26,
      CertificateData.intervals[i]!.2 = CertificateData.intervals[i + 1]!.1 := by native_decide

theorem interval_strict :
    ∀ ab ∈ CertificateData.intervals.toList, ab.1 < ab.2 := by native_decide

set_option maxHeartbeats 0 in
theorem exact_bernstein_margin :
    ∀ i (hi : i < CertificateData.intervals.size),
      ∀ j (hj : j < certificateDegree + 1),
        (bernsteinCoefficients CertificateData.intervals[i].1
          CertificateData.intervals[i].2)[j]! < -(1 / 100000 : ℚ) := by
  intro i hi j hj
  have hvalid := (Array.all_eq_true.mp bounded_certificate_valid i hi)
  dsimp only [intervalCertificateValid] at hvalid
  rw [Bool.and_eq_true] at hvalid
  have hjsize : j < (bernsteinCoefficients CertificateData.intervals[i].1
      CertificateData.intervals[i].2).size := by
    simpa [bernsteinCoefficients] using hj
  rw [getElem!_pos
    (bernsteinCoefficients CertificateData.intervals[i].1 CertificateData.intervals[i].2)
    j hjsize]
  exact of_decide_eq_true (Array.all_eq_true.mp hvalid.2 j hjsize)

set_option maxHeartbeats 0 in
theorem exact_bernstein_power_identity :
    ∀ i (hi : i < CertificateData.intervals.size),
      qPowerCoefficients CertificateData.intervals[i].1 CertificateData.intervals[i].2 =
        bernsteinPowerCoefficientsFrom
          (bernsteinCoefficients CertificateData.intervals[i].1
            CertificateData.intervals[i].2) := by
  intro i hi
  have hvalid := (Array.all_eq_true.mp bounded_certificate_valid i hi)
  dsimp only [intervalCertificateValid] at hvalid
  rw [Bool.and_eq_true] at hvalid
  exact beq_iff_eq.mp hvalid.1

end UncertaintyUpperBound
