import ErdosMinimum.AnalyticCertificate
import ErdosMinimum.BudgetComputation
import ErdosMinimum.CertificateData
import ErdosMinimum.FixedSupport

/-!
# Kernel-checked assembly of the numerical certificate

This file is the narrow interface between the exact-rational interval replay
and the analytic dual-certificate theorem.  The row-specific computations are
kept below; the first lemmas contain no certificate data.
-/

open MeasureTheory Set

namespace ErdosMinimum

noncomputable section

/-- Transfer positivity from a fixed-size generated vector to the list-indexed
atom family used by `RatRow`. -/
theorem vector_dual_alpha_pos {n : ℕ} (v : Vector RatAtom n)
    (h : ∀ j, 0 < (v.get j).toDual.alpha)
    (i : Fin v.toList.length) : 0 < ((v.toList.get i).toDual).alpha := by
  rw [List.get_eq_getElem]
  simp only [Vector.getElem_toList]
  let j : Fin n := ⟨i.val, by simpa using i.isLt⟩
  simpa [j] using h j

set_option maxRecDepth 100000 in
theorem row0_dualAtoms_alpha_pos (i : Fin CertificateData.row0.atoms.length) :
    0 < (CertificateData.row0.dualAtoms i).alpha := by
  apply vector_dual_alpha_pos CertificateData.row0AtomVector
  exact CertificateData.row0_dual_alpha_pos

set_option maxRecDepth 100000 in
theorem row1_dualAtoms_alpha_pos (i : Fin CertificateData.row1.atoms.length) :
    0 < (CertificateData.row1.dualAtoms i).alpha := by
  apply vector_dual_alpha_pos CertificateData.row1AtomVector
  exact CertificateData.row1_dual_alpha_pos

set_option maxRecDepth 100000 in
theorem row2_dualAtoms_alpha_pos (i : Fin CertificateData.row2.atoms.length) :
    0 < (CertificateData.row2.dualAtoms i).alpha := by
  apply vector_dual_alpha_pos CertificateData.row2AtomVector
  exact CertificateData.row2_dual_alpha_pos

set_option maxRecDepth 100000 in
theorem row3_dualAtoms_alpha_pos (i : Fin CertificateData.row3.atoms.length) :
    0 < (CertificateData.row3.dualAtoms i).alpha := by
  apply vector_dual_alpha_pos CertificateData.row3AtomVector
  exact CertificateData.row3_dual_alpha_pos

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row0_frequencies_nonzero :
    RowFrequenciesNonzero CertificateData.row0 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row0Symmetric_frequencies_nonzero :
    RowFrequenciesNonzero CertificateData.row0Symmetric := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row1_frequencies_nonzero :
    RowFrequenciesNonzero CertificateData.row1 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row2_frequencies_nonzero :
    RowFrequenciesNonzero CertificateData.row2 := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3_frequencies_nonzero :
    RowFrequenciesNonzero CertificateData.row3 := by decide +kernel

def row0SupportUpper : ℚ := 0.003008517111
def row1SupportUpper : ℚ := 0.003015309081
def row2SupportUpper : ℚ := 0.002818535987
def row3SupportUpper : ℚ := 0.007136427401

theorem atoms_alpha_pos_of_dualAtoms (row : RatRow)
    (h : ∀ i, 0 < (row.dualAtoms i).alpha) :
    ∀ a ∈ row.atoms, 0 < a.alpha := by
  rw [List.forall_mem_iff_get]
  intro i
  exact (Rat.cast_pos (K := ℝ)).mp (by
    simpa [RatRow.dualAtoms, RatAtom.toDual] using h i)

set_option maxRecDepth 100000 in
theorem row0Symmetric_dualAtoms_alpha_pos
    (i : Fin CertificateData.row0Symmetric.atoms.length) :
    0 < (CertificateData.row0Symmetric.dualAtoms i).alpha := by
  have horiginal := atoms_alpha_pos_of_dualAtoms CertificateData.row0
    row0_dualAtoms_alpha_pos
  have hmem := List.get_mem CertificateData.row0Symmetric.atoms i
  change 0 < ((CertificateData.row0Symmetric.atoms.get i).alpha : ℝ)
  simp only [CertificateData.row0Symmetric] at hmem
  simp only [CertificateData.row0Symmetric]
  rcases List.mem_map.mp hmem with ⟨atom, hatom, heq⟩
  rw [← heq]
  simpa using horiginal atom (by
    simpa [CertificateData.row0, CertificateData.row0AtomList] using hatom)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row0_fixed_support_bound :
    fixedSupportChargeUpper CertificateData.row0 ≤ row0SupportUpper := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row0Symmetric_fixed_support_bound :
    fixedSupportChargeUpper CertificateData.row0Symmetric ≤ row0SupportUpper := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row1_fixed_support_bound :
    fixedSupportChargeUpper CertificateData.row1 ≤ row1SupportUpper := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row2_fixed_support_bound :
    fixedSupportChargeUpper CertificateData.row2 ≤ row2SupportUpper := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem row3_fixed_support_bound :
    fixedSupportChargeUpper CertificateData.row3 ≤ row3SupportUpper := by
  decide +kernel

theorem row0_charge_le_supportUpper :
    (∑ i, atomCharge (CertificateData.row0.dualAtoms i)) ≤
      (row0SupportUpper : ℝ) := by
  exact (sum_atomCharge_le_fixedSupportChargeUpper CertificateData.row0
    (atoms_alpha_pos_of_dualAtoms _ row0_dualAtoms_alpha_pos)
    row0_frequencies_nonzero).trans
    (by exact_mod_cast row0_fixed_support_bound)

theorem row0Symmetric_charge_le_supportUpper :
    (∑ i, atomCharge (CertificateData.row0Symmetric.dualAtoms i)) ≤
      (row0SupportUpper : ℝ) := by
  exact (sum_atomCharge_le_fixedSupportChargeUpper CertificateData.row0Symmetric
    (atoms_alpha_pos_of_dualAtoms _ row0Symmetric_dualAtoms_alpha_pos)
    row0Symmetric_frequencies_nonzero).trans
    (by exact_mod_cast row0Symmetric_fixed_support_bound)

theorem row1_charge_le_supportUpper :
    (∑ i, atomCharge (CertificateData.row1.dualAtoms i)) ≤
      (row1SupportUpper : ℝ) := by
  exact (sum_atomCharge_le_fixedSupportChargeUpper CertificateData.row1
    (atoms_alpha_pos_of_dualAtoms _ row1_dualAtoms_alpha_pos)
    row1_frequencies_nonzero).trans
    (by exact_mod_cast row1_fixed_support_bound)

theorem row2_charge_le_supportUpper :
    (∑ i, atomCharge (CertificateData.row2.dualAtoms i)) ≤
      (row2SupportUpper : ℝ) := by
  exact (sum_atomCharge_le_fixedSupportChargeUpper CertificateData.row2
    (atoms_alpha_pos_of_dualAtoms _ row2_dualAtoms_alpha_pos)
    row2_frequencies_nonzero).trans
    (by exact_mod_cast row2_fixed_support_bound)

theorem row3_charge_le_supportUpper :
    (∑ i, atomCharge (CertificateData.row3.dualAtoms i)) ≤
      (row3SupportUpper : ℝ) := by
  exact (sum_atomCharge_le_fixedSupportChargeUpper CertificateData.row3
    (atoms_alpha_pos_of_dualAtoms _ row3_dualAtoms_alpha_pos)
    row3_frequencies_nonzero).trans
    (by exact_mod_cast row3_fixed_support_bound)

theorem row0_coefficient_bounds :
    row0.c0 + (row0SupportUpper : ℝ) ≤
        (CertificateData.row0.a0 : ℝ) +
          (CertificateData.row0.a2 : ℝ) * (2 / 3) ∧
      row0.a1 ≤ (CertificateData.row0.a1 : ℝ) ∧
      row0.a2 ≤ (CertificateData.row0.a2 : ℝ) := by
  norm_num [row0, row0SupportUpper, CertificateData.row0]

theorem row0Symmetric_coefficient_bounds :
    row0.c0 + (row0SupportUpper : ℝ) ≤
        (CertificateData.row0Symmetric.a0 : ℝ) +
          (CertificateData.row0Symmetric.a2 : ℝ) * (2 / 3) ∧
      row0.a1 ≤ (CertificateData.row0Symmetric.a1 : ℝ) ∧
      row0.a2 ≤ (CertificateData.row0Symmetric.a2 : ℝ) := by
  norm_num [row0, row0SupportUpper, CertificateData.row0Symmetric]

theorem row0Symmetric_is_symmetric :
    RatRowSymmetric CertificateData.row0Symmetric := by
  constructor
  · rfl
  · intro atom hatom
    simp only [CertificateData.row0Symmetric] at hatom
    rcases List.mem_map.mp hatom with ⟨original, _, rfl⟩
    rfl

theorem row1_coefficient_bounds :
    row1.c0 + (row1SupportUpper : ℝ) ≤
        (CertificateData.row1.a0 : ℝ) +
          (CertificateData.row1.a2 : ℝ) * (2 / 3) ∧
      row1.a1 ≤ (CertificateData.row1.a1 : ℝ) ∧
      row1.a2 ≤ (CertificateData.row1.a2 : ℝ) := by
  norm_num [row1, row1SupportUpper, CertificateData.row1]

theorem row2_coefficient_bounds :
    row2.c0 + (row2SupportUpper : ℝ) ≤
        (CertificateData.row2.a0 : ℝ) +
          (CertificateData.row2.a2 : ℝ) * (2 / 3) ∧
      row2.a1 ≤ (CertificateData.row2.a1 : ℝ) ∧
      row2.a2 ≤ (CertificateData.row2.a2 : ℝ) := by
  norm_num [row2, row2SupportUpper, CertificateData.row2]

theorem row3_coefficient_bounds :
    row3.c0 + (row3SupportUpper : ℝ) ≤
        (CertificateData.row3.a0 : ℝ) +
          (CertificateData.row3.a2 : ℝ) * (2 / 3) ∧
      row3.a1 ≤ (CertificateData.row3.a1 : ℝ) ∧
      row3.a2 ≤ (CertificateData.row3.a2 : ℝ) := by
  norm_num [row3, row3SupportUpper, CertificateData.row3]

/-- Convert the oriented interval integral used by the adaptive checker to the
closed-set integral used by the analytic certificate.  The two differ only at
one endpoint, a null set. -/
theorem positivePartBudget_setIntegral_le (row : RatRow) (depth : ℕ)
    (hfreq : RowFrequenciesNonzero row) :
    (∫ x in Icc (-2 : ℝ) 2, max (ratRowFunction row x) 0) ≤
      (positivePartBudget row depth : ℝ) := by
  have h := positivePartBudget_interval_le row depth hfreq
  rw [intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)] at h
  rw [integral_Icc_eq_integral_Ioc]
  simpa [positivePart] using h

/-- A computed rational budget at most one discharges the analytic budget
premise without any floating-point reasoning. -/
theorem row_budget_le_one (row : RatRow) (depth : ℕ)
    (hfreq : RowFrequenciesNonzero row)
    (hbudget : positivePartBudget row depth ≤ 1) :
    (∫ x in Icc (-2 : ℝ) 2, max (ratRowFunction row x) 0) ≤ 1 := by
  exact (positivePartBudget_setIntegral_le row depth hfreq).trans
    (by exact_mod_cast hbudget)

theorem even_row_budget_le_one (row : RatRow) (depth : ℕ)
    (hsymmetric : RatRowSymmetric row)
    (hfreq : RowFrequenciesNonzero row)
    (hbudget : positivePartEvenBudget row depth ≤ 1) :
    (∫ x in Icc (-2 : ℝ) 2, max (ratRowFunction row x) 0) ≤ 1 := by
  have h := positivePartEvenBudget_interval_le row depth hsymmetric hfreq
  rw [intervalIntegral.integral_of_le (by norm_num : (-2 : ℝ) ≤ 2)] at h
  rw [integral_Icc_eq_integral_Ioc]
  have hle :
      (∫ x in Ioc (-2 : ℝ) 2, max (ratRowFunction row x) 0) ≤
        (positivePartEvenBudget row depth : ℝ) := by
    simpa [positivePart] using h
  exact hle.trans (by exact_mod_cast hbudget)

/-- All analytic obligations for one exact-rational row once its continuous
positive-part budget has been established. -/
theorem ratRowCertificate_rowApplies_of_integral_budget
    {f : ℝ → ℝ} (hf : Admissible f)
    (verified : VerifiedRow) (row : RatRow)
    (halpha : ∀ i, 0 < (row.dualAtoms i).alpha)
    (hbudget : (∫ x in Icc (-2 : ℝ) 2,
      max (ratRowFunction row x) 0) ≤ 1)
    (supportUpper : ℚ)
    (hcharge : (∑ i, atomCharge (row.dualAtoms i)) ≤ (supportUpper : ℝ))
    (hc0 : verified.c0 + (supportUpper : ℝ) ≤
      (row.a0 : ℝ) + (row.a2 : ℝ) * ((2 : ℝ) / 3))
    (ha1 : verified.a1 ≤ (row.a1 : ℝ))
    (ha2 : verified.a2 ≤ (row.a2 : ℝ)) :
    RowApplies verified (overlapMaximum f) |overlapFirstMoment f| := by
  have hbudget' : ∫ x in Icc (-2 : ℝ) 2,
      max (dualRowFunction row.a0 row.a1 row.a2 row.dualAtoms x) 0 ≤ 1 := by
    simpa only [← ratRowFunction_eq_dualRowFunction] using
      hbudget
  apply dualCertificate_rowApplies hf verified row.a0 row.a1 row.a2
      row.dualAtoms halpha hbudget'
  · calc
      verified.c0 + ∑ i, atomCharge (row.dualAtoms i) ≤
          verified.c0 + (supportUpper : ℝ) :=
        add_le_add_right hcharge verified.c0
      _ ≤ (row.a0 : ℝ) + (row.a2 : ℝ) * ((2 : ℝ) / 3) := hc0
  · exact ha1
  · exact ha2

/-- Standard wrapper using the full-interval fixed-dyadic replay. -/
theorem ratRowCertificate_rowApplies {f : ℝ → ℝ} (hf : Admissible f)
    (verified : VerifiedRow) (row : RatRow) (depth : ℕ)
    (halpha : ∀ i, 0 < (row.dualAtoms i).alpha)
    (hfreq : RowFrequenciesNonzero row)
    (hbudget : positivePartBudget row depth ≤ 1)
    (supportUpper : ℚ)
    (hcharge : (∑ i, atomCharge (row.dualAtoms i)) ≤ (supportUpper : ℝ))
    (hc0 : verified.c0 + (supportUpper : ℝ) ≤
      (row.a0 : ℝ) + (row.a2 : ℝ) * ((2 : ℝ) / 3))
    (ha1 : verified.a1 ≤ (row.a1 : ℝ))
    (ha2 : verified.a2 ≤ (row.a2 : ℝ)) :
    RowApplies verified (overlapMaximum f) |overlapFirstMoment f| := by
  exact ratRowCertificate_rowApplies_of_integral_budget hf verified row halpha
    (row_budget_le_one row depth hfreq hbudget) supportUpper hcharge hc0 ha1 ha2

end

end ErdosMinimum
