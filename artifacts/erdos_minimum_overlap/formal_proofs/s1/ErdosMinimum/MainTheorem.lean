import ErdosMinimum.VerifiedCertificate
import ErdosMinimum.ComputedAdaptiveRow0
import ErdosMinimum.ComputedAdaptiveRow1
import ErdosMinimum.ComputedAdaptiveRow2
import ErdosMinimum.ComputedAdaptiveRow3
import ErdosMinimum.CertificateReplay
import ErdosMinimum.PaperProblem

/-!
# Unconditional Erdős minimum-overlap lower bound

This file assembles the four fully checked numerical rows with the analytic
dual-certificate theorem and the exact `sInf` bridge.
-/

namespace ErdosMinimum

noncomputable section

theorem row0_verified_applies {f : ℝ → ℝ} (hf : Admissible f) :
    RowApplies row0 (overlapMaximum f) |overlapFirstMoment f| := by
  apply ratRowCertificate_rowApplies_of_integral_budget hf row0
    CertificateData.row0Symmetric row0Symmetric_dualAtoms_alpha_pos
    row0_adaptive_even_integral_budget
    row0SupportUpper row0Symmetric_charge_le_supportUpper
  · exact row0Symmetric_coefficient_bounds.1
  · exact row0Symmetric_coefficient_bounds.2.1
  · exact row0Symmetric_coefficient_bounds.2.2

theorem row1_verified_applies {f : ℝ → ℝ} (hf : Admissible f) :
    RowApplies row1 (overlapMaximum f) |overlapFirstMoment f| := by
  apply ratRowCertificate_rowApplies_of_integral_budget hf row1
    CertificateData.row1 row1_dualAtoms_alpha_pos row1_adaptive_integral_budget
    row1SupportUpper row1_charge_le_supportUpper
  · exact row1_coefficient_bounds.1
  · exact row1_coefficient_bounds.2.1
  · exact row1_coefficient_bounds.2.2

theorem row2_verified_applies {f : ℝ → ℝ} (hf : Admissible f) :
    RowApplies row2 (overlapMaximum f) |overlapFirstMoment f| := by
  apply ratRowCertificate_rowApplies_of_integral_budget hf row2
    CertificateData.row2 row2_dualAtoms_alpha_pos row2_adaptive_integral_budget
    row2SupportUpper row2_charge_le_supportUpper
  · exact row2_coefficient_bounds.1
  · exact row2_coefficient_bounds.2.1
  · exact row2_coefficient_bounds.2.2

theorem row3_verified_applies {f : ℝ → ℝ} (hf : Admissible f) :
    RowApplies row3 (overlapMaximum f) |overlapFirstMoment f| := by
  apply ratRowCertificate_rowApplies_of_integral_budget hf row3
    CertificateData.row3 row3_dualAtoms_alpha_pos row3_adaptive_integral_budget
    row3SupportUpper row3_charge_le_supportUpper
  · exact row3_coefficient_bounds.1
  · exact row3_coefficient_bounds.2.1
  · exact row3_coefficient_bounds.2.2

theorem all_concrete_rows_apply (f : ℝ → ℝ) (hf : Admissible f) :
    ∀ i, RowApplies (concreteRows i) (overlapMaximum f)
      |overlapFirstMoment f| := by
  intro i
  fin_cases i
  · exact row0_verified_applies hf
  · exact row1_verified_applies hf
  · exact row2_verified_applies hf
  · exact row3_verified_applies hf

/-- The paper's main lower bound, with no mathematical hypotheses left. -/
theorem erdos_minimum_overlap_lower_bound :
    (380552 : ℝ) / 1000000 < erdosMinimum := by
  apply erdos_minimum_overlap_lower_bound_of_concrete_rows
  intro f hf
  exact all_concrete_rows_apply f hf

/-- The paper's main lower bound in its full a.e.-measurable,
measure-theoretic `L∞` formulation. -/
theorem paper_erdos_minimum_overlap_lower_bound :
    (380552 : ℝ) / 1000000 < paperErdosMinimum := by
  rw [paperErdosMinimum_eq_erdosMinimum]
  exact erdos_minimum_overlap_lower_bound

end

end ErdosMinimum
