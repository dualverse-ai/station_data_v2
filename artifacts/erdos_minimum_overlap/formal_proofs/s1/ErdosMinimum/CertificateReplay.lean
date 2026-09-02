import ErdosMinimum.CertificateCover
import ErdosMinimum.FirstMomentIdentity

/-!
# Interface from analytic row verification to the continuum theorem

This file connects the exact four-row cover to the genuine measurable-profile
definition and its infimum.  Its two premises are precisely the obligations
still requiring a Lean-kernel replay: construction/bounding of the overlap
first moment and the four directed analytic row inequalities.
-/

namespace ErdosMinimum

noncomputable section

/-- Once the moment bound and all four concrete row inequalities are supplied
for every admissible profile, the unconditional-looking paper statement
follows with the correct uniform floor before taking `sInf`. -/
theorem erdos_minimum_overlap_lower_bound_of_rows
    (moment : (ℝ → ℝ) → ℝ)
    (hmoment : ∀ f, Admissible f → |moment f| ≤ 1)
    (hrows : ∀ f, Admissible f → ∀ i,
      RowApplies (concreteRows i) (overlapMaximum f) |moment f|) :
    (380552 : ℝ) / 1000000 < erdosMinimum := by
  apply erdos_minimum_overlap_lower_bound_of_certificate
  intro f hf
  exact concrete_certificate_uniform_floor (overlapMaximum f) (moment f)
    (hmoment f hf) (hrows f hf)

/-- Specialization using the genuine overlap first moment.  Fubini identifies
it with the algebraic moment and the bathtub bound is discharged in Lean;
only the four analytic row inequalities remain as a premise. -/
theorem erdos_minimum_overlap_lower_bound_of_concrete_rows
    (hrows : ∀ f, Admissible f → ∀ i,
      RowApplies (concreteRows i) (overlapMaximum f)
        |overlapFirstMoment f|) :
    (380552 : ℝ) / 1000000 < erdosMinimum := by
  exact erdos_minimum_overlap_lower_bound_of_rows overlapFirstMoment
    (fun _ hf => by
      rw [overlapFirstMoment_eq_algebraicOverlapFirstMoment hf]
      exact abs_algebraicOverlapFirstMoment_le_one hf) hrows

end

end ErdosMinimum
