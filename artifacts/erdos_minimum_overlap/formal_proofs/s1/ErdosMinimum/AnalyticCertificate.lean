import ErdosMinimum.DualCertificate
import ErdosMinimum.CertificateCover

/-!
# Analytic dual certificates imply row obligations

This module is the interface between the analytic theorem for a finite dual
certificate and the exact cover in `CertificateCover`.  In particular, it
handles the sign of the overlap first moment by reflecting the profile, and
allows the coefficients stored in a `VerifiedRow` to be conservative lower
bounds for the coefficients obtained from the analytic certificate.
-/

open MeasureTheory Set

namespace ErdosMinimum

noncomputable section

/-- Lowering all three coefficients lowers a quadratic on the nonnegative
half-line. -/
theorem quadratic_mono_of_nonneg
    {c0 c0' a1 a1' a2 a2' m : ℝ}
    (hm : 0 ≤ m) (hc0 : c0 ≤ c0') (ha1 : a1 ≤ a1') (ha2 : a2 ≤ a2') :
    quadratic c0 a1 a2 m ≤ quadratic c0' a1' a2' m := by
  dsimp [quadratic]
  nlinarith [sq_nonneg m]

/-- A dual row may be evaluated at the absolute value of the overlap first
moment.  When that moment is negative, apply the row to the reflected
admissible profile; reflection negates the moment and preserves the maximum. -/
theorem dualRow_le_overlapMaximum_abs {f : ℝ → ℝ} (hf : Admissible f)
    {n : ℕ} (a0 a1 a2 : ℝ) (atoms : Fin n → DualAtom)
    (halpha : ∀ i, 0 < (atoms i).alpha)
    (hbudget : ∫ x in Icc (-2 : ℝ) 2,
      max (dualRowFunction a0 a1 a2 atoms x) 0 ≤ 1) :
    a0 + a1 * |overlapFirstMoment f| +
        a2 * ((2 : ℝ) / 3 + |overlapFirstMoment f| ^ 2 / 2) -
        ∑ i, atomCharge (atoms i) ≤ overlapMaximum f := by
  by_cases hm : 0 ≤ overlapFirstMoment f
  · simpa [abs_of_nonneg hm] using
      dualRow_le_overlapMaximum hf a0 a1 a2 atoms halpha hbudget
  · have hm' : overlapFirstMoment f < 0 := lt_of_not_ge hm
    have h := dualRow_le_overlapMaximum (reflectProfile_admissible hf)
      a0 a1 a2 atoms halpha hbudget
    rw [overlapFirstMoment_reflect, overlapMaximum_reflect] at h
    simpa [abs_of_neg hm'] using h

/-- Exact data for one analytic dual certificate discharge the corresponding
`RowApplies` obligation.  The last three hypotheses say that the row's stored
quadratic coefficients are conservative lower bounds: the constant-term
hypothesis includes the complete Fourier support charge. -/
theorem dualCertificate_rowApplies {f : ℝ → ℝ} (hf : Admissible f)
    (row : VerifiedRow) {n : ℕ} (a0 a1 a2 : ℝ)
    (atoms : Fin n → DualAtom)
    (halpha : ∀ i, 0 < (atoms i).alpha)
    (hbudget : ∫ x in Icc (-2 : ℝ) 2,
      max (dualRowFunction a0 a1 a2 atoms x) 0 ≤ 1)
    (hc0 : row.c0 + ∑ i, atomCharge (atoms i) ≤
      a0 + a2 * ((2 : ℝ) / 3))
    (ha1 : row.a1 ≤ a1)
    (ha2 : row.a2 ≤ a2) :
    RowApplies row (overlapMaximum f) |overlapFirstMoment f| := by
  intro _hlo _hhi
  let m := |overlapFirstMoment f|
  have hm : 0 ≤ m := abs_nonneg _
  have hc0' : row.c0 ≤
      a0 + a2 * ((2 : ℝ) / 3) - ∑ i, atomCharge (atoms i) := by
    linarith
  have hmono := quadratic_mono_of_nonneg hm hc0' ha1 ha2
  have hdual := dualRow_le_overlapMaximum_abs hf a0 a1 a2 atoms halpha hbudget
  calc
    quadratic row.c0 row.a1 row.a2 m ≤
        quadratic
          (a0 + a2 * ((2 : ℝ) / 3) - ∑ i, atomCharge (atoms i))
          a1 a2 m := hmono
    _ = a0 + a1 * |overlapFirstMoment f| +
          a2 * ((2 : ℝ) / 3 + |overlapFirstMoment f| ^ 2 / 2) -
          ∑ i, atomCharge (atoms i) := by
      dsimp [quadratic, m]
      ring
    _ ≤ overlapMaximum f := hdual

end

end ErdosMinimum
