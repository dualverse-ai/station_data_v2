import ErdosMinimum.SecondMoment
import ErdosMinimum.FourierCorrelation
import ErdosMinimum.PositivePart
import ErdosMinimum.DualRow

/-!
# Analytic interpretation of a finite dual row

This module reduces a row of the numerical certificate to two explicit
finite-dimensional obligations: positivity of every Fourier coefficient and
an upper bound for the positive-part integral of the row function.  All
measure theory, moment identities, and Fourier support inequalities are
proved here once and for all.
-/

open MeasureTheory Set

namespace ErdosMinimum

noncomputable section

structure DualAtom where
  frequency : ℝ
  alpha : ℝ
  beta : ℝ

def atomFunction (atom : DualAtom) (x : ℝ) : ℝ :=
  atom.alpha * Real.cos (atom.frequency * x) +
    atom.beta * Real.sin (atom.frequency * x)

def dualRowFunction {n : ℕ} (a0 a1 a2 : ℝ) (atoms : Fin n → DualAtom)
    (x : ℝ) : ℝ :=
  a0 + a1 * x + a2 * x ^ 2 - ∑ i, atomFunction (atoms i) x

def atomCharge (atom : DualAtom) : ℝ :=
  Real.sinc atom.frequency ^ 2 *
    (atom.alpha + atom.beta ^ 2 / atom.alpha)

private theorem continuous_dualRowFunction {n : ℕ} (a0 a1 a2 : ℝ)
    (atoms : Fin n → DualAtom) :
    Continuous (dualRowFunction a0 a1 a2 atoms) := by
  apply Continuous.sub
  · fun_prop
  · apply continuous_finset_sum
    intro i _
    unfold atomFunction
    fun_prop

private theorem overlap_mul_dualRow_integrable {f : ℝ → ℝ} (hf : Admissible f)
    {n : ℕ} (a0 a1 a2 : ℝ) (atoms : Fin n → DualAtom) :
    Integrable (fun x ↦ overlap f x * dualRowFunction a0 a1 a2 atoms x) := by
  apply (integrableOn_iff_integrable_of_support_subset (s := Icc (-2 : ℝ) 2) ?_).mp
  · exact (overlap_integrable hf).integrableOn.mul_continuousOn
      (continuous_dualRowFunction a0 a1 a2 atoms).continuousOn isCompact_Icc
  · intro x hx
    by_contra hmem
    exact hx (by simp [overlap_eq_zero_of_not_mem hf hmem])

private theorem dualRow_positive_part_integrableOn {n : ℕ} (a0 a1 a2 : ℝ)
    (atoms : Fin n → DualAtom) :
    IntegrableOn (fun x ↦ max (dualRowFunction a0 a1 a2 atoms x) 0)
      (Icc (-2 : ℝ) 2) := by
  exact ((continuous_dualRowFunction a0 a1 a2 atoms).max continuous_const).continuousOn
    |>.integrableOn_compact isCompact_Icc

private theorem overlap_mul_positive_part_integrableOn {f : ℝ → ℝ}
    (hf : Admissible f) {n : ℕ} (a0 a1 a2 : ℝ)
    (atoms : Fin n → DualAtom) :
    IntegrableOn
      (fun x ↦ overlap f x * max (dualRowFunction a0 a1 a2 atoms x) 0)
      (Icc (-2 : ℝ) 2) := by
  exact (overlap_integrable hf).integrableOn.mul_continuousOn
    ((continuous_dualRowFunction a0 a1 a2 atoms).max continuous_const).continuousOn
    isCompact_Icc

private theorem constant_mul_positive_part_integrableOn (M : ℝ) {n : ℕ}
    (a0 a1 a2 : ℝ) (atoms : Fin n → DualAtom) :
    IntegrableOn (fun x ↦ M * max (dualRowFunction a0 a1 a2 atoms x) 0)
      (Icc (-2 : ℝ) 2) :=
  (dualRow_positive_part_integrableOn a0 a1 a2 atoms).const_mul M

private theorem overlap_mul_atom_integrable {f : ℝ → ℝ} (hf : Admissible f)
    (atom : DualAtom) :
    Integrable (fun x ↦ overlap f x * atomFunction atom x) := by
  apply (overlap_integrable hf).mul_bdd
    (c := |atom.alpha| + |atom.beta|)
  · apply Continuous.aestronglyMeasurable
    unfold atomFunction
    fun_prop
  · filter_upwards [] with x
    rw [Real.norm_eq_abs]
    calc
      |atomFunction atom x| ≤ |atom.alpha * Real.cos (atom.frequency * x)| +
          |atom.beta * Real.sin (atom.frequency * x)| := abs_add_le _ _
      _ ≤ |atom.alpha| + |atom.beta| := by
        rw [abs_mul, abs_mul]
        exact add_le_add
          (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
          (mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _))

private theorem setIntegral_overlap_mul_dualRow {f : ℝ → ℝ}
    (hf : Admissible f) {n : ℕ} (a0 a1 a2 : ℝ)
    (atoms : Fin n → DualAtom) :
    ∫ x in Icc (-2 : ℝ) 2, overlap f x * dualRowFunction a0 a1 a2 atoms x =
      a0 + a1 * overlapFirstMoment f + a2 * overlapSecondMoment f -
        ∑ i, ((atoms i).alpha * cosineTransform (overlap f) (atoms i).frequency +
          (atoms i).beta * sineTransform (overlap f) (atoms i).frequency) := by
  have hsupp : ∀ᵐ x, x ∉ Icc (-2 : ℝ) 2 →
      overlap f x * dualRowFunction a0 a1 a2 atoms x = 0 := by
    filter_upwards [] with x hx
    simp [overlap_eq_zero_of_not_mem hf hx]
  rw [setIntegral_eq_integral_of_ae_compl_eq_zero hsupp]
  unfold dualRowFunction
  simp_rw [mul_sub, mul_add, Finset.mul_sum]
  have h0 : (∫ x, overlap f x * a0) = a0 := by
    rw [integral_mul_const, integral_overlap hf, one_mul]
  have h1 : (∫ x, overlap f x * (a1 * x)) = a1 * overlapFirstMoment f := by
    calc
      (∫ x, overlap f x * (a1 * x)) = ∫ x, a1 * (x * overlap f x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = a1 * ∫ x, x * overlap f x := by rw [integral_const_mul]
      _ = a1 * overlapFirstMoment f := rfl
  have h2 : (∫ x, overlap f x * (a2 * x ^ 2)) = a2 * overlapSecondMoment f := by
    calc
      (∫ x, overlap f x * (a2 * x ^ 2)) = ∫ x, a2 * (x ^ 2 * overlap f x) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = a2 * ∫ x, x ^ 2 * overlap f x := by rw [integral_const_mul]
      _ = a2 * overlapSecondMoment f := rfl
  have hatom : ∀ i, (∫ x, overlap f x * atomFunction (atoms i) x) =
      (atoms i).alpha * cosineTransform (overlap f) (atoms i).frequency +
        (atoms i).beta * sineTransform (overlap f) (atoms i).frequency := by
    intro i
    have hcos : Integrable (fun x ↦ overlap f x *
        Real.cos ((atoms i).frequency * x)) := by
      apply (overlap_integrable hf).mul_bdd
      · fun_prop
      · filter_upwards [] with x
        simpa [Real.norm_eq_abs] using Real.abs_cos_le_one ((atoms i).frequency * x)
    have hsin : Integrable (fun x ↦ overlap f x *
        Real.sin ((atoms i).frequency * x)) := by
      apply (overlap_integrable hf).mul_bdd
      · fun_prop
      · filter_upwards [] with x
        simpa [Real.norm_eq_abs] using Real.abs_sin_le_one ((atoms i).frequency * x)
    calc
      (∫ x, overlap f x * atomFunction (atoms i) x) =
          ∫ x, (atoms i).alpha *
              (overlap f x * Real.cos ((atoms i).frequency * x)) +
            (atoms i).beta *
              (overlap f x * Real.sin ((atoms i).frequency * x)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        simp [atomFunction]
        ring
      _ = (atoms i).alpha *
              (∫ x, overlap f x * Real.cos ((atoms i).frequency * x)) +
            (atoms i).beta *
              (∫ x, overlap f x * Real.sin ((atoms i).frequency * x)) := by
        rw [integral_add (hcos.const_mul _) (hsin.const_mul _),
          integral_const_mul, integral_const_mul]
      _ = _ := rfl
  have hp0 : Integrable (fun x ↦ overlap f x * a0) :=
    (overlap_integrable hf).mul_const a0
  have hp1 : Integrable (fun x ↦ overlap f x * (a1 * x)) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      (overlap_first_moment_integrable hf).const_mul a1
  have hp2 : Integrable (fun x ↦ overlap f x * (a2 * x ^ 2)) := by
    simpa only [mul_assoc, mul_comm, mul_left_comm] using
      (overlap_second_moment_integrable hf).const_mul a2
  have hpoly : Integrable (fun x ↦
      overlap f x * a0 + overlap f x * (a1 * x) + overlap f x * (a2 * x ^ 2)) :=
    (hp0.add hp1).add hp2
  have hsum : Integrable (fun x ↦ ∑ i, overlap f x * atomFunction (atoms i) x) :=
    integrable_finset_sum _ (fun i _ ↦ overlap_mul_atom_integrable hf (atoms i))
  have hpolyIntegral :
      (∫ x, overlap f x * a0 + overlap f x * (a1 * x) +
        overlap f x * (a2 * x ^ 2)) =
      ((∫ x, overlap f x * a0) + ∫ x, overlap f x * (a1 * x)) +
        ∫ x, overlap f x * (a2 * x ^ 2) := by
    calc
      _ = (∫ x, overlap f x * a0 + overlap f x * (a1 * x)) +
          ∫ x, overlap f x * (a2 * x ^ 2) := by
        exact integral_add (hp0.add hp1) hp2
      _ = _ := by
        rw [integral_add hp0 hp1]
  rw [integral_sub hpoly hsum, hpolyIntegral, h0, h1, h2,
    integral_finset_sum _ (fun i _ ↦ overlap_mul_atom_integrable hf (atoms i))]
  simp_rw [hatom]

/-- A finite dual row bounds the overlap maximum once its numerical
positive-part budget and coefficient positivity have been certified. -/
theorem dualRow_le_overlapMaximum {f : ℝ → ℝ} (hf : Admissible f)
    {n : ℕ} (a0 a1 a2 : ℝ) (atoms : Fin n → DualAtom)
    (halpha : ∀ i, 0 < (atoms i).alpha)
    (hbudget : ∫ x in Icc (-2 : ℝ) 2,
      max (dualRowFunction a0 a1 a2 atoms x) 0 ≤ 1) :
    a0 + a1 * overlapFirstMoment f +
        a2 * ((2 : ℝ) / 3 + overlapFirstMoment f ^ 2 / 2) -
        ∑ i, atomCharge (atoms i) ≤ overlapMaximum f := by
  have hrawIntegral := integral_mul_le_of_positive_part_budget
    (Icc (-2 : ℝ) 2) (overlap f) (dualRowFunction a0 a1 a2 atoms)
    (overlapMaximum f) measurableSet_Icc
    (fun x _ ↦ overlap_nonneg hf x)
    (fun x _ ↦ overlap_le_overlapMaximum hf x)
    (overlapMaximum_nonneg hf) hbudget
    ((overlap_mul_dualRow_integrable hf a0 a1 a2 atoms).integrableOn)
    (overlap_mul_positive_part_integrableOn hf a0 a1 a2 atoms)
    (constant_mul_positive_part_integrableOn (overlapMaximum f) a0 a1 a2 atoms)
  rw [setIntegral_overlap_mul_dualRow hf a0 a1 a2 atoms,
    overlap_second_moment_identity hf] at hrawIntegral
  exact one_dual_row (overlapMaximum f) (overlapFirstMoment f) a0 a1 a2
    (fun i ↦ cosineTransform (overlap f) (atoms i).frequency)
    (fun i ↦ sineTransform (overlap f) (atoms i).frequency)
    (fun i ↦ (atoms i).alpha) (fun i ↦ (atoms i).beta)
    (fun i ↦ atomCharge (atoms i)) hrawIntegral
    (fun i ↦ overlap_phaseSupport_sinc hf _ _ _ (halpha i))

end

end ErdosMinimum
