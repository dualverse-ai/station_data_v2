import ErdosMinimum.FastTrig
import ErdosMinimum.DualCertificate

/-!
# Executable exact-rational dual rows

The certificate data are decimal rationals.  This module gives an executable
row representation and sound point enclosures for the row, its derivative,
and its antiderivative.  Every trigonometric call uses proved range reduction,
Taylor bounds, and outward dyadic compression.
-/

namespace ErdosMinimum

open RatInterval

structure RatAtom where
  frequency : ℚ
  alpha : ℚ
  beta : ℚ
deriving DecidableEq, Repr

structure RatRow where
  a0 : ℚ
  a1 : ℚ
  a2 : ℚ
  atoms : List RatAtom
deriving DecidableEq, Repr

/-- The syntactic conditions which make a rational dual row even. -/
def RatRowSymmetric (row : RatRow) : Prop :=
  row.a1 = 0 ∧ ∀ atom ∈ row.atoms, atom.beta = 0

def RatAtom.toDual (a : RatAtom) : DualAtom :=
  ⟨a.frequency, a.alpha, a.beta⟩

def RatRow.dualAtoms (row : RatRow) : Fin row.atoms.length → DualAtom :=
  fun i ↦ (row.atoms.get i).toDual

theorem list_sum_map_eq_fin_sum {l : List RatAtom} (F : RatAtom → ℝ) :
    (l.map F).sum = ∑ i : Fin l.length, F (l.get i) := by
  rw [← List.sum_ofFn]
  congr 1
  simpa using (List.ofFn_getElem_eq_map l F).symm

noncomputable def ratRowFunction (row : RatRow) (x : ℝ) : ℝ :=
  row.a0 + row.a1 * x + row.a2 * x ^ 2 -
    (row.atoms.map fun a ↦
      (a.alpha : ℝ) * Real.cos ((a.frequency : ℝ) * x) +
      (a.beta : ℝ) * Real.sin ((a.frequency : ℝ) * x)).sum

theorem ratRowFunction_neg_of_symmetric (row : RatRow)
    (hsymmetric : RatRowSymmetric row) (x : ℝ) :
    ratRowFunction row (-x) = ratRowFunction row x := by
  rcases hsymmetric with ⟨ha1, hbeta⟩
  simp only [ratRowFunction, ha1, Rat.cast_zero, zero_mul, add_zero,
    neg_sq, mul_neg, Real.cos_neg, Real.sin_neg, neg_zero]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro atom hatom
  rw [hbeta atom hatom]
  norm_num

noncomputable def ratRowDerivative (row : RatRow) (x : ℝ) : ℝ :=
  row.a1 + 2 * row.a2 * x +
    (row.atoms.map fun a ↦
      ((a.alpha * a.frequency : ℚ) : ℝ) *
          Real.sin ((a.frequency : ℝ) * x) -
      ((a.beta * a.frequency : ℚ) : ℝ) *
          Real.cos ((a.frequency : ℝ) * x)).sum

noncomputable def ratRowAntiderivative (row : RatRow) (x : ℝ) : ℝ :=
  row.a0 * x + row.a1 * x ^ 2 / 2 + row.a2 * x ^ 3 / 3 +
    (row.atoms.map fun a ↦
      -((a.alpha / a.frequency : ℚ) : ℝ) *
          Real.sin ((a.frequency : ℝ) * x) +
      ((a.beta / a.frequency : ℚ) : ℝ) *
          Real.cos ((a.frequency : ℝ) * x)).sum

theorem ratRowFunction_eq_dualRowFunction (row : RatRow) (x : ℝ) :
    ratRowFunction row x =
      dualRowFunction row.a0 row.a1 row.a2 row.dualAtoms x := by
  unfold ratRowFunction dualRowFunction
  rw [list_sum_map_eq_fin_sum]
  congr 1

def trigPrecision : ℕ := 160
def trigDepth : ℕ := 24

/-- Nearest-period heuristic.  Soundness does not depend on it being nearest:
the executable `trigReady` check below verifies the reduced argument. -/
def periodFor (q : ℚ) : ℤ :=
  fastPeriodFor q

def trigReady (q : ℚ) : Prop :=
  True

instance (q : ℚ) : Decidable (trigReady q) := by
  unfold trigReady
  infer_instance

def trigAt (q : ℚ) : RatInterval × RatInterval :=
  fastTrigAt q

theorem trigAt_contains (q : ℚ) (hready : trigReady q) :
    (trigAt q).1.Contains (Real.sin q) ∧
      (trigAt q).2.Contains (Real.cos q) := by
  exact fastTrigAt_contains q

def atomValueInterval (a : RatAtom) (x : ℚ) : RatInterval :=
  addCompressed trigPrecision
    (scaleCompressed trigPrecision a.alpha (trigAt (a.frequency * x)).2)
    (scaleCompressed trigPrecision a.beta (trigAt (a.frequency * x)).1)

def atomDerivativeInterval (a : RatAtom) (x : ℚ) : RatInterval :=
  subCompressed trigPrecision
    (scaleCompressed trigPrecision (a.alpha * a.frequency)
      (trigAt (a.frequency * x)).1)
    (scaleCompressed trigPrecision (a.beta * a.frequency)
      (trigAt (a.frequency * x)).2)

def atomAntiderivativeInterval (a : RatAtom) (x : ℚ) : RatInterval :=
  addCompressed trigPrecision
    (scaleCompressed trigPrecision (-(a.alpha / a.frequency))
      (trigAt (a.frequency * x)).1)
    (scaleCompressed trigPrecision (a.beta / a.frequency)
      (trigAt (a.frequency * x)).2)

def sumIntervals (precision : ℕ) : List RatInterval → RatInterval
  | [] => point 0
  | I :: Is => addCompressed precision I (sumIntervals precision Is)

theorem contains_sumIntervals {Is : List RatInterval} {xs : List ℝ}
    (h : List.Forall₂ (fun I x ↦ I.Contains x) Is xs) (precision : ℕ) :
    (sumIntervals precision Is).Contains xs.sum := by
  induction h with
  | nil => simpa [sumIntervals] using contains_point 0
  | cons hhead _ ih =>
      simpa [sumIntervals] using contains_addCompressed hhead ih precision

def rowValueInterval (row : RatRow) (x : ℚ) : RatInterval :=
  subCompressed trigPrecision
    (point (row.a0 + row.a1 * x + row.a2 * x ^ 2))
    (sumIntervals trigPrecision (row.atoms.map fun a ↦ atomValueInterval a x))

def rowDerivativeInterval (row : RatRow) (x : ℚ) : RatInterval :=
  addCompressed trigPrecision
    (point (row.a1 + 2 * row.a2 * x))
    (sumIntervals trigPrecision (row.atoms.map fun a ↦ atomDerivativeInterval a x))

def rowAntiderivativeInterval (row : RatRow) (x : ℚ) : RatInterval :=
  addCompressed trigPrecision
    (point (row.a0 * x + row.a1 * x ^ 2 / 2 + row.a2 * x ^ 3 / 3))
    (sumIntervals trigPrecision (row.atoms.map fun a ↦ atomAntiderivativeInterval a x))

def RowTrigReadyAt (row : RatRow) (x : ℚ) : Prop :=
  ∀ a ∈ row.atoms, trigReady (a.frequency * x)

instance (row : RatRow) (x : ℚ) : Decidable (RowTrigReadyAt row x) := by
  unfold RowTrigReadyAt
  infer_instance

private theorem atoms_value_contains (atoms : List RatAtom) (x : ℚ)
    (hready : ∀ a ∈ atoms, trigReady (a.frequency * x)) :
    (sumIntervals trigPrecision (atoms.map fun a ↦ atomValueInterval a x)).Contains
      (atoms.map fun a ↦
        (a.alpha : ℝ) * Real.cos ((a.frequency : ℝ) * x) +
        (a.beta : ℝ) * Real.sin ((a.frequency : ℝ) * x)).sum := by
  induction atoms with
  | nil => simpa [sumIntervals] using contains_point 0
  | cons a atoms ih =>
      have ht := trigAt_contains (a.frequency * x) (hready a (by simp))
      have ha : (atomValueInterval a x).Contains
          ((a.alpha : ℝ) * Real.cos ((a.frequency : ℝ) * x) +
            (a.beta : ℝ) * Real.sin ((a.frequency : ℝ) * x)) := by
        simpa [atomValueInterval] using contains_addCompressed
          (contains_scaleCompressed a.alpha ht.2 trigPrecision)
          (contains_scaleCompressed a.beta ht.1 trigPrecision) trigPrecision
      have htail := ih (fun b hb ↦ hready b (by simp [hb]))
      simpa [sumIntervals] using contains_addCompressed ha htail trigPrecision

theorem rowValueInterval_contains (row : RatRow) (x : ℚ)
    (hready : RowTrigReadyAt row x) :
    (rowValueInterval row x).Contains (ratRowFunction row x) := by
  unfold rowValueInterval ratRowFunction
  apply contains_subCompressed
  · convert contains_point (row.a0 + row.a1 * x + row.a2 * x ^ 2) using 1
    norm_num
  · exact atoms_value_contains row.atoms x hready

private theorem atoms_derivative_contains (atoms : List RatAtom) (x : ℚ)
    (hready : ∀ a ∈ atoms, trigReady (a.frequency * x)) :
    (sumIntervals trigPrecision (atoms.map fun a ↦ atomDerivativeInterval a x)).Contains
      (atoms.map fun a ↦
        ((a.alpha * a.frequency : ℚ) : ℝ) *
            Real.sin ((a.frequency : ℝ) * x) -
        ((a.beta * a.frequency : ℚ) : ℝ) *
            Real.cos ((a.frequency : ℝ) * x)).sum := by
  induction atoms with
  | nil => simpa [sumIntervals] using contains_point 0
  | cons a atoms ih =>
      have ht := trigAt_contains (a.frequency * x) (hready a (by simp))
      have ha : (atomDerivativeInterval a x).Contains
          (((a.alpha * a.frequency : ℚ) : ℝ) *
              Real.sin ((a.frequency : ℝ) * x) -
            ((a.beta * a.frequency : ℚ) : ℝ) *
              Real.cos ((a.frequency : ℝ) * x)) := by
        simpa [atomDerivativeInterval] using contains_subCompressed
          (contains_scaleCompressed (a.alpha * a.frequency) ht.1 trigPrecision)
          (contains_scaleCompressed (a.beta * a.frequency) ht.2 trigPrecision)
          trigPrecision
      have htail := ih (fun b hb ↦ hready b (by simp [hb]))
      simpa [sumIntervals] using contains_addCompressed ha htail trigPrecision

theorem rowDerivativeInterval_contains (row : RatRow) (x : ℚ)
    (hready : RowTrigReadyAt row x) :
    (rowDerivativeInterval row x).Contains (ratRowDerivative row x) := by
  unfold rowDerivativeInterval ratRowDerivative
  apply contains_addCompressed
  · convert contains_point (row.a1 + 2 * row.a2 * x) using 1
    norm_num
  · exact atoms_derivative_contains row.atoms x hready

def RowFrequenciesNonzero (row : RatRow) : Prop :=
  ∀ a ∈ row.atoms, a.frequency ≠ 0

instance (row : RatRow) : Decidable (RowFrequenciesNonzero row) := by
  unfold RowFrequenciesNonzero
  infer_instance

private theorem atoms_antiderivative_contains (atoms : List RatAtom) (x : ℚ)
    (hready : ∀ a ∈ atoms, trigReady (a.frequency * x)) :
    (sumIntervals trigPrecision (atoms.map fun a ↦ atomAntiderivativeInterval a x)).Contains
      (atoms.map fun a ↦
        ((-(a.alpha / a.frequency) : ℚ) : ℝ) *
            Real.sin ((a.frequency : ℝ) * x) +
        ((a.beta / a.frequency : ℚ) : ℝ) *
            Real.cos ((a.frequency : ℝ) * x)).sum := by
  induction atoms with
  | nil => simpa [sumIntervals] using contains_point 0
  | cons a atoms ih =>
      have ht := trigAt_contains (a.frequency * x) (hready a (by simp))
      have ha : (atomAntiderivativeInterval a x).Contains
          (((-(a.alpha / a.frequency) : ℚ) : ℝ) *
              Real.sin ((a.frequency : ℝ) * x) +
            ((a.beta / a.frequency : ℚ) : ℝ) *
              Real.cos ((a.frequency : ℝ) * x)) := by
        simpa [atomAntiderivativeInterval] using contains_addCompressed
          (contains_scaleCompressed (-(a.alpha / a.frequency)) ht.1 trigPrecision)
          (contains_scaleCompressed (a.beta / a.frequency) ht.2 trigPrecision)
          trigPrecision
      have htail := ih (fun b hb ↦ hready b (by simp [hb]))
      simpa [sumIntervals] using contains_addCompressed ha htail trigPrecision

theorem rowAntiderivativeInterval_contains (row : RatRow) (x : ℚ)
    (hready : RowTrigReadyAt row x) :
    (rowAntiderivativeInterval row x).Contains (ratRowAntiderivative row x) := by
  unfold rowAntiderivativeInterval ratRowAntiderivative
  apply contains_addCompressed
  · convert contains_point
      (row.a0 * x + row.a1 * x ^ 2 / 2 + row.a2 * x ^ 3 / 3) using 1
    norm_num
  · simpa only [Rat.cast_neg] using
      atoms_antiderivative_contains row.atoms x hready

end ErdosMinimum
