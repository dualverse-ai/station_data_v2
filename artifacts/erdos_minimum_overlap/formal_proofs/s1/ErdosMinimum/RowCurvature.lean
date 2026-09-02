import ErdosMinimum.NumericRow
import ErdosMinimum.SecondOrderRange

/-!
# Global curvature bound for executable dual rows

The bound is independent of `x`; it uses only `|sin|, |cos| ≤ 1` and is
therefore especially cheap to replay once per row.
-/

namespace ErdosMinimum

/-- The explicit second derivative of a rational dual row. -/
noncomputable def ratRowSecondDerivative (row : RatRow) (x : ℝ) : ℝ :=
  2 * row.a2 +
    (row.atoms.map fun a ↦
      ((a.alpha * a.frequency ^ 2 : ℚ) : ℝ) *
          Real.cos ((a.frequency : ℝ) * x) +
      ((a.beta * a.frequency ^ 2 : ℚ) : ℝ) *
          Real.sin ((a.frequency : ℝ) * x)).sum

/-- Exact rational global upper bound for the absolute second derivative. -/
def rowCurvatureBound (row : RatRow) : ℚ :=
  |2 * row.a2| +
    (row.atoms.map fun a ↦
      |a.alpha * a.frequency ^ 2| + |a.beta * a.frequency ^ 2|).sum

private theorem hasDerivAt_atom_value (a : RatAtom) (x : ℝ) :
    HasDerivAt (fun y : ℝ =>
      (a.alpha : ℝ) * Real.cos ((a.frequency : ℝ) * y) +
      (a.beta : ℝ) * Real.sin ((a.frequency : ℝ) * y))
      (-((a.alpha * a.frequency : ℚ) : ℝ) *
          Real.sin ((a.frequency : ℝ) * x) +
       ((a.beta * a.frequency : ℚ) : ℝ) *
          Real.cos ((a.frequency : ℝ) * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ => (a.frequency : ℝ) * y)
      (a.frequency : ℝ) x := by
    simpa using (hasDerivAt_id x).const_mul (a.frequency : ℝ)
  have hc := (Real.hasDerivAt_cos ((a.frequency : ℝ) * x)).comp x hlin
  have hs := (Real.hasDerivAt_sin ((a.frequency : ℝ) * x)).comp x hlin
  convert (hc.const_mul (a.alpha : ℝ)).add (hs.const_mul (a.beta : ℝ)) using 1
  all_goals push_cast
  all_goals ring

private theorem hasDerivAt_atom_derivative (a : RatAtom) (x : ℝ) :
    HasDerivAt (fun y : ℝ =>
      ((a.alpha * a.frequency : ℚ) : ℝ) *
          Real.sin ((a.frequency : ℝ) * y) -
      ((a.beta * a.frequency : ℚ) : ℝ) *
          Real.cos ((a.frequency : ℝ) * y))
      (((a.alpha * a.frequency ^ 2 : ℚ) : ℝ) *
          Real.cos ((a.frequency : ℝ) * x) +
       ((a.beta * a.frequency ^ 2 : ℚ) : ℝ) *
          Real.sin ((a.frequency : ℝ) * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ => (a.frequency : ℝ) * y)
      (a.frequency : ℝ) x := by
    simpa using (hasDerivAt_id x).const_mul (a.frequency : ℝ)
  have hs := (Real.hasDerivAt_sin ((a.frequency : ℝ) * x)).comp x hlin
  have hc := (Real.hasDerivAt_cos ((a.frequency : ℝ) * x)).comp x hlin
  convert (hs.const_mul (((a.alpha * a.frequency : ℚ) : ℝ))).sub
    (hc.const_mul (((a.beta * a.frequency : ℚ) : ℝ))) using 1
  all_goals push_cast
  all_goals ring

private theorem hasDerivAt_atoms_value (atoms : List RatAtom) (x : ℝ) :
    HasDerivAt (fun y : ℝ =>
      (atoms.map fun a ↦
        (a.alpha : ℝ) * Real.cos ((a.frequency : ℝ) * y) +
        (a.beta : ℝ) * Real.sin ((a.frequency : ℝ) * y)).sum)
      ((atoms.map fun a ↦
        -((a.alpha * a.frequency : ℚ) : ℝ) *
            Real.sin ((a.frequency : ℝ) * x) +
        ((a.beta * a.frequency : ℚ) : ℝ) *
            Real.cos ((a.frequency : ℝ) * x)).sum) x := by
  induction atoms with
  | nil => simpa using hasDerivAt_const x (0 : ℝ)
  | cons a atoms ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (hasDerivAt_atom_value a x).add ih

private theorem hasDerivAt_atoms_derivative (atoms : List RatAtom) (x : ℝ) :
    HasDerivAt (fun y : ℝ =>
      (atoms.map fun a ↦
        ((a.alpha * a.frequency : ℚ) : ℝ) *
            Real.sin ((a.frequency : ℝ) * y) -
        ((a.beta * a.frequency : ℚ) : ℝ) *
            Real.cos ((a.frequency : ℝ) * y)).sum)
      ((atoms.map fun a ↦
        ((a.alpha * a.frequency ^ 2 : ℚ) : ℝ) *
            Real.cos ((a.frequency : ℝ) * x) +
        ((a.beta * a.frequency ^ 2 : ℚ) : ℝ) *
            Real.sin ((a.frequency : ℝ) * x)).sum) x := by
  induction atoms with
  | nil => simpa using hasDerivAt_const x (0 : ℝ)
  | cons a atoms ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (hasDerivAt_atom_derivative a x).add ih

private theorem hasDerivAt_atom_antiderivative (a : RatAtom) (x : ℝ)
    (hfreq : a.frequency ≠ 0) :
    HasDerivAt (fun y : ℝ =>
      -((a.alpha / a.frequency : ℚ) : ℝ) *
          Real.sin ((a.frequency : ℝ) * y) +
      ((a.beta / a.frequency : ℚ) : ℝ) *
          Real.cos ((a.frequency : ℝ) * y))
      (-((a.alpha : ℚ) : ℝ) * Real.cos ((a.frequency : ℝ) * x) -
       ((a.beta : ℚ) : ℝ) * Real.sin ((a.frequency : ℝ) * x)) x := by
  have hlin : HasDerivAt (fun y : ℝ => (a.frequency : ℝ) * y)
      (a.frequency : ℝ) x := by
    simpa using (hasDerivAt_id x).const_mul (a.frequency : ℝ)
  have hs := (Real.hasDerivAt_sin ((a.frequency : ℝ) * x)).comp x hlin
  have hc := (Real.hasDerivAt_cos ((a.frequency : ℝ) * x)).comp x hlin
  convert (hs.const_mul (-((a.alpha / a.frequency : ℚ) : ℝ))).add
    (hc.const_mul (((a.beta / a.frequency : ℚ) : ℝ))) using 1
  all_goals push_cast
  all_goals field_simp
  all_goals ring

private theorem hasDerivAt_atoms_antiderivative (atoms : List RatAtom) (x : ℝ)
    (hfreq : ∀ a ∈ atoms, a.frequency ≠ 0) :
    HasDerivAt (fun y : ℝ =>
      (atoms.map fun a ↦
        -((a.alpha / a.frequency : ℚ) : ℝ) *
            Real.sin ((a.frequency : ℝ) * y) +
        ((a.beta / a.frequency : ℚ) : ℝ) *
            Real.cos ((a.frequency : ℝ) * y)).sum)
      ((atoms.map fun a ↦
        -((a.alpha : ℚ) : ℝ) * Real.cos ((a.frequency : ℝ) * x) -
        ((a.beta : ℚ) : ℝ) * Real.sin ((a.frequency : ℝ) * x)).sum) x := by
  induction atoms with
  | nil => simpa using hasDerivAt_const x (0 : ℝ)
  | cons a atoms ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (hasDerivAt_atom_antiderivative a x (hfreq a (by simp))).add
        (ih fun b hb ↦ hfreq b (by simp [hb]))

private theorem contDiff_atoms_value (atoms : List RatAtom) :
    ContDiff ℝ 2 (fun y : ℝ =>
      (atoms.map fun a ↦
        (a.alpha : ℝ) * Real.cos ((a.frequency : ℝ) * y) +
        (a.beta : ℝ) * Real.sin ((a.frequency : ℝ) * y)).sum) := by
  induction atoms with
  | nil => simpa using (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => (0 : ℝ)))
  | cons a atoms ih =>
      simp only [List.map_cons, List.sum_cons]
      apply ContDiff.add
      · fun_prop
      · exact ih

theorem contDiff_ratRowFunction (row : RatRow) : ContDiff ℝ 2 (ratRowFunction row) := by
  unfold ratRowFunction
  apply ContDiff.sub
  · fun_prop
  · exact contDiff_atoms_value row.atoms

theorem hasDerivAt_ratRowFunction (row : RatRow) (x : ℝ) :
    HasDerivAt (ratRowFunction row) (ratRowDerivative row x) x := by
  unfold ratRowFunction ratRowDerivative
  have hpoly : HasDerivAt
      (fun y : ℝ => (row.a0 : ℝ) + row.a1 * y + row.a2 * y ^ 2)
      ((row.a1 : ℝ) + 2 * row.a2 * x) x := by
    convert (((hasDerivAt_const x (row.a0 : ℝ)).add
      ((hasDerivAt_id x).const_mul (row.a1 : ℝ))).add
      (((hasDerivAt_id x).pow 2).const_mul (row.a2 : ℝ))) using 1
    all_goals simp [id]
    all_goals ring
  have hsum :
      (row.atoms.map fun a ↦
        ((a.alpha * a.frequency : ℚ) : ℝ) *
            Real.sin ((a.frequency : ℝ) * x) -
        ((a.beta * a.frequency : ℚ) : ℝ) *
            Real.cos ((a.frequency : ℝ) * x)).sum =
      -(row.atoms.map fun a ↦
        -((a.alpha * a.frequency : ℚ) : ℝ) *
            Real.sin ((a.frequency : ℝ) * x) +
        ((a.beta * a.frequency : ℚ) : ℝ) *
            Real.cos ((a.frequency : ℝ) * x)).sum := by
    induction row.atoms with
    | nil => simp
    | cons a atoms ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        ring
  convert hpoly.sub (hasDerivAt_atoms_value row.atoms x) using 1
  rw [hsum]
  ring

theorem deriv_ratRowFunction (row : RatRow) (x : ℝ) :
    deriv (ratRowFunction row) x = ratRowDerivative row x :=
  (hasDerivAt_ratRowFunction row x).deriv

/-- The executable antiderivative differentiates to the row function whenever
all atom frequencies are nonzero. -/
theorem hasDerivAt_ratRowAntiderivative (row : RatRow) (x : ℝ)
    (hfreq : RowFrequenciesNonzero row) :
    HasDerivAt (ratRowAntiderivative row) (ratRowFunction row x) x := by
  unfold ratRowAntiderivative ratRowFunction
  have hpoly : HasDerivAt
      (fun y : ℝ => (row.a0 : ℝ) * y + row.a1 * y ^ 2 / 2 + row.a2 * y ^ 3 / 3)
      ((row.a0 : ℝ) + row.a1 * x + row.a2 * x ^ 2) x := by
    convert ((((hasDerivAt_id x).const_mul (row.a0 : ℝ)).add
      (((hasDerivAt_id x).pow 2).const_mul (row.a1 : ℝ) |>.div_const 2)).add
      (((hasDerivAt_id x).pow 3).const_mul (row.a2 : ℝ) |>.div_const 3)) using 1
    all_goals simp [id]
    all_goals ring
  have hatoms := hasDerivAt_atoms_antiderivative row.atoms x hfreq
  have hsum :
      (row.atoms.map fun a ↦
        -((a.alpha : ℚ) : ℝ) * Real.cos ((a.frequency : ℝ) * x) -
        ((a.beta : ℚ) : ℝ) * Real.sin ((a.frequency : ℝ) * x)).sum =
      -(row.atoms.map fun a ↦
        (a.alpha : ℝ) * Real.cos ((a.frequency : ℝ) * x) +
        (a.beta : ℝ) * Real.sin ((a.frequency : ℝ) * x)).sum := by
    induction row.atoms with
    | nil => simp
    | cons a atoms ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [ih]
        ring
  convert hpoly.add hatoms using 1
  rw [hsum]
  ring

theorem hasDerivAt_ratRowDerivative (row : RatRow) (x : ℝ) :
    HasDerivAt (ratRowDerivative row) (ratRowSecondDerivative row x) x := by
  unfold ratRowDerivative ratRowSecondDerivative
  have hpoly : HasDerivAt (fun y : ℝ => (row.a1 : ℝ) + 2 * row.a2 * y)
      (2 * row.a2 : ℝ) x := by
    convert (hasDerivAt_const x (row.a1 : ℝ)).add
      ((hasDerivAt_id x).const_mul (2 * row.a2 : ℝ)) using 1
    all_goals ring
  exact hpoly.add (hasDerivAt_atoms_derivative row.atoms x)

theorem iteratedDeriv_two_ratRowFunction (row : RatRow) (x : ℝ) :
    iteratedDeriv 2 (ratRowFunction row) x = ratRowSecondDerivative row x := by
  rw [show 2 = Nat.succ 1 by omega, iteratedDeriv_succ]
  rw [show 1 = Nat.succ 0 by omega, iteratedDeriv_succ]
  rw [iteratedDeriv_zero]
  rw [show deriv (ratRowFunction row) = ratRowDerivative row from
    funext (deriv_ratRowFunction row)]
  exact (hasDerivAt_ratRowDerivative row x).deriv

private theorem atom_second_abs_le (a : RatAtom) (x : ℝ) :
    |((a.alpha * a.frequency ^ 2 : ℚ) : ℝ) *
          Real.cos ((a.frequency : ℝ) * x) +
      ((a.beta * a.frequency ^ 2 : ℚ) : ℝ) *
          Real.sin ((a.frequency : ℝ) * x)| ≤
      ((|a.alpha * a.frequency ^ 2| + |a.beta * a.frequency ^ 2| : ℚ) : ℝ) := by
  calc
    |_ + _| ≤
        |((a.alpha * a.frequency ^ 2 : ℚ) : ℝ) *
          Real.cos ((a.frequency : ℝ) * x)| +
        |((a.beta * a.frequency ^ 2 : ℚ) : ℝ) *
          Real.sin ((a.frequency : ℝ) * x)| := abs_add_le _ _
    _ = |((a.alpha * a.frequency ^ 2 : ℚ) : ℝ)| *
          |Real.cos ((a.frequency : ℝ) * x)| +
        |((a.beta * a.frequency ^ 2 : ℚ) : ℝ)| *
          |Real.sin ((a.frequency : ℝ) * x)| := by rw [abs_mul, abs_mul]
    _ ≤ |((a.alpha * a.frequency ^ 2 : ℚ) : ℝ)| +
        |((a.beta * a.frequency ^ 2 : ℚ) : ℝ)| := by
      exact add_le_add
        (by
          calc
            |((a.alpha * a.frequency ^ 2 : ℚ) : ℝ)| *
                |Real.cos ((a.frequency : ℝ) * x)| ≤
                |((a.alpha * a.frequency ^ 2 : ℚ) : ℝ)| * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _)
            _ = _ := mul_one _)
        (by
          calc
            |((a.beta * a.frequency ^ 2 : ℚ) : ℝ)| *
                |Real.sin ((a.frequency : ℝ) * x)| ≤
                |((a.beta * a.frequency ^ 2 : ℚ) : ℝ)| * 1 :=
              mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)
            _ = _ := mul_one _)
    _ = ((|a.alpha * a.frequency ^ 2| + |a.beta * a.frequency ^ 2| : ℚ) : ℝ) := by
      rw [Rat.cast_add, Rat.cast_abs, Rat.cast_abs]

private theorem atoms_second_abs_le (atoms : List RatAtom) (x : ℝ) :
    |(atoms.map fun a ↦
      ((a.alpha * a.frequency ^ 2 : ℚ) : ℝ) *
          Real.cos ((a.frequency : ℝ) * x) +
      ((a.beta * a.frequency ^ 2 : ℚ) : ℝ) *
          Real.sin ((a.frequency : ℝ) * x)).sum| ≤
    (((atoms.map fun a ↦
      |a.alpha * a.frequency ^ 2| + |a.beta * a.frequency ^ 2|).sum : ℚ) : ℝ) := by
  induction atoms with
  | nil => simp
  | cons a atoms ih =>
      simp only [List.map_cons, List.sum_cons]
      calc
        |_ + _| ≤ |_| + |_| := abs_add_le _ _
        _ ≤ ((|a.alpha * a.frequency ^ 2| + |a.beta * a.frequency ^ 2| : ℚ) : ℝ) +
            (((atoms.map fun b ↦
              |b.alpha * b.frequency ^ 2| + |b.beta * b.frequency ^ 2|).sum : ℚ) : ℝ) :=
          add_le_add (atom_second_abs_le a x) ih
        _ = _ := by push_cast; rfl

theorem abs_ratRowSecondDerivative_le (row : RatRow) (x : ℝ) :
    |ratRowSecondDerivative row x| ≤ (rowCurvatureBound row : ℝ) := by
  unfold ratRowSecondDerivative rowCurvatureBound
  calc
    |_ + _| ≤ |2 * (row.a2 : ℝ)| +
        |(row.atoms.map fun a ↦
          ((a.alpha * a.frequency ^ 2 : ℚ) : ℝ) *
              Real.cos ((a.frequency : ℝ) * x) +
          ((a.beta * a.frequency ^ 2 : ℚ) : ℝ) *
              Real.sin ((a.frequency : ℝ) * x)).sum| := abs_add_le _ _
    _ = ((|2 * row.a2| : ℚ) : ℝ) +
        |(row.atoms.map fun a ↦
          ((a.alpha * a.frequency ^ 2 : ℚ) : ℝ) *
              Real.cos ((a.frequency : ℝ) * x) +
          ((a.beta * a.frequency ^ 2 : ℚ) : ℝ) *
              Real.sin ((a.frequency : ℝ) * x)).sum| := by push_cast; rfl
    _ ≤ ((|2 * row.a2| : ℚ) : ℝ) +
        (((row.atoms.map fun a ↦
          |a.alpha * a.frequency ^ 2| + |a.beta * a.frequency ^ 2|).sum : ℚ) : ℝ) := by
      simpa [add_comm] using
        add_le_add_right (atoms_second_abs_le row.atoms x) ((|2 * row.a2| : ℚ) : ℝ)
    _ = _ := by push_cast; simp

/-- Whole-cell enclosure for a row, using only the value and derivative
enclosures at the left endpoint and the global curvature bound. -/
def rowCellInterval (row : RatRow) (a b : ℚ) : RatInterval :=
  secondOrderCell (rowValueInterval row a) (rowDerivativeInterval row a)
    (b - a) (rowCurvatureBound row)

theorem rowCellInterval_contains (row : RatRow) {a b : ℚ} {x : ℝ}
    (hab : a ≤ b) (hx : (a : ℝ) ≤ x ∧ x ≤ (b : ℝ))
    (hready : RowTrigReadyAt row a) :
    (rowCellInterval row a b).Contains (ratRowFunction row x) := by
  unfold rowCellInterval
  apply secondOrderCell_contains hab hx
  · exact rowValueInterval_contains row a hready
  · simpa [deriv_ratRowFunction] using rowDerivativeInterval_contains row a hready
  · exact contDiff_ratRowFunction row
  · intro y _
    rw [iteratedDeriv_two_ratRowFunction]
    exact abs_ratRowSecondDerivative_le row y

end ErdosMinimum
