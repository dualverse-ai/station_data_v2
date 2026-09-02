import ErdosMinimum.BudgetComputation

/-!
# Uniformly chunked replay for even rows

This module is separate from `BudgetComputation` so the core adaptive replay
and its compiled artifact remain stable while positive-half chunks are checked.
-/

namespace ErdosMinimum

open FixedInterval

/-- Uniform partition point on the positive half interval `[0,2]`. -/
def uniformHalfPoint (cells i : ℕ) : ℚ := 2 * i / cells

/-- One independently replayable cell on the positive half interval. -/
def fixedUniformHalfCellTicks (row : RatRow) (cells depth i : ℕ) : ℤ :=
  let fixed := FixedRow.ofRatRow row
  let a := uniformHalfPoint cells i
  let b := uniformHalfPoint cells (i+1)
  fixedCellUpperFromLeft row fixed (ofRat (rowCurvatureBound row))
    depth a b (ofRat (2/cells)) (fixedRowValueDerivative fixed a)

def fixedUniformHalfBudgetTicks (row : RatRow) (cells depth : ℕ) : ℤ :=
  ∑ i ∈ Finset.range cells, fixedUniformHalfCellTicks row cells depth i

/-- Full `[-2,2]` budget obtained by doubling uniformly replayed positive-half
cells of an even row. -/
def positivePartUniformEvenBudget (row : RatRow) (cells depth : ℕ) : ℚ :=
  (2 * fixedUniformHalfBudgetTicks row cells depth : ℚ) / fixedDyadicScale

/-- One positive-half cell using fixed row and curvature data checked once by
separate equality certificates. -/
def fixedUniformHalfCellTicksPrepared (row : RatRow) (fixed : FixedRow)
    (curvature : FixedInterval) (cells depth i : ℕ) : ℤ :=
  let a := uniformHalfPoint cells i
  let b := uniformHalfPoint cells (i+1)
  fixedCellUpperFromLeft row fixed curvature depth a b (ofRat (2/cells))
    (fixedRowValueDerivative fixed a)

def fixedUniformHalfPreparedBudgetTicks (row : RatRow) (fixed : FixedRow)
    (curvature : FixedInterval) (cells depth : ℕ) : ℤ :=
  ∑ i ∈ Finset.range cells,
    fixedUniformHalfCellTicksPrepared row fixed curvature cells depth i

/-- Full even budget obtained from prepared positive-half cells. -/
def positivePartUniformPreparedEvenBudget (row : RatRow) (fixed : FixedRow)
    (curvature : FixedInterval) (cells depth : ℕ) : ℚ :=
  (2 * fixedUniformHalfPreparedBudgetTicks row fixed curvature cells depth : ℚ) /
    fixedDyadicScale

theorem positivePartUniformHalfBudget_interval_le (row : RatRow)
    (cells depth : ℕ) (hcells : 0 < cells)
    (hfreq : RowFrequenciesNonzero row) :
    (∫ x in (0:ℝ)..2, positivePart (ratRowFunction row) x) ≤
      (fixedUniformHalfBudgetTicks row cells depth : ℝ) /
        fixedDyadicScale := by
  let g : ℝ → ℝ := positivePart (ratRowFunction row)
  have hg_cont : Continuous g := by
    simpa [g, positivePart] using
      (contDiff_ratRowFunction row).continuous.max continuous_const
  have hcell (i : ℕ) (hi : i < cells) :
      (∫ x in (uniformHalfPoint cells i : ℚ)..
          uniformHalfPoint cells (i+1), g x) ≤
        (fixedUniformHalfCellTicks row cells depth i : ℝ) /
          fixedDyadicScale := by
    have hab : uniformHalfPoint cells i ≤ uniformHalfPoint cells (i+1) := by
      dsimp [uniformHalfPoint]
      have hiQ : (i : ℚ) ≤ ((i+1 : ℕ) : ℚ) := by
        exact_mod_cast Nat.le_succ i
      have hcQ : (0 : ℚ) ≤ (cells : ℚ) := by
        exact_mod_cast hcells.le
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hiQ (by norm_num : (0:ℚ) ≤ 2)) hcQ
    have hwidth : (ofRat (2/cells)).Contains
        (((uniformHalfPoint cells (i+1):ℚ):ℝ) -
          (uniformHalfPoint cells i:ℚ)) := by
      convert contains_ofRat (2/cells) using 1
      · dsimp [uniformHalfPoint]
        push_cast
        field_simp
        ring
    have h := fixedCellUpperFromLeft_interval_le row (rowCurvatureBound row)
      (fun y ↦ abs_ratRowSecondDerivative_le row y) hfreq depth
      (uniformHalfPoint cells i) (uniformHalfPoint cells (i+1))
      (ofRat (2/cells))
      (fixedRowValueDerivative (FixedRow.ofRatRow row)
        (uniformHalfPoint cells i))
      hab hwidth
      (fixedRowValueDerivative_contains row (uniformHalfPoint cells i)).1
      (fixedRowValueDerivative_contains row (uniformHalfPoint cells i)).2
    simpa [g, fixedUniformHalfCellTicks] using h
  have hsum := Finset.sum_le_sum (fun i hi ↦
    hcell i (Finset.mem_range.mp hi))
  have hintegrable (i : ℕ) (hi : i < cells) : IntervalIntegrable g
      MeasureTheory.volume (uniformHalfPoint cells i : ℚ)
        (uniformHalfPoint cells (i+1) : ℚ) :=
    hg_cont.intervalIntegrable _ _
  have htel := intervalIntegral.sum_integral_adjacent_intervals
    (f := g) (a := fun i ↦ ((uniformHalfPoint cells i : ℚ) : ℝ))
    (n := cells) hintegrable
  rw [htel] at hsum
  have hzero : ((uniformHalfPoint cells 0 : ℚ) : ℝ) = 0 := by
    simp [uniformHalfPoint]
  have hend : ((uniformHalfPoint cells cells : ℚ) : ℝ) = 2 := by
    dsimp [uniformHalfPoint]
    push_cast
    field_simp
  change (∫ x in ((uniformHalfPoint cells 0 : ℚ) : ℝ)..
      ((uniformHalfPoint cells cells : ℚ) : ℝ), g x) ≤ _ at hsum
  rw [hzero, hend] at hsum
  calc
    (∫ x in (0:ℝ)..2, positivePart (ratRowFunction row) x) =
        ∫ x in (0:ℝ)..2, g x := rfl
    _ ≤ ∑ i ∈ Finset.range cells,
        (fixedUniformHalfCellTicks row cells depth i : ℝ) /
          fixedDyadicScale := hsum
    _ = (fixedUniformHalfBudgetTicks row cells depth : ℝ) /
        fixedDyadicScale := by
      simp [fixedUniformHalfBudgetTicks]
      rw [← Finset.sum_div]

theorem positivePartUniformEvenBudget_interval_le (row : RatRow)
    (cells depth : ℕ) (hcells : 0 < cells)
    (hsymmetric : RatRowSymmetric row)
    (hfreq : RowFrequenciesNonzero row) :
    (∫ x in (-2:ℝ)..2, positivePart (ratRowFunction row) x) ≤
      (positivePartUniformEvenBudget row cells depth : ℝ) := by
  let g : ℝ → ℝ := positivePart (ratRowFunction row)
  have hg_even (x : ℝ) : g (-x) = g x := by
    simp only [g, positivePart, ratRowFunction_neg_of_symmetric row hsymmetric]
  have hg_cont : Continuous g := by
    simpa [g, positivePart] using
      (contDiff_ratRowFunction row).continuous.max continuous_const
  have hneg : (∫ x in (-2:ℝ)..0, g x) = ∫ x in (0:ℝ)..2, g x := by
    calc
      (∫ x in (-2:ℝ)..0, g x) = ∫ x in (0:ℝ)..2, g (-x) := by
        symm
        simpa using (intervalIntegral.integral_comp_neg (f := g)
          (a := (0:ℝ)) (b := 2))
      _ = ∫ x in (0:ℝ)..2, g x := by
        apply intervalIntegral.integral_congr
        intro x _
        exact hg_even x
  have hsplit : (∫ x in (-2:ℝ)..2, g x) =
      (∫ x in (-2:ℝ)..0, g x) + ∫ x in (0:ℝ)..2, g x := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hg_cont.intervalIntegrable (-2) 0) (hg_cont.intervalIntegrable 0 2)]
  have hhalf := positivePartUniformHalfBudget_interval_le row cells depth
    hcells hfreq
  rw [hsplit, hneg]
  calc
    (∫ x in (0:ℝ)..2, g x) + ∫ x in (0:ℝ)..2, g x ≤
        2 * ((fixedUniformHalfBudgetTicks row cells depth : ℝ) /
          fixedDyadicScale) := by
      dsimp [g] at hhalf ⊢
      linarith
    _ = (positivePartUniformEvenBudget row cells depth : ℝ) := by
      simp [positivePartUniformEvenBudget, fixedUniformHalfBudgetTicks]
      push_cast
      ring

theorem positivePartUniformPreparedEvenBudget_interval_le (row : RatRow)
    (fixed : FixedRow) (curvature : FixedInterval) (cells depth : ℕ)
    (hfixed : fixed = FixedRow.ofRatRow row)
    (hcurvature : curvature = ofRat (rowCurvatureBound row))
    (hcells : 0 < cells) (hsymmetric : RatRowSymmetric row)
    (hfreq : RowFrequenciesNonzero row) :
    (∫ x in (-2:ℝ)..2, positivePart (ratRowFunction row) x) ≤
      (positivePartUniformPreparedEvenBudget row fixed curvature cells depth : ℝ) := by
  subst fixed
  subst curvature
  simpa [positivePartUniformPreparedEvenBudget,
    fixedUniformHalfPreparedBudgetTicks, fixedUniformHalfCellTicksPrepared,
    positivePartUniformEvenBudget, fixedUniformHalfBudgetTicks,
    fixedUniformHalfCellTicks] using
      positivePartUniformEvenBudget_interval_le row cells depth hcells
        hsymmetric hfreq

end ErdosMinimum
