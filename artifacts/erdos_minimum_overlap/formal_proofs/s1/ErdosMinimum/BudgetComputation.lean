import ErdosMinimum.RowCurvature
import ErdosMinimum.IntervalPartition
import ErdosMinimum.FixedDyadic

/-!
# Executable adaptive positive-part budget

This is the exact-rational analogue of the MPFI subdivision checker.  Its
soundness theorem is kept next to the executable recursion so the branch
decisions cannot drift away from the proof.
-/

namespace ErdosMinimum

open RatInterval

namespace FixedInterval

def hull (I J : FixedInterval) : FixedInterval :=
  ⟨min I.lo J.lo, max I.hi J.hi⟩

def widenUpper (I remainder : FixedInterval) : FixedInterval :=
  ⟨I.lo - remainder.hi, I.hi + remainder.hi⟩

theorem contains_hull_left {I J : FixedInterval} {x : ℝ}
    (hx : I.Contains x) : (hull I J).Contains x := by
  rcases hx with ⟨hlo, hhi⟩
  constructor
  · exact (div_le_div_of_nonneg_right (by exact_mod_cast min_le_left I.lo J.lo)
      (by exact_mod_cast fixedDyadicScale_pos.le)).trans hlo
  · exact hhi.trans (div_le_div_of_nonneg_right
      (by exact_mod_cast le_max_left I.hi J.hi)
      (by exact_mod_cast fixedDyadicScale_pos.le))

theorem contains_hull_right {I J : FixedInterval} {x : ℝ}
    (hx : J.Contains x) : (hull I J).Contains x := by
  rcases hx with ⟨hlo, hhi⟩
  constructor
  · exact (div_le_div_of_nonneg_right (by exact_mod_cast min_le_right I.lo J.lo)
      (by exact_mod_cast fixedDyadicScale_pos.le)).trans hlo
  · exact hhi.trans (div_le_div_of_nonneg_right
      (by exact_mod_cast le_max_right I.hi J.hi)
      (by exact_mod_cast fixedDyadicScale_pos.le))

theorem contains_widenUpper {I R : FixedInterval} {p z r : ℝ}
    (hp : I.Contains p) (hr : R.Contains r) (hr0 : 0 ≤ r)
    (herr : |z-p| ≤ r) : (widenUpper I R).Contains z := by
  rcases hp with ⟨hplo, hphi⟩
  have hrhi := hr.2
  rcases abs_le.mp herr with ⟨herrlo, herrhi⟩
  constructor
  · dsimp [Contains, widenUpper]
    push_cast
    rw [show ((I.lo:ℝ)-(R.hi:ℝ))/fixedDyadicScale =
      (I.lo:ℝ)/fixedDyadicScale-(R.hi:ℝ)/fixedDyadicScale by ring]
    linarith
  · dsimp [Contains, widenUpper]
    push_cast
    rw [show ((I.hi:ℝ)+(R.hi:ℝ))/fixedDyadicScale =
      (I.hi:ℝ)/fixedDyadicScale+(R.hi:ℝ)/fixedDyadicScale by ring]
    linarith

end FixedInterval

open FixedInterval

def fixedHalf : FixedInterval := ofRat (1/2)

/-- Fixed-dyadic second-order Taylor range for a half-cell. -/
def fixedSecondOrderCell (value deriv width curvature : FixedInterval) :
    FixedInterval :=
  let delta : FixedInterval := ⟨0, width.hi⟩
  let linear := add value (mul deriv delta)
  let remainder := mul fixedHalf (mul curvature (mul width width))
  widenUpper linear remainder

def fixedCellRangeFromVD (curvature halfWidth : FixedInterval)
    (left middle : FixedInterval × FixedInterval) : FixedInterval :=
  hull
    (fixedSecondOrderCell left.1 left.2 halfWidth curvature)
    (fixedSecondOrderCell middle.1 middle.2 halfWidth curvature)

theorem fixedSecondOrderCell_contains {f : ℝ → ℝ} {a b : ℚ} {x M : ℝ}
    {value derivAtLeft width curvature : FixedInterval}
    (hab : a ≤ b) (hx : (a:ℝ) ≤ x ∧ x ≤ (b:ℝ))
    (hvalue : value.Contains (f a))
    (hderiv : derivAtLeft.Contains (deriv f a))
    (hwidth : width.Contains ((b:ℝ)-(a:ℝ)))
    (hcurvature : curvature.Contains M)
    (hcurv : ∀ y ∈ Set.Icc (a:ℝ) (b:ℝ),
      |iteratedDeriv 2 f y| ≤ M)
    (hf : ContDiff ℝ 2 f) :
    (fixedSecondOrderCell value derivAtLeft width curvature).Contains (f x) := by
  have hdelta0 : 0 ≤ x-(a:ℝ) := sub_nonneg.mpr hx.1
  have hdeltaw : x-(a:ℝ) ≤ (width.hi:ℝ)/fixedDyadicScale :=
    (sub_le_sub_right hx.2 (a:ℝ)).trans hwidth.2
  have hdelta : (⟨0, width.hi⟩ : FixedInterval).Contains (x-(a:ℝ)) := by
    exact ⟨by simpa [FixedInterval.Contains] using hdelta0, hdeltaw⟩
  have hlinear := contains_add hvalue (contains_mul hderiv hdelta)
  have hw0 : 0 ≤ (b:ℝ)-(a:ℝ) := sub_nonneg.mpr (by exact_mod_cast hab)
  have hhalf := contains_ofRat (1/2)
  have hw2 := contains_mul hwidth hwidth
  have hcrem := contains_mul hcurvature hw2
  have hremI := contains_mul hhalf hcrem
  have hM0 : 0 ≤ M :=
    (abs_nonneg (iteratedDeriv 2 f (a:ℝ))).trans
      (hcurv _ ⟨le_rfl, by exact_mod_cast hab⟩)
  have hrem0 : 0 ≤ (((1/2:ℚ):ℝ)) *
      (M *
        (((b:ℝ)-(a:ℝ))*((b:ℝ)-(a:ℝ)))) := by positivity
  apply contains_widenUpper hlinear hremI hrem0
  have htaylor := abs_sub_taylor_one_le hx.1 hf (fun y hy ↦
    hcurv y ⟨hy.1, hy.2.trans hx.2⟩)
  calc
    |f x - (f (a:ℝ) + deriv f (a:ℝ) * (x-(a:ℝ)))| ≤
        M * (x-(a:ℝ))^2/2 := htaylor
    _ ≤ M * ((b:ℝ)-(a:ℝ))^2/2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply mul_le_mul_of_nonneg_left _ hM0
      exact (sq_le_sq₀ hdelta0 hw0).2 (by linarith [hx.2])
    _ = (((1/2:ℚ):ℝ)) * (M *
        (((b:ℝ)-(a:ℝ))*((b:ℝ)-(a:ℝ)))) := by ring

/-- Cell range from already available left-endpoint and midpoint value/derivative
enclosures. -/
def cellRangeFromVD (curvature a b : ℚ)
    (left middle : FixedInterval × FixedInterval) : RatInterval :=
  let mid := (a + b) / 2
  compress trigPrecision <| hull
    (secondOrderCell left.1.toRatInterval left.2.toRatInterval
      (mid - a) curvature)
    (secondOrderCell middle.1.toRatInterval middle.2.toRatInterval
      (b - mid) curvature)

def cellRange (_row : RatRow) (fixed : FixedRow) (curvature a b : ℚ) : RatInterval :=
  let mid := (a + b) / 2
  cellRangeFromVD curvature a b
    (fixedRowValueDerivative fixed a)
    (fixedRowValueDerivative fixed mid)

def positiveCellUpper (fixed : FixedRow) (a b : ℚ) : ℚ :=
  (fixedRowAntiderivative fixed b).toRatInterval.hi -
    (fixedRowAntiderivative fixed a).toRatInterval.lo

def terminalCellUpper (row : RatRow) (fixed : FixedRow)
    (curvature a b : ℚ) : ℚ :=
  (b - a) * max (cellRange row fixed curvature a b).hi 0

def terminalCellUpperFromRange (a b : ℚ) (range : RatInterval) : ℚ :=
  (b - a) * max range.hi 0

def cellUpperFromLeft (row : RatRow) (fixed : FixedRow)
    (curvature : ℚ) :
    ℕ → ℚ → ℚ → (FixedInterval × FixedInterval) → ℚ
  | depth, a, b, left =>
      let mid := (a + b) / 2
      let middle := fixedRowValueDerivative fixed mid
      let range := cellRangeFromVD curvature a b left middle
      if range.hi ≤ 0 then 0
      else if 0 ≤ range.lo then positiveCellUpper fixed a b
      else match depth with
        | 0 => terminalCellUpperFromRange a b range
        | d + 1 =>
            cellUpperFromLeft row fixed curvature d a mid left +
              cellUpperFromLeft row fixed curvature d mid b middle

def cellUpper (row : RatRow) (fixed : FixedRow)
    (curvature : ℚ) (depth : ℕ) (a b : ℚ) : ℚ :=
  cellUpperFromLeft row fixed curvature depth a b
    (fixedRowValueDerivative fixed a)

def positivePartBudgetRational (row : RatRow) (depth : ℕ) : ℚ :=
  let fixed := FixedRow.ofRatRow row
  let curvature := rowCurvatureBound row
  cellUpper row fixed curvature depth (-2) 2

/-! ## Fixed-dyadic hot recursion -/

def fixedTerminalUpper (width range : FixedInterval) : ℤ :=
  let upper : FixedInterval := ⟨max range.hi 0, max range.hi 0⟩
  (mul width upper).hi

def fixedPositiveCellUpper (fixed : FixedRow) (a b : ℚ) : ℤ :=
  (fixedRowAntiderivative fixed b).hi - (fixedRowAntiderivative fixed a).lo

def fixedCellUpperFromLeft (row : RatRow) (fixed : FixedRow)
    (curvature : FixedInterval) :
    ℕ → ℚ → ℚ → FixedInterval →
      (FixedInterval × FixedInterval) → ℤ
  | depth, a, b, width, left =>
      let mid := (a+b)/2
      let halfWidth := mul fixedHalf width
      let middle := fixedRowValueDerivative fixed mid
      let range := fixedCellRangeFromVD curvature halfWidth left middle
      if range.hi ≤ 0 then 0
      else if 0 ≤ range.lo then fixedPositiveCellUpper fixed a b
      else match depth with
        | 0 => fixedTerminalUpper width range
        | d+1 =>
            fixedCellUpperFromLeft row fixed curvature d a mid halfWidth left +
              fixedCellUpperFromLeft row fixed curvature d mid b halfWidth middle

def fixedPositivePartBudgetTicks (row : RatRow) (depth : ℕ) : ℤ :=
  let fixed := FixedRow.ofRatRow row
  fixedCellUpperFromLeft row fixed (ofRat (rowCurvatureBound row))
    depth (-2) 2 (ofRat 4) (fixedRowValueDerivative fixed (-2))

def positivePartBudgetFixed (row : RatRow) (depth : ℕ) : ℚ :=
  (fixedPositivePartBudgetTicks row depth : ℚ) / fixedDyadicScale

/-- Public budget API: the hot recursion remains fixed-dyadic and converts
its final integer upper bound to an exact rational only once. -/
def positivePartBudget (row : RatRow) (depth : ℕ) : ℚ :=
  positivePartBudgetFixed row depth

/-- Fixed-dyadic replay on the positive half of an even row. -/
def fixedPositivePartHalfBudgetTicks (row : RatRow) (depth : ℕ) : ℤ :=
  let fixed := FixedRow.ofRatRow row
  fixedCellUpperFromLeft row fixed (ofRat (rowCurvatureBound row))
    depth 0 2 (ofRat 2) (fixedRowValueDerivative fixed 0)

/-- Full `[-2,2]` budget obtained by doubling the positive-half replay of an
even row. -/
def positivePartEvenBudget (row : RatRow) (depth : ℕ) : ℚ :=
  (2 * fixedPositivePartHalfBudgetTicks row depth : ℚ) / fixedDyadicScale

/-! ## Uniformly chunked replay

The chunked form has the same semantic guarantee as the adaptive root
replay, but permits each closed cell calculation to be proved independently.
This bounds elaborator memory during kernel-only checking.
-/

def uniformPoint (cells i : ℕ) : ℚ := -2 + 4 * i / cells

def fixedUniformCellTicks (row : RatRow) (cells depth i : ℕ) : ℤ :=
  let fixed := FixedRow.ofRatRow row
  let a := uniformPoint cells i
  let b := uniformPoint cells (i+1)
  fixedCellUpperFromLeft row fixed (ofRat (rowCurvatureBound row))
    depth a b (ofRat (4/cells)) (fixedRowValueDerivative fixed a)

def fixedUniformBudgetTicks (row : RatRow) (cells depth : ℕ) : ℤ :=
  ∑ i ∈ Finset.range cells, fixedUniformCellTicks row cells depth i

def positivePartUniformBudget (row : RatRow) (cells depth : ℕ) : ℚ :=
  (fixedUniformBudgetTicks row cells depth : ℚ) / fixedDyadicScale

/-! ## Prepared uniformly chunked replay

The fixed row and curvature enclosure can be generated once and checked once,
then reused by every independent cell declaration.  The soundness theorem
below requires definitional equality with the canonical conversions, so these
arguments cannot alter the certified calculation.
-/

def fixedUniformCellTicksPrepared (row : RatRow) (fixed : FixedRow)
    (curvature : FixedInterval) (cells depth i : ℕ) : ℤ :=
  let a := uniformPoint cells i
  let b := uniformPoint cells (i+1)
  fixedCellUpperFromLeft row fixed curvature depth a b (ofRat (4/cells))
    (fixedRowValueDerivative fixed a)

def fixedUniformPreparedBudgetTicks (row : RatRow) (fixed : FixedRow)
    (curvature : FixedInterval) (cells depth : ℕ) : ℤ :=
  ∑ i ∈ Finset.range cells,
    fixedUniformCellTicksPrepared row fixed curvature cells depth i

def positivePartUniformPreparedBudget (row : RatRow) (fixed : FixedRow)
    (curvature : FixedInterval) (cells depth : ℕ) : ℚ :=
  (fixedUniformPreparedBudgetTicks row fixed curvature cells depth : ℚ) /
    fixedDyadicScale

theorem fixedCellRangeFromVD_contains (row : RatRow) (curvature : ℚ)
    {a b : ℚ} {x : ℝ} (halfWidth : FixedInterval)
    (left middle : FixedInterval × FixedInterval)
    (hab : a ≤ b) (hx : (a:ℝ) ≤ x ∧ x ≤ (b:ℝ))
    (hwidth : halfWidth.Contains ((((a+b)/2:ℚ):ℝ)-(a:ℝ)))
    (hleftV : left.1.Contains (ratRowFunction row a))
    (hleftD : left.2.Contains (ratRowDerivative row a))
    (hmiddleV : middle.1.Contains (ratRowFunction row (((a+b)/2:ℚ):ℝ)))
    (hmiddleD : middle.2.Contains (ratRowDerivative row (((a+b)/2:ℚ):ℝ)))
    (hcurv : ∀ y, |ratRowSecondDerivative row y| ≤ (curvature:ℝ)) :
    (fixedCellRangeFromVD (ofRat curvature) halfWidth left middle).Contains
      (ratRowFunction row x) := by
  let mid : ℚ := (a+b)/2
  have ham : a ≤ mid := by dsimp [mid]; linarith
  have hmb : mid ≤ b := by dsimp [mid]; linarith
  have hc := contains_ofRat curvature
  by_cases hxm : x ≤ (mid:ℝ)
  · apply FixedInterval.contains_hull_left
    apply fixedSecondOrderCell_contains ham ⟨hx.1,hxm⟩ hleftV
      (by simpa [deriv_ratRowFunction] using hleftD) hwidth hc
    · intro y _
      rw [iteratedDeriv_two_ratRowFunction]
      exact hcurv y
    · exact contDiff_ratRowFunction row
  · apply FixedInterval.contains_hull_right
    have hwright : halfWidth.Contains ((b:ℝ)-(mid:ℝ)) := by
      convert hwidth using 1
      dsimp [mid]
      push_cast
      ring
    apply fixedSecondOrderCell_contains hmb ⟨le_of_not_ge hxm,hx.2⟩ hmiddleV
      (by simpa [mid, deriv_ratRowFunction] using hmiddleD) hwright hc
    · intro y _
      rw [iteratedDeriv_two_ratRowFunction]
      exact hcurv y
    · exact contDiff_ratRowFunction row

theorem fixedCellUpperFromLeft_interval_le (row : RatRow) (curvature : ℚ)
    (hcurv : ∀ y, |ratRowSecondDerivative row y| ≤ (curvature:ℝ))
    (hfreq : RowFrequenciesNonzero row) :
    ∀ (depth : ℕ) (a b : ℚ) (width : FixedInterval)
      (left : FixedInterval × FixedInterval),
      a ≤ b → width.Contains ((b:ℝ)-(a:ℝ)) →
      left.1.Contains (ratRowFunction row a) →
      left.2.Contains (ratRowDerivative row a) →
      (∫ x in (a:ℝ)..b, positivePart (ratRowFunction row) x) ≤
        (fixedCellUpperFromLeft row (FixedRow.ofRatRow row) (ofRat curvature)
          depth a b width left : ℝ) / fixedDyadicScale := by
  intro depth
  induction depth with
  | zero =>
      intro a b width left hab hwidth hleftV hleftD
      let mid : ℚ := (a+b)/2
      let halfWidth := mul fixedHalf width
      let middle := fixedRowValueDerivative (FixedRow.ofRatRow row) mid
      let range := fixedCellRangeFromVD (ofRat curvature) halfWidth left middle
      have hhalf : halfWidth.Contains ((mid:ℝ)-(a:ℝ)) := by
        have h := contains_mul (contains_ofRat (1/2)) hwidth
        convert h using 1
        dsimp [mid, halfWidth, fixedHalf]
        push_cast
        ring
      have hm := fixedRowValueDerivative_contains row mid
      have hrange : ∀ {x:ℝ}, (a:ℝ)≤x ∧ x≤(b:ℝ) →
          range.Contains (ratRowFunction row x) := by
        intro x hx
        exact fixedCellRangeFromVD_contains row curvature halfWidth left middle
          hab hx (by simpa [mid] using hhalf) hleftV hleftD
          (by simpa [mid] using hm.1) (by simpa [mid] using hm.2)
          hcurv
      simp only [fixedCellUpperFromLeft]
      split_ifs with hneg hpos
      · rw [positivePart_integral_eq_zero_of_nonpositive hab
          (fun x hx ↦ (hrange hx).2.trans (by
            change (range.hi:ℝ)/fixedDyadicScale ≤ 0
            exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hneg)
              (by exact_mod_cast fixedDyadicScale_pos.le)))]
        norm_num
      · have hi := positivePart_integral_le_of_antiderivative hab
          (contDiff_ratRowFunction row).continuous.continuousOn
          (fun x hx ↦ by
            have hr := hrange hx
            have : (0:ℝ) ≤ (range.lo:ℝ)/fixedDyadicScale :=
              div_nonneg (by exact_mod_cast hpos) (by exact_mod_cast fixedDyadicScale_pos.le)
            exact this.trans hr.1)
          (fun x _ ↦ hasDerivAt_ratRowAntiderivative row x hfreq)
          (FixedInterval.contains_toRatInterval (fixedRowAntiderivative_contains row a))
          (FixedInterval.contains_toRatInterval (fixedRowAntiderivative_contains row b))
        convert hi using 1 <;>
          simp [fixedPositiveCellUpper, FixedInterval.toRatInterval] <;> ring
      · let u : ℚ := (range.hi:ℚ)/fixedDyadicScale
        have hri : 0 ≤ range.hi := (le_of_lt (lt_of_not_ge hneg))
        have hu0 : 0 ≤ u := div_nonneg (by exact_mod_cast hri)
          (by exact_mod_cast fixedDyadicScale_pos.le)
        have hi := positivePart_integral_le_rectangle hab
          (contDiff_ratRowFunction row).continuous.continuousOn
          (u := u) (fun x hx ↦ by
            simpa [u] using (hrange hx).2)
        have hu0R : (0:ℝ) ≤ (u:ℝ) := by exact_mod_cast hu0
        have huEq : (u:ℝ) = (range.hi:ℝ)/fixedDyadicScale := by
          dsimp [u]
          push_cast
          rfl
        have hwprod := contains_mul hwidth
          (show (⟨max range.hi 0, max range.hi 0⟩ : FixedInterval).Contains
              (max (u:ℝ) 0) by
            rw [max_eq_left hri, max_eq_left hu0R]
            constructor <;> dsimp [FixedInterval.Contains] <;> rw [huEq])
        change (∫ x in (a:ℝ)..b, positivePart (ratRowFunction row) x) ≤
          (fixedTerminalUpper width range:ℝ)/fixedDyadicScale
        exact hi.trans (by
          have := hwprod.2
          simpa [fixedTerminalUpper, u, max_eq_left hu0R] using this)
  | succ depth ih =>
      intro a b width left hab hwidth hleftV hleftD
      let mid : ℚ := (a+b)/2
      let halfWidth := mul fixedHalf width
      let middle := fixedRowValueDerivative (FixedRow.ofRatRow row) mid
      let range := fixedCellRangeFromVD (ofRat curvature) halfWidth left middle
      have hhalf : halfWidth.Contains ((mid:ℝ)-(a:ℝ)) := by
        have h := contains_mul (contains_ofRat (1/2)) hwidth
        convert h using 1
        dsimp [mid, halfWidth, fixedHalf]
        push_cast
        ring
      have hm := fixedRowValueDerivative_contains row mid
      have hrange : ∀ {x:ℝ}, (a:ℝ)≤x ∧ x≤(b:ℝ) →
          range.Contains (ratRowFunction row x) := by
        intro x hx
        exact fixedCellRangeFromVD_contains row curvature halfWidth left middle
          hab hx (by simpa [mid] using hhalf) hleftV hleftD
          (by simpa [mid] using hm.1) (by simpa [mid] using hm.2)
          hcurv
      simp only [fixedCellUpperFromLeft]
      split_ifs with hneg hpos
      · rw [positivePart_integral_eq_zero_of_nonpositive hab
          (fun x hx ↦ (hrange hx).2.trans (by
            change (range.hi:ℝ)/fixedDyadicScale ≤ 0
            exact div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hneg)
              (by exact_mod_cast fixedDyadicScale_pos.le)))]
        norm_num
      · have hi := positivePart_integral_le_of_antiderivative hab
          (contDiff_ratRowFunction row).continuous.continuousOn
          (fun x hx ↦ by
            have hr := hrange hx
            have : (0:ℝ) ≤ (range.lo:ℝ)/fixedDyadicScale :=
              div_nonneg (by exact_mod_cast hpos) (by exact_mod_cast fixedDyadicScale_pos.le)
            exact this.trans hr.1)
          (fun x _ ↦ hasDerivAt_ratRowAntiderivative row x hfreq)
          (FixedInterval.contains_toRatInterval (fixedRowAntiderivative_contains row a))
          (FixedInterval.contains_toRatInterval (fixedRowAntiderivative_contains row b))
        convert hi using 1 <;>
          simp [fixedPositiveCellUpper, FixedInterval.toRatInterval] <;> ring
      · have ham : a ≤ mid := by dsimp [mid]; linarith
        have hmb : mid ≤ b := by dsimp [mid]; linarith
        have hl := ih a mid halfWidth left ham hhalf hleftV hleftD
        have hr := ih mid b halfWidth middle hmb (by
            convert hhalf using 1 <;> dsimp [mid] <;> push_cast <;> ring)
          (by simpa [mid] using hm.1) (by simpa [mid] using hm.2)
        have hcontL : ContinuousOn (positivePart (ratRowFunction row))
            (Set.Icc (a:ℝ) (mid:ℝ)) := continuousOn_positivePart
          (contDiff_ratRowFunction row).continuous.continuousOn
        have hcontR : ContinuousOn (positivePart (ratRowFunction row))
            (Set.Icc (mid:ℝ) (b:ℝ)) := continuousOn_positivePart
          (contDiff_ratRowFunction row).continuous.continuousOn
        have hli : IntervalIntegrable (positivePart (ratRowFunction row)) MeasureTheory.volume
            (a:ℝ) (mid:ℝ) :=
          hcontL.intervalIntegrable_of_Icc (by exact_mod_cast ham)
        have hri : IntervalIntegrable (positivePart (ratRowFunction row)) MeasureTheory.volume
            (mid:ℝ) (b:ℝ) :=
          hcontR.intervalIntegrable_of_Icc (by exact_mod_cast hmb)
        rw [← intervalIntegral.integral_add_adjacent_intervals hli hri]
        simpa [mid, halfWidth, middle, add_div] using add_le_add hl hr

theorem positivePartBudgetFixed_interval_le (row : RatRow) (depth : ℕ)
    (hfreq : RowFrequenciesNonzero row) :
    (∫ x in (-2:ℝ)..2, positivePart (ratRowFunction row) x) ≤
      (positivePartBudgetFixed row depth : ℝ) := by
  have h := fixedCellUpperFromLeft_interval_le row (rowCurvatureBound row)
    (fun y ↦ abs_ratRowSecondDerivative_le row y) hfreq
    depth (-2) 2 (ofRat 4)
    (fixedRowValueDerivative (FixedRow.ofRatRow row) (-2)) (by norm_num)
    (by convert contains_ofRat 4 using 1 <;> norm_num)
    (fixedRowValueDerivative_contains row (-2)).1
    (fixedRowValueDerivative_contains row (-2)).2
  simpa [positivePartBudgetFixed, fixedPositivePartBudgetTicks] using h

theorem positivePartUniformBudget_interval_le (row : RatRow)
    (cells depth : ℕ) (hcells : 0 < cells)
    (hfreq : RowFrequenciesNonzero row) :
    (∫ x in (-2:ℝ)..2, positivePart (ratRowFunction row) x) ≤
      (positivePartUniformBudget row cells depth : ℝ) := by
  let g : ℝ → ℝ := positivePart (ratRowFunction row)
  have hg_cont : Continuous g := by
    simpa [g, positivePart] using
      (contDiff_ratRowFunction row).continuous.max continuous_const
  have hcell (i : ℕ) (hi : i < cells) :
      (∫ x in (uniformPoint cells i : ℚ)..uniformPoint cells (i+1), g x) ≤
        (fixedUniformCellTicks row cells depth i : ℝ) / fixedDyadicScale := by
    have hab : uniformPoint cells i ≤ uniformPoint cells (i+1) := by
      dsimp [uniformPoint]
      have hiQ : (i : ℚ) ≤ ((i+1 : ℕ) : ℚ) := by
        exact_mod_cast Nat.le_succ i
      have hcQ : (0 : ℚ) ≤ (cells : ℚ) := by
        exact_mod_cast hcells.le
      have hfrac := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hiQ
          (by norm_num : (0:ℚ) ≤ 4))
        hcQ
      linarith
    have hwidth : (ofRat (4/cells)).Contains
        (((uniformPoint cells (i+1):ℚ):ℝ) -
          (uniformPoint cells i:ℚ)) := by
      convert contains_ofRat (4/cells) using 1
      · dsimp [uniformPoint]
        push_cast
        field_simp
        ring
    have h := fixedCellUpperFromLeft_interval_le row (rowCurvatureBound row)
      (fun y ↦ abs_ratRowSecondDerivative_le row y) hfreq depth
      (uniformPoint cells i) (uniformPoint cells (i+1)) (ofRat (4/cells))
      (fixedRowValueDerivative (FixedRow.ofRatRow row) (uniformPoint cells i))
      hab hwidth
      (fixedRowValueDerivative_contains row (uniformPoint cells i)).1
      (fixedRowValueDerivative_contains row (uniformPoint cells i)).2
    simpa [g, fixedUniformCellTicks] using h
  have hsum := Finset.sum_le_sum (fun i hi ↦ hcell i (Finset.mem_range.mp hi))
  have hintegrable (i : ℕ) (hi : i < cells) : IntervalIntegrable g
      MeasureTheory.volume (uniformPoint cells i : ℚ)
        (uniformPoint cells (i+1) : ℚ) :=
    hg_cont.intervalIntegrable _ _
  have htel := intervalIntegral.sum_integral_adjacent_intervals
    (f := g) (a := fun i ↦ ((uniformPoint cells i : ℚ) : ℝ))
    (n := cells) hintegrable
  rw [htel] at hsum
  have hzero : ((uniformPoint cells 0 : ℚ) : ℝ) = -2 := by
    simp [uniformPoint]
  have hend : ((uniformPoint cells cells : ℚ) : ℝ) = 2 := by
    dsimp [uniformPoint]
    push_cast
    field_simp
    ring
  change (∫ x in ((uniformPoint cells 0 : ℚ) : ℝ)..
      ((uniformPoint cells cells : ℚ) : ℝ), g x) ≤ _ at hsum
  rw [hzero, hend] at hsum
  calc
    (∫ x in (-2:ℝ)..2, positivePart (ratRowFunction row) x) =
        ∫ x in (-2:ℝ)..2, g x := rfl
    _ ≤ ∑ i ∈ Finset.range cells,
        (fixedUniformCellTicks row cells depth i : ℝ) /
          fixedDyadicScale := hsum
    _ = (positivePartUniformBudget row cells depth : ℝ) := by
      simp [positivePartUniformBudget, fixedUniformBudgetTicks]
      rw [← Finset.sum_div]

theorem positivePartUniformPreparedBudget_interval_le (row : RatRow)
    (fixed : FixedRow) (curvature : FixedInterval) (cells depth : ℕ)
    (hfixed : fixed = FixedRow.ofRatRow row)
    (hcurvature : curvature = ofRat (rowCurvatureBound row))
    (hcells : 0 < cells) (hfreq : RowFrequenciesNonzero row) :
    (∫ x in (-2:ℝ)..2, positivePart (ratRowFunction row) x) ≤
      (positivePartUniformPreparedBudget row fixed curvature cells depth : ℝ) := by
  subst fixed
  subst curvature
  simpa [positivePartUniformPreparedBudget, fixedUniformPreparedBudgetTicks,
    fixedUniformCellTicksPrepared, positivePartUniformBudget,
    fixedUniformBudgetTicks, fixedUniformCellTicks] using
      positivePartUniformBudget_interval_le row cells depth hcells hfreq

theorem positivePartEvenBudget_interval_le (row : RatRow) (depth : ℕ)
    (hsymmetric : RatRowSymmetric row)
    (hfreq : RowFrequenciesNonzero row) :
    (∫ x in (-2:ℝ)..2, positivePart (ratRowFunction row) x) ≤
      (positivePartEvenBudget row depth : ℝ) := by
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
  have hhalf := fixedCellUpperFromLeft_interval_le row (rowCurvatureBound row)
    (fun y ↦ abs_ratRowSecondDerivative_le row y) hfreq
    depth 0 2 (ofRat 2)
    (fixedRowValueDerivative (FixedRow.ofRatRow row) 0) (by norm_num)
    (by convert contains_ofRat 2 using 1 <;> norm_num)
    (fixedRowValueDerivative_contains row 0).1
    (fixedRowValueDerivative_contains row 0).2
  have hhalf' : (∫ x in (0:ℝ)..2, positivePart (ratRowFunction row) x) ≤
      (fixedPositivePartHalfBudgetTicks row depth : ℝ) /
        fixedDyadicScale := by
    simpa [fixedPositivePartHalfBudgetTicks] using hhalf
  rw [hsplit, hneg]
  calc
    (∫ x in (0:ℝ)..2, g x) + ∫ x in (0:ℝ)..2, g x ≤
        2 * ((fixedPositivePartHalfBudgetTicks row depth : ℝ) /
          fixedDyadicScale) := by
      dsimp [g] at hhalf ⊢
      linarith [hhalf']
    _ = (positivePartEvenBudget row depth : ℝ) := by
      simp [positivePartEvenBudget, fixedPositivePartHalfBudgetTicks]
      push_cast
      ring

theorem cellRangeFromVD_contains (row : RatRow) (curvature : ℚ)
    {a b : ℚ} {x : ℝ} (left middle : FixedInterval × FixedInterval)
    (hab : a ≤ b) (hx : (a : ℝ) ≤ x ∧ x ≤ (b : ℝ))
    (hleftV : left.1.Contains (ratRowFunction row a))
    (hleftD : left.2.Contains (ratRowDerivative row a))
    (hmiddleV : middle.1.Contains
      (ratRowFunction row ((((a+b)/2 : ℚ)) : ℝ)))
    (hmiddleD : middle.2.Contains
      (ratRowDerivative row ((((a+b)/2 : ℚ)) : ℝ)))
    (hcurv : ∀ y, |ratRowSecondDerivative row y| ≤ (curvature : ℝ)) :
    (cellRangeFromVD curvature a b left middle).Contains
      (ratRowFunction row x) := by
  let mid : ℚ := (a + b) / 2
  have ham : a ≤ mid := by dsimp [mid]; linarith
  have hmb : mid ≤ b := by dsimp [mid]; linarith
  apply contains_compress
  by_cases hxm : x ≤ (mid : ℝ)
  · apply RatInterval.contains_hull_left
    apply secondOrderCell_contains ham ⟨hx.1, hxm⟩
    · exact FixedInterval.contains_toRatInterval hleftV
    · simpa [deriv_ratRowFunction] using
        FixedInterval.contains_toRatInterval hleftD
    · exact contDiff_ratRowFunction row
    · intro y _
      rw [iteratedDeriv_two_ratRowFunction]
      exact hcurv y
  · apply RatInterval.contains_hull_right
    apply secondOrderCell_contains hmb ⟨le_of_not_ge hxm, hx.2⟩
    · exact FixedInterval.contains_toRatInterval hmiddleV
    · simpa [mid, deriv_ratRowFunction] using
        FixedInterval.contains_toRatInterval hmiddleD
    · exact contDiff_ratRowFunction row
    · intro y _
      rw [iteratedDeriv_two_ratRowFunction]
      exact hcurv y

theorem cellRange_contains (row : RatRow) (curvature : ℚ) {a b : ℚ} {x : ℝ}
    (hab : a ≤ b) (hx : (a : ℝ) ≤ x ∧ x ≤ (b : ℝ))
    (hcurv : ∀ y, |ratRowSecondDerivative row y| ≤ (curvature : ℝ)) :
    (cellRange row (FixedRow.ofRatRow row) curvature a b).Contains
      (ratRowFunction row x) := by
  exact cellRangeFromVD_contains row curvature _ _ hab hx
    (fixedRowValueDerivative_contains row a).1
    (fixedRowValueDerivative_contains row a).2
    (fixedRowValueDerivative_contains row ((a+b)/2)).1
    (fixedRowValueDerivative_contains row ((a+b)/2)).2 hcurv

/-- Semantic invariant for the optimized worker: `left` already encloses the
value and derivative at the cell's left endpoint. -/
theorem cellUpperFromLeft_partition (row : RatRow) (curvature : ℚ)
    (hcurv : ∀ y, |ratRowSecondDerivative row y| ≤ (curvature : ℝ))
    (hfreq : RowFrequenciesNonzero row) :
    ∀ (depth : ℕ) (a b : ℚ) (left : FixedInterval × FixedInterval),
      a ≤ b →
      left.1.Contains (ratRowFunction row a) →
      left.2.Contains (ratRowDerivative row a) →
      PositivePartPartition (ratRowFunction row) a b
        (cellUpperFromLeft row (FixedRow.ofRatRow row) curvature
          depth a b left : ℝ) := by
  intro depth
  induction depth with
  | zero =>
      intro a b left hab hleftV hleftD
      let mid : ℚ := (a+b)/2
      let middle := fixedRowValueDerivative (FixedRow.ofRatRow row) mid
      let range := cellRangeFromVD curvature a b left middle
      have hmiddle := fixedRowValueDerivative_contains row mid
      have hrange : ∀ {x : ℝ}, (a:ℝ) ≤ x ∧ x ≤ (b:ℝ) →
          range.Contains (ratRowFunction row x) := by
        intro x hx
        exact cellRangeFromVD_contains row curvature left middle hab hx
          hleftV hleftD (by simpa [mid] using hmiddle.1)
          (by simpa [mid] using hmiddle.2) hcurv
      simp only [cellUpperFromLeft]
      split_ifs with hneg hpos
      · simpa using PositivePartPartition.nonpositive (f := ratRowFunction row) hab
          (fun x hx ↦ by
            have hr := hrange hx
            exact hr.2.trans (by exact_mod_cast hneg))
      · apply PositivePartPartition.antiderivative
          (ratRowAntiderivative row)
          (fixedRowAntiderivative (FixedRow.ofRatRow row) a).toRatInterval
          (fixedRowAntiderivative (FixedRow.ofRatRow row) b).toRatInterval hab
        · intro x hx
          have hr := hrange hx
          have hp : (0 : ℝ) ≤ (range.lo : ℝ) := by
            exact_mod_cast hpos
          exact hp.trans hr.1
        · intro x hx
          exact hasDerivAt_ratRowAntiderivative row x hfreq
        · exact FixedInterval.contains_toRatInterval
            (fixedRowAntiderivative_contains row a)
        · exact FixedInterval.contains_toRatInterval
            (fixedRowAntiderivative_contains row b)
      · apply PositivePartPartition.rectangle hab
        intro x hx
        have hr := hrange hx
        exact hr.2
  | succ depth ih =>
      intro a b left hab hleftV hleftD
      let mid : ℚ := (a+b)/2
      let middle := fixedRowValueDerivative (FixedRow.ofRatRow row) mid
      let range := cellRangeFromVD curvature a b left middle
      have hmiddle := fixedRowValueDerivative_contains row mid
      have hrange : ∀ {x : ℝ}, (a:ℝ) ≤ x ∧ x ≤ (b:ℝ) →
          range.Contains (ratRowFunction row x) := by
        intro x hx
        exact cellRangeFromVD_contains row curvature left middle hab hx
          hleftV hleftD (by simpa [mid] using hmiddle.1)
          (by simpa [mid] using hmiddle.2) hcurv
      simp only [cellUpperFromLeft]
      split_ifs with hneg hpos
      · simpa using PositivePartPartition.nonpositive (f := ratRowFunction row) hab
          (fun x hx ↦ by
            have hr := hrange hx
            exact hr.2.trans (by exact_mod_cast hneg))
      · apply PositivePartPartition.antiderivative
          (ratRowAntiderivative row)
          (fixedRowAntiderivative (FixedRow.ofRatRow row) a).toRatInterval
          (fixedRowAntiderivative (FixedRow.ofRatRow row) b).toRatInterval hab
        · intro x hx
          have hr := hrange hx
          have hp : (0 : ℝ) ≤ (range.lo : ℝ) := by
            exact_mod_cast hpos
          exact hp.trans hr.1
        · intro x hx
          exact hasDerivAt_ratRowAntiderivative row x hfreq
        · exact FixedInterval.contains_toRatInterval
            (fixedRowAntiderivative_contains row a)
        · exact FixedInterval.contains_toRatInterval
            (fixedRowAntiderivative_contains row b)
      · have ham : a ≤ mid := by dsimp [mid]; linarith
        have hmb : mid ≤ b := by dsimp [mid]; linarith
        have hl := ih a mid left ham hleftV hleftD
        have hr := ih mid b middle hmb
          (by simpa [mid] using hmiddle.1)
          (by simpa [mid] using hmiddle.2)
        simpa [mid] using PositivePartPartition.split ham hmb hl hr

/-- The executable recursion produces a semantic integration certificate. -/
theorem cellUpper_partition (row : RatRow) (curvature : ℚ)
    (hcurv : ∀ y, |ratRowSecondDerivative row y| ≤ (curvature : ℝ))
    (hfreq : RowFrequenciesNonzero row) :
    ∀ (depth : ℕ) (a b : ℚ), a ≤ b →
      PositivePartPartition (ratRowFunction row) a b
        (cellUpper row (FixedRow.ofRatRow row) curvature depth a b : ℝ) := by
  intro depth a b hab
  apply cellUpperFromLeft_partition row curvature hcurv hfreq
    depth a b (fixedRowValueDerivative (FixedRow.ofRatRow row) a) hab
  · exact (fixedRowValueDerivative_contains row a).1
  · exact (fixedRowValueDerivative_contains row a).2

theorem positivePartBudget_interval_le (row : RatRow) (depth : ℕ)
    (hfreq : RowFrequenciesNonzero row) :
    (∫ x in (-2 : ℝ)..2, positivePart (ratRowFunction row) x) ≤
      (positivePartBudget row depth : ℝ) := by
  simpa [positivePartBudget] using
    positivePartBudgetFixed_interval_le row depth hfreq

end ErdosMinimum
