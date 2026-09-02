import ErdosMinimum.BudgetComputation

/-!
# Prepared budgets on an adaptive rational partition

This module is the small, generic soundness layer used by generated
certificates whose top-level cells need not have a uniform width or recursion
depth.  Every segment calculation is a closed integer expression, so generated
files can prove the segment equalities independently and an aggregate file only
has to add the resulting integers.
-/

namespace ErdosMinimum

open RatInterval FixedInterval

/-- One top-level segment of an adaptive certificate.  `depth` is the maximum
subdivision depth used by `fixedCellUpperFromLeft` inside this segment. -/
structure AdaptiveSegment where
  left : ℚ
  right : ℚ
  depth : ℕ
deriving Repr, DecidableEq

/-- The segments form an ordered, gap-free partition from `start` to `finish`.
In particular, each segment is oriented from left to right. -/
def AdaptiveChain : ℚ → ℚ → List AdaptiveSegment → Prop
  | start, finish, [] => start = finish
  | start, finish, segment :: rest =>
      segment.left = start ∧ start ≤ segment.right ∧
        AdaptiveChain segment.right finish rest

theorem AdaptiveChain.append {start middle finish : ℚ}
    {left right : List AdaptiveSegment}
    (hleft : AdaptiveChain start middle left)
    (hright : AdaptiveChain middle finish right) :
    AdaptiveChain start finish (left ++ right) := by
  induction left generalizing start with
  | nil =>
      simp only [AdaptiveChain] at hleft
      subst start
      simpa using hright
  | cons segment rest ih =>
      simp only [AdaptiveChain] at hleft ⊢
      exact ⟨hleft.1, hleft.2.1, ih hleft.2.2⟩

/-- The independently replayable fixed-dyadic calculation for one adaptive
segment. -/
def fixedAdaptiveSegmentTicksPrepared (row : RatRow) (fixed : FixedRow)
    (curvature : FixedInterval) (segment : AdaptiveSegment) : ℤ :=
  fixedCellUpperFromLeft row fixed curvature segment.depth
    segment.left segment.right (ofRat (segment.right - segment.left))
    (fixedRowValueDerivative fixed segment.left)

/-- Sum of the independently replayable segment results. -/
def fixedAdaptiveBudgetTicksPrepared (row : RatRow) (fixed : FixedRow)
    (curvature : FixedInterval) : List AdaptiveSegment → ℤ
  | [] => 0
  | segment :: rest =>
      fixedAdaptiveSegmentTicksPrepared row fixed curvature segment +
        fixedAdaptiveBudgetTicksPrepared row fixed curvature rest

theorem fixedAdaptiveBudgetTicksPrepared_append (row : RatRow)
    (fixed : FixedRow) (curvature : FixedInterval)
    (left right : List AdaptiveSegment) :
    fixedAdaptiveBudgetTicksPrepared row fixed curvature (left ++ right) =
      fixedAdaptiveBudgetTicksPrepared row fixed curvature left +
        fixedAdaptiveBudgetTicksPrepared row fixed curvature right := by
  induction left with
  | nil => simp [fixedAdaptiveBudgetTicksPrepared]
  | cons segment rest ih =>
      simp [fixedAdaptiveBudgetTicksPrepared, ih, add_assoc]

/-- Exact rational budget represented by the adaptive fixed-dyadic ticks. -/
def positivePartAdaptivePreparedBudget (row : RatRow) (fixed : FixedRow)
    (curvature : FixedInterval) (segments : List AdaptiveSegment) : ℚ :=
  (fixedAdaptiveBudgetTicksPrepared row fixed curvature segments : ℚ) /
    fixedDyadicScale

/-- Soundness on arbitrary rational endpoints.  The equalities for `fixed` and
`curvature` ensure that prepared data cannot change the mathematical function
or weaken its curvature bound. -/
theorem positivePartAdaptivePreparedBudget_interval_le_of_chain
    (row : RatRow) (fixed : FixedRow) (curvature : FixedInterval)
    {start finish : ℚ} {segments : List AdaptiveSegment}
    (hfixed : fixed = FixedRow.ofRatRow row)
    (hcurvature : curvature = ofRat (rowCurvatureBound row))
    (hchain : AdaptiveChain start finish segments)
    (hfreq : RowFrequenciesNonzero row) :
    (∫ x in (start : ℝ)..finish,
      positivePart (ratRowFunction row) x) ≤
      (positivePartAdaptivePreparedBudget row fixed curvature segments : ℝ) := by
  subst fixed
  subst curvature
  let g : ℝ → ℝ := positivePart (ratRowFunction row)
  have hg_cont : Continuous g := by
    simpa [g, positivePart] using
      (contDiff_ratRowFunction row).continuous.max continuous_const
  induction segments generalizing start with
  | nil =>
      have hstart : start = finish := by
        simpa [AdaptiveChain] using hchain
      subst finish
      simp [positivePartAdaptivePreparedBudget,
        fixedAdaptiveBudgetTicksPrepared]
  | cons segment rest ih =>
      rcases hchain with ⟨hleft, horiented, hrest⟩
      subst start
      have hcell := fixedCellUpperFromLeft_interval_le row
        (rowCurvatureBound row)
        (fun y ↦ abs_ratRowSecondDerivative_le row y) hfreq
        segment.depth segment.left segment.right
        (ofRat (segment.right - segment.left))
        (fixedRowValueDerivative (FixedRow.ofRatRow row) segment.left)
        horiented
        (by
          simpa only [Rat.cast_sub] using
            (contains_ofRat (segment.right - segment.left)))
        (fixedRowValueDerivative_contains row segment.left).1
        (fixedRowValueDerivative_contains row segment.left).2
      have hcell' :
          (∫ x in (segment.left : ℝ)..segment.right, g x) ≤
            (fixedAdaptiveSegmentTicksPrepared row (FixedRow.ofRatRow row)
              (ofRat (rowCurvatureBound row)) segment : ℝ) /
                fixedDyadicScale := by
        simpa [g, fixedAdaptiveSegmentTicksPrepared] using hcell
      have htail := ih hrest
      have hinterLeft : IntervalIntegrable g MeasureTheory.volume
          (segment.left : ℝ) (segment.right : ℝ) :=
        hg_cont.intervalIntegrable _ _
      have hinterRight : IntervalIntegrable g MeasureTheory.volume
          (segment.right : ℝ) (finish : ℝ) :=
        hg_cont.intervalIntegrable _ _
      calc
        (∫ x in (segment.left : ℝ)..finish, g x) =
            (∫ x in (segment.left : ℝ)..segment.right, g x) +
              ∫ x in (segment.right : ℝ)..finish, g x := by
                rw [intervalIntegral.integral_add_adjacent_intervals
                  hinterLeft hinterRight]
        _ ≤
            (fixedAdaptiveSegmentTicksPrepared row (FixedRow.ofRatRow row)
                (ofRat (rowCurvatureBound row)) segment : ℝ) /
                  fixedDyadicScale +
              (positivePartAdaptivePreparedBudget row (FixedRow.ofRatRow row)
                (ofRat (rowCurvatureBound row)) rest : ℝ) :=
            add_le_add hcell' htail
        _ =
            (positivePartAdaptivePreparedBudget row (FixedRow.ofRatRow row)
              (ofRat (rowCurvatureBound row)) (segment :: rest) : ℝ) := by
          simp only [positivePartAdaptivePreparedBudget,
            fixedAdaptiveBudgetTicksPrepared]
          push_cast
          ring

/-- Main `[-2,2]` API for generated adaptive certificates. -/
theorem positivePartAdaptivePreparedBudget_interval_le
    (row : RatRow) (fixed : FixedRow) (curvature : FixedInterval)
    (segments : List AdaptiveSegment)
    (hfixed : fixed = FixedRow.ofRatRow row)
    (hcurvature : curvature = ofRat (rowCurvatureBound row))
    (hchain : AdaptiveChain (-2) 2 segments)
    (hfreq : RowFrequenciesNonzero row) :
    (∫ x in (-2 : ℝ)..2, positivePart (ratRowFunction row) x) ≤
      (positivePartAdaptivePreparedBudget row fixed curvature segments : ℝ) := by
  simpa using
    (positivePartAdaptivePreparedBudget_interval_le_of_chain row fixed
      curvature hfixed hcurvature hchain hfreq)

end ErdosMinimum
