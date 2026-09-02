import ErdosMinimum.RationalInterval

/-!
# Recursive interval bounds for positive-part integrals

This module packages the generic integration step used by a directed
certificate.  Endpoints and numerical bounds are exact rationals.  A leaf can
discard a nonpositive cell, integrate a nonnegative cell using an
antiderivative with enclosed endpoint values, or charge a constant rectangle.
Adjacent certified cells compose recursively by additivity of the interval
integral.
-/

open MeasureTheory Set

namespace ErdosMinimum

/-- The positive part of a real-valued function. -/
def positivePart (f : ℝ → ℝ) (x : ℝ) : ℝ := max (f x) 0

theorem continuousOn_positivePart {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b)) :
    ContinuousOn (positivePart f) (Icc a b) := by
  simpa [positivePart, Function.comp_def] using
    continuous_max.comp_continuousOn (hf.prodMk continuousOn_const)

/-- A cell on which `f ≤ 0` contributes nothing to its positive-part integral. -/
theorem positivePart_integral_eq_zero_of_nonpositive
    {f : ℝ → ℝ} {a b : ℚ} (hab : a ≤ b)
    (hnonpositive : ∀ x ∈ Icc (a : ℝ) (b : ℝ), f x ≤ 0) :
    (∫ x in (a : ℝ)..(b : ℝ), positivePart f x) = 0 := by
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  rw [intervalIntegral.integral_congr (f := positivePart f) (g := fun _ ↦ 0) ?_]
  · simp
  · intro x hx
    have hx' : x ∈ Icc (a : ℝ) (b : ℝ) := by
      simpa [uIcc_of_le hab'] using hx
    exact max_eq_right (hnonpositive x hx')

/-- On a nonnegative cell, endpoint enclosures for an antiderivative give an
exact rational upper bound for the positive-part integral. -/
theorem positivePart_integral_le_of_antiderivative
    {f F : ℝ → ℝ} {a b : ℚ} {left right : RatInterval}
    (hab : a ≤ b)
    (hf : ContinuousOn f (Icc (a : ℝ) (b : ℝ)))
    (hnonnegative : ∀ x ∈ Icc (a : ℝ) (b : ℝ), 0 ≤ f x)
    (hderiv : ∀ x ∈ Icc (a : ℝ) (b : ℝ), HasDerivAt F (f x) x)
    (hleft : left.Contains (F (a : ℝ)))
    (hright : right.Contains (F (b : ℝ))) :
    (∫ x in (a : ℝ)..(b : ℝ), positivePart f x) ≤
      ((right.hi - left.lo : ℚ) : ℝ) := by
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hfi : IntervalIntegrable f volume (a : ℝ) (b : ℝ) :=
    hf.intervalIntegrable_of_Icc hab'
  have hposEq : EqOn (positivePart f) f (uIcc (a : ℝ) (b : ℝ)) := by
    intro x hx
    have hx' : x ∈ Icc (a : ℝ) (b : ℝ) := by
      simpa [uIcc_of_le hab'] using hx
    exact max_eq_left (hnonnegative x hx')
  rw [intervalIntegral.integral_congr hposEq]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := F) (f' := f) (a := (a : ℝ)) (b := (b : ℝ))]
  · rcases hleft with ⟨hleft, _⟩
    rcases hright with ⟨_, hright⟩
    push_cast
    linarith
  · intro x hx
    apply hderiv x
    simpa [uIcc_of_le hab'] using hx
  · exact hfi

/-- A pointwise upper bound charges at most one constant rectangle. -/
theorem positivePart_integral_le_rectangle
    {f : ℝ → ℝ} {a b u : ℚ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc (a : ℝ) (b : ℝ)))
    (hupper : ∀ x ∈ Icc (a : ℝ) (b : ℝ), f x ≤ (u : ℝ)) :
    (∫ x in (a : ℝ)..(b : ℝ), positivePart f x) ≤
      (((b - a) * max u 0 : ℚ) : ℝ) := by
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hposInt : IntervalIntegrable (positivePart f) volume (a : ℝ) (b : ℝ) :=
    (continuousOn_positivePart hf).intervalIntegrable_of_Icc hab'
  have hconstInt : IntervalIntegrable (fun _ : ℝ ↦ max (u : ℝ) 0)
      volume (a : ℝ) (b : ℝ) :=
    continuous_const.intervalIntegrable _ _
  calc
    (∫ x in (a : ℝ)..(b : ℝ), positivePart f x) ≤
        ∫ _ in (a : ℝ)..(b : ℝ), max (u : ℝ) 0 := by
      apply intervalIntegral.integral_mono_on hab' hposInt hconstInt
      intro x hx
      exact max_le_max (hupper x hx) le_rfl
    _ = ((b : ℝ) - (a : ℝ)) * max (u : ℝ) 0 := by simp
    _ = (((b - a) * max u 0 : ℚ) : ℝ) := by
      push_cast
      rfl

/-- A recursively composable proof that the positive-part integral on the
rational cell `[a,b]` is at most `budget`. -/
inductive PositivePartPartition (f : ℝ → ℝ) : ℚ → ℚ → ℝ → Prop where
  | nonpositive {a b : ℚ}
      (hab : a ≤ b)
      (hnonpositive : ∀ x ∈ Icc (a : ℝ) (b : ℝ), f x ≤ 0) :
      PositivePartPartition f a b 0
  | antiderivative {a b : ℚ} (F : ℝ → ℝ) (left right : RatInterval)
      (hab : a ≤ b)
      (hnonnegative : ∀ x ∈ Icc (a : ℝ) (b : ℝ), 0 ≤ f x)
      (hderiv : ∀ x ∈ Icc (a : ℝ) (b : ℝ), HasDerivAt F (f x) x)
      (hleft : left.Contains (F (a : ℝ)))
      (hright : right.Contains (F (b : ℝ))) :
      PositivePartPartition f a b ((right.hi - left.lo : ℚ) : ℝ)
  | rectangle {a b u : ℚ}
      (hab : a ≤ b)
      (hupper : ∀ x ∈ Icc (a : ℝ) (b : ℝ), f x ≤ (u : ℝ)) :
      PositivePartPartition f a b (((b - a) * max u 0 : ℚ) : ℝ)
  | split {a m b : ℚ} {leftBudget rightBudget : ℝ}
      (ham : a ≤ m) (hmb : m ≤ b)
      (left : PositivePartPartition f a m leftBudget)
      (right : PositivePartPartition f m b rightBudget) :
      PositivePartPartition f a b (leftBudget + rightBudget)

/-- Every recursively assembled partition bound is sound.  Continuity is
assumed only on the root interval and restricted to child cells during the
recursive proof. -/
theorem PositivePartPartition.integral_le
    {f : ℝ → ℝ} {a b : ℚ} {budget : ℝ}
    (certificate : PositivePartPartition f a b budget)
    (hcontinuous : ContinuousOn f (Icc (a : ℝ) (b : ℝ))) :
    (∫ x in (a : ℝ)..(b : ℝ), positivePart f x) ≤ budget := by
  induction certificate with
  | nonpositive hab hnonpositive =>
      rw [positivePart_integral_eq_zero_of_nonpositive hab hnonpositive]
  | antiderivative F left right hab hnonnegative hderiv hleft hright =>
      exact positivePart_integral_le_of_antiderivative hab hcontinuous hnonnegative hderiv
        hleft hright
  | rectangle hab hupper =>
      exact positivePart_integral_le_rectangle hab hcontinuous hupper
  | @split a m b leftBudget rightBudget ham hmb left right ihLeft ihRight =>
      have ham' : (a : ℝ) ≤ (m : ℝ) := by exact_mod_cast ham
      have hmb' : (m : ℝ) ≤ (b : ℝ) := by exact_mod_cast hmb
      have hab' : (a : ℝ) ≤ (b : ℝ) := ham'.trans hmb'
      have hcontinuousLeft : ContinuousOn f (Icc (a : ℝ) (m : ℝ)) :=
        hcontinuous.mono (Icc_subset_Icc le_rfl hmb')
      have hcontinuousRight : ContinuousOn f (Icc (m : ℝ) (b : ℝ)) :=
        hcontinuous.mono (Icc_subset_Icc ham' le_rfl)
      have hleftInt : IntervalIntegrable (positivePart f) volume (a : ℝ) (m : ℝ) :=
        (continuousOn_positivePart hcontinuousLeft).intervalIntegrable_of_Icc ham'
      have hrightInt : IntervalIntegrable (positivePart f) volume (m : ℝ) (b : ℝ) :=
        (continuousOn_positivePart hcontinuousRight).intervalIntegrable_of_Icc hmb'
      rw [← intervalIntegral.integral_add_adjacent_intervals hleftInt hrightInt]
      exact add_le_add (ihLeft hcontinuousLeft) (ihRight hcontinuousRight)

end ErdosMinimum
