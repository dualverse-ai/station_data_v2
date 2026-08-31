import KakeyaNeedleC3C4.SortedIntervals

namespace KakeyaNeedleC3C4

open Set MeasureTheory

noncomputable section

theorem intervalIntegral_affine (A B a b : ℝ) :
    (∫ y : ℝ in a..b, A + B*y) =
      A*(b-a) + B*(b^2-a^2)/2 := by
  have hderiv (z : ℝ) : HasDerivAt
      (fun t : ℝ ↦ A*t + B*t^2/2) (A+B*z) z := by
    convert ((hasDerivAt_id z).const_mul A).add
      (((hasDerivAt_id z).pow 2).const_mul B |>.div_const 2) using 1 <;>
      simp only [id_eq] <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun z _ ↦ hderiv z)
    (intervalIntegral.intervalIntegrable_const.add
      (intervalIntegral.intervalIntegrable_id.const_mul B))]
  ring

/-- Integrate a finite exact sweep schedule.  The breakpoints and affine
coefficients may themselves depend on external parameters; the theorem only
requires the certified slice identity on each closed slab. -/
theorem sliceArea_eq_sum_piecewise_affine (n k : ℕ) (x : Fin n → ℝ)
    (breakpoint A B : ℕ → ℝ)
    (hzero : breakpoint 0 = 0) (hone : breakpoint k = 1)
    (horder : ∀ i < k, breakpoint i ≤ breakpoint (i+1))
    (hslice : ∀ i < k, EqOn (sliceLength n x)
      (fun y ↦ A i + B i*y) (Icc (breakpoint i) (breakpoint (i+1)))) :
    sliceArea n x = ∑ i ∈ Finset.range k,
      (A i * (breakpoint (i+1)-breakpoint i) +
        B i * (breakpoint (i+1)^2-breakpoint i^2)/2) := by
  have hint : ∀ i < k, IntervalIntegrable (sliceLength n x) volume
      (breakpoint i) (breakpoint (i+1)) := by
    intro i hi
    have haff : IntervalIntegrable (fun y : ℝ ↦ A i + B i*y) volume
        (breakpoint i) (breakpoint (i+1)) :=
      intervalIntegral.intervalIntegrable_const.add
        (intervalIntegral.intervalIntegrable_id.const_mul (B i))
    apply haff.congr
    rw [uIoc_of_le (horder i hi)]
    exact (hslice i hi).symm.mono Ioc_subset_Icc_self
  rw [sliceArea, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    ← hzero, ← hone,
    ← intervalIntegral.sum_integral_adjacent_intervals hint]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  rw [intervalIntegral.integral_congr (by
    rw [uIcc_of_le (horder i hi)]
    exact hslice i hi), intervalIntegral_affine]

end

end KakeyaNeedleC3C4
