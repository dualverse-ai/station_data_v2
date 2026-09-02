import ErdosMinimum.RationalInterval
import Mathlib.Analysis.Calculus.Taylor

/-!
# Second-order range propagation from point enclosures

This module turns enclosures of `f(a)` and `f'(a)`, together with a uniform
bound on `|f''|`, into an enclosure on a whole rational cell `[a,b]`.
The analytic remainder is Lagrange's `M (x-a)^2 / 2` bound; the executable
part is only exact rational interval arithmetic.
-/

namespace ErdosMinimum

open Set
open RatInterval

/-- One-sided second-order Taylor remainder, expanded at the left endpoint. -/
theorem abs_sub_taylor_one_le {f : ℝ → ℝ} {a x M : ℝ}
    (hax : a ≤ x) (hf : ContDiff ℝ 2 f)
    (hM : ∀ y ∈ Set.Icc a x, |iteratedDeriv 2 f y| ≤ M) :
    |f x - (f a + deriv f a * (x - a))| ≤ M * (x - a) ^ 2 / 2 := by
  rcases hax.eq_or_lt with rfl | hax
  · simp
  · obtain ⟨y, hy, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv (n := 1) hax
        hf.contDiffOn
    have htaylor : taylorWithinEval f 1 (Set.Icc a x) a x =
        f a + deriv f a * (x - a) := by
      rw [show 1 = 0 + 1 by omega, taylorWithinEval_succ, taylor_within_zero_eval]
      simp only [Nat.zero_add, Nat.cast_one, Nat.factorial_zero, pow_one, smul_eq_mul]
      rw [iteratedDerivWithin_eq_iteratedDeriv (n := 1) (uniqueDiffOn_Icc hax)
        (hf.of_le (by norm_num) : ContDiff ℝ 1 f).contDiffAt
        (left_mem_Icc.mpr hax.le)]
      norm_num
      ring
    rw [htaylor] at hrem
    rw [hrem, abs_div, abs_mul, abs_pow]
    norm_num
    have hyM := hM y ⟨hy.1.le, hy.2.le⟩
    have hsq : 0 ≤ (x - a) ^ 2 := sq_nonneg _
    have hM0 : 0 ≤ M := (abs_nonneg _).trans hyM
    gcongr

/-- Rational enclosure obtained from value and derivative enclosures at the
left endpoint of a cell. -/
def secondOrderCell (value derivAtLeft : RatInterval) (width curvature : ℚ) :
    RatInterval :=
  widen (add value (mul derivAtLeft ⟨0, width⟩))
    (curvature * width ^ 2 / 2)

/-- Soundness of `secondOrderCell`.  This is the integration-facing theorem:
`value` and `derivAtLeft` can be produced by pointwise trigonometric replay,
while `curvature` can be one global rational bound for the entire row. -/
theorem secondOrderCell_contains {f : ℝ → ℝ} {a b : ℚ} {x : ℝ}
    {value derivAtLeft : RatInterval} {curvature : ℚ}
    (hab : a ≤ b) (hx : (a : ℝ) ≤ x ∧ x ≤ (b : ℝ))
    (hvalue : value.Contains (f (a : ℝ)))
    (hderiv : derivAtLeft.Contains (deriv f (a : ℝ)))
    (hf : ContDiff ℝ 2 f)
    (hcurv : ∀ y ∈ Set.Icc (a : ℝ) (b : ℝ),
      |iteratedDeriv 2 f y| ≤ (curvature : ℝ)) :
    (secondOrderCell value derivAtLeft (b - a) curvature).Contains (f x) := by
  have hax : (a : ℝ) ≤ x := hx.1
  have hxb : x ≤ (b : ℝ) := hx.2
  have hwidth : 0 ≤ b - a := sub_nonneg.mpr hab
  have hdelta : (⟨0, b - a⟩ : RatInterval).Contains (x - (a : ℝ)) := by
    constructor
    · dsimp
      simpa using sub_nonneg.mpr hx.1
    · dsimp
      push_cast
      linarith
  have hlinear := contains_add hvalue (contains_mul hderiv hdelta)
  have hrem := abs_sub_taylor_one_le hax hf fun y hy ↦
    hcurv y ⟨hy.1, hy.2.trans hxb⟩
  have hcurv0 : (0 : ℝ) ≤ (curvature : ℝ) :=
    (abs_nonneg (iteratedDeriv 2 f (a : ℝ))).trans
      (hcurv (a : ℝ) ⟨le_rfl, by exact_mod_cast hab⟩)
  have hdelta0 : (0 : ℝ) ≤ x - (a : ℝ) := sub_nonneg.mpr hax
  have hdeltawidth : x - (a : ℝ) ≤ (b : ℝ) - (a : ℝ) := by linarith
  apply contains_widen_of_abs_sub_le hlinear
  calc
    |f x - (f (a : ℝ) + deriv f (a : ℝ) * (x - (a : ℝ)))| ≤
        (curvature : ℝ) * (x - (a : ℝ)) ^ 2 / 2 := hrem
    _ ≤ (curvature : ℝ) * ((b : ℝ) - (a : ℝ)) ^ 2 / 2 := by gcongr
    _ = ((curvature * (b - a) ^ 2 / 2 : ℚ) : ℝ) := by push_cast; ring

end ErdosMinimum
