import ErdosMinimum.RationalInterval
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Kernel-checked trigonometric range reduction

This module extends the exact rational interval foundation with a rigorous
20-decimal enclosure of `π` from mathlib.  A caller supplies an integer period;
the reduced interval is computed exactly and can then be checked to lie in
`[-1,1]` before applying the local sine/cosine Taylor enclosures.
-/

namespace ErdosMinimum.RatInterval

/-- Mathlib-proved 20-decimal rational enclosure of `π`. -/
def piInterval : RatInterval := ⟨3.14159265358979323846, 3.14159265358979323847⟩

theorem pi_mem_interval : piInterval.Contains Real.pi := by
  constructor
  · exact Real.pi_gt_d20.le
  · exact Real.pi_lt_d20.le

/-- Subtract `n` periods of `2π`, propagating the exact rational `π` interval. -/
def reduceTwoPi (I : RatInterval) (n : ℤ) : RatInterval :=
  sub I (scale (((2 * n : ℤ) : ℚ)) piInterval)

theorem contains_reduceTwoPi {I : RatInterval} {x : ℝ} (hx : I.Contains x) (n : ℤ) :
    (reduceTwoPi I n).Contains (x - (n : ℝ) * (2 * Real.pi)) := by
  have h := contains_sub hx (contains_scale (((2 * n : ℤ) : ℚ)) pi_mem_interval)
  convert h using 1
  push_cast
  ring

/-- A globally valid sine enclosure after certified period reduction. -/
theorem sin_mem_reduced_enclosure {I : RatInterval} {x : ℝ} (hx : I.Contains x) (n : ℤ)
    (hunit : ((reduceTwoPi I n).absBound : ℝ) ≤ 1) :
    (sinEnclosure (reduceTwoPi I n)).Contains (Real.sin x) := by
  rw [← Real.sin_sub_int_mul_two_pi x n]
  exact sin_mem_enclosure (contains_reduceTwoPi hx n) hunit

/-- A globally valid cosine enclosure after certified period reduction. -/
theorem cos_mem_reduced_enclosure {I : RatInterval} {x : ℝ} (hx : I.Contains x) (n : ℤ)
    (hunit : ((reduceTwoPi I n).absBound : ℝ) ≤ 1) :
    (cosEnclosure (reduceTwoPi I n)).Contains (Real.cos x) := by
  rw [← Real.cos_sub_int_mul_two_pi x n]
  exact cos_mem_enclosure (contains_reduceTwoPi hx n) hunit

example : (reduceTwoPi ⟨6, 7⟩ 1).Valid := by
  norm_num [reduceTwoPi, piInterval, Valid, sub, add, neg, scale]

end ErdosMinimum.RatInterval
