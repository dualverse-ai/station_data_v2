import ErdosMinimum.PiRangeReduction

/-!
# High-precision trigonometric enclosures by exact double-angle iteration

The local Taylor enclosure in `RationalInterval` is intentionally low degree.
This module makes it arbitrarily sharp without adding a new transcendental
principle: scale the argument by `2⁻ⁿ`, apply the proved local enclosure, then
propagate it through the exact double-angle identities `n` times.  All
endpoint operations remain rational and reducible by the kernel.
-/

namespace ErdosMinimum.RatInterval

/-- One exact interval propagation step for `(sin x, cos x) ↦ (sin 2x, cos 2x)`. -/
def doubleTrig (B : RatInterval × RatInterval) : RatInterval × RatInterval :=
  (scale 2 (mul B.1 B.2), sub (scale 2 (mul B.2 B.2)) (point 1))

def doubleTrigN : ℕ → RatInterval × RatInterval → RatInterval × RatInterval
  | 0, B => B
  | n + 1, B => doubleTrigN n (doubleTrig B)

theorem doubleTrig_contains {S C : RatInterval} {x : ℝ}
    (hs : S.Contains (Real.sin x)) (hc : C.Contains (Real.cos x)) :
    (doubleTrig (S, C)).1.Contains (Real.sin (2 * x)) ∧
      (doubleTrig (S, C)).2.Contains (Real.cos (2 * x)) := by
  constructor
  · rw [Real.sin_two_mul]
    simpa [doubleTrig, mul_assoc] using contains_scale 2 (contains_mul hs hc)
  · rw [Real.cos_two_mul]
    simpa [doubleTrig, pow_two] using
      contains_sub (contains_scale 2 (contains_mul hc hc)) (contains_point 1)

theorem doubleTrigN_contains (n : ℕ) {S C : RatInterval} {x : ℝ}
    (hs : S.Contains (Real.sin x)) (hc : C.Contains (Real.cos x)) :
    (doubleTrigN n (S, C)).1.Contains (Real.sin ((2 : ℝ) ^ n * x)) ∧
      (doubleTrigN n (S, C)).2.Contains (Real.cos ((2 : ℝ) ^ n * x)) := by
  induction n generalizing S C x with
  | zero => simpa [doubleTrigN] using And.intro hs hc
  | succ n ih =>
      rw [doubleTrigN]
      have hd := doubleTrig_contains hs hc
      have h := ih hd.1 hd.2
      simpa [pow_succ, mul_assoc] using h

/-- Simultaneous sine/cosine enclosure obtained by scaling and `n`
double-angle steps. -/
def trigEnclosureScaled (I : RatInterval) (n : ℕ) : RatInterval × RatInterval :=
  let J := scale (1 / (2 : ℚ) ^ n) I
  doubleTrigN n (sinEnclosure J, cosEnclosure J)

theorem trig_mem_scaled_enclosure {I : RatInterval} {x : ℝ} (hx : I.Contains x) (n : ℕ)
    (hunit : (((scale (1 / (2 : ℚ) ^ n) I).absBound : ℚ) : ℝ) ≤ 1) :
    (trigEnclosureScaled I n).1.Contains (Real.sin x) ∧
      (trigEnclosureScaled I n).2.Contains (Real.cos x) := by
  let J := scale (1 / (2 : ℚ) ^ n) I
  have hxJ : J.Contains (x / (2 : ℝ) ^ n) := by
    have h := contains_scale (1 / (2 : ℚ) ^ n) hx
    convert h using 1
    push_cast
    field_simp
  have hs := sin_mem_enclosure hxJ hunit
  have hc := cos_mem_enclosure hxJ hunit
  have h := doubleTrigN_contains n hs hc
  have hcancel : (2 : ℝ) ^ n * (x / (2 : ℝ) ^ n) = x := by
    field_simp
  simpa [trigEnclosureScaled, J, hcancel] using h

/-- Globally sound and arbitrarily sharp enclosure: first subtract an integer
multiple of `2π`, then scale and recover by double-angle iteration. -/
theorem trig_mem_reduced_scaled_enclosure {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) (period : ℤ) (depth : ℕ)
    (hunit : (((scale (1 / (2 : ℚ) ^ depth) (reduceTwoPi I period)).absBound : ℚ) : ℝ) ≤ 1) :
    (trigEnclosureScaled (reduceTwoPi I period) depth).1.Contains (Real.sin x) ∧
      (trigEnclosureScaled (reduceTwoPi I period) depth).2.Contains (Real.cos x) := by
  have h := trig_mem_scaled_enclosure (contains_reduceTwoPi hx period) depth hunit
  simpa only [Real.sin_sub_int_mul_two_pi, Real.cos_sub_int_mul_two_pi] using h

end ErdosMinimum.RatInterval
