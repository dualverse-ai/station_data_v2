import ErdosMinimum.DoubleAngle

/-!
# Fixed-precision compression for exact rational intervals

Uncompressed repeated interval multiplication creates enormous rational
denominators.  These operations round outward to a dyadic grid after every
step.  The endpoints remain exact rationals, and the theorems below prove
that compression never loses a contained real value.
-/

namespace ErdosMinimum.RatInterval

def dyadicDenom (precision : ℕ) : ℚ := (2 : ℚ) ^ precision

def roundDown (precision : ℕ) (q : ℚ) : ℚ :=
  (⌊q * dyadicDenom precision⌋ : ℤ) / dyadicDenom precision

def roundUp (precision : ℕ) (q : ℚ) : ℚ :=
  (⌈q * dyadicDenom precision⌉ : ℤ) / dyadicDenom precision

theorem dyadicDenom_pos (precision : ℕ) : 0 < dyadicDenom precision := by
  change 0 < (2 : ℚ) ^ precision
  positivity

theorem roundDown_le (precision : ℕ) (q : ℚ) : roundDown precision q ≤ q := by
  have h : ((⌊q * dyadicDenom precision⌋ : ℤ) : ℚ) ≤
      q * dyadicDenom precision := Int.floor_le _
  rw [roundDown]
  exact (div_le_iff₀ (dyadicDenom_pos precision)).2 (by
    simpa [mul_comm] using h)

theorem le_roundUp (precision : ℕ) (q : ℚ) : q ≤ roundUp precision q := by
  have h : q * dyadicDenom precision ≤
      ((⌈q * dyadicDenom precision⌉ : ℤ) : ℚ) := Int.le_ceil _
  rw [roundUp]
  exact (le_div_iff₀ (dyadicDenom_pos precision)).2 (by
    simpa [mul_comm] using h)

def compress (precision : ℕ) (I : RatInterval) : RatInterval :=
  ⟨roundDown precision I.lo, roundUp precision I.hi⟩

theorem contains_compress {I : RatInterval} {x : ℝ} (hx : I.Contains x)
    (precision : ℕ) : (compress precision I).Contains x := by
  rcases hx with ⟨hlo, hhi⟩
  constructor
  · change ((roundDown precision I.lo : ℚ) : ℝ) ≤ x
    have hq : ((roundDown precision I.lo : ℚ) : ℝ) ≤ (I.lo : ℝ) := by
      exact_mod_cast roundDown_le precision I.lo
    exact hq.trans hlo
  · change x ≤ ((roundUp precision I.hi : ℚ) : ℝ)
    have hq : (I.hi : ℝ) ≤ ((roundUp precision I.hi : ℚ) : ℝ) := by
      exact_mod_cast le_roundUp precision I.hi
    exact hhi.trans hq

def addCompressed (precision : ℕ) (I J : RatInterval) : RatInterval :=
  compress precision (add I J)

def subCompressed (precision : ℕ) (I J : RatInterval) : RatInterval :=
  compress precision (sub I J)

def mulCompressed (precision : ℕ) (I J : RatInterval) : RatInterval :=
  compress precision (mul I J)

def scaleCompressed (precision : ℕ) (q : ℚ) (I : RatInterval) : RatInterval :=
  compress precision (scale q I)

theorem contains_addCompressed {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) (precision : ℕ) :
    (addCompressed precision I J).Contains (x + y) :=
  contains_compress (contains_add hx hy) precision

theorem contains_subCompressed {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) (precision : ℕ) :
    (subCompressed precision I J).Contains (x - y) :=
  contains_compress (contains_sub hx hy) precision

theorem contains_mulCompressed {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) (precision : ℕ) :
    (mulCompressed precision I J).Contains (x * y) :=
  contains_compress (contains_mul hx hy) precision

theorem contains_scaleCompressed {I : RatInterval} {x : ℝ}
    (q : ℚ) (hx : I.Contains x) (precision : ℕ) :
    (scaleCompressed precision q I).Contains ((q : ℝ) * x) :=
  contains_compress (contains_scale q hx) precision

/-- Compressed double-angle propagation. -/
def doubleTrigCompressed (precision : ℕ) (B : RatInterval × RatInterval) :
    RatInterval × RatInterval :=
  (scaleCompressed precision 2 (mulCompressed precision B.1 B.2),
    subCompressed precision
      (scaleCompressed precision 2 (mulCompressed precision B.2 B.2)) (point 1))

def doubleTrigCompressedN (precision : ℕ) :
    ℕ → RatInterval × RatInterval → RatInterval × RatInterval
  | 0, B => B
  | n + 1, B => doubleTrigCompressedN precision n (doubleTrigCompressed precision B)

theorem doubleTrigCompressed_contains (precision : ℕ)
    {S C : RatInterval} {x : ℝ}
    (hs : S.Contains (Real.sin x)) (hc : C.Contains (Real.cos x)) :
    (doubleTrigCompressed precision (S, C)).1.Contains (Real.sin (2 * x)) ∧
      (doubleTrigCompressed precision (S, C)).2.Contains (Real.cos (2 * x)) := by
  constructor
  · rw [Real.sin_two_mul]
    simpa [doubleTrigCompressed, mul_assoc] using
      contains_scaleCompressed 2 (contains_mulCompressed hs hc precision) precision
  · rw [Real.cos_two_mul]
    simpa [doubleTrigCompressed, pow_two] using
      contains_subCompressed
        (contains_scaleCompressed 2 (contains_mulCompressed hc hc precision) precision)
        (contains_point 1) precision

theorem doubleTrigCompressedN_contains (precision n : ℕ)
    {S C : RatInterval} {x : ℝ}
    (hs : S.Contains (Real.sin x)) (hc : C.Contains (Real.cos x)) :
    (doubleTrigCompressedN precision n (S, C)).1.Contains
        (Real.sin ((2 : ℝ) ^ n * x)) ∧
      (doubleTrigCompressedN precision n (S, C)).2.Contains
        (Real.cos ((2 : ℝ) ^ n * x)) := by
  induction n generalizing S C x with
  | zero => simpa [doubleTrigCompressedN] using And.intro hs hc
  | succ n ih =>
      rw [doubleTrigCompressedN]
      have hd := doubleTrigCompressed_contains precision hs hc
      have h := ih hd.1 hd.2
      simpa [pow_succ, mul_assoc] using h

def trigEnclosureCompressed (precision : ℕ) (I : RatInterval) (depth : ℕ) :
    RatInterval × RatInterval :=
  let J := scale (1 / (2 : ℚ) ^ depth) I
  let S := compress precision (sinEnclosure J)
  let C := compress precision (cosEnclosure J)
  doubleTrigCompressedN precision depth (S, C)

theorem trig_mem_compressed_enclosure {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) (precision depth : ℕ)
    (hunit : (((scale (1 / (2 : ℚ) ^ depth) I).absBound : ℚ) : ℝ) ≤ 1) :
    (trigEnclosureCompressed precision I depth).1.Contains (Real.sin x) ∧
      (trigEnclosureCompressed precision I depth).2.Contains (Real.cos x) := by
  let J := scale (1 / (2 : ℚ) ^ depth) I
  have hxJ : J.Contains (x / (2 : ℝ) ^ depth) := by
    have h := contains_scale (1 / (2 : ℚ) ^ depth) hx
    convert h using 1
    push_cast
    field_simp
  have hs := contains_compress (sin_mem_enclosure hxJ hunit) precision
  have hc := contains_compress (cos_mem_enclosure hxJ hunit) precision
  have h := doubleTrigCompressedN_contains precision depth hs hc
  have hcancel : (2 : ℝ) ^ depth * (x / (2 : ℝ) ^ depth) = x := by
    field_simp
  simpa [trigEnclosureCompressed, J, hcancel] using h

def trigEnclosureReducedCompressed (precision : ℕ) (I : RatInterval)
    (period : ℤ) (depth : ℕ) : RatInterval × RatInterval :=
  trigEnclosureCompressed precision (reduceTwoPi I period) depth

theorem trig_mem_reduced_compressed_enclosure {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) (precision depth : ℕ) (period : ℤ)
    (hunit : (((scale (1 / (2 : ℚ) ^ depth)
      (reduceTwoPi I period)).absBound : ℚ) : ℝ) ≤ 1) :
    (trigEnclosureReducedCompressed precision I period depth).1.Contains (Real.sin x) ∧
      (trigEnclosureReducedCompressed precision I period depth).2.Contains (Real.cos x) := by
  have h := trig_mem_compressed_enclosure (contains_reduceTwoPi hx period)
    precision depth hunit
  simpa [trigEnclosureReducedCompressed, Real.sin_sub_int_mul_two_pi,
    Real.cos_sub_int_mul_two_pi] using h

end ErdosMinimum.RatInterval
