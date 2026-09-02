import Mathlib

/-!
# Exact rational interval arithmetic

This module is a small, kernel-checked foundation for replaying numerical
certificates whose inputs and outward-rounded endpoints are rational numbers.
An interval contains real numbers, while every operation on endpoints is
computed in `ℚ`.  The enclosure theorems therefore have no floating-point
or code-generation trust boundary.

The final section gives executable cubic/quadratic Taylor enclosures for
`Real.sin` and `Real.cos` on intervals contained in `[-1, 1]`.  They use
mathlib's proved Taylor remainder bounds.  Range reduction for the much larger
arguments in the Erdős certificate remains a separate task.
-/

namespace ErdosMinimum

/-- A closed interval with exact rational endpoints.  Keeping validity as a
separate predicate makes all constructors executable without proof fields. -/
structure RatInterval where
  lo : ℚ
  hi : ℚ
deriving DecidableEq, Repr

namespace RatInterval

/-- The endpoints occur in increasing order. -/
def Valid (I : RatInterval) : Prop := I.lo ≤ I.hi

/-- The real number `x` lies in the rational interval `I`. -/
def Contains (I : RatInterval) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- A point interval. -/
def point (q : ℚ) : RatInterval := ⟨q, q⟩

/-- Interval hull. -/
def hull (I J : RatInterval) : RatInterval := ⟨min I.lo J.lo, max I.hi J.hi⟩

/-- Minkowski sum. -/
def add (I J : RatInterval) : RatInterval := ⟨I.lo + J.lo, I.hi + J.hi⟩

/-- Additive inverse. -/
def neg (I : RatInterval) : RatInterval := ⟨-I.hi, -I.lo⟩

/-- Minkowski difference. -/
def sub (I J : RatInterval) : RatInterval := add I (neg J)

/-- Scalar multiplication, with the endpoint order selected exactly in `ℚ`. -/
def scale (q : ℚ) (I : RatInterval) : RatInterval :=
  if 0 ≤ q then ⟨q * I.lo, q * I.hi⟩ else ⟨q * I.hi, q * I.lo⟩

/-- The standard four-corner product enclosure. -/
def mul (I J : RatInterval) : RatInterval :=
  let p₁ := I.lo * J.lo
  let p₂ := I.lo * J.hi
  let p₃ := I.hi * J.lo
  let p₄ := I.hi * J.hi
  ⟨min (min p₁ p₂) (min p₃ p₄), max (max p₁ p₂) (max p₃ p₄)⟩

/-- Enlarge both endpoints by an exact rational radius. -/
def widen (I : RatInterval) (r : ℚ) : RatInterval := ⟨I.lo - r, I.hi + r⟩

/-- A rational upper bound for the absolute value of every contained real. -/
def absBound (I : RatInterval) : ℚ := max |I.lo| |I.hi|

theorem valid_point (q : ℚ) : (point q).Valid := by simp [Valid, point]

theorem contains_point (q : ℚ) : (point q).Contains (q : ℝ) := by simp [Contains, point]

theorem contains_hull_left {I J : RatInterval} {x : ℝ} (hx : I.Contains x) :
    (hull I J).Contains x := by
  rcases hx with ⟨hx₁, hx₂⟩
  constructor
  · exact le_trans (by exact_mod_cast min_le_left I.lo J.lo) hx₁
  · exact le_trans hx₂ (by exact_mod_cast le_max_left I.hi J.hi)

theorem contains_hull_right {I J : RatInterval} {x : ℝ} (hx : J.Contains x) :
    (hull I J).Contains x := by
  rcases hx with ⟨hx₁, hx₂⟩
  constructor
  · exact le_trans (by exact_mod_cast min_le_right I.lo J.lo) hx₁
  · exact le_trans hx₂ (by exact_mod_cast le_max_right I.hi J.hi)

theorem contains_add {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (add I J).Contains (x + y) := by
  rcases hx with ⟨hx₁, hx₂⟩
  rcases hy with ⟨hy₁, hy₂⟩
  constructor <;> dsimp [Contains, add] <;> push_cast <;> linarith

theorem contains_neg {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    (neg I).Contains (-x) := by
  rcases hx with ⟨hx₁, hx₂⟩
  constructor <;> dsimp [Contains, neg] <;> push_cast <;> linarith

theorem contains_sub {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (sub I J).Contains (x - y) := by
  simpa [sub_eq_add_neg, sub] using contains_add hx (contains_neg hy)

theorem contains_scale {I : RatInterval} {x : ℝ} (q : ℚ) (hx : I.Contains x) :
    (scale q I).Contains ((q : ℝ) * x) := by
  rcases hx with ⟨hx₁, hx₂⟩
  by_cases hq : 0 ≤ q
  · rw [scale, if_pos hq]
    constructor <;> dsimp [Contains] <;> push_cast
    · exact mul_le_mul_of_nonneg_left hx₁ (by exact_mod_cast hq)
    · exact mul_le_mul_of_nonneg_left hx₂ (by exact_mod_cast hq)
  · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast le_of_not_ge hq
    rw [scale, if_neg hq]
    constructor <;> dsimp [Contains] <;> push_cast
    · exact mul_le_mul_of_nonpos_left hx₂ hq'
    · exact mul_le_mul_of_nonpos_left hx₁ hq'

private theorem mul_lower {a b c d x y : ℝ}
    (hax : a ≤ x) (hxb : x ≤ b) (hcy : c ≤ y) (hyd : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
  by_cases hx : 0 ≤ x
  · have hxy : x * c ≤ x * y := mul_le_mul_of_nonneg_left hcy hx
    by_cases hc : 0 ≤ c
    · exact (min_le_of_left_le (min_le_of_left_le (mul_le_mul_of_nonneg_right hax hc))).trans hxy
    · have hc' : c ≤ 0 := le_of_not_ge hc
      exact (min_le_of_right_le (min_le_of_left_le (mul_le_mul_of_nonpos_right hxb hc'))).trans hxy
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hxy : x * d ≤ x * y := mul_le_mul_of_nonpos_left hyd hx'
    by_cases hd : 0 ≤ d
    · exact (min_le_of_left_le (min_le_of_right_le (mul_le_mul_of_nonneg_right hax hd))).trans hxy
    · have hd' : d ≤ 0 := le_of_not_ge hd
      exact (min_le_of_right_le (min_le_of_right_le (mul_le_mul_of_nonpos_right hxb hd'))).trans hxy

private theorem mul_upper {a b c d x y : ℝ}
    (hax : a ≤ x) (hxb : x ≤ b) (hcy : c ≤ y) (hyd : y ≤ d) :
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  by_cases hx : 0 ≤ x
  · have hxy : x * y ≤ x * d := mul_le_mul_of_nonneg_left hyd hx
    by_cases hd : 0 ≤ d
    · exact hxy.trans (le_max_of_le_right (le_max_of_le_right (mul_le_mul_of_nonneg_right hxb hd)))
    · have hd' : d ≤ 0 := le_of_not_ge hd
      exact hxy.trans (le_max_of_le_left (le_max_of_le_right (mul_le_mul_of_nonpos_right hax hd')))
  · have hx' : x ≤ 0 := le_of_not_ge hx
    have hxy : x * y ≤ x * c := mul_le_mul_of_nonpos_left hcy hx'
    by_cases hc : 0 ≤ c
    · exact hxy.trans (le_max_of_le_right (le_max_of_le_left (mul_le_mul_of_nonneg_right hxb hc)))
    · have hc' : c ≤ 0 := le_of_not_ge hc
      exact hxy.trans (le_max_of_le_left (le_max_of_le_left (mul_le_mul_of_nonpos_right hax hc')))

theorem contains_mul {I J : RatInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (mul I J).Contains (x * y) := by
  rcases hx with ⟨hx₁, hx₂⟩
  rcases hy with ⟨hy₁, hy₂⟩
  constructor
  · dsimp [Contains, mul]
    push_cast
    exact mul_lower hx₁ hx₂ hy₁ hy₂
  · dsimp [Contains, mul]
    push_cast
    exact mul_upper hx₁ hx₂ hy₁ hy₂

theorem abs_le_absBound {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    |x| ≤ (I.absBound : ℝ) := by
  rcases hx with ⟨hx₁, hx₂⟩
  rw [abs_le]
  constructor
  · have hb : (|I.lo| : ℝ) ≤ (I.absBound : ℝ) := by
      exact_mod_cast le_max_left |I.lo| |I.hi|
    exact (neg_le_neg hb).trans ((neg_abs_le (I.lo : ℝ)).trans hx₁)
  · have h : (I.hi : ℝ) ≤ (|I.hi| : ℚ) := by exact_mod_cast le_abs_self I.hi
    exact hx₂.trans (h.trans (by exact_mod_cast le_max_right |I.lo| |I.hi|))

theorem absBound_nonneg (I : RatInterval) : 0 ≤ I.absBound :=
  le_trans (abs_nonneg I.lo) (le_max_left _ _)

theorem contains_widen_of_abs_sub_le {I : RatInterval} {p z : ℝ} {r : ℚ}
    (hp : I.Contains p) (hr : |z - p| ≤ (r : ℝ)) : (widen I r).Contains z := by
  rcases hp with ⟨hp₁, hp₂⟩
  rcases abs_le.mp hr with ⟨hr₁, hr₂⟩
  constructor <;> dsimp [Contains, widen] <;> push_cast <;> linarith

/-! ## Polynomial evaluation -/

/-- Horner evaluation of coefficients in ascending order. -/
def evalPoly : List ℚ → RatInterval → RatInterval
  | [], _ => point 0
  | a :: as, I => add (point a) (mul I (evalPoly as I))

/-- Real evaluation of the same ascending coefficient list. -/
def evalReal : List ℚ → ℝ → ℝ
  | [], _ => 0
  | a :: as, x => (a : ℝ) + x * evalReal as x

theorem contains_evalPoly (coeffs : List ℚ) {I : RatInterval} {x : ℝ}
    (hx : I.Contains x) :
    (evalPoly coeffs I).Contains (evalReal coeffs x) := by
  induction coeffs with
  | nil => simp [evalPoly, evalReal, Contains, point]
  | cons a as ih =>
      simpa [evalPoly, evalReal] using
        contains_add (contains_point a) (contains_mul hx ih)

/-! ## Trigonometric Taylor enclosures on `[-1,1]` -/

/-- Cubic Taylor polynomial `x - x³/6`, evaluated by interval arithmetic. -/
def sinTaylor3 (I : RatInterval) : RatInterval := evalPoly [0, 1, 0, -(1 / 6)] I

/-- Quadratic Taylor polynomial `1 - x²/2`, evaluated by interval arithmetic. -/
def cosTaylor2 (I : RatInterval) : RatInterval := evalPoly [1, 0, -(1 / 2)] I

/-- Uniform remainder radius supplied by mathlib's degree-three bounds. -/
def trigRemainder (I : RatInterval) : ℚ := I.absBound ^ 4 * (5 / 96)

def sinEnclosure (I : RatInterval) : RatInterval := widen (sinTaylor3 I) (trigRemainder I)

def cosEnclosure (I : RatInterval) : RatInterval := widen (cosTaylor2 I) (trigRemainder I)

theorem contains_sinTaylor3 {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    (sinTaylor3 I).Contains (x - x ^ 3 / 6) := by
  have h := contains_evalPoly [0, 1, 0, -(1 / 6)] hx
  rw [show evalReal [0, 1, 0, -(1 / 6)] x = x - x ^ 3 / 6 by
    simp [evalReal]; ring] at h
  exact h

theorem contains_cosTaylor2 {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    (cosTaylor2 I).Contains (1 - x ^ 2 / 2) := by
  have h := contains_evalPoly [1, 0, -(1 / 2)] hx
  rw [show evalReal [1, 0, -(1 / 2)] x = 1 - x ^ 2 / 2 by
    simp [evalReal]; ring] at h
  exact h

theorem sin_mem_enclosure {I : RatInterval} {x : ℝ} (hx : I.Contains x)
    (hunit : (I.absBound : ℝ) ≤ 1) : (sinEnclosure I).Contains (Real.sin x) := by
  apply contains_widen_of_abs_sub_le (contains_sinTaylor3 hx)
  have habs := abs_le_absBound hx
  have hs := Real.sin_bound (habs.trans hunit)
  apply hs.trans
  dsimp [trigRemainder]
  push_cast
  gcongr

theorem cos_mem_enclosure {I : RatInterval} {x : ℝ} (hx : I.Contains x)
    (hunit : (I.absBound : ℝ) ≤ 1) : (cosEnclosure I).Contains (Real.cos x) := by
  apply contains_widen_of_abs_sub_le (contains_cosTaylor2 hx)
  have habs := abs_le_absBound hx
  have hc := Real.cos_bound (habs.trans hunit)
  apply hc.trans
  dsimp [trigRemainder]
  push_cast
  gcongr

/-! The following examples reduce using exact rational arithmetic. -/

example : (sinEnclosure ⟨-(1 / 10), 1 / 10⟩).Valid := by norm_num [Valid, sinEnclosure,
  sinTaylor3, trigRemainder, absBound, widen, evalPoly, point, add, mul]

example {x : ℝ} (hx : (-(1 : ℝ) / 10) ≤ x ∧ x ≤ 1 / 10) :
    (sinEnclosure ⟨-(1 / 10), 1 / 10⟩).Contains (Real.sin x) := by
  apply sin_mem_enclosure
  · constructor <;> norm_num [Contains] at hx ⊢ <;> tauto
  · norm_num [absBound]

end RatInterval

end ErdosMinimum
