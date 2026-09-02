import ErdosMinimum.CompressedInterval
import ErdosMinimum.RationalTrig

/-!
# Fast global rational trigonometric enclosures

For a rational argument, first use the existing certified `2π` range
reduction, then divide the resulting interval by four.  The order-24 point
evaluator from `RationalTrig` is run only once, at the rational midpoint of
that small interval.  The point enclosure is widened by the half-width,
using the fact that sine and cosine are `1`-Lipschitz, and two compressed
double-angle steps recover the original reduced argument.

The public evaluator has a `[-1,1]` fallback if accumulated uncertainty in
the `π` interval makes the midpoint unsuitable for the local point evaluator.
Thus its containment theorem is unconditional, while ordinary certificate
arguments take the substantially sharper fast branch.
-/

namespace ErdosMinimum

/-- Guard precision for the rational trigonometric enclosure.  The downstream
fixed evaluator rounds outward to an 80-bit grid; twenty additional bits keep
that conversion stable while substantially reducing exact-replay time. -/
def fastTrigPrecision : ℕ := 100

def fastPeriodFor (q : ℚ) : ℤ :=
  ⌊q / (628318530717958647692 / 100000000000000000000 : ℚ) + 1 / 2⌋

namespace RatInterval

/-- Rational midpoint of an interval. -/
def midpoint (I : RatInterval) : ℚ := (I.lo + I.hi) / 2

/-- Half the rational endpoint width of an interval. -/
def halfWidth (I : RatInterval) : ℚ := (I.hi - I.lo) / 2

theorem valid_neg {I : RatInterval} (hI : I.Valid) : I.neg.Valid := by
  exact neg_le_neg hI

theorem valid_add {I J : RatInterval} (hI : I.Valid) (hJ : J.Valid) :
    (add I J).Valid := by
  exact add_le_add hI hJ

theorem valid_sub {I J : RatInterval} (hI : I.Valid) (hJ : J.Valid) :
    (sub I J).Valid :=
  valid_add hI (valid_neg hJ)

theorem valid_scale {I : RatInterval} (hI : I.Valid) (q : ℚ) :
    (scale q I).Valid := by
  by_cases hq : 0 ≤ q
  · rw [scale, if_pos hq]
    exact mul_le_mul_of_nonneg_left hI hq
  · rw [scale, if_neg hq]
    exact mul_le_mul_of_nonpos_left hI (le_of_not_ge hq)

theorem piInterval_valid : piInterval.Valid := by
  norm_num [Valid, piInterval]

theorem valid_reduceTwoPi {I : RatInterval} (hI : I.Valid) (n : ℤ) :
    (reduceTwoPi I n).Valid :=
  valid_sub hI (valid_scale piInterval_valid _)

theorem abs_sub_midpoint_le_halfWidth {I : RatInterval} {x : ℝ}
    (hI : I.Valid) (hx : I.Contains x) :
    |x - (I.midpoint : ℝ)| ≤ (I.halfWidth : ℝ) := by
  rcases hx with ⟨hxlo, hxhi⟩
  have hvalid : (I.lo : ℝ) ≤ (I.hi : ℝ) := by exact_mod_cast hI
  rw [abs_le]
  constructor <;> dsimp [midpoint, halfWidth] <;> push_cast <;> linarith

/-- The degree-22 cosine coefficients used by `RationalTrig.cosTaylor12`. -/
def cosCoeffs12 : List ℚ :=
  [1, -(1 / 2), 1 / 24, -(1 / 720), 1 / 40320,
    -(1 / 3628800), 1 / 479001600, -(1 / 87178291200),
    1 / 20922789888000, -(1 / 6402373705728000),
    1 / 2432902008176640000, -(1 / 1124000727777607680000)]

/-- The degree-22 even polynomial coefficients whose product with `q` is
`RationalTrig.sinTaylor12 q`. -/
def sinCoeffs12 : List ℚ :=
  [1, -(1 / 6), 1 / 120, -(1 / 5040), 1 / 362880,
    -(1 / 39916800), 1 / 6227020800, -(1 / 1307674368000),
    1 / 355687428096000, -(1 / 121645100408832000),
    1 / 51090942171709440000, -(1 / 25852016738884976640000)]

/-- Horner evaluation with outward dyadic compression after every multiply
and add. -/
def hornerCompressed (precision : ℕ) : List ℚ → RatInterval → RatInterval
  | [], _ => point 0
  | a :: as, X => addCompressed precision (point a)
      (mulCompressed precision X (hornerCompressed precision as X))

theorem hornerCompressed_contains (precision : ℕ) (coeffs : List ℚ)
    {X : RatInterval} {q : ℚ} (hq : X.Contains (q : ℝ)) :
    (hornerCompressed precision coeffs X).Contains
      (RationalTrig.horner coeffs q : ℝ) := by
  induction coeffs with
  | nil => simpa [hornerCompressed, RationalTrig.horner] using contains_point 0
  | cons a as ih =>
      simpa [hornerCompressed, RationalTrig.horner] using
        contains_addCompressed (contains_point a)
          (contains_mulCompressed hq ih precision) precision

/-- Compressed computation of the point interval for `q²`. -/
def squarePointCompressed (precision : ℕ) (q : ℚ) : RatInterval :=
  mulCompressed precision (point q) (point q)

theorem squarePointCompressed_contains (precision : ℕ) (q : ℚ) :
    (squarePointCompressed precision q).Contains ((q * q : ℚ) : ℝ) := by
  simpa [squarePointCompressed] using
    contains_mulCompressed (contains_point q) (contains_point q) precision

/-- Compressed Horner enclosure of the exact degree-22 cosine polynomial. -/
def cosTaylor12Compressed (precision : ℕ) (q : ℚ) : RatInterval :=
  hornerCompressed precision cosCoeffs12 (squarePointCompressed precision q)

/-- Compressed Horner enclosure of the exact degree-23 sine polynomial. -/
def sinTaylor12Compressed (precision : ℕ) (q : ℚ) : RatInterval :=
  mulCompressed precision (point q)
    (hornerCompressed precision sinCoeffs12 (squarePointCompressed precision q))

theorem cosTaylor12Compressed_contains (precision : ℕ) (q : ℚ) :
    (cosTaylor12Compressed precision q).Contains
      (RationalTrig.cosTaylor12 q : ℝ) := by
  have h := hornerCompressed_contains precision cosCoeffs12
    (squarePointCompressed_contains precision q)
  simpa [cosTaylor12Compressed, RationalTrig.cosTaylor12, cosCoeffs12] using h

theorem sinTaylor12Compressed_contains (precision : ℕ) (q : ℚ) :
    (sinTaylor12Compressed precision q).Contains
      (RationalTrig.sinTaylor12 q : ℝ) := by
  have hhorner := hornerCompressed_contains precision sinCoeffs12
    (squarePointCompressed_contains precision q)
  have h := contains_mulCompressed (contains_point q) hhorner precision
  simpa [sinTaylor12Compressed, RationalTrig.sinTaylor12, sinCoeffs12] using h

/-- Outward-compressed widening by the analytic order-24 remainder. -/
def sinEnclosure12Compressed (precision : ℕ) (q : ℚ) : RatInterval :=
  compress precision
    (widen (sinTaylor12Compressed precision q) (RationalTrig.radius12 q))

/-- Outward-compressed widening by the analytic order-24 remainder. -/
def cosEnclosure12Compressed (precision : ℕ) (q : ℚ) : RatInterval :=
  compress precision
    (widen (cosTaylor12Compressed precision q) (RationalTrig.radius12 q))

private theorem sinTaylor12_error (q : ℚ) (hq : |q| ≤ 1) :
    |Real.sin (q : ℝ) - (RationalTrig.sinTaylor12 q : ℝ)| ≤
      (RationalTrig.radius12 q : ℝ) := by
  have h := RationalTrig.sin_mem_enclosure12 q hq
  rcases h with ⟨hlo, hhi⟩
  rw [abs_le]
  constructor <;>
    dsimp [RationalTrig.sinEnclosure12, Contains] at hlo hhi ⊢ <;>
    push_cast at hlo hhi ⊢ <;> linarith

private theorem cosTaylor12_error (q : ℚ) (hq : |q| ≤ 1) :
    |Real.cos (q : ℝ) - (RationalTrig.cosTaylor12 q : ℝ)| ≤
      (RationalTrig.radius12 q : ℝ) := by
  have h := RationalTrig.cos_mem_enclosure12 q hq
  rcases h with ⟨hlo, hhi⟩
  rw [abs_le]
  constructor <;>
    dsimp [RationalTrig.cosEnclosure12, Contains] at hlo hhi ⊢ <;>
    push_cast at hlo hhi ⊢ <;> linarith

theorem sinEnclosure12Compressed_contains (precision : ℕ) (q : ℚ)
    (hq : |q| ≤ 1) :
    (sinEnclosure12Compressed precision q).Contains (Real.sin (q : ℝ)) := by
  exact contains_compress
    (contains_widen_of_abs_sub_le (sinTaylor12Compressed_contains precision q)
      (sinTaylor12_error q hq)) precision

theorem cosEnclosure12Compressed_contains (precision : ℕ) (q : ℚ)
    (hq : |q| ≤ 1) :
    (cosEnclosure12Compressed precision q).Contains (Real.cos (q : ℝ)) := by
  exact contains_compress
    (contains_widen_of_abs_sub_le (cosTaylor12Compressed_contains precision q)
      (cosTaylor12_error q hq)) precision

/-- Point-Taylor enclosure at the midpoint, evaluated by compressed Horner
and widened to cover the entire input interval by the Lipschitz bound. -/
def midpointTrigEnclosure (precision : ℕ) (I : RatInterval) :
    RatInterval × RatInterval :=
  (compress precision
      (widen (sinEnclosure12Compressed precision I.midpoint) I.halfWidth),
    compress precision
      (widen (cosEnclosure12Compressed precision I.midpoint) I.halfWidth))

theorem midpointTrigEnclosure_contains {I : RatInterval} {x : ℝ}
    (precision : ℕ) (hI : I.Valid) (hx : I.Contains x)
    (hmid : |I.midpoint| ≤ 1) :
    (midpointTrigEnclosure precision I).1.Contains (Real.sin x) ∧
      (midpointTrigEnclosure precision I).2.Contains (Real.cos x) := by
  have hdist := abs_sub_midpoint_le_halfWidth hI hx
  constructor
  · apply contains_compress
    apply contains_widen_of_abs_sub_le
      (sinEnclosure12Compressed_contains precision I.midpoint hmid)
    exact (Real.abs_sin_sub_sin_le x (I.midpoint : ℝ)).trans hdist
  · apply contains_compress
    apply contains_widen_of_abs_sub_le
      (cosEnclosure12Compressed_contains precision I.midpoint hmid)
    exact (Real.abs_cos_sub_cos_le x (I.midpoint : ℝ)).trans hdist

/-- Fast enclosure on an already reduced interval: quarter, evaluate its
midpoint, widen by its half-width, then take two compressed double angles. -/
def fastTrigReduced (precision : ℕ) (I : RatInterval) :
    RatInterval × RatInterval :=
  let J := scale (1 / 4) I
  doubleTrigCompressedN precision 2 (midpointTrigEnclosure precision J)

theorem fastTrigReduced_contains {I : RatInterval} {x : ℝ}
    (hI : I.Valid) (hx : I.Contains x) (precision : ℕ)
    (hmid : |(scale (1 / 4) I).midpoint| ≤ 1) :
    (fastTrigReduced precision I).1.Contains (Real.sin x) ∧
      (fastTrigReduced precision I).2.Contains (Real.cos x) := by
  let J := scale (1 / 4) I
  have hJ : J.Valid := valid_scale hI (1 / 4)
  have hxJ : J.Contains (x / 4) := by
    have h := contains_scale (1 / 4) hx
    convert h using 1
    norm_num [J, div_eq_mul_inv]
    ring
  have hbase := midpointTrigEnclosure_contains precision hJ hxJ hmid
  have hdouble := doubleTrigCompressedN_contains precision 2 hbase.1 hbase.2
  have hcancel : (2 : ℝ) ^ 2 * (x / 4) = x := by ring
  simpa [fastTrigReduced, J, hcancel] using hdouble

end RatInterval

open RatInterval

/-- The quarter-sized interval on which the midpoint Taylor evaluation is
performed. -/
def fastTrigQuarter (q : ℚ) : RatInterval :=
  scale (1 / 4) (reduceTwoPi (point q) (fastPeriodFor q))

/-- Exact executable guard for the local order-24 point theorem. -/
def fastTrigReady (q : ℚ) : Prop := |(fastTrigQuarter q).midpoint| ≤ 1

instance (q : ℚ) : Decidable (fastTrigReady q) := by
  unfold fastTrigReady
  infer_instance

/-- The sharp branch of the fast global evaluator. -/
def fastTrigRaw (precision : ℕ) (q : ℚ) : RatInterval × RatInterval :=
  fastTrigReduced precision (reduceTwoPi (point q) (fastPeriodFor q))

theorem fastTrigRaw_contains (precision : ℕ) (q : ℚ)
    (hready : fastTrigReady q) :
    (fastTrigRaw precision q).1.Contains (Real.sin (q : ℝ)) ∧
      (fastTrigRaw precision q).2.Contains (Real.cos (q : ℝ)) := by
  have h := fastTrigReduced_contains
    (valid_reduceTwoPi (valid_point q) (fastPeriodFor q))
    (contains_reduceTwoPi (contains_point q) (fastPeriodFor q)) precision hready
  simpa [fastTrigRaw, fastTrigQuarter, Real.sin_sub_int_mul_two_pi,
    Real.cos_sub_int_mul_two_pi] using h

/-- Universal fallback used only when the exact readiness check fails. -/
def unitTrigInterval : RatInterval := ⟨-1, 1⟩

/-- Executable global sine/cosine enclosure on the proved 100-bit guard grid. -/
def fastTrigAt (q : ℚ) : RatInterval × RatInterval :=
  if fastTrigReady q then fastTrigRaw fastTrigPrecision q
  else (unitTrigInterval, unitTrigInterval)

/-- The fast evaluator encloses sine and cosine for every rational input. -/
theorem fastTrigAt_contains (q : ℚ) :
    (fastTrigAt q).1.Contains (Real.sin (q : ℝ)) ∧
      (fastTrigAt q).2.Contains (Real.cos (q : ℝ)) := by
  by_cases hready : fastTrigReady q
  · simpa [fastTrigAt, hready] using fastTrigRaw_contains fastTrigPrecision q hready
  · simp only [fastTrigAt, hready, if_false]
    constructor
    · simpa [unitTrigInterval, RatInterval.Contains] using
        (show -1 ≤ Real.sin (q : ℝ) ∧ Real.sin (q : ℝ) ≤ 1 from
          ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩)
    · simpa [unitTrigInterval, RatInterval.Contains] using
        (show -1 ≤ Real.cos (q : ℝ) ∧ Real.cos (q : ℝ) ≤ 1 from
          ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)

end ErdosMinimum
