import ErdosMinimum.RationalInterval
import Mathlib.Analysis.Complex.Exponential

/-!
# Fast kernel-checked trigonometric enclosures at rational points

This file supplies exact-rational enclosures for `Real.sin q` and `Real.cos q`.
It uses the real and imaginary parts of the degree `2 * terms - 1` Taylor
polynomial for `Complex.exp (q * I)`, together with `Complex.exp_bound`.

All executable data are rational.  The theorem is proved once for an arbitrary
number of terms, so certificate replay only reduces finite rational sums and a
small number of comparisons.
-/

namespace ErdosMinimum.RationalTrig

open scoped ComplexConjugate
open Finset

/-- One even term of the cosine Taylor series. -/
def cosTerm (q : ℚ) (k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k * q ^ (2 * k) / (2 * k).factorial

/-- One odd term of the sine Taylor series. -/
def sinTerm (q : ℚ) (k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k * q ^ (2 * k + 1) / (2 * k + 1).factorial

/-- The first `terms` nonzero cosine Taylor terms. -/
def cosTaylor (q : ℚ) (terms : ℕ) : ℚ :=
  ∑ k ∈ range terms, cosTerm q k

/-- The first `terms` nonzero sine Taylor terms. -/
def sinTaylor (q : ℚ) (terms : ℕ) : ℚ :=
  ∑ k ∈ range terms, sinTerm q k

/-- A shared remainder radius for both Taylor sums.

This is the rational form of the bound used by `Complex.exp_bound`, at
truncation index `2 * terms`. -/
def radius (q : ℚ) (terms : ℕ) : ℚ :=
  |q| ^ (2 * terms) * ((2 * terms + 1 : ℕ) : ℚ) /
    (((2 * terms).factorial : ℕ) * (2 * terms : ℕ))

/-- Rational enclosure of cosine at the rational point `q`. -/
def cosEnclosure (q : ℚ) (terms : ℕ) : RatInterval :=
  ⟨cosTaylor q terms - radius q terms, cosTaylor q terms + radius q terms⟩

/-- Rational enclosure of sine at the rational point `q`. -/
def sinEnclosure (q : ℚ) (terms : ℕ) : RatInterval :=
  ⟨sinTaylor q terms - radius q terms, sinTaylor q terms + radius q terms⟩

private lemma sum_two_mul (f : ℕ → ℂ) (n : ℕ) :
    ∑ m ∈ range (2 * n), f m = ∑ k ∈ range n, (f (2 * k) + f (2 * k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.mul_succ, sum_range_succ, sum_range_succ, sum_range_succ, ih]
      ring

private lemma complex_pair (q : ℚ) (k : ℕ) :
    (((q : ℂ) * Complex.I) ^ (2 * k) / ((2 * k).factorial : ℂ) +
      ((q : ℂ) * Complex.I) ^ (2 * k + 1) / ((2 * k + 1).factorial : ℂ)) =
      (cosTerm q k : ℂ) + (sinTerm q k : ℂ) * Complex.I := by
  simp only [cosTerm, sinTerm]
  push_cast
  have hi_even : Complex.I ^ (2 * k) = (-1 : ℂ) ^ k := by
    rw [pow_mul, Complex.I_sq]
  have hi_odd : Complex.I ^ (2 * k + 1) = (-1 : ℂ) ^ k * Complex.I := by
    rw [pow_add, hi_even, pow_one]
  rw [mul_pow, mul_pow, hi_even, hi_odd]
  ring

private lemma complex_partial (q : ℚ) (terms : ℕ) :
    ∑ m ∈ range (2 * terms), (((q : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) =
      (cosTaylor q terms : ℂ) + (sinTaylor q terms : ℂ) * Complex.I := by
  rw [sum_two_mul]
  simp_rw [complex_pair]
  simp only [cosTaylor, sinTaylor, Rat.cast_sum]
  rw [sum_add_distrib, Finset.sum_mul]

private lemma exp_error_bound (q : ℚ) (terms : ℕ) (hq : |q| ≤ 1) (hterms : 0 < terms) :
    ‖Complex.exp ((q : ℂ) * Complex.I) -
      ((cosTaylor q terms : ℂ) + (sinTaylor q terms : ℂ) * Complex.I)‖ ≤
        (radius q terms : ℝ) := by
  rw [← complex_partial]
  have hnorm : ‖(q : ℂ) * Complex.I‖ ≤ 1 := by
    simpa using (show (|q| : ℝ) ≤ 1 by exact_mod_cast hq)
  have h := Complex.exp_bound hnorm (show 0 < 2 * terms by omega)
  convert h using 1
  all_goals push_cast
  all_goals simp [radius]
  all_goals ring

theorem cos_mem_enclosure (q : ℚ) (terms : ℕ) (hq : |q| ≤ 1) (hterms : 0 < terms) :
    (cosEnclosure q terms).Contains (Real.cos (q : ℝ)) := by
  have h := exp_error_bound q terms hq hterms
  have hre : |Real.cos (q : ℝ) - (cosTaylor q terms : ℝ)| ≤ (radius q terms : ℝ) := by
    calc
      |Real.cos (q : ℝ) - (cosTaylor q terms : ℝ)| =
          |(Complex.exp ((q : ℂ) * Complex.I) -
            ((cosTaylor q terms : ℂ) + (sinTaylor q terms : ℂ) * Complex.I)).re| := by
              change _ = |(Complex.exp ((q : ℂ) * Complex.I)).re -
                (((cosTaylor q terms : ℂ) + (sinTaylor q terms : ℂ) * Complex.I)).re|
              rw [show (q : ℂ) = ((q : ℝ) : ℂ) by norm_cast,
                Complex.exp_ofReal_mul_I_re]
              simp
      _ ≤ ‖Complex.exp ((q : ℂ) * Complex.I) -
            ((cosTaylor q terms : ℂ) + (sinTaylor q terms : ℂ) * Complex.I)‖ :=
              Complex.abs_re_le_norm _
      _ ≤ (radius q terms : ℝ) := h
  exact RatInterval.contains_widen_of_abs_sub_le
    (RatInterval.contains_point (cosTaylor q terms)) hre

theorem sin_mem_enclosure (q : ℚ) (terms : ℕ) (hq : |q| ≤ 1) (hterms : 0 < terms) :
    (sinEnclosure q terms).Contains (Real.sin (q : ℝ)) := by
  have h := exp_error_bound q terms hq hterms
  have him : |Real.sin (q : ℝ) - (sinTaylor q terms : ℝ)| ≤ (radius q terms : ℝ) := by
    calc
      |Real.sin (q : ℝ) - (sinTaylor q terms : ℝ)| =
          |(Complex.exp ((q : ℂ) * Complex.I) -
            ((cosTaylor q terms : ℂ) + (sinTaylor q terms : ℂ) * Complex.I)).im| := by
              change _ = |(Complex.exp ((q : ℂ) * Complex.I)).im -
                (((cosTaylor q terms : ℂ) + (sinTaylor q terms : ℂ) * Complex.I)).im|
              rw [show (q : ℂ) = ((q : ℝ) : ℂ) by norm_cast,
                Complex.exp_ofReal_mul_I_im]
              simp
      _ ≤ ‖Complex.exp ((q : ℂ) * Complex.I) -
            ((cosTaylor q terms : ℂ) + (sinTaylor q terms : ℂ) * Complex.I)‖ :=
              Complex.abs_im_le_norm _
      _ ≤ (radius q terms : ℝ) := h
  exact RatInterval.contains_widen_of_abs_sub_le
    (RatInterval.contains_point (sinTaylor q terms)) him

/-! ## Specialized high-throughput order-24 evaluator

The generic API above is convenient when experimenting with the order.  For a
large certificate, repeatedly normalizing powers and factorials is needless
work.  The following specialization has the same proved error bound, but uses
Horner form with already normalized rational coefficients.  At `|q| ≤ 1` its
radius is less than `1.7e-24`.
-/

/-- Horner evaluation of coefficients listed in ascending order. -/
def horner : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: as, x => a + x * horner as x

/-- Twelve-term (degree 22) cosine Taylor polynomial in Horner form. -/
def cosTaylor12 (q : ℚ) : ℚ :=
  horner [1, -(1 / 2), 1 / 24, -(1 / 720), 1 / 40320,
    -(1 / 3628800), 1 / 479001600, -(1 / 87178291200),
    1 / 20922789888000, -(1 / 6402373705728000),
    1 / 2432902008176640000, -(1 / 1124000727777607680000)] (q * q)

/-- Twelve-term (degree 23) sine Taylor polynomial in Horner form. -/
def sinTaylor12 (q : ℚ) : ℚ :=
  q * horner [1, -(1 / 6), 1 / 120, -(1 / 5040), 1 / 362880,
    -(1 / 39916800), 1 / 6227020800, -(1 / 1307674368000),
    1 / 355687428096000, -(1 / 121645100408832000),
    1 / 51090942171709440000, -(1 / 25852016738884976640000)] (q * q)

/-- Shared order-24 error radius, in normalized rational form. -/
def radius12 (q : ℚ) : ℚ := |q| ^ 24 / 595630465663909861785600

/-- High-throughput cosine enclosure, accurate to better than `1.7e-24` on
`[-1,1]`. -/
def cosEnclosure12 (q : ℚ) : RatInterval :=
  ⟨cosTaylor12 q - radius12 q, cosTaylor12 q + radius12 q⟩

/-- High-throughput sine enclosure, accurate to better than `1.7e-24` on
`[-1,1]`. -/
def sinEnclosure12 (q : ℚ) : RatInterval :=
  ⟨sinTaylor12 q - radius12 q, sinTaylor12 q + radius12 q⟩

private theorem cosTaylor12_eq (q : ℚ) : cosTaylor12 q = cosTaylor q 12 := by
  norm_num [cosTaylor12, horner, cosTaylor, cosTerm, sum_range_succ]
  ring

private theorem sinTaylor12_eq (q : ℚ) : sinTaylor12 q = sinTaylor q 12 := by
  norm_num [sinTaylor12, horner, sinTaylor, sinTerm, sum_range_succ]
  ring

private theorem radius12_eq (q : ℚ) : radius12 q = radius q 12 := by
  norm_num [radius12, radius]
  ring

theorem cos_mem_enclosure12 (q : ℚ) (hq : |q| ≤ 1) :
    (cosEnclosure12 q).Contains (Real.cos (q : ℝ)) := by
  simpa only [cosEnclosure12, cosEnclosure, cosTaylor12_eq, radius12_eq] using
    cos_mem_enclosure q 12 hq (by norm_num)

theorem sin_mem_enclosure12 (q : ℚ) (hq : |q| ≤ 1) :
    (sinEnclosure12 q).Contains (Real.sin (q : ℝ)) := by
  simpa only [sinEnclosure12, sinEnclosure, sinTaylor12_eq, radius12_eq] using
    sin_mem_enclosure q 12 hq (by norm_num)

theorem radius12_nonneg (q : ℚ) : 0 ≤ radius12 q := by
  apply div_nonneg
  · exact pow_nonneg (abs_nonneg q) _
  · norm_num

theorem cosEnclosure12_valid (q : ℚ) : (cosEnclosure12 q).Valid := by
  dsimp [RatInterval.Valid, cosEnclosure12]
  linarith [radius12_nonneg q]

theorem sinEnclosure12_valid (q : ℚ) : (sinEnclosure12 q).Valid := by
  dsimp [RatInterval.Valid, sinEnclosure12]
  linarith [radius12_nonneg q]

end ErdosMinimum.RationalTrig
