import FiniteKakeyaS3.Overlap
import FiniteKakeyaS3.Penalty

/-!
# Spotlight 3: uniform full-family penalty

The generic theorem is proved over an arbitrary finite field of odd
characteristic.  The final two theorems specialize it to the odd prime field
`ZMod p`, first in denominator-free integer form and then exactly as the
notebook's rational inequality.
-/

namespace FiniteKakeyaS3

open Finset

/-- Uniform full-family penalty over every finite field of odd
characteristic.  This is the denominator-free version of Theorem 4.1. -/
theorem boundaryPenalty_int_bound
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2) (lambda A B r u v : F)
    (hlambda : lambda ≠ 0) (hD : familyD A B r ≠ 0) :
    |8 * (boundaryPenalty lambda A B r u v : ℤ) -
        3 * (Fintype.card F : ℤ) ^ 2| <
      40 * (Fintype.card F : ℤ) := by
  let q : ℤ := Fintype.card F
  let pen : ℤ := boundaryPenalty lambda A B r u v
  let overlap : ℤ :=
    (finiteLineUnion A B r ∩ scaledSquareFootprint lambda).card
  let extra : ℤ := (extraPoints lambda A B r u v).card
  have hbookNat := penalty_add_overlap lambda A B r u v
  have hbook : pen + overlap = (finiteLineUnion A B r).card + extra := by
    dsimp [pen, overlap, extra]
    exact_mod_cast hbookNat
  have hfinite := two_mul_card_finiteLineUnion hchar A B r hD
  have hover := abs_eight_mul_card_finiteLine_overlap_sub_sq_le
    hchar hlambda hD
  have hextraNat := card_extraPoints_le lambda A B r u v
  have hextra : extra ≤ 2 * q := by
    dsimp [extra, q]
    exact_mod_cast hextraNat
  have hextra0 : 0 ≤ extra := by dsimp [extra]; positivity
  have hqodd := FiniteField.odd_card_of_char_ne_two hchar
  have hqone : 1 < Fintype.card F := Fintype.one_lt_card
  have hq3Nat : 3 ≤ Fintype.card F := by omega
  have hq3 : 3 ≤ q := by
    dsimp [q]
    exact_mod_cast hq3Nat
  have hid :
      8 * pen - 3 * q ^ 2 =
        -(8 * overlap - q ^ 2) + (4 * q - 8) + 8 * extra := by
    dsimp [q, pen, overlap, extra] at hbook hfinite ⊢
    nlinarith
  rw [show 8 * (boundaryPenalty lambda A B r u v : ℤ) -
      3 * (Fintype.card F : ℤ) ^ 2 = 8 * pen - 3 * q ^ 2 by rfl, hid]
  have htri :
      |-(8 * overlap - q ^ 2) + (4 * q - 8) + 8 * extra| ≤
        |8 * overlap - q ^ 2| + (4 * q - 8) + 8 * extra := by
    calc
      _ ≤ |-(8 * overlap - q ^ 2) + (4 * q - 8)| + |8 * extra| :=
        abs_add_le _ _
      _ ≤ (|-(8 * overlap - q ^ 2)| + |4 * q - 8|) + |8 * extra| := by
        gcongr
        exact abs_add_le _ _
      _ = |8 * overlap - q ^ 2| + (4 * q - 8) + 8 * extra := by
        rw [abs_neg, abs_of_nonneg (by omega : 0 ≤ 4 * q - 8),
          abs_of_nonneg (by positivity : 0 ≤ 8 * extra)]
  change |8 * overlap - q ^ 2| ≤ 15 * q + 10 at hover
  change |-(8 * overlap - q ^ 2) + (4 * q - 8) + 8 * extra| < 40 * q
  omega

/-- Prime-field form with the denominator cleared. -/
theorem finite_kakeya_s3_int
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p) :
    letI : Fact p.Prime := ⟨hp⟩
    ∀ lambda A B r u v : ZMod p,
      lambda ≠ 0 → familyD A B r ≠ 0 →
      |8 * (boundaryPenalty lambda A B r u v : ℤ) - 3 * (p : ℤ) ^ 2| <
        40 * (p : ℤ) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro lambda A B r u v hlambda hD
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hpodd
  have hchar : ringChar (ZMod p) ≠ 2 := by
    simpa [ZMod.ringChar_zmod_n] using hp2
  simpa [ZMod.card] using
    boundaryPenalty_int_bound (ZMod p) hchar lambda A B r u v hlambda hD

/-- **Spotlight 3 / Theorem 4.1 (uniform full-family penalty).**

For every odd prime and every nondegenerate one-pole completion, the number
of boundary points outside `(lambda Q)^2` differs from `3p²/8` by less than
`5p`.  This is the theorem exactly in the notebook's rational form. -/
theorem finite_kakeya_s3
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p) :
    letI : Fact p.Prime := ⟨hp⟩
    ∀ lambda A B r u v : ZMod p,
      lambda ≠ 0 → familyD A B r ≠ 0 →
      |(boundaryPenalty lambda A B r u v : ℚ) - 3 * (p : ℚ) ^ 2 / 8| <
        5 * (p : ℚ) := by
  letI : Fact p.Prime := ⟨hp⟩
  intro lambda A B r u v hlambda hD
  have hint := finite_kakeya_s3_int p hp hpodd lambda A B r u v hlambda hD
  rw [abs_lt] at hint ⊢
  constructor
  · have hcast : -(40 * (p : ℚ)) <
        8 * (boundaryPenalty lambda A B r u v : ℚ) - 3 * (p : ℚ) ^ 2 := by
      exact_mod_cast hint.1
    linarith
  · have hcast :
        8 * (boundaryPenalty lambda A B r u v : ℚ) - 3 * (p : ℚ) ^ 2 <
          40 * (p : ℚ) := by
      exact_mod_cast hint.2
    linarith

end FiniteKakeyaS3
