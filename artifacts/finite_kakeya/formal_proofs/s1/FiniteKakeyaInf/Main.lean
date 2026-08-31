import FiniteKakeyaInf.Coverage
import FiniteKakeyaInf.Counting

namespace FiniteKakeyaInf

open Finset

/-- The paper's explicit construction is Kakeya and has the claimed exact
cardinality, in denominator-free form. -/
theorem onePoleKakeya_main
    (p : ℕ) [hp : Fact p.Prime] (hp4 : p % 4 = 3) :
    IsKakeya (onePoleKakeya (ZMod p)) ∧
      8 * (onePoleKakeya (ZMod p)).card = 2 * p ^ 3 + 7 * p ^ 2 + 3 := by
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hp4
  have hchar : ringChar (ZMod p) ≠ 2 := by
    simpa [ZMod.ringChar_zmod_n] using hp2
  constructor
  · exact onePoleKakeya_isKakeya (ZMod p)
  · have hc := eight_mul_card_onePoleKakeya (ZMod p) hchar
    have hnonsquare : ¬IsSquare (-1 : ZMod p) := by
      rw [FiniteField.isSquare_neg_one_iff, ZMod.card, hp4]
      simp
    have hchi : quadraticChar (ZMod p) (-1) = -1 :=
      quadraticChar_neg_one_iff_not_isSquare.mpr hnonsquare
    rw [ZMod.card, hchi] at hc
    norm_num at hc
    exact_mod_cast hc

/-- The headline formula, with natural-number division exactly as printed in
the paper. -/
theorem onePoleKakeya_card
    (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) :
    (onePoleKakeya (ZMod p)).card = (2 * p ^ 3 + 7 * p ^ 2 + 3) / 8 := by
  exact Nat.eq_div_of_mul_eq_right (by norm_num)
    (onePoleKakeya_main p hp4).2

/-- Existential form of the discovery: for each prime `p ≡ 3 (mod 4)` there
is a Kakeya set in `𝔽_p³` of the stated size. -/
theorem exists_kakeya_set_of_card
    (p : ℕ) [Fact p.Prime] (hp4 : p % 4 = 3) :
    ∃ K : Finset (Point (ZMod p)),
      IsKakeya K ∧ K.card = (2 * p ^ 3 + 7 * p ^ 2 + 3) / 8 := by
  exact ⟨onePoleKakeya (ZMod p), (onePoleKakeya_main p hp4).1,
    onePoleKakeya_card p hp4⟩

/-- The discovery in ordinary hypothesis form: for every prime natural number
`p` congruent to `3` modulo `4`, there is a Kakeya set in `𝔽_p³` with the
paper's cardinality.  The local `Fact` only supplies mathlib's field instance
for `ZMod p`. -/
theorem finite_kakeya_inf
    (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 3) :
    letI : Fact p.Prime := ⟨hp⟩
    ∃ K : Finset (Point (ZMod p)),
      IsKakeya K ∧ K.card = (2 * p ^ 3 + 7 * p ^ 2 + 3) / 8 := by
  letI : Fact p.Prime := ⟨hp⟩
  exact exists_kakeya_set_of_card p hp4

end FiniteKakeyaInf
