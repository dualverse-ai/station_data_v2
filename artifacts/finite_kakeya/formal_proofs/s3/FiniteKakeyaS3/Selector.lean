import FiniteKakeyaS3.Character
import FiniteKakeyaS3.Geometry

/-!
# The discriminant selector

Exact indicator and zero-locus facts for the selector occurring in the
Spotlight 3 overlap calculation.
-/

namespace FiniteKakeyaS3

open scoped BigOperators
open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Integer indicator of the singleton `{0}`. -/
def zeroIndicator (x : F) : ℤ := if x = 0 then 1 else 0

/-- Integer indicator of the square set, including zero. -/
def squareIndicator (x : F) : ℤ := if IsSquare x then 1 else 0

/-- The exact identity `2 1_Q = 1 + χ + 1_{0}`. -/
theorem two_mul_squareIndicator (x : F) :
    2 * squareIndicator x = 1 + quadraticChar F x + zeroIndicator x := by
  by_cases hx : x = 0
  · subst x
    simp [squareIndicator, zeroIndicator]
  · by_cases hs : IsSquare x
    · rw [(quadraticChar_one_iff_isSquare hx).2 hs]
      simp [squareIndicator, zeroIndicator, hx, hs]
    · rw [quadraticChar_neg_one_iff_not_isSquare.2 hs]
      simp [squareIndicator, zeroIndicator, hx, hs]

/-- The discriminant zero locus. -/
def selectorZeroLocus (A B r : F) : Finset (F × F) :=
  univ.filter fun q => selectorDiscriminant A B r q.1 q.2 = 0

/-- Each horizontal row of the discriminant zero locus has
`1 + χ(Dy)` points. -/
theorem selector_zero_row_card (hchar : ringChar F ≠ 2)
    (A B r y : F) :
    (((univ : Finset F).filter fun z => selectorDiscriminant A B r y z = 0).card : ℤ) =
      quadraticChar F (familyD A B r * y) + 1 := by
  have h2 := two_ne_zero_of_ringChar F hchar
  let e : F → F := fun w => w + A + r * y
  have he : Function.Bijective e := by
    constructor
    · intro a b h
      dsimp [e] at h
      exact add_right_cancel (add_right_cancel h)
    · intro z
      refine ⟨z - A - r * y, ?_⟩
      dsimp [e]
      ring
  have hcard :
      ((univ : Finset F).filter fun w => w ^ 2 = 4 * familyD A B r * y).card =
        ((univ : Finset F).filter fun z => selectorDiscriminant A B r y z = 0).card := by
    apply Finset.card_bij (fun w _ => e w)
    · intro w hw
      simp only [mem_filter, mem_univ, true_and] at hw ⊢
      dsimp [e, selectorDiscriminant]
      linear_combination hw
    · intro a _ b _ hab
      exact he.1 hab
    · intro z hz
      rcases he.2 z with ⟨w, rfl⟩
      refine ⟨w, ?_, rfl⟩
      simp only [mem_filter, mem_univ, true_and] at hz ⊢
      dsimp [e, selectorDiscriminant] at hz
      linear_combination hz
  rw [← hcard]
  have hr := quadraticChar_card_sqrts hchar (4 * familyD A B r * y)
  rw [Set.toFinset_setOf] at hr
  have hfour : quadraticChar F (4 : F) = 1 := by
    rw [show (4 : F) = (2 : F) ^ 2 by norm_num]
    exact quadraticChar_sq_one' h2
  have hmul : quadraticChar F (4 * familyD A B r * y) =
      quadraticChar F 4 * quadraticChar F (familyD A B r * y) := by
    change quadraticCharFun F (4 * familyD A B r * y) =
      quadraticCharFun F 4 * quadraticCharFun F (familyD A B r * y)
    rw [show 4 * familyD A B r * y = 4 * (familyD A B r * y) by ring,
      quadraticCharFun_mul]
  calc
    _ = quadraticChar F (4 * familyD A B r * y) + 1 := hr
    _ = quadraticChar F 4 * quadraticChar F (familyD A B r * y) + 1 := by
      rw [hmul]
    _ = quadraticChar F (familyD A B r * y) + 1 := by rw [hfour]; ring

/-- The discriminant curve has exactly `q` affine points. -/
theorem card_selectorZeroLocus (hchar : ringChar F ≠ 2)
    (A B r : F) (hD : familyD A B r ≠ 0) :
    (selectorZeroLocus A B r).card = Fintype.card F := by
  have hsum : ((selectorZeroLocus A B r).card : ℤ) =
      ∑ y : F,
        (((univ : Finset F).filter fun z => selectorDiscriminant A B r y z = 0).card : ℤ) := by
    calc
      _ = ∑ q : F × F,
          if selectorDiscriminant A B r q.1 q.2 = 0 then (1 : ℤ) else 0 := by
        rw [selectorZeroLocus, card_filter]
        push_cast
        rfl
      _ = ∑ y : F, ∑ z : F,
          if selectorDiscriminant A B r y z = 0 then (1 : ℤ) else 0 := by
        rw [Fintype.sum_prod_type]
      _ = _ := by
        apply sum_congr rfl
        intro y _
        rw [card_filter]
        push_cast
        rfl
  simp_rw [selector_zero_row_card hchar A B r] at hsum
  have hmul : (∑ y : F, quadraticChar F (familyD A B r * y)) = 0 := by
    let e : F → F := fun y => familyD A B r * y
    have he : Function.Bijective e := by
      constructor
      · intro x y h
        exact mul_left_cancel₀ hD h
      · intro z
        refine ⟨z / familyD A B r, ?_⟩
        dsimp [e]
        field_simp
    calc
      _ = ∑ z : F, quadraticChar F z :=
        Equiv.sum_comp (Equiv.ofBijective e he) (quadraticChar F)
      _ = 0 := quadraticChar_sum_zero (F := F) hchar
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one] at hsum
  rw [hmul, zero_add] at hsum
  exact_mod_cast hsum

/-- Complete character cancellation for the selector discriminant. -/
theorem selector_full_character_sum (hchar : ringChar F ≠ 2)
    (A B r : F) (hD : familyD A B r ≠ 0) :
    (∑ y : F, ∑ z : F, quadraticChar F (selectorDiscriminant A B r y z)) = 0 := by
  have h2 := two_ne_zero_of_ringChar F hchar
  have hrow (y : F) :
      (∑ z : F, quadraticChar F (selectorDiscriminant A B r y z)) =
        if y = 0 then (Fintype.card F : ℤ) - 1 else -1 := by
    let e : F → F := fun w => w + A + r * y
    have he : Function.Bijective e := by
      constructor
      · intro a b h
        dsimp [e] at h
        exact add_right_cancel (add_right_cancel h)
      · intro z
        refine ⟨z - A - r * y, ?_⟩
        dsimp [e]
        ring
    by_cases hy : y = 0
    · subst y
      simp only [if_true]
      calc
        _ = ∑ w : F, quadraticChar F (selectorDiscriminant A B r 0 (w + A)) := by
          exact (Equiv.sum_comp (Equiv.addRight A)
            (fun z => quadraticChar F (selectorDiscriminant A B r 0 z))).symm
        _ = ∑ w : F, quadraticChar F (((w + A) - A) ^ 2) := by
          apply sum_congr rfl
          intro w _
          simp [selectorDiscriminant]
        _ = ∑ w : F, if w = 0 then 0 else (1 : ℤ) := by
          apply sum_congr rfl
          intro w _
          simp only [add_sub_cancel_right]
          by_cases hw : w = 0
          · simp [hw]
          · rw [quadraticChar_sq_one' hw]
            simp [hw]
        _ = (Fintype.card F : ℤ) - 1 := by
          rw [Finset.sum_ite]
          have hz : ((univ : Finset F).filter fun w => w = 0).card = 1 := by
            have : ((univ : Finset F).filter fun w => w = 0) = {0} := by ext; simp
            rw [this, card_singleton]
          have hn : ((univ : Finset F).filter fun w => ¬w = 0).card =
              Fintype.card F - 1 := by
            have hp := filter_card_add_filter_neg_card_eq_card
              (s := (univ : Finset F)) (fun w => w = 0)
            rw [hz, card_univ] at hp
            omega
          simp only [sum_const_zero, sum_const, nsmul_eq_mul, mul_one, zero_add]
          rw [hn, Nat.cast_sub (by have := Fintype.card_pos (α := F); omega)]
          norm_num
    · simp only [hy, if_false]
      calc
        _ = ∑ w : F, quadraticChar F (selectorDiscriminant A B r y (e w)) := by
          exact (Equiv.sum_comp (Equiv.ofBijective e he)
            (fun z => quadraticChar F (selectorDiscriminant A B r y z))).symm
        _ = ∑ w : F, quadraticChar F (w ^ 2 - 4 * familyD A B r * y) := by
          apply sum_congr rfl
          intro w _
          congr 1
          dsimp [e, selectorDiscriminant]
          ring
        _ = -1 := sum_quadratic_square_sub F hchar _
          (mul_ne_zero (mul_ne_zero (by
            rw [show (4 : F) = 2 * 2 by norm_num]
            exact mul_ne_zero h2 h2) hD) hy)
  calc
    _ = ∑ y : F, if y = 0 then (Fintype.card F : ℤ) - 1 else -1 := by
      apply sum_congr rfl
      intro y _
      exact hrow y
    _ = 0 := by
      rw [Finset.sum_ite]
      have hz : ((univ : Finset F).filter fun y => y = 0).card = 1 := by
        have : ((univ : Finset F).filter fun y => y = 0) = {0} := by ext; simp
        rw [this, card_singleton]
      have hn : ((univ : Finset F).filter fun y => ¬y = 0).card =
          Fintype.card F - 1 := by
        have hp := filter_card_add_filter_neg_card_eq_card
          (s := (univ : Finset F)) (fun y => y = 0)
        rw [hz, card_univ] at hp
        omega
      simp only [sum_const, nsmul_eq_mul]
      rw [hz, hn, Nat.cast_sub (by have := Fintype.card_pos (α := F); omega)]
      push_cast
      ring

/-- Exact size of the square-discriminant selector. -/
theorem two_mul_card_selector (hchar : ringChar F ≠ 2)
    (A B r : F) (hD : familyD A B r ≠ 0) :
    2 * ((selector A B r).card : ℤ) =
      (Fintype.card F : ℤ) ^ 2 + Fintype.card F := by
  have hind := Finset.sum_congr rfl fun q (_ : q ∈ (univ : Finset (F × F))) =>
    two_mul_squareIndicator (selectorDiscriminant A B r q.1 q.2)
  have hcard : (∑ q : F × F,
      2 * squareIndicator (selectorDiscriminant A B r q.1 q.2)) =
      2 * ((selector A B r).card : ℤ) := by
    rw [selector, card_filter]
    push_cast
    simp only [squareIndicator, Finset.mul_sum]
  have hzero : (∑ q : F × F,
      zeroIndicator (selectorDiscriminant A B r q.1 q.2)) =
      (selectorZeroLocus A B r).card := by
    rw [selectorZeroLocus, card_filter]
    push_cast
    rfl
  rw [hcard] at hind
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_prod,
    Nat.cast_mul, nsmul_eq_mul, mul_one] at hind
  rw [Fintype.sum_prod_type, selector_full_character_sum hchar A B r hD,
    hzero, card_selectorZeroLocus hchar A B r hD] at hind
  norm_num at hind ⊢
  simpa [pow_two] using hind

/-- The selector and actual non-pole union differ at exactly `(0,A)`. -/
theorem finiteLineUnion_eq_selector_erase (hchar : ringChar F ≠ 2)
    (A B r : F) (hD : familyD A B r ≠ 0) :
    finiteLineUnion A B r = (selector A B r).erase (0, A) := by
  have h2 := two_ne_zero_of_ringChar F hchar
  ext q
  rcases q with ⟨y, z⟩
  by_cases hy : y = 0
  · subst y
    rw [zero_row_mem_finiteLineUnion_iff A B r z hD, mem_erase, mem_selector]
    constructor
    · intro hz
      refine ⟨?_, ?_⟩
      · intro h
        exact hz (congrArg Prod.snd h)
      · exact ⟨z - A, by simp [selectorDiscriminant, pow_two]⟩
    · rintro ⟨hne, _⟩ hza
      subst z
      exact hne rfl
  · rw [mem_erase, mem_selector]
    have hne : (y, z) ≠ (0, A) := by
      intro h
      exact hy (congrArg Prod.fst h)
    rw [and_iff_right hne]
    exact finiteLine_selector_iff A B r y z hD hy h2

/-- Equation (1), in denominator-free form. -/
theorem two_mul_card_finiteLineUnion (hchar : ringChar F ≠ 2)
    (A B r : F) (hD : familyD A B r ≠ 0) :
    2 * ((finiteLineUnion A B r).card : ℤ) =
      (Fintype.card F : ℤ) ^ 2 + Fintype.card F - 2 := by
  have hmem : (0, A) ∈ selector A B r := by
    rw [mem_selector]
    exact ⟨0, by simp [selectorDiscriminant]⟩
  rw [finiteLineUnion_eq_selector_erase hchar A B r hD,
    card_erase_of_mem hmem, Nat.cast_sub (card_pos.mpr ⟨(0, A), hmem⟩)]
  have hs := two_mul_card_selector hchar A B r hD
  push_cast
  omega

end FiniteKakeyaS3
