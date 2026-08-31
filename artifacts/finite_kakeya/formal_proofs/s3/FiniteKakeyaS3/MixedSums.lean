import FiniteKakeyaS3.Character
import FiniteKakeyaS3.Definitions

set_option maxHeartbeats 800000

/-!
# Mixed character sums for the uniform one-pole family

This file proves the four estimates used in the square-indicator expansion of
the overlap with `(lambda Q)^2`.  The two genuinely mixed sums are deliberately
estimated coarsely: only the number of exceptional parameters matters for the
final `5p` bound.
-/

namespace FiniteKakeyaS3

open scoped BigOperators
open Finset

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

/-- The discriminant character `X`. -/
def xChar (A B r y z : F) : ℤ :=
  quadraticChar F (selectorDiscriminant A B r y z)

/-- The scaled-square coordinate character `Y`. -/
def yChar (lambda y : F) : ℤ := quadraticChar F (y / lambda)

/-- The scaled-square coordinate character `Z`. -/
def zChar (lambda z : F) : ℤ := quadraticChar F (z / lambda)

private theorem abs_quadraticChar_le_one (a : F) : |quadraticChar F a| ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · rcases quadraticChar_dichotomy (F := F) ha with h | h <;> simp [h]

private theorem abs_quadraticChar_eq_one {a : F} (ha : a ≠ 0) :
    |quadraticChar F a| = 1 := by
  rcases quadraticChar_dichotomy (F := F) ha with h | h <;> simp [h]

private theorem sum_char_div_eq_zero (hchar : ringChar F ≠ 2) {lambda : F}
    (hlambda : lambda ≠ 0) :
    (∑ y : F, yChar F lambda y) = 0 := by
  simpa [yChar, div_eq_mul_inv, mul_comm] using
    sum_quadratic_affine F hchar lambda⁻¹ 0 (inv_ne_zero hlambda)

private theorem discriminant_translate (A B r y x : F) :
    selectorDiscriminant A B r y (x + A + r * y) =
      x ^ 2 - 4 * familyD A B r * y := by
  simp only [selectorDiscriminant, familyD]
  ring

/-- The complete `X`-sum on one horizontal row. -/
theorem sum_xChar_row (hchar : ringChar F ≠ 2) {A B r y : F}
    (hD : familyD A B r ≠ 0) :
    (∑ z : F, xChar F A B r y z) =
      if y = 0 then (Fintype.card F : ℤ) - 1 else -1 := by
  let e : F → F := fun x ↦ x + A + r * y
  have he : Function.Bijective e := by
    constructor
    · intro x x' h
      exact add_right_cancel (add_right_cancel h)
    · intro z
      exact ⟨z - A - r * y, by dsimp [e]; ring⟩
  calc
    (∑ z : F, xChar F A B r y z) =
        ∑ x : F, quadraticChar F (x ^ 2 - 4 * familyD A B r * y) := by
      rw [show (∑ z : F, xChar F A B r y z) =
          ∑ x : F, xChar F A B r y (e x) by
        exact (Equiv.sum_comp (Equiv.ofBijective e he) (xChar F A B r y)).symm]
      apply sum_congr rfl
      intro x _
      rw [xChar, discriminant_translate]
    _ = if y = 0 then (Fintype.card F : ℤ) - 1 else -1 := by
      have hsum := sum_quadratic_general F hchar 1 0
        (-4 * familyD A B r * y) one_ne_zero
      rw [show (∑ x : F, quadraticChar F (x ^ 2 - 4 * familyD A B r * y)) =
          ∑ x : F, quadraticChar F
            (1 * x ^ 2 + 0 * x + (-4 * familyD A B r * y)) by
        apply sum_congr rfl
        intro x _
        congr 1
        ring]
      rw [hsum]
      by_cases hy : y = 0
      · simp [hy]
      · have h2 := two_ne_zero_of_ringChar F hchar
        have h4 : (4 : F) ≠ 0 := by
          rw [show (4 : F) = 2 * 2 by norm_num]
          exact mul_ne_zero h2 h2
        have h16 : (16 : F) ≠ 0 := by
          rw [show (16 : F) = 4 * 4 by norm_num]
          exact mul_ne_zero h4 h4
        have hdisc : (0 : F) ^ 2 - 4 * 1 * (-4 * familyD A B r * y) ≠ 0 := by
          rw [show (0 : F) ^ 2 - 4 * 1 * (-4 * familyD A B r * y) =
            16 * familyD A B r * y by ring]
          exact mul_ne_zero (mul_ne_zero h16 hD) hy
        simp [hy, h4, hD]

/-- The complete discriminant character sum vanishes. -/
theorem sum_xChar_eq_zero (hchar : ringChar F ≠ 2) {A B r : F}
    (hD : familyD A B r ≠ 0) :
    (∑ y : F, ∑ z : F, xChar F A B r y z) = 0 := by
  simp_rw [sum_xChar_row F hchar hD]
  rw [Finset.sum_ite]
  have hz : ((univ : Finset F).filter fun y ↦ y = 0).card = 1 := by
    have heq : ((univ : Finset F).filter fun y ↦ y = 0) = {0} := by ext; simp
    rw [heq, card_singleton]
  have hn : ((univ : Finset F).filter fun y ↦ ¬y = 0).card =
      Fintype.card F - 1 := by
    have hp := filter_card_add_filter_neg_card_eq_card
      (s := (univ : Finset F)) (fun y : F ↦ y = 0)
    rw [hz, card_univ] at hp
    omega
  simp only [sum_const, nsmul_eq_mul]
  rw [hz, hn, Nat.cast_sub (by have := Fintype.card_pos (α := F); omega)]
  ring

/-- The `YX` mixed sum vanishes row by row after summing over `y`. -/
theorem sum_yChar_mul_xChar_eq_zero (hchar : ringChar F ≠ 2)
    {lambda A B r : F} (hlambda : lambda ≠ 0) (hD : familyD A B r ≠ 0) :
    (∑ y : F, ∑ z : F, yChar F lambda y * xChar F A B r y z) = 0 := by
  calc
    _ = ∑ y : F, yChar F lambda y *
        (if y = 0 then (Fintype.card F : ℤ) - 1 else -1) := by
      apply sum_congr rfl
      intro y _
      rw [← Finset.mul_sum, sum_xChar_row F hchar hD]
    _ = -(∑ y : F, yChar F lambda y) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro y _
      by_cases hy : y = 0
      · simp [hy, yChar]
      · simp [hy]
    _ = 0 := by rw [sum_char_div_eq_zero F hchar hlambda]; simp

private theorem card_quadratic_zero_le_two (a b c : F) (ha : a ≠ 0) :
    ((univ : Finset F).filter fun x ↦ a * x ^ 2 + b * x + c = 0).card ≤ 2 := by
  let P : Polynomial F := Polynomial.C a * Polynomial.X ^ 2 +
    Polynomial.C b * Polynomial.X + Polynomial.C c
  have hP : P ≠ 0 := by
    intro h
    have hc := congrArg (fun Q : Polynomial F ↦ Q.coeff 2) h
    simp [P] at hc
    exact ha hc
  have hsub : ((univ : Finset F).filter fun x ↦ a * x ^ 2 + b * x + c = 0) ⊆
      P.roots.toFinset := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and] at hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP, Polynomial.IsRoot.def]
    simpa [P] using hx
  calc
    _ ≤ P.roots.toFinset.card := card_le_card hsub
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ 2 := by
      apply Polynomial.natDegree_le_iff_degree_le.2
      dsimp [P]
      apply (Polynomial.degree_add_le _ _).trans
      apply max_le
      · apply (Polynomial.degree_add_le _ _).trans
        exact max_le (Polynomial.degree_C_mul_X_pow_le 2 a)
          ((Polynomial.degree_C_mul_X_le b).trans (by norm_num))
      · exact Polynomial.degree_C_le.trans (by norm_num)

private theorem abs_scaled_ZX_le_raw {lambda A B r : F} (hlambda : lambda ≠ 0) :
    |(∑ y : F, ∑ z : F, zChar F lambda z * xChar F A B r y z)| ≤
      |(∑ y : F, ∑ z : F, quadraticChar F z * xChar F A B r y z)| := by
  have heq :
      (∑ y : F, ∑ z : F, zChar F lambda z * xChar F A B r y z) =
        quadraticChar F lambda⁻¹ *
          (∑ y : F, ∑ z : F, quadraticChar F z * xChar F A B r y z) := by
    calc
      _ = ∑ y : F, ∑ z : F,
          quadraticChar F lambda⁻¹ *
            (quadraticChar F z * xChar F A B r y z) := by
        apply sum_congr rfl
        intro y _
        apply sum_congr rfl
        intro z _
        rw [zChar, div_eq_mul_inv]
        change quadraticCharFun F (z * lambda⁻¹) * _ = _
        rw [quadraticCharFun_mul]
        change quadraticCharFun F z * quadraticCharFun F lambda⁻¹ *
            xChar F A B r y z = quadraticCharFun F lambda⁻¹ *
              (quadraticCharFun F z * xChar F A B r y z)
        ring
      _ = _ := by simp_rw [Finset.mul_sum]
  rw [heq, abs_mul, abs_quadraticChar_eq_one F (inv_ne_zero hlambda), one_mul]

private theorem raw_ZX_reindex (A B r : F) :
    (∑ y : F, ∑ z : F, quadraticChar F z * xChar F A B r y z) =
      ∑ x : F, ∑ y : F,
        quadraticChar F (x + A + r * y) *
          quadraticChar F (x ^ 2 - 4 * familyD A B r * y) := by
  calc
    _ = ∑ y : F, ∑ x : F,
        quadraticChar F (x + A + r * y) *
          quadraticChar F (x ^ 2 - 4 * familyD A B r * y) := by
      apply sum_congr rfl
      intro y _
      let e : F → F := fun x ↦ x + A + r * y
      have he : Function.Bijective e := by
        constructor
        · intro x x' h
          exact add_right_cancel (add_right_cancel h)
        · intro z
          exact ⟨z - A - r * y, by dsimp [e]; ring⟩
      rw [show (∑ z : F, quadraticChar F z * xChar F A B r y z) =
          ∑ x : F, quadraticChar F (e x) * xChar F A B r y (e x) by
        exact (Equiv.sum_comp (Equiv.ofBijective e he)
          (fun z ↦ quadraticChar F z * xChar F A B r y z)).symm]
      apply sum_congr rfl
      intro x _
      rw [xChar, discriminant_translate]
    _ = _ := by rw [sum_comm]

/-- The `ZX` mixed sum has the coarse bound needed for Theorem 4.1. -/
theorem abs_sum_zChar_mul_xChar_le_three_card (hchar : ringChar F ≠ 2)
    {lambda A B r : F} (hlambda : lambda ≠ 0) (hD : familyD A B r ≠ 0) :
    |(∑ y : F, ∑ z : F, zChar F lambda z * xChar F A B r y z)| ≤
      3 * (Fintype.card F : ℤ) := by
  apply (abs_scaled_ZX_le_raw F hlambda).trans
  rw [raw_ZX_reindex F A B r]
  by_cases hr : r = 0
  · subst r
    have h4 : (4 : F) ≠ 0 := by
      have h2 := two_ne_zero_of_ringChar F hchar
      rw [show (4 : F) = 2 * 2 by norm_num]
      exact mul_ne_zero h2 h2
    have hcoef : -4 * familyD A B 0 ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr h4) hD
    have hinner (x : F) :
        (∑ y : F, quadraticChar F (x + A + 0 * y) *
          quadraticChar F (x ^ 2 - 4 * familyD A B 0 * y)) = 0 := by
      rw [show (∑ y : F, quadraticChar F (x + A + 0 * y) *
          quadraticChar F (x ^ 2 - 4 * familyD A B 0 * y)) =
          quadraticChar F (x + A) *
            (∑ y : F, quadraticChar F ((-4 * familyD A B 0) * y + x ^ 2)) by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro y _
        congr 1
        · ring
        · congr 1 <;> ring]
      rw [sum_quadratic_affine F hchar _ _ hcoef, mul_zero]
    simp_rw [hinner]
    simp
  · let bad : Finset F := univ.filter fun x ↦
        r * x ^ 2 + 4 * familyD A B r * x + 4 * familyD A B r * A = 0
    have hbad : bad.card ≤ 2 := by
      exact card_quadratic_zero_le_two F r (4 * familyD A B r)
        (4 * familyD A B r * A) hr
    let a : F := -4 * familyD A B r * r
    have ha : a ≠ 0 := by
      have h2 := two_ne_zero_of_ringChar F hchar
      have h4 : (4 : F) ≠ 0 := by
        rw [show (4 : F) = 2 * 2 by norm_num]
        exact mul_ne_zero h2 h2
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr h4) hD) hr
    have hinner (x : F) :
        |(∑ y : F, quadraticChar F (x + A + r * y) *
          quadraticChar F (x ^ 2 - 4 * familyD A B r * y))| ≤
          1 + if x ∈ bad then (Fintype.card F : ℤ) else 0 := by
      rw [show (∑ y : F, quadraticChar F (x + A + r * y) *
          quadraticChar F (x ^ 2 - 4 * familyD A B r * y)) =
          ∑ y : F, quadraticChar F
            (a * y ^ 2 +
              (r * x ^ 2 - 4 * familyD A B r * (x + A)) * y +
              (x + A) * x ^ 2) by
        apply sum_congr rfl
        intro y _
        change quadraticCharFun F (x + A + r * y) *
            quadraticCharFun F (x ^ 2 - 4 * familyD A B r * y) = _
        rw [← quadraticCharFun_mul]
        congr 1
        dsimp [a]
        ring]
      rw [sum_quadratic_general F hchar _ _ _ ha]
      have hdisc :
          (r * x ^ 2 - 4 * familyD A B r * (x + A)) ^ 2 -
              4 * a * ((x + A) * x ^ 2) =
            (r * x ^ 2 + 4 * familyD A B r * x +
              4 * familyD A B r * A) ^ 2 := by
        dsimp [a]
        ring
      rw [hdisc]
      by_cases hx : r * x ^ 2 + 4 * familyD A B r * x +
          4 * familyD A B r * A = 0
      · have hmem : x ∈ bad := by simp [bad, hx]
        have hp0 : (r * x ^ 2 + 4 * familyD A B r * x +
            4 * familyD A B r * A) ^ 2 = 0 := by rw [hx]; simp
        rw [if_pos hp0, if_pos hmem]
        rw [abs_mul, abs_quadraticChar_eq_one F ha, mul_one]
        have hq := Fintype.card_pos (α := F)
        push_cast
        rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ (Fintype.card F : ℤ) - 1)]
        omega
      · have hmem : x ∉ bad := by simp [bad, hx]
        have hpne : (r * x ^ 2 + 4 * familyD A B r * x +
            4 * familyD A B r * A) ^ 2 ≠ 0 := pow_ne_zero 2 hx
        rw [if_neg hpne, if_neg hmem, add_zero, abs_neg,
          abs_quadraticChar_eq_one F ha]
    calc
      |(∑ x : F, ∑ y : F, quadraticChar F (x + A + r * y) *
          quadraticChar F (x ^ 2 - 4 * familyD A B r * y))| ≤
          ∑ x : F, |(∑ y : F, quadraticChar F (x + A + r * y) *
            quadraticChar F (x ^ 2 - 4 * familyD A B r * y))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x : F, (1 + if x ∈ bad then (Fintype.card F : ℤ) else 0) :=
        sum_le_sum fun x _ ↦ hinner x
      _ = (Fintype.card F : ℤ) + bad.card * Fintype.card F := by
        rw [sum_add_distrib]
        simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
        congr 1
        rw [← Finset.sum_filter]
        simp [bad]
      _ ≤ 3 * (Fintype.card F : ℤ) := by
        have hq : 0 ≤ (Fintype.card F : ℤ) := by positivity
        have hb : (bad.card : ℤ) ≤ 2 := by exact_mod_cast hbad
        nlinarith

private def qPoly (A B r t y : F) : F :=
  (t - r) ^ 2 * y ^ 2 -
    2 * (A * (t - r) + 2 * familyD A B r) * y + A ^ 2

private theorem discriminant_slope_substitution (A B r t y : F) :
    selectorDiscriminant A B r y (t * y) = qPoly F A B r t y := by
  simp only [selectorDiscriminant, familyD, qPoly]
  ring

private theorem scaled_product_on_nonzero {lambda y t : F}
    (hlambda : lambda ≠ 0) (hy : y ≠ 0) :
    yChar F lambda y * zChar F lambda (t * y) = quadraticChar F t := by
  change quadraticCharFun F (y / lambda) * quadraticCharFun F (t * y / lambda) =
    quadraticCharFun F t
  rw [← quadraticCharFun_mul]
  rw [show y / lambda * (t * y / lambda) = t * (y / lambda) ^ 2 by field_simp]
  rw [quadraticCharFun_mul,
    show quadraticCharFun F ((y / lambda) ^ 2) = 1 from
      quadraticChar_sq_one' (div_ne_zero hy hlambda), mul_one]

private theorem YZX_reindex {lambda A B r : F} (hlambda : lambda ≠ 0) :
    (∑ y : F, ∑ z : F,
      yChar F lambda y * zChar F lambda z * xChar F A B r y z) =
      ∑ t : F, quadraticChar F t *
        (∑ y ∈ (univ : Finset F).erase 0,
          quadraticChar F (qPoly F A B r t y)) := by
  let G : F → ℤ := fun y ↦ ∑ z : F,
    yChar F lambda y * zChar F lambda z * xChar F A B r y z
  have hG0 : G 0 = 0 := by simp [G, yChar]
  calc
    (∑ y : F, ∑ z : F,
      yChar F lambda y * zChar F lambda z * xChar F A B r y z) =
        ∑ y ∈ (univ : Finset F).erase 0, G y := by
      rw [show (∑ y : F, ∑ z : F,
          yChar F lambda y * zChar F lambda z * xChar F A B r y z) =
          ∑ y : F, G y by rfl]
      rw [sum_erase_eq_sub (mem_univ 0), hG0, sub_zero]
    _ = ∑ y ∈ (univ : Finset F).erase 0, ∑ t : F,
        quadraticChar F t * quadraticChar F (qPoly F A B r t y) := by
      apply sum_congr rfl
      intro y hyu
      have hy : y ≠ 0 := ne_of_mem_erase hyu
      dsimp [G]
      rw [show (∑ z : F,
          yChar F lambda y * zChar F lambda z * xChar F A B r y z) =
          ∑ t : F, yChar F lambda y * zChar F lambda (t * y) *
            xChar F A B r y (t * y) by
        exact (Equiv.sum_comp (Equiv.mulRight₀ y hy)
          (fun z ↦ yChar F lambda y * zChar F lambda z * xChar F A B r y z)).symm]
      apply sum_congr rfl
      intro t _
      rw [scaled_product_on_nonzero F hlambda hy, xChar,
        discriminant_slope_substitution]
      rfl
    _ = _ := by
      rw [sum_comm]
      apply sum_congr rfl
      intro t _
      rw [Finset.mul_sum]

private theorem card_linear_zero_le_one (A B : F) (hAB : A ≠ 0 ∨ B ≠ 0) :
    ((univ : Finset F).filter fun t ↦ A * t + B = 0).card ≤ 1 := by
  apply card_le_one.mpr
  intro x hx y hy
  simp only [mem_filter, mem_univ, true_and] at hx hy
  by_cases hA : A = 0
  · have hB : B ≠ 0 := hAB.resolve_left (fun hne ↦ hne hA)
    simp [hA] at hx
    exact (hB hx).elim
  · apply (mul_left_cancel₀ hA)
    exact sub_eq_zero.mp (by linear_combination hx - hy)

/-- The `YZX` mixed sum has the coarse bound needed for Theorem 4.1. -/
theorem abs_sum_yChar_mul_zChar_mul_xChar_le_four_card
    (hchar : ringChar F ≠ 2) {lambda A B r : F}
    (hlambda : lambda ≠ 0) (hD : familyD A B r ≠ 0) :
    |(∑ y : F, ∑ z : F,
      yChar F lambda y * zChar F lambda z * xChar F A B r y z)| ≤
      4 * (Fintype.card F : ℤ) := by
  rw [YZX_reindex F hlambda]
  let bad : Finset F := univ.filter fun t ↦ A * t + B = 0
  have hAB : A ≠ 0 ∨ B ≠ 0 := by
    by_cases hA : A = 0
    · right
      intro hB
      apply hD
      simp [familyD, hA, hB]
    · exact Or.inl hA
  have hbad : bad.card ≤ 1 := card_linear_zero_le_one F A B hAB
  have hinner (t : F) :
      |quadraticChar F t *
        (∑ y ∈ (univ : Finset F).erase 0,
          quadraticChar F (qPoly F A B r t y))| ≤
        2 + if t ∈ bad then (Fintype.card F : ℤ) else 0 := by
    rw [abs_mul]
    have htchar := abs_quadraticChar_le_one F t
    have herase :
        (∑ y ∈ (univ : Finset F).erase 0,
          quadraticChar F (qPoly F A B r t y)) =
        (∑ y : F, quadraticChar F (qPoly F A B r t y)) -
          quadraticChar F (A ^ 2) := by
      rw [sum_erase_eq_sub (mem_univ 0)]
      simp [qPoly]
    rw [herase]
    by_cases htr : t = r
    · subst t
      have hcoef : -4 * familyD A B r ≠ 0 := by
        have h2 := two_ne_zero_of_ringChar F hchar
        have h4 : (4 : F) ≠ 0 := by
          rw [show (4 : F) = 2 * 2 by norm_num]
          exact mul_ne_zero h2 h2
        exact mul_ne_zero (neg_ne_zero.mpr h4) hD
      have hsum : (∑ y : F, quadraticChar F (qPoly F A B r r y)) = 0 := by
        rw [show (∑ y : F, quadraticChar F (qPoly F A B r r y)) =
            ∑ y : F, quadraticChar F
              ((-4 * familyD A B r) * y + A ^ 2) by
          apply sum_congr rfl
          intro y _
          congr 1
          simp only [qPoly]
          ring]
        exact sum_quadratic_affine F hchar (-4 * familyD A B r) (A ^ 2) hcoef
      rw [hsum, zero_sub, abs_neg]
      have hnotbad : r ∉ bad := by simpa [bad, familyD] using hD
      rw [if_neg hnotbad]
      have hAchar := abs_quadraticChar_le_one F (A ^ 2)
      have hmul := mul_nonneg (sub_nonneg.mpr htchar)
        (abs_nonneg (quadraticChar F (A ^ 2)))
      nlinarith
    · have hlead : (t - r) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr htr)
      have hdisc :
          (-2 * (A * (t - r) + 2 * familyD A B r)) ^ 2 -
              4 * (t - r) ^ 2 * A ^ 2 =
            16 * familyD A B r * (A * t + B) := by
        simp only [familyD]
        ring
      have hsum := sum_quadratic_general F hchar ((t - r) ^ 2)
        (-2 * (A * (t - r) + 2 * familyD A B r)) (A ^ 2) hlead
      have hqpoly : (∑ y : F, quadraticChar F (qPoly F A B r t y)) =
          if A * t + B = 0 then (Fintype.card F : ℤ) - 1 else -1 := by
        rw [show (∑ y : F, quadraticChar F (qPoly F A B r t y)) =
          ∑ y : F, quadraticChar F
            ((t - r) ^ 2 * y ^ 2 +
              (-2 * (A * (t - r) + 2 * familyD A B r)) * y + A ^ 2) by
          apply sum_congr rfl
          intro y _
          congr 1
          simp [qPoly]
          ring]
        rw [hsum, hdisc]
        have h2 := two_ne_zero_of_ringChar F hchar
        have h16 : (16 : F) ≠ 0 := by
          have h4 : (4 : F) ≠ 0 := by
            rw [show (4 : F) = 2 * 2 by norm_num]
            exact mul_ne_zero h2 h2
          rw [show (16 : F) = 4 * 4 by norm_num]
          exact mul_ne_zero h4 h4
        have hfac : 16 * familyD A B r ≠ 0 := mul_ne_zero h16 hD
        have hsquarechar : quadraticChar F ((t - r) ^ 2) = 1 :=
          quadraticChar_sq_one' (sub_ne_zero.mpr htr)
        by_cases hAt : A * t + B = 0
        · simp [hAt, hsquarechar]
        · have : 16 * familyD A B r * (A * t + B) ≠ 0 := mul_ne_zero hfac hAt
          simp [hAt, this, hsquarechar]
      rw [hqpoly]
      by_cases hAt : A * t + B = 0
      · have hmem : t ∈ bad := by simp [bad, hAt]
        simp only [hAt, if_true, hmem]
        have hqc := abs_quadraticChar_le_one F (A ^ 2)
        have hqpos := Fintype.card_pos (α := F)
        have hprod : |quadraticChar F t| *
            |(Fintype.card F : ℤ) - 1 - quadraticChar F (A ^ 2)| ≤
              (Fintype.card F : ℤ) := by
          have hsub : |(Fintype.card F : ℤ) - 1 - quadraticChar F (A ^ 2)| ≤
              (Fintype.card F : ℤ) := by
            have hA : A ≠ 0 := by
              intro hAz
              have hB : B = 0 := by simpa [hAz] using hAt
              apply hD
              rw [familyD, hAz, zero_mul, zero_add, hB]
            rcases quadraticChar_dichotomy (F := F) (pow_ne_zero 2 hA) with h | h
            · rw [h]
              have hq2 := Fintype.one_lt_card (α := F)
              rw [abs_of_nonneg (by omega :
                (0 : ℤ) ≤ (Fintype.card F : ℤ) - 1 - 1)]
              omega
            · rw [h]
              simp
          have hmul := mul_nonneg (sub_nonneg.mpr htchar)
            (abs_nonneg ((Fintype.card F : ℤ) - 1 - quadraticChar F (A ^ 2)))
          nlinarith
        nlinarith
      · have hmem : t ∉ bad := by simp [bad, hAt]
        simp only [hAt, if_false, hmem]
        have hqc := abs_quadraticChar_le_one F (A ^ 2)
        have hsmall : |-1 - quadraticChar F (A ^ 2)| ≤ 2 := by
          by_cases hA2 : A ^ 2 = 0
          · simp [hA2]
          · rcases quadraticChar_dichotomy (F := F) hA2 with h | h <;> simp [h]
        have hmul := mul_nonneg (sub_nonneg.mpr htchar)
          (abs_nonneg (-1 - quadraticChar F (A ^ 2)))
        nlinarith
  calc
    |(∑ t : F, quadraticChar F t *
        (∑ y ∈ (univ : Finset F).erase 0,
          quadraticChar F (qPoly F A B r t y)))| ≤
        ∑ t : F, |quadraticChar F t *
          (∑ y ∈ (univ : Finset F).erase 0,
            quadraticChar F (qPoly F A B r t y))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ t : F, (2 + if t ∈ bad then (Fintype.card F : ℤ) else 0) :=
      sum_le_sum fun t _ ↦ hinner t
    _ = 2 * (Fintype.card F : ℤ) + bad.card * Fintype.card F := by
      rw [sum_add_distrib]
      calc
        (∑ _ : F, (2 : ℤ)) +
            ∑ t : F, (if t ∈ bad then (Fintype.card F : ℤ) else 0) =
            2 * (Fintype.card F : ℤ) +
              ∑ t : F, (if t ∈ bad then (Fintype.card F : ℤ) else 0) := by
                simp only [sum_const, card_univ, nsmul_eq_mul]
                ring
        _ = _ := by
          congr 1
          rw [← Finset.sum_filter]
          simp [bad]
    _ ≤ 4 * (Fintype.card F : ℤ) := by
      have hq : 0 ≤ (Fintype.card F : ℤ) := by positivity
      have hb : (bad.card : ℤ) ≤ 1 := by exact_mod_cast hbad
      nlinarith

end FiniteKakeyaS3
