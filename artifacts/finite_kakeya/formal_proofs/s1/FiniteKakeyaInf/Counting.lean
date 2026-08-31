import FiniteKakeyaInf.Definitions
import Mathlib.NumberTheory.JacobiSum.Basic

namespace FiniteKakeyaInf

open scoped BigOperators
open Finset

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

@[simp] theorem mem_squares (y : F) : y ∈ squares F ↔ IsSquare y := by
  simp only [squares, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, pow_two x⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, pow_two x⟩

theorem square_root_card (h2 : ringChar F ≠ 2) (y : F) :
    ((univ : Finset F).filter fun x => x ^ 2 = y).card =
      if y ∈ squares F then if y = 0 then 1 else 2 else 0 := by
  have h := quadraticChar_card_sqrts h2 y
  rw [Set.toFinset_setOf] at h
  by_cases hy0 : y = 0
  · subst y
    simpa using h
  · by_cases hys : y ∈ squares F
    · have hc : quadraticChar F y = 1 :=
        (quadraticChar_one_iff_isSquare hy0).2 ((mem_squares F y).1 hys)
      simp only [hys, hy0, if_true, if_false]
      rw [hc] at h
      norm_num at h
      exact_mod_cast h
    · have hns : ¬ IsSquare y := by simpa using hys
      have hc : quadraticChar F y = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.2 hns
      simp only [hys, if_false]
      simpa [hc] using h

/-- Root-lifting over the square map: nonzero squares have two roots and zero
has one. -/
theorem sum_square_lift (h2 : ringChar F ≠ 2) (f : F → ℤ) :
    (∑ x : F, f (x ^ 2)) = 2 * (∑ y ∈ squares F, f y) - f 0 := by
  calc
    (∑ x : F, f (x ^ 2)) =
        ∑ y : F, ∑ x ∈ (univ : Finset F) with x ^ 2 = y, f (x ^ 2) := by
          symm
          exact Finset.sum_fiberwise (univ : Finset F) (fun x : F => x ^ 2)
            (fun x => f (x ^ 2))
    _ = ∑ y : F, (((univ : Finset F).filter fun x => x ^ 2 = y).card : ℤ) * f y := by
      apply Finset.sum_congr rfl
      intro y _
      calc
        (∑ x ∈ (univ : Finset F) with x ^ 2 = y, f (x ^ 2)) =
            ∑ _x ∈ (univ : Finset F) with _x ^ 2 = y, f y := by
              apply Finset.sum_congr rfl
              intro x hx
              exact congrArg f (mem_filter.1 hx).2
        _ = ((filter (fun x : F => x ^ 2 = y) univ).card : ℤ) * f y := by simp
        _ = _ := rfl
    _ = ∑ y : F,
        (if y ∈ squares F then if y = 0 then 1 else 2 else 0 : ℤ) * f y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [square_root_card F h2 y]
      push_cast
      rfl
    _ = 2 * (∑ y ∈ squares F, f y) - f 0 := by
      classical
      simp only [ite_mul, zero_mul]
      calc
        (∑ y : F, if y ∈ squares F then (if y = 0 then 1 * f y else 2 * f y) else 0) =
            ∑ y ∈ squares F, (if y = 0 then f y else 2 * f y) := by
              symm
              have hs := Finset.sum_filter (s := (univ : Finset F))
                (fun y : F => y ∈ squares F) (fun y => if y = 0 then f y else 2 * f y)
              simpa only [filter_mem_eq_inter, univ_inter, one_mul] using hs
        _ = ∑ y ∈ squares F, (2 * f y - if y = 0 then f y else 0) := by
              apply Finset.sum_congr rfl
              intro y _
              split_ifs <;> ring
        _ = 2 * (∑ y ∈ squares F, f y) - f 0 := by
              rw [sum_sub_distrib]
              simp [squares, Finset.mul_sum]

theorem sum_square_lift₂ (h2 : ringChar F ≠ 2) (G : F → F → ℤ) :
    (∑ a : F, ∑ b : F, G (a ^ 2) (b ^ 2)) =
      4 * (∑ y ∈ squares F, ∑ z ∈ squares F, G y z) -
      2 * (∑ y ∈ squares F, G y 0) -
      2 * (∑ z ∈ squares F, G 0 z) + G 0 0 := by
  have hinner : ∀ a : F,
      (∑ b : F, G (a ^ 2) (b ^ 2)) =
        2 * (∑ z ∈ squares F, G (a ^ 2) z) - G (a ^ 2) 0 :=
    fun a => sum_square_lift F h2 (fun z => G (a ^ 2) z)
  calc
    (∑ a : F, ∑ b : F, G (a ^ 2) (b ^ 2)) =
        ∑ a : F, (2 * (∑ z ∈ squares F, G (a ^ 2) z) - G (a ^ 2) 0) := by
          apply sum_congr rfl
          intro a _
          exact hinner a
    _ = 2 * (∑ z ∈ squares F, ∑ a : F, G (a ^ 2) z) -
        ∑ a : F, G (a ^ 2) 0 := by
          rw [sum_sub_distrib, ← mul_sum]
          simp_rw [sum_comm (f := fun a z => G (a ^ 2) z)]
    _ = 2 * (∑ z ∈ squares F,
          (2 * (∑ y ∈ squares F, G y z) - G 0 z)) -
        (2 * (∑ y ∈ squares F, G y 0) - G 0 0) := by
          congr 1
          · congr 1
            apply sum_congr rfl
            intro z _
            exact sum_square_lift F h2 (fun y => G y z)
          · exact sum_square_lift F h2 (fun y => G y 0)
    _ = _ := by
      rw [sum_sub_distrib, ← mul_sum]
      simp_rw [sum_comm (f := fun z y => G y z)]
      ring

theorem card_squares (h2 : ringChar F ≠ 2) :
    (squares F).card = (Fintype.card F + 1) / 2 := by
  have hlift := sum_square_lift F h2 (fun _ => (1 : ℤ))
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at hlift
  have hodd := FiniteField.odd_card_of_char_ne_two h2
  omega

private def bodyParam (r : F × F × F) : Point F :=
  (r.1, (r.2.1 - r.1 ^ 2) / 4, (r.2.2 - r.1 ^ 2) / 4)

theorem card_body (h2 : ringChar F ≠ 2) :
    (body F).card = Fintype.card F * (squares F).card ^ 2 := by
  have hfour : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero (Ring.two_ne_zero h2) (Ring.two_ne_zero h2)
  let domain : Finset (F × F × F) := univ ×ˢ (squares F ×ˢ squares F)
  have himage : domain.image (bodyParam F) = body F := by
    ext q
    simp only [domain, mem_image, mem_product, mem_univ, true_and, body,
      mem_filter, bodyParam]
    constructor
    · rintro ⟨r, ⟨hr₁, hr₂⟩, rfl⟩
      constructor
      · convert hr₁ using 1
        field_simp
        ring
      · convert hr₂ using 1
        field_simp
        ring
    · rintro ⟨hy, hz⟩
      refine ⟨(q.1, q.1 ^ 2 + 4 * q.2.1, q.1 ^ 2 + 4 * q.2.2),
        ⟨hy, hz⟩, ?_⟩
      apply Prod.ext
      · rfl
      · apply Prod.ext <;> dsimp [bodyParam] <;> field_simp <;> ring
  have hinj : Function.Injective (bodyParam F) := by
    rintro ⟨x, y, z⟩ ⟨x', y', z'⟩ h
    have hx : x = x' := congrArg Prod.fst h
    subst x'
    have hy : (y - x ^ 2) / 4 = (y' - x ^ 2) / 4 := congrArg (fun q => q.2.1) h
    have hz : (z - x ^ 2) / 4 = (z' - x ^ 2) / 4 := congrArg (fun q => q.2.2) h
    have hye : y = y' := by
      field_simp at hy
      exact sub_left_inj.mp hy
    have hze : z = z' := by
      field_simp at hz
      exact sub_left_inj.mp hz
    simp [hye, hze]
  rw [← himage, card_image_of_injective domain hinj]
  simp [domain, card_product]
  ring

/-- Discriminant selecting the finite one-pole lines in the boundary plane. -/
def delta (y z : F) : F := (1 - y - z) ^ 2 - 4 * y * z

theorem two_ne_zero_of_ringChar (hchar : ringChar F ≠ 2) : (2 : F) ≠ 0 := by
  intro h2
  apply hchar
  exact CharP.ringChar_of_prime_eq_zero Nat.prime_two h2

theorem finite_or_vertical_iff (h2 : (2 : F) ≠ 0) (q : Point F) :
    q ∈ finiteBoundary F ∪ verticalBoundary F ↔
      q.1 = 0 ∧ IsSquare (delta F q.2.1 q.2.2) := by
  classical
  simp only [mem_union, finiteBoundary, verticalBoundary, mem_filter, mem_univ, true_and]
  constructor
  · rintro (⟨hx, c, hc, hz⟩ | ⟨hx, hy⟩)
    · refine ⟨hx, ?_⟩
      let r : F := 2 * q.2.1 * c + (1 - q.2.1 - q.2.2)
      have hpoly : q.2.1 * c ^ 2 + (1 - q.2.1 - q.2.2) * c + q.2.2 = 0 := by
        field_simp [sub_ne_zero.mpr hc] at hz
        linear_combination -hz
      refine ⟨r, ?_⟩
      dsimp [r, delta]
      symm
      calc
        (2 * q.2.1 * c + (1 - q.2.1 - q.2.2)) *
            (2 * q.2.1 * c + (1 - q.2.1 - q.2.2)) =
            delta F q.2.1 q.2.2 + 4 * q.2.1 *
              (q.2.1 * c ^ 2 + (1 - q.2.1 - q.2.2) * c + q.2.2) := by
                dsimp [delta]
                ring
        _ = delta F q.2.1 q.2.2 := by rw [hpoly]; ring
    · refine ⟨hx, 1 - q.2.2, ?_⟩
      dsimp [delta]
      rw [hy]
      ring
  · rintro ⟨hx, hs⟩
    by_cases hy : q.2.1 = 0
    · exact Or.inr ⟨hx, hy⟩
    · left
      rcases hs with ⟨r, hr⟩
      let c : F := (q.2.1 + q.2.2 - 1 + r) / (2 * q.2.1)
      have hden : (2 : F) * q.2.1 ≠ 0 := mul_ne_zero h2 hy
      have hpoly : q.2.1 * c ^ 2 + (1 - q.2.1 - q.2.2) * c + q.2.2 = 0 := by
        dsimp [delta] at hr
        dsimp [c]
        field_simp [hden]
        linear_combination -hr
      have hc : c ≠ 1 := by
        intro hc
        have hone : (1 : F) = 0 := by
          calc
            1 = q.2.1 * (1 : F) ^ 2 + (1 - q.2.1 - q.2.2) * 1 + q.2.2 := by ring
            _ = 0 := by simpa [hc] using hpoly
        exact one_ne_zero hone
      refine ⟨hx, c, hc, ?_⟩
      field_simp [sub_ne_zero.mpr hc]
      linear_combination -hpoly

/-- The standard character identity used in the exact selector count. -/
theorem sum_quadratic_one_sub_square (h2 : (2 : F) ≠ 0) :
    (∑ u : F, quadraticChar F (1 - u ^ 2)) = -quadraticChar F (-1) := by
  have hchar : ringChar F ≠ 2 := by
    intro h
    apply h2
    have hr := @ringChar.Nat.cast_ringChar F _
    norm_num [h] at hr ⊢
    exact hr
  let e : F → F := fun x => 1 - 2 * x
  have he : Function.Bijective e := by
    constructor
    · intro x y hxy
      dsimp [e] at hxy
      exact (mul_left_cancel₀ h2) (sub_right_inj.mp hxy)
    · intro u
      refine ⟨(1 - u) / 2, ?_⟩
      dsimp [e]
      field_simp
      ring
  calc
    _ = ∑ x : F, quadraticChar F x * quadraticChar F (1 - x) := by
      symm
      apply Fintype.sum_equiv (Equiv.ofBijective e he)
      intro x
      dsimp [e]
      have hfour : quadraticChar F (4 : F) = 1 := by
        rw [show (4 : F) = (2 : F) ^ 2 by norm_num]
        exact quadraticChar_sq_one' h2
      rw [show 1 - (1 - 2 * x) ^ 2 = 4 * (x * (1 - x)) by ring]
      symm
      rw [quadraticCharFun_mul, show quadraticCharFun F 4 = 1 from hfour,
        one_mul, quadraticCharFun_mul]
    _ = jacobiSum (quadraticChar F) (quadraticChar F) := rfl
    _ = jacobiSum (quadraticChar F) (quadraticChar F)⁻¹ := by
      rw [(quadraticChar_isQuadratic F).inv]
    _ = _ := jacobiSum_nontrivial_inv (quadraticChar_ne_one hchar)

theorem sum_quadratic_one_sub_four_square (hchar : ringChar F ≠ 2) :
    (∑ a : F, quadraticChar F (1 - 4 * a ^ 2)) = -quadraticChar F (-1) := by
  have h2 := two_ne_zero_of_ringChar F hchar
  let e : F → F := fun a => 2 * a
  have he : Function.Bijective e := by
    constructor
    · intro a b hab
      exact mul_left_cancel₀ h2 hab
    · intro u
      refine ⟨u / 2, ?_⟩
      dsimp [e]
      exact mul_div_cancel₀ u h2
  calc
    _ = ∑ u : F, quadraticChar F (1 - u ^ 2) := by
      apply Fintype.sum_equiv (Equiv.ofBijective e he)
      intro a
      dsimp [e]
      congr 2
      ring
    _ = _ := sum_quadratic_one_sub_square F h2

theorem diagonal_character_sum (hchar : ringChar F ≠ 2) :
    2 * (∑ y ∈ squares F, quadraticChar F (1 - 4 * y)) =
      1 - quadraticChar F (-1) := by
  have hlift := sum_square_lift F hchar (fun y => quadraticChar F (1 - 4 * y))
  rw [sum_quadratic_one_sub_four_square F hchar] at hlift
  norm_num at hlift ⊢
  linarith

def diagonalBad : Finset F :=
  (squares F).filter fun y => quadraticChar F (1 - 4 * y) = -1

theorem diagonal_bad_indicator (hchar : ringChar F ≠ 2) (y : F) :
    2 * (if quadraticChar F (1 - 4 * y) = -1 then 1 else 0 : ℤ) =
      1 - quadraticChar F (1 - 4 * y) - (if 1 - 4 * y = 0 then 1 else 0) := by
  by_cases hz : 1 - 4 * y = 0
  · simp [hz]
  · rcases quadraticChar_dichotomy (F := F) hz with h | h <;> simp [hz, h]

theorem diagonal_zero_filter (hchar : ringChar F ≠ 2) :
    ((squares F).filter fun y => 1 - 4 * y = 0).card = 1 := by
  have h2 := two_ne_zero_of_ringChar F hchar
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  have heq : (squares F).filter (fun y => 1 - 4 * y = 0) = {(1 : F) / 4} := by
    ext y
    simp only [mem_filter, mem_squares, mem_singleton]
    constructor
    · rintro ⟨_, hy⟩
      apply (eq_div_iff h4).2
      calc
        y * 4 = 4 * y := mul_comm _ _
        _ = 1 := (sub_eq_zero.mp hy).symm
    · intro hy
      subst y
      constructor
      · refine ⟨(1 : F) / 2, ?_⟩
        field_simp
        norm_num
      · field_simp
        ring
  rw [heq, card_singleton]

theorem four_mul_card_diagonalBad (hchar : ringChar F ≠ 2) :
    4 * ((diagonalBad F).card : ℤ) =
      Fintype.card F - 2 + quadraticChar F (-1) := by
  have hind := Finset.sum_congr rfl fun y (_ : y ∈ squares F) =>
    diagonal_bad_indicator F hchar y
  have hsum := diagonal_character_sum F hchar
  have hsquare := sum_square_lift F hchar (fun _ => (1 : ℤ))
  have hzero := diagonal_zero_filter F hchar
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hind
  have hbad :
      (∑ y ∈ squares F,
        if quadraticChar F (1 - 4 * y) = -1 then (1 : ℤ) else 0) =
        (diagonalBad F).card := by
    rw [← Finset.sum_filter]
    simp [diagonalBad]
  have hzsum :
      (∑ y ∈ squares F, if 1 - 4 * y = 0 then (1 : ℤ) else 0) = 1 := by
    rw [← Finset.sum_filter]
    simpa using congrArg (fun n : ℕ => (n : ℤ)) hzero
  conv_lhs at hind => rw [← Finset.mul_sum]
  rw [hbad, hzsum] at hind
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at hsquare
  omega

theorem delta_square_square (a b : F) :
    delta F (a ^ 2) (b ^ 2) =
      (1 - (a + b) ^ 2) * (1 - (a - b) ^ 2) := by
  simp only [delta]
  ring

theorem delta_root_lift_character_sum (hchar : ringChar F ≠ 2) :
    (∑ a : F, ∑ b : F, quadraticChar F (delta F (a ^ 2) (b ^ 2))) = 1 := by
  have h2 := two_ne_zero_of_ringChar F hchar
  let e : F × F → F × F := fun ab => (ab.1 + ab.2, ab.1 - ab.2)
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨a, b⟩ ⟨c, d⟩ h
      simp only [e, Prod.mk.injEq] at h
      ext
      · apply mul_left_cancel₀ h2
        linear_combination h.1 + h.2
      · apply mul_left_cancel₀ h2
        linear_combination h.1 - h.2
    · rintro ⟨u, v⟩
      refine ⟨((u + v) / 2, (u - v) / 2), ?_⟩
      simp only [e, Prod.mk.injEq]
      constructor <;> field_simp <;> ring
  calc
    _ = ∑ ab : F × F, quadraticChar F (delta F (ab.1 ^ 2) (ab.2 ^ 2)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ uv : F × F,
        quadraticChar F (1 - uv.1 ^ 2) * quadraticChar F (1 - uv.2 ^ 2) := by
      apply Fintype.sum_equiv (Equiv.ofBijective e he)
      rintro ⟨a, b⟩
      dsimp [e]
      rw [delta_square_square, quadraticCharFun_mul]
    _ = (∑ u : F, quadraticChar F (1 - u ^ 2)) *
        (∑ v : F, quadraticChar F (1 - v ^ 2)) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    _ = 1 := by
      rw [sum_quadratic_one_sub_square F h2]
      have hm1 : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
      have hs := quadraticChar_sq_one (F := F) hm1
      nlinarith

theorem delta_axis_character_sum :
    (∑ z ∈ squares F, quadraticChar F (delta F 0 z)) = (squares F).card - 1 := by
  have h1 : (1 : F) ∈ squares F := by simp
  calc
    _ = (∑ z ∈ squares F \ {1}, quadraticChar F (delta F 0 z)) +
        ∑ z ∈ ({1} : Finset F), quadraticChar F (delta F 0 z) := by
      exact (sum_sdiff (f := fun z => quadraticChar F (delta F 0 z))
        (singleton_subset_iff.2 h1)).symm
    _ = ∑ _z ∈ squares F \ {1}, (1 : ℤ) := by
      rw [show (∑ z ∈ squares F \ {1}, quadraticChar F (delta F 0 z)) =
          ∑ _z ∈ squares F \ {1}, (1 : ℤ) by
        apply Finset.sum_congr rfl
        intro z hz
        rw [show delta F 0 z = (1 - z) ^ 2 by simp [delta]]
        rw [quadraticChar_sq_one']
        exact sub_ne_zero.mpr (Ne.symm (by simpa using (mem_sdiff.1 hz).2))]
      simp [delta]
    _ = (squares F).card - 1 := by
      rw [sum_const, nsmul_eq_mul, mul_one]
      have hc : (squares F \ {1}).card = (squares F).card - 1 := by
        rw [card_sdiff]
        simp [h1]
      have hle : 1 ≤ (squares F).card := card_pos.mpr ⟨1, h1⟩
      rw [hc, Int.natCast_sub hle]
      norm_num

theorem delta_axis_character_sum_right :
    (∑ y ∈ squares F, quadraticChar F (delta F y 0)) = (squares F).card - 1 := by
  simpa [delta] using delta_axis_character_sum F

theorem two_mul_delta_square_grid_character_sum (hchar : ringChar F ≠ 2) :
    2 * (∑ y ∈ squares F, ∑ z ∈ squares F, quadraticChar F (delta F y z)) =
      Fintype.card F - 1 := by
  have hlift := sum_square_lift₂ F hchar (fun y z => quadraticChar F (delta F y z))
  rw [delta_root_lift_character_sum F hchar, delta_axis_character_sum F,
    delta_axis_character_sum_right F] at hlift
  have h00 : quadraticChar F (delta F 0 0) = 1 := by simp [delta]
  rw [h00] at hlift
  have hsquare := sum_square_lift F hchar (fun _ => (1 : ℤ))
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at hsquare
  omega

def deltaZeroGrid : Finset (F × F) :=
  (squares F ×ˢ squares F).filter fun yz => delta F yz.1 yz.2 = 0

private def pmOne : Finset F := {1, -1}

private theorem card_pmOne (hchar : ringChar F ≠ 2) : (pmOne F).card = 2 := by
  have hne : (1 : F) ≠ -1 := by
    exact Ne.symm (Ring.neg_one_ne_one_of_char_ne_two hchar)
  simp [pmOne, hne]

private theorem one_sub_square_eq_zero_iff_mem_pmOne (u : F) :
    1 - u ^ 2 = 0 ↔ u ∈ pmOne F := by
  rw [sub_eq_zero, eq_comm, sq_eq_one_iff]
  simp [pmOne, eq_comm]

theorem delta_root_lift_zero_sum (hchar : ringChar F ≠ 2) :
    (∑ a : F, ∑ b : F, if delta F (a ^ 2) (b ^ 2) = 0 then (1 : ℤ) else 0) =
      4 * Fintype.card F - 4 := by
  have h2 := two_ne_zero_of_ringChar F hchar
  let e : F × F → F × F := fun ab => (ab.1 + ab.2, ab.1 - ab.2)
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨a, b⟩ ⟨c, d⟩ h
      simp only [e, Prod.mk.injEq] at h
      ext
      · apply mul_left_cancel₀ h2
        linear_combination h.1 + h.2
      · apply mul_left_cancel₀ h2
        linear_combination h.1 - h.2
    · rintro ⟨u, v⟩
      refine ⟨((u + v) / 2, (u - v) / 2), ?_⟩
      simp only [e, Prod.mk.injEq]
      constructor <;> field_simp <;> ring
  calc
    _ = ∑ ab : F × F,
        if delta F (ab.1 ^ 2) (ab.2 ^ 2) = 0 then (1 : ℤ) else 0 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ uv : F × F,
        if (1 - uv.1 ^ 2) * (1 - uv.2 ^ 2) = 0 then (1 : ℤ) else 0 := by
      apply Fintype.sum_equiv (Equiv.ofBijective e he)
      rintro ⟨a, b⟩
      dsimp [e]
      rw [delta_square_square]
    _ = (((pmOne F ×ˢ (univ : Finset F)) ∪
          ((univ : Finset F) ×ˢ pmOne F)).card : ℤ) := by
      rw [show (∑ uv : F × F,
          if (1 - uv.1 ^ 2) * (1 - uv.2 ^ 2) = 0 then (1 : ℤ) else 0) =
          ∑ uv ∈ ((univ : Finset F) ×ˢ (univ : Finset F)),
            if uv.1 ∈ pmOne F ∨ uv.2 ∈ pmOne F then (1 : ℤ) else 0 by
        rw [univ_product_univ]
        apply Finset.sum_congr rfl
        intro uv _
        simp only [mul_eq_zero, one_sub_square_eq_zero_iff_mem_pmOne]]
      rw [← Finset.sum_filter]
      simp only [sum_const, nsmul_eq_mul, mul_one]
      norm_cast
      apply congrArg Finset.card
      ext uv
      simp [or_comm]
    _ = 4 * Fintype.card F - 4 := by
      have hinter :
          (pmOne F ×ˢ (univ : Finset F)) ∩ ((univ : Finset F) ×ˢ pmOne F) =
            pmOne F ×ˢ pmOne F := by
        ext uv
        simp
      rw [Finset.card_union]
      rw [hinter]
      simp [card_pmOne F hchar, Finset.card_product]
      rw [Nat.cast_sub (by have := Fintype.card_pos (α := F); omega)]
      push_cast
      ring

theorem card_deltaZeroGrid (hchar : ringChar F ≠ 2) :
    (deltaZeroGrid F).card = Fintype.card F := by
  let Z : F → F → ℤ := fun y z => if delta F y z = 0 then 1 else 0
  have hlift := sum_square_lift₂ F hchar Z
  have hfull := delta_root_lift_zero_sum F hchar
  have haxisL : (∑ z ∈ squares F, Z 0 z) = 1 := by
    have heq : (squares F).filter (fun z => delta F 0 z = 0) = {1} := by
      ext z
      simp only [mem_filter, mem_squares, mem_singleton]
      constructor
      · rintro ⟨_, hz⟩
        have : (1 - z) ^ 2 = 0 := by simpa [delta] using hz
        exact (sub_eq_zero.mp (sq_eq_zero_iff.mp this)).symm
      · intro hz
        subst z
        simp [delta]
    rw [show (∑ z ∈ squares F, Z 0 z) =
        (((squares F).filter fun z => delta F 0 z = 0).card : ℤ) by
      dsimp [Z]
      rw [card_filter]
      push_cast
      rfl, heq]
    simp
  have haxisR : (∑ y ∈ squares F, Z y 0) = 1 := by
    simpa [Z, delta] using haxisL
  have h00 : Z 0 0 = 0 := by simp [Z, delta]
  have hgrid : (∑ y ∈ squares F, ∑ z ∈ squares F, Z y z) =
      ((deltaZeroGrid F).card : ℤ) := by
    calc
      _ = ∑ yz ∈ squares F ×ˢ squares F, Z yz.1 yz.2 := by
        rw [Finset.sum_product]
      _ = ((deltaZeroGrid F).card : ℤ) := by
        dsimp [Z, deltaZeroGrid]
        rw [card_filter]
        push_cast
        rfl
  rw [hfull, haxisL, haxisR, h00, hgrid] at hlift
  exact_mod_cast (by omega : ((deltaZeroGrid F).card : ℤ) = Fintype.card F)

theorem square_indicator (a : F) :
    2 * (if IsSquare a then 1 else 0 : ℤ) =
      1 + quadraticChar F a + (if a = 0 then 1 else 0) := by
  by_cases ha : a = 0
  · subst a
    simp
  · by_cases hs : IsSquare a
    · rw [(quadraticChar_one_iff_isSquare ha).2 hs]
      simp [ha, hs]
    · rw [quadraticChar_neg_one_iff_not_isSquare.2 hs]
      simp [ha, hs]

def selectorSquareGrid : Finset (F × F) :=
  (squares F ×ˢ squares F).filter fun yz => IsSquare (delta F yz.1 yz.2)

theorem eight_mul_card_selectorSquareGrid (hchar : ringChar F ≠ 2) :
    8 * ((selectorSquareGrid F).card : ℤ) =
      (Fintype.card F : ℤ) ^ 2 + 8 * Fintype.card F - 1 := by
  let D := squares F ×ˢ squares F
  have hind := Finset.sum_congr rfl fun yz (_ : yz ∈ D) =>
    square_indicator F (delta F yz.1 yz.2)
  have hselector :
      (∑ yz ∈ D, if IsSquare (delta F yz.1 yz.2) then (1 : ℤ) else 0) =
        (selectorSquareGrid F).card := by
    rw [← Finset.sum_filter]
    simp [selectorSquareGrid, D]
  have hcharSum :
      (∑ yz ∈ D, quadraticChar F (delta F yz.1 yz.2)) =
        ∑ y ∈ squares F, ∑ z ∈ squares F, quadraticChar F (delta F y z) := by
    rw [Finset.sum_product]
  have hzeroSum :
      (∑ yz ∈ D, if delta F yz.1 yz.2 = 0 then (1 : ℤ) else 0) =
        (deltaZeroGrid F).card := by
    rw [← Finset.sum_filter]
    simp [deltaZeroGrid, D]
  conv_lhs at hind => rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hind
  rw [hselector, hcharSum, hzeroSum] at hind
  have hchars := two_mul_delta_square_grid_character_sum F hchar
  have hzero := card_deltaZeroGrid F hchar
  have hsquare := sum_square_lift F hchar (fun _ => (1 : ℤ))
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at hsquare
  have hD : (D.card : ℤ) = (squares F).card ^ 2 := by
    simp [D, card_product]
    ring
  rw [hD, hzero] at hind
  nlinarith

private def rootPairs (a : F) := {rx : F × F // rx.1 ^ 2 = rx.2 ^ 2 - a}

private def productPairs (a : F) := {uv : F × F // uv.1 * uv.2 = -a}

private def rootPairsEquivProductPairs (h2 : (2 : F) ≠ 0) (a : F) :
    rootPairs F a ≃ productPairs F a where
  toFun rx := ⟨(rx.1.1 - rx.1.2, rx.1.1 + rx.1.2), by
    change (rx.1.1 - rx.1.2) * (rx.1.1 + rx.1.2) = -a
    calc
      _ = rx.1.1 ^ 2 - rx.1.2 ^ 2 := by ring
      _ = -a := by rw [rx.2]; ring⟩
  invFun uv := ⟨((uv.1.1 + uv.1.2) / 2, (uv.1.2 - uv.1.1) / 2), by
    change ((uv.1.1 + uv.1.2) / 2) ^ 2 = ((uv.1.2 - uv.1.1) / 2) ^ 2 - a
    field_simp
    have hp := uv.2
    linear_combination 4 * hp⟩
  left_inv rx := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> field_simp <;> ring
  right_inv uv := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> field_simp <;> ring

private def productPairsEquivNonzero (ha : a ≠ 0) :
    productPairs F a ≃ {u : F // u ≠ 0} where
  toFun uv := ⟨uv.1.1, by
    intro hu
    have hp := uv.2
    rw [hu, zero_mul] at hp
    exact ha (neg_eq_zero.mp hp.symm)⟩
  invFun u := ⟨(u.1, -a / u.1), by
    change u.1 * (-a / u.1) = -a
    rw [mul_comm]
    exact div_mul_cancel₀ (-a) u.2⟩
  left_inv uv := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp
      have huv : uv.1.1 ≠ 0 := by
        intro hu
        have hp := uv.2
        rw [hu, zero_mul] at hp
        exact ha (neg_eq_zero.mp hp.symm)
      apply (div_eq_iff huv).2
      simpa [mul_comm] using uv.2.symm
  right_inv u := rfl

private def sigmaRootsEquivRootPairs (a : F) :
    (Σ x : F, {r : F // r ^ 2 = x ^ 2 - a}) ≃ rootPairs F a where
  toFun xr := ⟨(xr.2.1, xr.1), xr.2.2⟩
  invFun rx := ⟨rx.1.2, ⟨rx.1.1, rx.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def rootFiberEquivFinset (a x : F) :
    {r : F // r ^ 2 = x ^ 2 - a} ≃
      ↥((univ : Finset F).filter fun r => r ^ 2 = x ^ 2 - a) where
  toFun r := ⟨r.1, by simp [r.2]⟩
  invFun r := ⟨r.1, (mem_filter.1 r.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A monic quadratic with nonzero constant shift has character sum `-1`. -/
theorem sum_quadratic_square_sub (hchar : ringChar F ≠ 2) (a : F) (ha : a ≠ 0) :
    (∑ x : F, quadraticChar F (x ^ 2 - a)) = -1 := by
  classical
  have h2 := two_ne_zero_of_ringChar F hchar
  have hnonzero : Fintype.card {u : F // u ≠ 0} = Fintype.card F - 1 := by
    simpa using Fintype.card_subtype_compl (fun u : F => u = 0)
  letI : Fintype (productPairs F a) :=
    Fintype.ofEquiv {u : F // u ≠ 0} (productPairsEquivNonzero F ha).symm
  letI : Fintype (rootPairs F a) :=
    Fintype.ofEquiv (productPairs F a) (rootPairsEquivProductPairs F h2 a).symm
  letI (x : F) : Fintype {r : F // r ^ 2 = x ^ 2 - a} :=
    Fintype.ofEquiv ↥((univ : Finset F).filter fun r => r ^ 2 = x ^ 2 - a)
      (rootFiberEquivFinset F a x).symm
  have hpairs : Fintype.card (rootPairs F a) = Fintype.card F - 1 := by
    calc
      _ = Fintype.card (productPairs F a) := Fintype.card_congr (rootPairsEquivProductPairs F h2 a)
      _ = Fintype.card {u : F // u ≠ 0} := Fintype.card_congr (productPairsEquivNonzero F ha)
      _ = _ := hnonzero
  have hsigma :
      Fintype.card (rootPairs F a) =
        ∑ x : F, Fintype.card {r : F // r ^ 2 = x ^ 2 - a} := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (sigmaRootsEquivRootPairs F a).symm
  have hroot (x : F) :
      (Fintype.card {r : F // r ^ 2 = x ^ 2 - a} : ℤ) =
        quadraticChar F (x ^ 2 - a) + 1 := by
    rw [Fintype.card_congr (rootFiberEquivFinset F a x), Fintype.card_coe]
    simpa [Set.toFinset_setOf] using quadraticChar_card_sqrts hchar (x ^ 2 - a)
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) hsigma
  change (Fintype.card (rootPairs F a) : ℤ) =
    ((∑ x : F, Fintype.card {r : F // r ^ 2 = x ^ 2 - a}) : ℕ) at hcast
  rw [Nat.cast_sum] at hcast
  simp_rw [hroot] at hcast
  rw [hpairs] at hcast
  have hpos := Fintype.card_pos (α := F)
  rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card F)] at hcast
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one] at hcast
  omega

theorem delta_full_character_sum (hchar : ringChar F ≠ 2) :
    (∑ y : F, ∑ z : F, quadraticChar F (delta F y z)) = 0 := by
  have h2 := two_ne_zero_of_ringChar F hchar
  have hrow (y : F) :
      (∑ z : F, quadraticChar F (delta F y z)) =
        if y = 0 then (Fintype.card F : ℤ) - 1 else (-1 : ℤ) := by
    by_cases hy : y = 0
    · subst y
      simp only [if_true]
      calc
        (∑ z : F, quadraticChar F (delta F 0 z)) =
            ∑ z : F, if z = 1 then 0 else (1 : ℤ) := by
          apply sum_congr rfl
          intro z _
          by_cases hz : z = 1
          · subst z
            simp [delta]
          · rw [show delta F 0 z = (1 - z) ^ 2 by simp [delta],
              quadraticChar_sq_one' (sub_ne_zero.mpr (Ne.symm hz))]
            simp [hz]
        _ = Fintype.card F - 1 := by
          have hc : ((univ : Finset F).filter fun z => z ≠ 1).card =
              Fintype.card F - 1 := by
            have heq : ((univ : Finset F).filter fun z => z ≠ 1) = univ.erase 1 := by
              ext z
              simp [and_comm]
            rw [heq, card_erase_of_mem (mem_univ 1), card_univ]
          calc
            _ = (((univ : Finset F).filter fun z => z ≠ 1).card : ℤ) := by
              rw [card_filter]
              push_cast
              apply sum_congr rfl
              intro z _
              by_cases hz : z = 1 <;> simp [hz]
            _ = _ := by
              rw [hc, Nat.cast_sub (by
                have hp := Fintype.card_pos (α := F)
                omega)]
              norm_num
    · simp only [hy, if_false]
      let e : F → F := fun w => w + (1 + y)
      have he : Function.Bijective e := by
        constructor
        · intro a b h
          exact add_right_cancel h
        · intro z
          exact ⟨z - (1 + y), by simp [e]⟩
      calc
        _ = ∑ w : F, quadraticChar F (delta F y (e w)) := by
          exact (Equiv.sum_comp (Equiv.ofBijective e he)
            (fun z => quadraticChar F (delta F y z))).symm
        _ = ∑ w : F, quadraticChar F (w ^ 2 - 4 * y) := by
          apply sum_congr rfl
          intro w _
          rw [show delta F y (e w) = w ^ 2 - 4 * y by
            dsimp [e, delta]
            ring]
        _ = -1 := sum_quadratic_square_sub F hchar (4 * y)
          (mul_ne_zero (by
            rw [show (4 : F) = 2 * 2 by norm_num]
            exact mul_ne_zero h2 h2) hy)
  calc
    _ = ∑ y : F, if y = 0 then (Fintype.card F - 1 : ℤ) else -1 := by
      apply sum_congr rfl
      intro y _
      exact hrow y
    _ = 0 := by
      rw [show (∑ y : F, if y = 0 then (Fintype.card F - 1 : ℤ) else -1) =
          (Fintype.card F - 1) + (Fintype.card F - 1) * (-1 : ℤ) by
        rw [Finset.sum_ite]
        have hp := Fintype.card_pos (α := F)
        have hz : ((univ : Finset F).filter fun y => y = 0).card = 1 := by
          have heq : ((univ : Finset F).filter fun y => y = 0) = {0} := by ext; simp
          rw [heq, card_singleton]
        have hn : ((univ : Finset F).filter fun y => ¬y = 0).card =
            Fintype.card F - 1 := by
          have hparts := filter_card_add_filter_neg_card_eq_card
            (s := (univ : Finset F)) (fun y => y = 0)
          rw [hz, card_univ] at hparts
          omega
        simp only [sum_const, nsmul_eq_mul]
        rw [hz, hn, Nat.cast_sub (by omega : 1 ≤ Fintype.card F)]
        push_cast
        ring]
      ring

def deltaZeroFull : Finset (F × F) :=
  univ.filter fun yz => delta F yz.1 yz.2 = 0

theorem card_deltaZeroFull (hchar : ringChar F ≠ 2) :
    (deltaZeroFull F).card = Fintype.card F := by
  have h2 := two_ne_zero_of_ringChar F hchar
  have hrow (y : F) :
      (((univ : Finset F).filter fun z => delta F y z = 0).card : ℤ) =
        quadraticChar F y + 1 := by
    let e : F → F := fun w => w + (1 + y)
    have he : Function.Bijective e := by
      constructor
      · intro a b h
        exact add_right_cancel h
      · intro z
        exact ⟨z - (1 + y), by simp [e]⟩
    have hcard' : (univ.filter fun w : F => w ^ 2 = 4 * y).card =
        (univ.filter fun z : F => delta F y z = 0).card := by
      apply Finset.card_bij (fun w _ => e w)
      · intro w hw
        simp only [mem_filter, mem_univ, true_and] at hw ⊢
        dsimp [e, delta]
        linear_combination hw
      · intro a _ b _ hab
        exact he.1 hab
      · intro z hz
        rcases he.2 z with ⟨w, rfl⟩
        refine ⟨w, ?_, rfl⟩
        simp only [mem_filter, mem_univ, true_and] at hz ⊢
        dsimp [e, delta] at hz
        linear_combination hz
    have hcard := hcard'.symm
    rw [hcard]
    have hr := quadraticChar_card_sqrts hchar (4 * y)
    rw [Set.toFinset_setOf] at hr
    have hfourchar : quadraticChar F (4 : F) = 1 := by
      rw [show (4 : F) = (2 : F) ^ 2 by norm_num]
      exact quadraticChar_sq_one' h2
    calc
      _ = quadraticChar F (4 * y) + 1 := hr
      _ = quadraticChar F 4 * quadraticChar F y + 1 := by
        exact congrArg (fun n : ℤ => n + 1) (quadraticCharFun_mul (F := F) 4 y)
      _ = quadraticChar F y + 1 := by rw [hfourchar]; ring
  have hsum : ((deltaZeroFull F).card : ℤ) =
      ∑ y : F, (((univ : Finset F).filter fun z => delta F y z = 0).card : ℤ) := by
    calc
      _ = ∑ yz : F × F, if delta F yz.1 yz.2 = 0 then (1 : ℤ) else 0 := by
        rw [deltaZeroFull, card_filter]
        push_cast
        rfl
      _ = ∑ y : F, ∑ z : F, if delta F y z = 0 then (1 : ℤ) else 0 := by
        rw [Fintype.sum_prod_type]
      _ = _ := by
        apply sum_congr rfl
        intro y _
        rw [card_filter]
        push_cast
        rfl
  simp_rw [hrow] at hsum
  have hq := quadraticChar_sum_zero (F := F) hchar
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one] at hsum
  rw [hq, zero_add] at hsum
  exact_mod_cast hsum

def selectorFull : Finset (F × F) :=
  univ.filter fun yz => IsSquare (delta F yz.1 yz.2)

theorem two_mul_card_selectorFull (hchar : ringChar F ≠ 2) :
    2 * ((selectorFull F).card : ℤ) =
      (Fintype.card F : ℤ) ^ 2 + Fintype.card F := by
  have hind := Finset.sum_congr rfl fun yz (_ : yz ∈ (univ : Finset (F × F))) =>
    square_indicator F (delta F yz.1 yz.2)
  have hselector :
      (∑ yz : F × F, if IsSquare (delta F yz.1 yz.2) then (1 : ℤ) else 0) =
        (selectorFull F).card := by
    rw [← Finset.sum_filter]
    simp [selectorFull]
  have hcharSum :
      (∑ yz : F × F, quadraticChar F (delta F yz.1 yz.2)) = 0 := by
    rw [Fintype.sum_prod_type]
    exact delta_full_character_sum F hchar
  have hzeroSum :
      (∑ yz : F × F, if delta F yz.1 yz.2 = 0 then (1 : ℤ) else 0) =
        (deltaZeroFull F).card := by
    rw [← Finset.sum_filter]
    simp [deltaZeroFull]
  conv_lhs at hind => rw [← Finset.mul_sum]
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one] at hind
  rw [hselector, hcharSum, hzeroSum, card_deltaZeroFull F hchar] at hind
  norm_num at hind
  simpa [Fintype.card_prod, pow_two] using hind

def diagonalBadFull : Finset F :=
  univ.filter fun y => quadraticChar F (1 - 4 * y) = -1

theorem two_mul_card_diagonalBadFull (hchar : ringChar F ≠ 2) :
    2 * ((diagonalBadFull F).card : ℤ) = Fintype.card F - 1 := by
  have hind := Finset.sum_congr rfl fun y (_ : y ∈ (univ : Finset F)) =>
    diagonal_bad_indicator F hchar y
  have hbad :
      (∑ y : F, if quadraticChar F (1 - 4 * y) = -1 then (1 : ℤ) else 0) =
        (diagonalBadFull F).card := by
    rw [← Finset.sum_filter]
    simp [diagonalBadFull]
  have hcharSum : (∑ y : F, quadraticChar F (1 - 4 * y)) = 0 := by
    have h4 : (4 : F) ≠ 0 := by
      rw [show (4 : F) = 2 * 2 by norm_num]
      exact mul_ne_zero (two_ne_zero_of_ringChar F hchar) (two_ne_zero_of_ringChar F hchar)
    let e : F → F := fun y => 1 - 4 * y
    have he : Function.Bijective e := by
      constructor
      · intro y z h
        dsimp [e] at h
        exact (mul_left_cancel₀ h4) (sub_right_inj.mp h)
      · intro u
        refine ⟨(1 - u) / 4, ?_⟩
        dsimp [e]
        field_simp
        ring
    exact (Equiv.sum_comp (Equiv.ofBijective e he) (quadraticChar F)).trans
      (quadraticChar_sum_zero hchar)
  have hzero :
      (∑ y : F, if 1 - 4 * y = 0 then (1 : ℤ) else 0) = 1 := by
    have h4 : (4 : F) ≠ 0 := by
      rw [show (4 : F) = 2 * 2 by norm_num]
      exact mul_ne_zero (two_ne_zero_of_ringChar F hchar) (two_ne_zero_of_ringChar F hchar)
    have heq : ((univ : Finset F).filter fun y => 1 - 4 * y = 0) = {1 / 4} := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_singleton]
      exact ⟨fun hy => (eq_div_iff h4).2 (by
        rw [mul_comm]
        exact (sub_eq_zero.mp hy).symm), fun hy => by subst y; field_simp; ring⟩
    rw [show (∑ y : F, if 1 - 4 * y = 0 then (1 : ℤ) else 0) =
        (((univ : Finset F).filter fun y => 1 - 4 * y = 0).card : ℤ) by
      rw [card_filter]
      push_cast
      rfl, heq]
    simp
  conv_lhs at hind => rw [← Finset.mul_sum]
  simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one] at hind
  rw [hbad, hcharSum, hzero] at hind
  omega

def boundaryPairs : Finset (F × F) :=
  univ.filter fun yz => IsSquare (delta F yz.1 yz.2) ∨ yz.2 = yz.1

private def diagonalPairsFull : Finset (F × F) :=
  (diagonalBadFull F).image fun y => (y, y)

theorem boundaryPairs_eq_union (hchar : ringChar F ≠ 2) :
    boundaryPairs F = selectorFull F ∪ diagonalPairsFull F := by
  ext yz
  simp only [boundaryPairs, selectorFull, diagonalPairsFull, mem_filter, mem_univ,
    true_and, mem_union, mem_image]
  constructor
  · rintro (hs | hd)
    · exact Or.inl hs
    · by_cases hs : IsSquare (delta F yz.1 yz.2)
      · exact Or.inl hs
      · right
        refine ⟨yz.1, ?_, by ext <;> simp [hd]⟩
        simp only [diagonalBadFull, mem_filter, mem_univ, true_and]
        apply quadraticChar_neg_one_iff_not_isSquare.mpr
        simpa [show delta F yz.1 yz.1 = 1 - 4 * yz.1 by simp [delta]; ring, hd] using hs
  · rintro (hs | ⟨y, hy, rfl⟩)
    · exact Or.inl hs
    · exact Or.inr rfl

theorem two_mul_card_boundaryPairs (hchar : ringChar F ≠ 2) :
    2 * ((boundaryPairs F).card : ℤ) =
      (Fintype.card F : ℤ) ^ 2 + 2 * Fintype.card F - 1 := by
  have hdis : Disjoint (selectorFull F) (diagonalPairsFull F) := by
    rw [Finset.disjoint_left]
    intro yz hs hd
    simp only [selectorFull, mem_filter, mem_univ, true_and] at hs
    simp only [diagonalPairsFull, mem_image] at hd
    rcases hd with ⟨y, hy, rfl⟩
    simp only [diagonalBadFull, mem_filter, mem_univ, true_and] at hy
    apply (quadraticChar_neg_one_iff_not_isSquare.mp hy)
    rw [show delta F y y = 1 - 4 * y by simp [delta]; ring] at hs
    exact hs
  have hdiag : (diagonalPairsFull F).card = (diagonalBadFull F).card := by
    apply card_image_of_injective
    intro y z h
    exact congrArg Prod.fst h
  rw [boundaryPairs_eq_union F hchar, card_union_of_disjoint hdis, Nat.cast_add,
    hdiag]
  have hs := two_mul_card_selectorFull F hchar
  have hd := two_mul_card_diagonalBadFull F hchar
  nlinarith

def boundarySquareGrid : Finset (F × F) :=
  (squares F ×ˢ squares F).filter fun yz =>
    IsSquare (delta F yz.1 yz.2) ∨ yz.2 = yz.1

private def diagonalPairsSquare : Finset (F × F) :=
  (diagonalBad F).image fun y => (y, y)

theorem boundarySquareGrid_eq_union (hchar : ringChar F ≠ 2) :
    boundarySquareGrid F = selectorSquareGrid F ∪ diagonalPairsSquare F := by
  ext yz
  simp only [boundarySquareGrid, selectorSquareGrid, diagonalPairsSquare, mem_filter,
    mem_product, mem_union, mem_image]
  constructor
  · rintro ⟨⟨hys, hzs⟩, hs | hd⟩
    · exact Or.inl ⟨⟨hys, hzs⟩, hs⟩
    · by_cases hs : IsSquare (delta F yz.1 yz.2)
      · exact Or.inl ⟨⟨hys, hzs⟩, hs⟩
      · right
        refine ⟨yz.1, ?_, by ext <;> simp [hd]⟩
        simp only [diagonalBad, mem_filter]
        refine ⟨hys, quadraticChar_neg_one_iff_not_isSquare.mpr ?_⟩
        simpa [show delta F yz.1 yz.1 = 1 - 4 * yz.1 by simp [delta]; ring, hd] using hs
  · rintro (⟨⟨hys, hzs⟩, hs⟩ | ⟨y, hy, rfl⟩)
    · exact ⟨⟨hys, hzs⟩, Or.inl hs⟩
    · simp only [diagonalBad, mem_filter] at hy
      exact ⟨⟨hy.1, hy.1⟩, Or.inr rfl⟩

theorem eight_mul_card_boundarySquareGrid (hchar : ringChar F ≠ 2) :
    8 * ((boundarySquareGrid F).card : ℤ) =
      (Fintype.card F : ℤ) ^ 2 + 10 * Fintype.card F - 5 +
        2 * quadraticChar F (-1) := by
  have hdis : Disjoint (selectorSquareGrid F) (diagonalPairsSquare F) := by
    rw [Finset.disjoint_left]
    intro yz hs hd
    simp only [selectorSquareGrid, mem_filter, mem_product] at hs
    simp only [diagonalPairsSquare, mem_image] at hd
    rcases hd with ⟨y, hy, rfl⟩
    simp only [diagonalBad, mem_filter] at hy
    apply (quadraticChar_neg_one_iff_not_isSquare.mp hy.2)
    rw [show delta F y y = 1 - 4 * y by simp [delta]; ring] at hs
    exact hs.2
  have hdiag : (diagonalPairsSquare F).card = (diagonalBad F).card := by
    apply card_image_of_injective
    intro y z h
    exact congrArg Prod.fst h
  rw [boundarySquareGrid_eq_union F hchar, card_union_of_disjoint hdis, Nat.cast_add,
    hdiag]
  have hs := eight_mul_card_selectorSquareGrid F hchar
  have hd := four_mul_card_diagonalBad F hchar
  nlinarith

theorem mem_boundary_iff (hchar : ringChar F ≠ 2) (q : Point F) :
    q ∈ boundary F ↔
      q.1 = 0 ∧ (IsSquare (delta F q.2.1 q.2.2) ∨ q.2.2 = q.2.1) := by
  have hsel := finite_or_vertical_iff F (two_ne_zero_of_ringChar F hchar) q
  simp only [boundary, mem_union]
  constructor
  · rintro ((hf | hd) | hv)
    · exact ⟨(mem_filter.1 hf).2.1, Or.inl (hsel.mp (mem_union_left _ hf)).2⟩
    · have hd' := (mem_filter.1 hd).2
      exact ⟨hd'.1, Or.inr hd'.2⟩
    · exact ⟨(mem_filter.1 hv).2.1, Or.inl (hsel.mp (mem_union_right _ hv)).2⟩
  · rintro ⟨hx, hs | hd⟩
    · rcases mem_union.mp (hsel.mpr ⟨hx, hs⟩) with hf | hv
      · exact Or.inl (Or.inl hf)
      · exact Or.inr hv
    · exact Or.inl (Or.inr (by simp [diagonalBoundary, hx, hd]))

private def planeEmbed (yz : F × F) : Point F := (0, yz.1, yz.2)

theorem boundary_eq_image_boundaryPairs (hchar : ringChar F ≠ 2) :
    boundary F = (boundaryPairs F).image (planeEmbed F) := by
  ext q
  rw [mem_boundary_iff F hchar]
  simp only [mem_image, boundaryPairs, mem_filter, mem_univ, true_and, planeEmbed]
  constructor
  · rintro ⟨hx, hq⟩
    exact ⟨(q.2.1, q.2.2), hq, by ext <;> simp [hx]⟩
  · rintro ⟨yz, hyz, rfl⟩
    exact ⟨rfl, hyz⟩

theorem two_mul_card_boundary (hchar : ringChar F ≠ 2) :
    2 * ((boundary F).card : ℤ) =
      (Fintype.card F : ℤ) ^ 2 + 2 * Fintype.card F - 1 := by
  rw [boundary_eq_image_boundaryPairs F hchar,
    card_image_of_injective (boundaryPairs F) (by
      intro yz uv h
      exact Prod.ext (congrArg (fun q => q.2.1) h) (congrArg (fun q => q.2.2) h))]
  exact two_mul_card_boundaryPairs F hchar

theorem four_mul_mem_squares_iff (hchar : ringChar F ≠ 2) (y : F) :
    4 * y ∈ squares F ↔ y ∈ squares F := by
  have h2 := two_ne_zero_of_ringChar F hchar
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  simp only [mem_squares]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a / 2, ?_⟩
    calc
      y = (4 * y) / 4 := by field_simp [h4]
      _ = (a * a) / 4 := by rw [ha]
      _ = (a / 2) * (a / 2) := by field_simp [h2, h4]; ring
  · rintro ⟨a, ha⟩
    refine ⟨2 * a, ?_⟩
    calc
      4 * y = 4 * (a * a) := by rw [ha]
      _ = (2 * a) * (2 * a) := by ring

theorem boundary_inter_body_eq_image (hchar : ringChar F ≠ 2) :
    boundary F ∩ body F = (boundarySquareGrid F).image (planeEmbed F) := by
  ext q
  simp only [mem_inter, mem_boundary_iff F hchar, body, mem_filter, mem_univ,
    true_and, mem_image, boundarySquareGrid, mem_product, planeEmbed]
  constructor
  · rintro ⟨⟨hx, hb⟩, hy, hz⟩
    rw [hx] at hy hz
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] at hy hz
    rw [four_mul_mem_squares_iff F hchar] at hy hz
    exact ⟨(q.2.1, q.2.2), ⟨⟨hy, hz⟩, hb⟩, by ext <;> simp [hx]⟩
  · rintro ⟨yz, ⟨⟨hy, hz⟩, hb⟩, rfl⟩
    refine ⟨⟨rfl, hb⟩, ?_, ?_⟩
    · simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
      rwa [four_mul_mem_squares_iff F hchar]
    · simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
      rwa [four_mul_mem_squares_iff F hchar]

theorem eight_mul_card_boundary_inter_body (hchar : ringChar F ≠ 2) :
    8 * (((boundary F ∩ body F).card : ℤ)) =
      (Fintype.card F : ℤ) ^ 2 + 10 * Fintype.card F - 5 +
        2 * quadraticChar F (-1) := by
  rw [boundary_inter_body_eq_image F hchar,
    card_image_of_injective (boundarySquareGrid F) (by
      intro yz uv h
      exact Prod.ext (congrArg (fun q => q.2.1) h) (congrArg (fun q => q.2.2) h))]
  exact eight_mul_card_boundarySquareGrid F hchar

theorem eight_mul_card_onePoleKakeya (hchar : ringChar F ≠ 2) :
    8 * ((onePoleKakeya F).card : ℤ) =
      2 * (Fintype.card F : ℤ) ^ 3 + 7 * (Fintype.card F : ℤ) ^ 2 + 1 -
        2 * quadraticChar F (-1) := by
  have hunion := card_union_add_card_inter (body F) (boundary F)
  have hbody := card_body F hchar
  have hsquare := sum_square_lift F hchar (fun _ => (1 : ℤ))
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at hsquare
  have hbody4 : 4 * ((body F).card : ℤ) =
      Fintype.card F * (Fintype.card F + 1) ^ 2 := by
    rw [hbody]
    push_cast
    have hrel : (Fintype.card F : ℤ) + 1 = 2 * (squares F).card := by omega
    rw [hrel]
    ring
  have hboundary := two_mul_card_boundary F hchar
  have hinter := eight_mul_card_boundary_inter_body F hchar
  have hunionZ := congrArg (fun n : ℕ => (n : ℤ)) hunion
  change ((body F ∪ boundary F).card : ℤ) + ((body F ∩ boundary F).card : ℤ) =
    (body F).card + (boundary F).card at hunionZ
  rw [inter_comm (body F) (boundary F)] at hunionZ
  change 8 * ((body F ∪ boundary F).card : ℤ) = _
  nlinarith

end FiniteKakeyaInf
