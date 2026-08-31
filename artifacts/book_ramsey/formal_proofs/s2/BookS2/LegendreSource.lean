import Mathlib
import BookS2.PeriodicSource

open scoped BigOperators

namespace BookS2

abbrev SquareUnits (F : Type*) [Field F] :=
  (powMonoidHom 2 : Fˣ →* Fˣ).range

section Character

variable {F : Type*} [Field F] [Fintype F]

attribute [local instance] Classical.decEq

local notation "χ" => quadraticChar F

lemma char_ne_two_of_card_mod_eight_eq_three
    (hcard : Fintype.card F % 8 = 3) : ringChar F ≠ 2 := by
  intro h
  have he := FiniteField.even_card_of_char_two h
  omega

lemma quadraticChar_neg_one_eq_neg_one
    (hcard : Fintype.card F % 8 = 3) : χ (-1) = -1 := by
  have hn : ¬ IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff]
    omega
  exact quadraticChar_neg_one_iff_not_isSquare.mpr hn

lemma quadraticChar_two_eq_neg_one
    (hcard : Fintype.card F % 8 = 3) : χ 2 = -1 := by
  have hn : ¬ IsSquare (2 : F) := by
    rw [FiniteField.isSquare_two_iff]
    omega
  exact quadraticChar_neg_one_iff_not_isSquare.mpr hn

lemma quadraticChar_square_unit (u : Fˣ) : χ ((u : F) ^ 2) = 1 := by
  exact quadraticChar_sq_one' u.ne_zero

lemma quadraticChar_inv_eq_self : χ⁻¹ = χ := by
  ext a
  rw [MulChar.inv_apply_eq_inv]
  rcases quadraticChar_dichotomy a.ne_zero with h | h
  · simp [h]
  · rw [h]
    apply (mul_left_cancel₀ (by norm_num : (-1 : ℤ) ≠ 0))
    rw [Ring.mul_inverse_cancel]
    · norm_num
    · exact IsUnit.neg isUnit_one

/-- The quadratic Jacobi sum, in the form needed below. -/
lemma sum_quadraticChar_mul_one_sub (hodd : ringChar F ≠ 2) :
    ∑ a : F, χ a * χ (1 - a) = -χ (-1) := by
  change jacobiSum χ χ = -χ (-1)
  calc
    jacobiSum χ χ = jacobiSum χ χ⁻¹ := by rw [quadraticChar_inv_eq_self]
    _ = -χ (-1) := jacobiSum_nontrivial_inv (quadraticChar_ne_one hodd)

/-- Character sum of a split quadratic with two distinct roots. -/
lemma sum_quadraticChar_mul_sub_mul_sub (hodd : ringChar F ≠ 2)
    (r s : F) (hrs : r ≠ s) :
    ∑ t : F, χ ((t - r) * (t - s)) = -1 := by
  let e : F ≃ F :=
    { toFun := fun a => r + (s - r) * a
      invFun := fun t => (s - r)⁻¹ * (t - r)
      left_inv := by
        intro a
        dsimp
        field_simp [sub_ne_zero.mpr hrs.symm]
        ring
      right_inv := by
        intro t
        dsimp
        field_simp [sub_ne_zero.mpr hrs.symm]
        ring }
  rw [← e.sum_comp]
  have he (a : F) :
      (e a - r) * (e a - s) = -(s - r) ^ 2 * (a * (1 - a)) := by
    dsimp [e]
    ring
  simp_rw [he]
  simp_rw [map_mul]
  rw [show -(s - r) ^ 2 = (-1 : F) * (s - r) ^ 2 by ring, map_mul,
    quadraticChar_sq_one' (sub_ne_zero.mpr hrs.symm)]
  simp only [mul_one, ← Finset.mul_sum]
  rw [sum_quadraticChar_mul_one_sub hodd]
  have hs := quadraticChar_sq_one (F := F) (neg_ne_zero.mpr (one_ne_zero' F))
  nlinarith

lemma unit_mem_squareUnits_iff (u : Fˣ) :
    u ∈ (powMonoidHom 2 : Fˣ →* Fˣ).range ↔ χ (u : F) = 1 := by
  constructor
  · rintro ⟨v, rfl⟩
    exact quadraticChar_square_unit v
  · intro hu
    have hs : IsSquare (u : F) := (quadraticChar_one_iff_isSquare u.ne_zero).mp hu
    obtain ⟨a, ha⟩ := hs
    have ha0 : a ≠ 0 := by
      intro h
      apply u.ne_zero
      rw [ha, h, zero_mul]
    refine ⟨Units.mk0 a ha0, ?_⟩
    apply Units.ext
    simpa [powMonoidHom_apply, pow_two] using ha.symm

/-- The indicator identity for the subgroup of nonzero squares. -/
lemma two_mul_sum_squareUnits (h : Fˣ → ℤ) :
    2 * ∑ t : SquareUnits F, h t =
      ∑ u : Fˣ, (1 + χ (u : F)) * h u := by
  calc
    2 * ∑ t : SquareUnits F, h t = ∑ t : SquareUnits F, 2 * h t := by
      rw [Finset.mul_sum]
    _ = ∑ u : Fˣ, if u ∈ (powMonoidHom 2 : Fˣ →* Fˣ).range then 2 * h u else 0 := by
      rw [← Finset.sum_filter]
      symm
      apply Finset.sum_subtype
      simp
    _ = ∑ u : Fˣ, (1 + χ (u : F)) * h u := by
      apply Finset.sum_congr rfl
      intro u hu
      by_cases hs : u ∈ (powMonoidHom 2 : Fˣ →* Fˣ).range
      · have hc := (unit_mem_squareUnits_iff u).mp hs
        simp [hs, hc]
      · have hc : χ (u : F) = -1 := by
          rcases quadraticChar_dichotomy u.ne_zero with hc | hc
          · exact False.elim (hs ((unit_mem_squareUnits_iff u).mpr hc))
          · exact hc
        simp [hs, hc]

/-- Cardinality of the square subgroup in an odd finite field. -/
theorem card_squareUnits (hodd : ringChar F ≠ 2) :
    Fintype.card (SquareUnits F) = (Fintype.card F - 1) / 2 := by
  rw [← Nat.card_eq_fintype_card, IsCyclic.card_powMonoidHom_range,
    Nat.card_eq_fintype_card, Fintype.card_units]
  have ho : (Fintype.card F - 1).gcd 2 = 2 := by
    rw [Nat.gcd_eq_right_iff_dvd]
    apply Nat.dvd_iff_mod_eq_zero.mpr
    have hc := FiniteField.odd_card_of_char_ne_two hodd
    omega
  rw [ho]

theorem card_squareUnits_of_mod_eight (hcard : Fintype.card F % 8 = 3) :
    Fintype.card (SquareUnits F) = (Fintype.card F - 1) / 2 :=
  card_squareUnits (char_ne_two_of_card_mod_eight_eq_three hcard)

lemma sum_units_eq_sum_sub (g : F → ℤ) :
    (∑ u : Fˣ, g u) = (∑ a : F, g a) - g 0 := by
  calc
    (∑ u : Fˣ, g u) = ∑ a : {a : F // a ≠ 0}, g a := by
      apply Fintype.sum_equiv unitsEquivNeZero
      intro u
      rfl
    _ = ∑ a ∈ (Finset.univ.erase (0 : F)), g a := by
      symm
      apply Finset.sum_subtype
      simp
    _ = (∑ a : F, g a) - g 0 := by
      have h := Finset.sum_erase_add (Finset.univ : Finset F) g (Finset.mem_univ 0)
      omega

lemma sum_quadraticChar_one_add (hodd : ringChar F ≠ 2) :
    ∑ a : F, χ (1 + a) = 0 := by
  have he := Equiv.sum_comp (Equiv.addLeft (-1 : F)) (fun a : F => χ (1 + a))
  calc
    (∑ a : F, χ (1 + a)) = ∑ a : F, χ a := by simpa using he.symm
    _ = 0 := quadraticChar_sum_zero hodd

lemma sum_quadraticChar_one_sub (hodd : ringChar F ≠ 2) :
    ∑ a : F, χ (1 - a) = 0 := by
  let e : F ≃ F :=
    { toFun := fun a => 1 - a
      invFun := fun a => 1 - a
      left_inv := by intro a; ring
      right_inv := by intro a; ring }
  have he := e.sum_comp (fun a : F => χ a)
  exact he.trans (quadraticChar_sum_zero hodd)

lemma sum_quadraticChar_mul_one_add (hodd : ringChar F ≠ 2)
    (hneg : χ (-1) = -1) :
    ∑ a : F, χ a * χ (1 + a) = -1 := by
  have hc (a : F) : χ (-a) = χ (-1) * χ a := by
    rw [← map_mul]
    congr 1
    ring
  calc
    (∑ a : F, χ a * χ (1 + a)) =
        ∑ a : F, -(χ a * χ (1 - a)) := by
      calc
        _ = ∑ a : F, χ ((Equiv.neg F) a) * χ (1 + (Equiv.neg F) a) :=
          (Equiv.sum_comp (Equiv.neg F) (fun a : F => χ a * χ (1 + a))).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a ha
          change χ (-a) * χ (1 + -a) = _
          rw [hc, hneg]
          congr 1
          ring
    _ = -(∑ a : F, χ a * χ (1 - a)) := by simp
    _ = -(-χ (-1)) := by rw [sum_quadraticChar_mul_one_sub hodd]
    _ = -1 := by rw [hneg]; norm_num

end Character

section Source

variable {F : Type*} [Field F] [Fintype F]

attribute [local instance] Classical.decEq

local notation "χ" => quadraticChar F

/-- The first sequence of the periodic Legendre source. -/
noncomputable def legendreX (t : SquareUnits F) : ℤ := -χ (1 + ((t : Fˣ) : F))

/-- The seam-corrected second sequence of the periodic Legendre source. -/
noncomputable def legendreY (t : SquareUnits F) : ℤ :=
  if t = 1 then -1 else -χ (1 - ((t : Fˣ) : F))

lemma sum_char_one_add_squareUnits (hcard : Fintype.card F % 8 = 3) :
    ∑ t : SquareUnits F, χ (1 + ((t : Fˣ) : F)) = -1 := by
  have hodd := char_ne_two_of_card_mod_eight_eq_three (F := F) hcard
  have hneg := quadraticChar_neg_one_eq_neg_one (F := F) hcard
  have hi := two_mul_sum_squareUnits (F := F)
    (fun u : Fˣ => χ (1 + (u : F)))
  have h₁ : (∑ u : Fˣ, χ (1 + (u : F))) = -1 := by
    calc
      _ = (∑ a : F, χ (1 + a)) - χ (1 + (0 : F)) :=
        sum_units_eq_sum_sub (fun a : F => χ (1 + a))
      _ = -1 := by rw [sum_quadraticChar_one_add hodd]; simp
  have h₂ : (∑ u : Fˣ, χ (u : F) * χ (1 + (u : F))) = -1 := by
    calc
      _ = (∑ a : F, χ a * χ (1 + a)) - χ 0 * χ (1 + (0 : F)) :=
        sum_units_eq_sum_sub (fun a : F => χ a * χ (1 + a))
      _ = -1 := by
        rw [sum_quadraticChar_mul_one_add hodd hneg]
        simp
  have hr : (∑ u : Fˣ, (1 + χ (u : F)) * χ (1 + (u : F))) = -2 := by
    calc
      _ = (∑ u : Fˣ, χ (1 + (u : F))) +
          ∑ u : Fˣ, χ (u : F) * χ (1 + (u : F)) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro u hu
            ring
      _ = -2 := by rw [h₁, h₂]; norm_num
  rw [hr] at hi
  omega

lemma sum_char_one_sub_squareUnits (hcard : Fintype.card F % 8 = 3) :
    ∑ t : SquareUnits F, χ (1 - ((t : Fˣ) : F)) = 0 := by
  have hodd := char_ne_two_of_card_mod_eight_eq_three (F := F) hcard
  have hneg := quadraticChar_neg_one_eq_neg_one (F := F) hcard
  have hi := two_mul_sum_squareUnits (F := F)
    (fun u : Fˣ => χ (1 - (u : F)))
  have h₁ : (∑ u : Fˣ, χ (1 - (u : F))) = -1 := by
    calc
      _ = (∑ a : F, χ (1 - a)) - χ (1 - (0 : F)) :=
        sum_units_eq_sum_sub (fun a : F => χ (1 - a))
      _ = -1 := by rw [sum_quadraticChar_one_sub hodd]; simp
  have h₂ : (∑ u : Fˣ, χ (u : F) * χ (1 - (u : F))) = 1 := by
    calc
      _ = (∑ a : F, χ a * χ (1 - a)) - χ 0 * χ (1 - (0 : F)) :=
        sum_units_eq_sum_sub (fun a : F => χ a * χ (1 - a))
      _ = 1 := by
        rw [sum_quadraticChar_mul_one_sub hodd]
        simp [hneg]
  have hr : (∑ u : Fˣ, (1 + χ (u : F)) * χ (1 - (u : F))) = 0 := by
    calc
      _ = (∑ u : Fˣ, χ (1 - (u : F))) +
          ∑ u : Fˣ, χ (u : F) * χ (1 - (u : F)) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro u hu
            ring
      _ = 0 := by rw [h₁, h₂]; norm_num
  rw [hr] at hi
  omega

lemma char_squareUnits (t : SquareUnits F) : χ ((t : Fˣ) : F) = 1 :=
  (unit_mem_squareUnits_iff (t : Fˣ)).mp t.property

lemma one_add_squareUnit_ne_zero (hcard : Fintype.card F % 8 = 3)
    (t : SquareUnits F) : 1 + ((t : Fˣ) : F) ≠ 0 := by
  intro ht
  have hv : ((t : Fˣ) : F) = -1 := by linear_combination ht
  have hc := char_squareUnits t
  rw [hv, quadraticChar_neg_one_eq_neg_one (F := F) hcard] at hc
  norm_num at hc

lemma one_sub_squareUnit_ne_zero {t : SquareUnits F} (ht : t ≠ 1) :
    1 - ((t : Fˣ) : F) ≠ 0 := by
  intro hz
  apply ht
  apply Subtype.ext
  apply Units.ext
  simpa using (sub_eq_zero.mp hz).symm

lemma legendreX_sign (hcard : Fintype.card F % 8 = 3) (t : SquareUnits F) :
    legendreX t = 1 ∨ legendreX t = -1 := by
  rcases quadraticChar_dichotomy (one_add_squareUnit_ne_zero hcard t) with h | h
  · right
    simp [legendreX, h]
  · left
    simp [legendreX, h]

lemma legendreY_sign (t : SquareUnits F) :
    legendreY t = 1 ∨ legendreY t = -1 := by
  by_cases ht : t = 1
  · right
    simp [legendreY, ht]
  · rcases quadraticChar_dichotomy (one_sub_squareUnit_ne_zero ht) with h | h
    · right
      simp [legendreY, ht, h]
    · left
      simp [legendreY, ht, h]

lemma legendreX_one (hcard : Fintype.card F % 8 = 3) :
    legendreX (1 : SquareUnits F) = 1 := by
  simp only [legendreX, Subgroup.coe_one, Units.val_one, one_add_one_eq_two]
  rw [quadraticChar_two_eq_neg_one (F := F) hcard]
  norm_num

lemma sum_legendreX (hcard : Fintype.card F % 8 = 3) :
    ∑ t : SquareUnits F, legendreX t = 1 := by
  simp only [legendreX]
  calc
    _ = -(∑ t : SquareUnits F, χ (1 + ((t : Fˣ) : F))) := by simp
    _ = 1 := by rw [sum_char_one_add_squareUnits hcard]; norm_num

lemma legendreY_eq_raw_sub_indicator (t : SquareUnits F) :
    legendreY t = -χ (1 - ((t : Fˣ) : F)) - if t = 1 then 1 else 0 := by
  by_cases ht : t = 1
  · subst t
    simp [legendreY]
  · simp [legendreY, ht]

lemma sum_legendreY (hcard : Fintype.card F % 8 = 3) :
    ∑ t : SquareUnits F, legendreY t = -1 := by
  simp_rw [legendreY_eq_raw_sub_indicator]
  rw [Finset.sum_sub_distrib]
  calc
    (∑ x : SquareUnits F, -χ (1 - ((x : Fˣ) : F))) -
        ∑ x : SquareUnits F, (if x = 1 then 1 else 0) =
        -(∑ x : SquareUnits F, χ (1 - ((x : Fˣ) : F))) - 1 := by simp
    _ = -1 := by rw [sum_char_one_sub_squareUnits hcard]; norm_num

lemma legendreX_inv (t : SquareUnits F) : legendreX t⁻¹ = legendreX t := by
  rw [legendreX, legendreX]
  congr 1
  have hv : (1 + (((t⁻¹ : SquareUnits F) : Fˣ) : F)) =
      (1 + ((t : Fˣ) : F)) * (((t⁻¹ : SquareUnits F) : Fˣ) : F) := by
    simp only [Subgroup.coe_inv, Units.val_inv_eq_inv_val]
    change 1 + (((t : Fˣ) : F))⁻¹ =
      (1 + ((t : Fˣ) : F)) * (((t : Fˣ) : F))⁻¹
    field_simp [Units.ne_zero]
    ring
  rw [hv, map_mul, char_squareUnits]
  simp

private lemma squareUnit_val_ne_one {δ : SquareUnits F} (hδ : δ ≠ 1) :
    ((δ : Fˣ) : F) ≠ 1 := by
  intro h
  apply hδ
  apply Subtype.ext
  apply Units.ext
  exact h

lemma sum_plus_polynomial (hcard : Fintype.card F % 8 = 3)
    {δ : SquareUnits F} (hδ : δ ≠ 1) :
    ∑ a : F, χ ((1 + a) * (1 + ((δ : Fˣ) : F) * a)) = -1 := by
  let d : F := ((δ : Fˣ) : F)
  have hd0 : d ≠ 0 := (δ : Fˣ).ne_zero
  have hd1 : d ≠ 1 := squareUnit_val_ne_one hδ
  have hrs : (-1 : F) ≠ -(d⁻¹) := by
    intro h
    have hi : d⁻¹ = 1 := neg_injective h.symm
    exact hd1 (inv_eq_one.mp hi)
  have hp (a : F) :
      (1 + a) * (1 + d * a) = d * ((a - (-1)) * (a - (-(d⁻¹)))) := by
    field_simp [hd0]
    ring
  change (∑ a : F, χ ((1 + a) * (1 + d * a))) = -1
  have hcd : χ d = 1 := char_squareUnits δ
  simp_rw [hp, map_mul, hcd, one_mul]
  simpa only [map_mul] using sum_quadraticChar_mul_sub_mul_sub
    (char_ne_two_of_card_mod_eight_eq_three (F := F) hcard) (-1) (-(d⁻¹)) hrs

lemma sum_minus_polynomial (hcard : Fintype.card F % 8 = 3)
    {δ : SquareUnits F} (hδ : δ ≠ 1) :
    ∑ a : F, χ ((1 - a) * (1 - ((δ : Fˣ) : F) * a)) = -1 := by
  let d : F := ((δ : Fˣ) : F)
  have hd0 : d ≠ 0 := (δ : Fˣ).ne_zero
  have hd1 : d ≠ 1 := squareUnit_val_ne_one hδ
  have hrs : (1 : F) ≠ d⁻¹ := by
    intro h
    have hi : d⁻¹ = 1 := h.symm
    exact hd1 (inv_eq_one.mp hi)
  have hp (a : F) :
      (1 - a) * (1 - d * a) = d * ((a - 1) * (a - d⁻¹)) := by
    field_simp [hd0]
    ring
  change (∑ a : F, χ ((1 - a) * (1 - d * a))) = -1
  have hcd : χ d = 1 := char_squareUnits δ
  simp_rw [hp, map_mul, hcd, one_mul]
  simpa only [map_mul] using sum_quadraticChar_mul_sub_mul_sub
    (char_ne_two_of_card_mod_eight_eq_three (F := F) hcard) 1 d⁻¹ hrs

lemma weighted_polynomials_cancel (hcard : Fintype.card F % 8 = 3)
    (δ : SquareUnits F) :
    (∑ a : F, χ a * χ ((1 + a) * (1 + ((δ : Fˣ) : F) * a))) +
      ∑ a : F, χ a * χ ((1 - a) * (1 - ((δ : Fˣ) : F) * a)) = 0 := by
  have hneg := quadraticChar_neg_one_eq_neg_one (F := F) hcard
  have hc (a : F) : χ (-a) = -χ a := by
    rw [show -a = (-1 : F) * a by ring, map_mul, hneg]
    ring
  have he := Equiv.sum_comp (Equiv.neg F)
    (fun a : F => χ a * χ ((1 + a) * (1 + ((δ : Fˣ) : F) * a)))
  have hs :
      (∑ a : F, χ a * χ ((1 + a) * (1 + ((δ : Fˣ) : F) * a))) =
      -(∑ a : F, χ a * χ ((1 - a) * (1 - ((δ : Fˣ) : F) * a))) := by
    calc
      _ = ∑ a : F, χ (-a) *
          χ ((1 + (-a)) * (1 + ((δ : Fˣ) : F) * (-a))) := he.symm
      _ = ∑ a : F, -(χ a *
          χ ((1 - a) * (1 - ((δ : Fˣ) : F) * a))) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [hc]
            congr 1
            ring
      _ = _ := by simp
  rw [hs]
  abel

lemma raw_combined_correlation (hcard : Fintype.card F % 8 = 3)
    {δ : SquareUnits F} (hδ : δ ≠ 1) :
    ∑ t : SquareUnits F,
      (χ ((1 + ((t : Fˣ) : F)) *
          (1 + ((δ : Fˣ) : F) * ((t : Fˣ) : F))) +
       χ ((1 - ((t : Fˣ) : F)) *
          (1 - ((δ : Fˣ) : F) * ((t : Fˣ) : F)))) = -2 := by
  let p : F → ℤ := fun a =>
    χ ((1 + a) * (1 + ((δ : Fˣ) : F) * a))
  let m : F → ℤ := fun a =>
    χ ((1 - a) * (1 - ((δ : Fˣ) : F) * a))
  have hpF : (∑ a : F, p a) = -1 := sum_plus_polynomial hcard hδ
  have hmF : (∑ a : F, m a) = -1 := sum_minus_polynomial hcard hδ
  have hp0 : p 0 = 1 := by simp [p]
  have hm0 : m 0 = 1 := by simp [m]
  have hpU : (∑ u : Fˣ, p u) = -2 := by
    rw [sum_units_eq_sum_sub, hpF, hp0]
    norm_num
  have hmU : (∑ u : Fˣ, m u) = -2 := by
    rw [sum_units_eq_sum_sub, hmF, hm0]
    norm_num
  have hwF : (∑ a : F, χ a * p a) + ∑ a : F, χ a * m a = 0 :=
    weighted_polynomials_cancel hcard δ
  have hwp0 : χ 0 * p 0 = 0 := by simp
  have hwm0 : χ 0 * m 0 = 0 := by simp
  have hwpU : (∑ u : Fˣ, χ (u : F) * p u) =
      (∑ a : F, χ a * p a) - χ 0 * p 0 :=
    sum_units_eq_sum_sub (fun a : F => χ a * p a)
  have hwmU : (∑ u : Fˣ, χ (u : F) * m u) =
      (∑ a : F, χ a * m a) - χ 0 * m 0 :=
    sum_units_eq_sum_sub (fun a : F => χ a * m a)
  have hwU : (∑ u : Fˣ, χ (u : F) * p u) +
      ∑ u : Fˣ, χ (u : F) * m u = 0 := by
    calc
      _ = ((∑ a : F, χ a * p a) - χ 0 * p 0) +
          ((∑ a : F, χ a * m a) - χ 0 * m 0) := by
            rw [hwpU, hwmU]
      _ = 0 := by rw [hwp0, hwm0]; simpa using hwF
  have hi := two_mul_sum_squareUnits (F := F) (fun u : Fˣ => p u + m u)
  have hr : (∑ u : Fˣ, (1 + χ (u : F)) * (p u + m u)) = -4 := by
    calc
      _ = (∑ u : Fˣ, p u) + (∑ u : Fˣ, m u) +
          ((∑ u : Fˣ, χ (u : F) * p u) +
            ∑ u : Fˣ, χ (u : F) * m u) := by
              repeat' rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro u hu
              ring
      _ = -4 := by rw [hpU, hmU, hwU]; norm_num
  have hi' : 2 * (∑ t : SquareUnits F,
      (fun u : Fˣ => p u + m u) t) = -4 := hi.trans hr
  have hs : (∑ t : SquareUnits F,
      (fun u : Fˣ => p u + m u) t) = -2 := by nlinarith [hi']
  simpa [p, m] using hs

private noncomputable def rawLegendreY (t : SquareUnits F) : ℤ :=
  -χ (1 - ((t : Fˣ) : F))

private noncomputable def seamIndicator (t : SquareUnits F) : ℤ := if t = 1 then 1 else 0

private lemma legendreY_eq_raw_sub_seam (t : SquareUnits F) :
    legendreY t = rawLegendreY t - seamIndicator t := by
  rw [legendreY_eq_raw_sub_indicator]
  rfl

private lemma sum_seam_mul_raw (δ : SquareUnits F) :
    ∑ t : SquareUnits F, seamIndicator t * rawLegendreY (δ * t) = rawLegendreY δ := by
  simp [seamIndicator]

private lemma sum_raw_mul_shifted_seam (δ : SquareUnits F) :
    ∑ t : SquareUnits F, rawLegendreY t * seamIndicator (δ * t) =
      rawLegendreY δ⁻¹ := by
  simp only [seamIndicator, mul_eq_one_iff_eq_inv]
  have heq (x : SquareUnits F) : δ = x⁻¹ ↔ x = δ⁻¹ := by
    simpa [eq_comm] using (inv_eq_iff_eq_inv (a := x) (b := δ))
  simp_rw [heq]
  simpa [mul_ite] using Fintype.sum_ite_eq' δ⁻¹ rawLegendreY

private lemma sum_seams_zero {δ : SquareUnits F} (hδ : δ ≠ 1) :
    ∑ t : SquareUnits F, seamIndicator t * seamIndicator (δ * t) = 0 := by
  apply Finset.sum_eq_zero
  intro t ht
  by_cases h : t = 1
  · subst t
    simp [seamIndicator, hδ]
  · simp [seamIndicator, h]

lemma seam_corrections_cancel (hcard : Fintype.card F % 8 = 3)
    (δ : SquareUnits F) : rawLegendreY δ + rawLegendreY δ⁻¹ = 0 := by
  have hneg := quadraticChar_neg_one_eq_neg_one (F := F) hcard
  have hv : 1 - ((((δ⁻¹ : SquareUnits F) : Fˣ) : F)) =
      -(1 - ((δ : Fˣ) : F)) * ((((δ⁻¹ : SquareUnits F) : Fˣ) : F)) := by
    simp only [Subgroup.coe_inv, Units.val_inv_eq_inv_val]
    field_simp [Units.ne_zero]
    ring
  rw [rawLegendreY, rawLegendreY, hv, map_mul]
  have hn : χ (-(1 - ((δ : Fˣ) : F))) =
      χ (-1) * χ (1 - ((δ : Fˣ) : F)) := by
    rw [show -(1 - ((δ : Fˣ) : F)) = (-1 : F) *
      (1 - ((δ : Fˣ) : F)) by ring, map_mul]
  rw [hn, hneg, char_squareUnits]
  ring

lemma sum_legendreY_product_eq_raw (hcard : Fintype.card F % 8 = 3)
    {δ : SquareUnits F} (hδ : δ ≠ 1) :
    (∑ t : SquareUnits F, legendreY t * legendreY (δ * t)) =
      ∑ t : SquareUnits F, rawLegendreY t * rawLegendreY (δ * t) := by
  simp_rw [legendreY_eq_raw_sub_seam]
  have h₁ := sum_seam_mul_raw δ
  have h₂ := sum_raw_mul_shifted_seam δ
  have h₃ := sum_seams_zero hδ
  have hc := seam_corrections_cancel hcard δ
  calc
    (∑ t : SquareUnits F,
        (rawLegendreY t - seamIndicator t) *
          (rawLegendreY (δ * t) - seamIndicator (δ * t))) =
      ∑ t : SquareUnits F,
        (rawLegendreY t * rawLegendreY (δ * t) -
        seamIndicator t * rawLegendreY (δ * t) -
        rawLegendreY t * seamIndicator (δ * t) +
        seamIndicator t * seamIndicator (δ * t)) := by
          apply Finset.sum_congr rfl
          intro t ht
          ring
    _ =
      (∑ t : SquareUnits F, rawLegendreY t * rawLegendreY (δ * t)) -
      (∑ t : SquareUnits F, seamIndicator t * rawLegendreY (δ * t)) -
      (∑ t : SquareUnits F, rawLegendreY t * seamIndicator (δ * t)) +
      (∑ t : SquareUnits F, seamIndicator t * seamIndicator (δ * t)) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_sub_distrib]
    _ = _ := by
      rw [h₁, h₂, h₃]
      have hci : rawLegendreY δ⁻¹ = -rawLegendreY δ := by linear_combination hc
      rw [hci]
      ring

lemma legendre_correlation (hcard : Fintype.card F % 8 = 3)
    {δ : SquareUnits F} (hδ : δ ≠ 1) :
    ∑ t : SquareUnits F,
      (legendreX t * legendreX (δ * t) +
       legendreY t * legendreY (δ * t)) = -2 := by
  rw [Finset.sum_add_distrib, sum_legendreY_product_eq_raw hcard hδ]
  have hr := raw_combined_correlation hcard hδ
  rw [← Finset.sum_add_distrib]
  convert hr using 1
  apply Finset.sum_congr rfl
  intro t ht
  simp only [legendreX, rawLegendreY, neg_mul_neg]
  rw [← map_mul, ← map_mul]
  congr 2

/-- The intrinsic periodic Legendre source over the subgroup of nonzero squares. -/
noncomputable def finiteFieldSource
    (hcard : Fintype.card F % 8 = 3) (_hlarge : 3 < Fintype.card F) :
    PeriodicLegendreSource (SquareUnits F) where
  x := legendreX
  y := legendreY
  x_sign := legendreX_sign hcard
  y_sign := legendreY_sign
  x_one := legendreX_one hcard
  sum_x := sum_legendreX hcard
  sum_y := sum_legendreY hcard
  x_inv := legendreX_inv
  correlation := fun δ hδ => legendre_correlation hcard (δ := δ) hδ

end Source

end BookS2
