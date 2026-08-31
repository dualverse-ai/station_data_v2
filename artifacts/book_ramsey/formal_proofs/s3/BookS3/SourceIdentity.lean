import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Algebra.Group.Subgroup.Even

open scoped BigOperators
open Finset

namespace BookS3

section QuadraticCharacter

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The self-Jacobi sum of the quadratic character in odd characteristic. -/
theorem jacobiSum_quadraticChar_self (hF : ringChar F ≠ 2) :
    jacobiSum (quadraticChar F) (quadraticChar F) = -quadraticChar F (-1) := by
  have hinv : (quadraticChar F)⁻¹ = quadraticChar F :=
    (quadraticChar_isQuadratic F).inv
  simpa only [hinv] using jacobiSum_nontrivial_inv (quadraticChar_ne_one hF)

/-- The quadratic-character sum of `y (1-y)`, in the form used in the
Yamada--Pott correlation calculation. -/
theorem sum_quadraticChar_mul_one_sub (hF : ringChar F ≠ 2) :
    ∑ y : F, quadraticChar F (y * (1 - y)) = -quadraticChar F (-1) := by
  simpa only [map_mul] using jacobiSum_quadraticChar_self (F := F) hF

/-- A quadratic polynomial with two distinct roots has quadratic-character
sum `-1`.  This is the exact unweighted quadratic-sum input in Lemma 4.1. -/
theorem sum_quadraticChar_two_roots (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    ∑ x : F, quadraticChar F ((x - a) * (x - b)) = -1 := by
  let d : F := b - a
  have hd : d ≠ 0 := sub_ne_zero.mpr hab.symm
  let e : F ≃ F := (Equiv.mulLeft₀ d hd).trans (Equiv.addLeft a)
  have he (y : F) : e y = a + d * y := rfl
  calc
    ∑ x : F, quadraticChar F ((x - a) * (x - b)) =
        ∑ y : F, quadraticChar F (((e y) - a) * ((e y) - b)) := by
          symm
          exact e.sum_comp (fun x : F ↦ quadraticChar F ((x - a) * (x - b)))
    _ = ∑ y : F, quadraticChar F ((-1) * d ^ 2 * (y * (1 - y))) := by
          apply sum_congr rfl
          intro y _
          congr 1
          rw [he]
          dsimp only [d]
          ring
    _ = quadraticChar F (-1) * (∑ y : F, quadraticChar F (y * (1 - y))) := by
          simp_rw [map_mul, quadraticChar_sq_one' hd, mul_one]
          exact (mul_sum ..).symm
    _ = -1 := by
          rw [sum_quadraticChar_mul_one_sub (F := F) hF]
          have hneg : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
          have hsq := quadraticChar_sq_one (F := F) hneg
          nlinarith

/-- The first of the two quadratic sums in the Yamada--Pott proof.  The
hypothesis on `quadraticChar t` records that `t` lies in the nonzero square
subgroup. -/
theorem sum_quadraticChar_one_add (hF : ringChar F ≠ 2) {t : F}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htsq : quadraticChar F t = 1) :
    ∑ x : F, quadraticChar F ((1 + x) * (1 + t * x)) = -1 := by
  have hroots : (-1 : F) ≠ -t⁻¹ := by
    intro h
    apply ht1
    have hi : t⁻¹ = 1 := neg_injective h.symm
    exact inv_eq_one.mp hi
  have hpoly (x : F) :
      (1 + x) * (1 + t * x) = t * ((x - (-1)) * (x - (-t⁻¹))) := by
    (field_simp; ring)
  calc
    ∑ x : F, quadraticChar F ((1 + x) * (1 + t * x)) =
        ∑ x : F, quadraticChar F (t * ((x - (-1)) * (x - (-t⁻¹)))) := by
          apply sum_congr rfl
          intro x _
          rw [hpoly]
    _ = quadraticChar F t *
        (∑ x : F, quadraticChar F ((x - (-1)) * (x - (-t⁻¹)))) := by
          simp_rw [map_mul]
          exact (mul_sum ..).symm
    _ = -1 := by
          rw [sum_quadraticChar_two_roots (F := F) hF hroots, htsq, one_mul]

/-- Removing `x = 0` changes the preceding complete sum from `-1` to `-2`.
This is the exact unweighted `Fₓˣ` sum quoted in Lemma 4.1. -/
theorem sum_quadraticChar_one_add_ne_zero (hF : ringChar F ≠ 2) {t : F}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htsq : quadraticChar F t = 1) :
    ∑ x ∈ Finset.univ.erase (0 : F), quadraticChar F ((1 + x) * (1 + t * x)) = -2 := by
  have hfull := sum_quadraticChar_one_add (F := F) hF ht0 ht1 htsq
  have herase := Finset.sum_erase_add (s := (Finset.univ : Finset F))
    (f := fun x : F ↦ quadraticChar F ((1 + x) * (1 + t * x))) (Finset.mem_univ 0)
  simp only [mul_zero, add_zero, one_mul, map_one] at herase
  linarith

/-- The companion quadratic sum with both signs reversed. -/
theorem sum_quadraticChar_one_sub (hF : ringChar F ≠ 2) {t : F}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htsq : quadraticChar F t = 1) :
    ∑ x : F, quadraticChar F ((1 - x) * (1 - t * x)) = -1 := by
  have hroots : (1 : F) ≠ t⁻¹ := by
    intro h
    apply ht1
    exact inv_eq_one.mp h.symm
  have hpoly (x : F) :
      (1 - x) * (1 - t * x) = t * ((x - 1) * (x - t⁻¹)) := by
    (field_simp; ring)
  calc
    ∑ x : F, quadraticChar F ((1 - x) * (1 - t * x)) =
        ∑ x : F, quadraticChar F (t * ((x - 1) * (x - t⁻¹))) := by
          apply sum_congr rfl
          intro x _
          rw [hpoly]
    _ = quadraticChar F t *
        (∑ x : F, quadraticChar F ((x - 1) * (x - t⁻¹))) := by
          simp_rw [map_mul]
          exact (mul_sum ..).symm
    _ = -1 := by
          rw [sum_quadraticChar_two_roots (F := F) hF hroots, htsq, one_mul]

/-- The second unweighted `Fₓˣ` sum in Lemma 4.1. -/
theorem sum_quadraticChar_one_sub_ne_zero (hF : ringChar F ≠ 2) {t : F}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htsq : quadraticChar F t = 1) :
    ∑ x ∈ Finset.univ.erase (0 : F), quadraticChar F ((1 - x) * (1 - t * x)) = -2 := by
  have hfull := sum_quadraticChar_one_sub (F := F) hF ht0 ht1 htsq
  have herase := Finset.sum_erase_add (s := (Finset.univ : Finset F))
    (f := fun x : F ↦ quadraticChar F ((1 - x) * (1 - t * x))) (Finset.mem_univ 0)
  simp only [mul_zero, sub_zero, one_mul, map_one] at herase
  linarith

/-- In a finite field of order `3 mod 4`, the quadratic character of `-1`
is `-1`. -/
theorem quadraticChar_neg_one_of_card_mod_four_eq_three (hF : ringChar F ≠ 2)
    (hcard : Fintype.card F % 4 = 3) : quadraticChar F (-1) = -1 := by
  rw [quadraticChar_neg_one hF, ZMod.χ₄_nat_three_mod_four hcard]

/-- The two weighted terms introduced by the square-subgroup indicator
cancel under `x ↦ -x`. -/
theorem weighted_quadratic_pair_cancel (hF : ringChar F ≠ 2)
    (hcard : Fintype.card F % 4 = 3) (t : F) :
    ∑ x : F, quadraticChar F x *
        (quadraticChar F ((1 + x) * (1 + t * x)) +
          quadraticChar F ((1 - x) * (1 - t * x))) = 0 := by
  have hneg : quadraticChar F (-1) = -1 :=
    quadraticChar_neg_one_of_card_mod_four_eq_three (F := F) hF hcard
  let Pplus : F → F := fun x ↦ (1 + x) * (1 + t * x)
  let Pminus : F → F := fun x ↦ (1 - x) * (1 - t * x)
  have hp (x : F) : Pplus (-x) = Pminus x := by
    dsimp only [Pplus, Pminus]
    ring
  have hcancel :
      (∑ x : F, quadraticChar F x * quadraticChar F (Pplus x)) =
        -(∑ x : F, quadraticChar F x * quadraticChar F (Pminus x)) := by
    calc
      ∑ x : F, quadraticChar F x * quadraticChar F (Pplus x) =
          ∑ x : F, quadraticChar F (-x) * quadraticChar F (Pplus (-x)) := by
            symm
            exact Equiv.sum_comp (Equiv.neg F)
              (fun x : F ↦ quadraticChar F x * quadraticChar F (Pplus x))
      _ = ∑ x : F, -(quadraticChar F x * quadraticChar F (Pminus x)) := by
            apply sum_congr rfl
            intro x _
            rw [hp, show (-x : F) = (-1) * x by ring, map_mul, hneg]
            ring
      _ = -(∑ x : F, quadraticChar F x * quadraticChar F (Pminus x)) := by
            simpa only using (Finset.sum_neg_distrib
              (s := (Finset.univ : Finset F))
              (f := fun x : F ↦ quadraticChar F x * quadraticChar F (Pminus x)))
  calc
    ∑ x : F, quadraticChar F x *
        (quadraticChar F ((1 + x) * (1 + t * x)) +
          quadraticChar F ((1 - x) * (1 - t * x))) =
        (∑ x : F, quadraticChar F x * quadraticChar F (Pplus x)) +
          (∑ x : F, quadraticChar F x * quadraticChar F (Pminus x)) := by
            rw [← sum_add_distrib]
            apply sum_congr rfl
            intro x _
            dsimp only [Pplus, Pminus]
            ring
    _ = 0 := by rw [hcancel, neg_add_cancel]

/-- The weighted cancellation remains true after removing zero, since the
quadratic character itself vanishes there. -/
theorem weighted_quadratic_pair_cancel_ne_zero (hF : ringChar F ≠ 2)
    (hcard : Fintype.card F % 4 = 3) (t : F) :
    ∑ x ∈ Finset.univ.erase (0 : F), quadraticChar F x *
        (quadraticChar F ((1 + x) * (1 + t * x)) +
          quadraticChar F ((1 - x) * (1 - t * x))) = 0 := by
  let f : F → ℤ := fun x ↦ quadraticChar F x *
    (quadraticChar F ((1 + x) * (1 + t * x)) +
      quadraticChar F ((1 - x) * (1 - t * x)))
  have hfull : ∑ x : F, f x = 0 := by
    simpa only [f] using weighted_quadratic_pair_cancel (F := F) hF hcard t
  have herase := Finset.sum_erase_add (s := (Finset.univ : Finset F))
    (f := f) (Finset.mem_univ 0)
  have hf0 : f 0 = 0 := by simp only [f, quadraticChar_zero, zero_mul]
  rw [hf0, add_zero, hfull] at herase
  exact herase

/-- On nonzero field elements, `1 + χ(x)` is exactly twice the indicator
of the square subgroup. -/
theorem weighted_square_indicator (f : F → ℤ) :
    (∑ x ∈ Finset.univ.erase (0 : F), (1 + quadraticChar F x) * f x) =
      2 * (∑ x ∈ (Finset.univ.erase (0 : F)).filter (IsSquare : F → Prop), f x) := by
  classical
  let s : Finset F := Finset.univ.erase 0
  calc
    (∑ x ∈ Finset.univ.erase (0 : F), (1 + quadraticChar F x) * f x) =
        ∑ x ∈ s, if IsSquare x then 2 * f x else 0 := by
          apply sum_congr rfl
          intro x hx
          have hx0 : x ≠ 0 := (Finset.mem_erase.mp hx).1
          by_cases hs : IsSquare x
          · rw [if_pos hs, (quadraticChar_one_iff_isSquare hx0).mpr hs]
            ring
          · rw [if_neg hs, quadraticChar_neg_one_iff_not_isSquare.mpr hs]
            ring
    _ = ∑ x ∈ s.filter (IsSquare : F → Prop), 2 * f x := by
          symm
          exact Finset.sum_filter (IsSquare : F → Prop) (fun x ↦ 2 * f x)
    _ = 2 * (∑ x ∈ (Finset.univ.erase (0 : F)).filter (IsSquare : F → Prop), f x) := by
          simp only [s]
          exact (mul_sum ..).symm

/-- The numerator obtained by replacing the nonzero-square sum with the
weight `1 + χ(x)` is `-4`: its unweighted part contributes `-2-2`, and
its weighted part cancels. -/
theorem weighted_YamadaPott_pair_sum (hF : ringChar F ≠ 2)
    (hcard : Fintype.card F % 4 = 3) {t : F}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htsq : quadraticChar F t = 1) :
    ∑ x ∈ Finset.univ.erase (0 : F), (1 + quadraticChar F x) *
        (quadraticChar F ((1 + x) * (1 + t * x)) +
          quadraticChar F ((1 - x) * (1 - t * x))) = -4 := by
  let P : F → ℤ := fun x ↦ quadraticChar F ((1 + x) * (1 + t * x))
  let M : F → ℤ := fun x ↦ quadraticChar F ((1 - x) * (1 - t * x))
  have hP : ∑ x ∈ Finset.univ.erase (0 : F), P x = -2 := by
    simpa only [P] using sum_quadraticChar_one_add_ne_zero (F := F) hF ht0 ht1 htsq
  have hM : ∑ x ∈ Finset.univ.erase (0 : F), M x = -2 := by
    simpa only [M] using sum_quadraticChar_one_sub_ne_zero (F := F) hF ht0 ht1 htsq
  have hW : ∑ x ∈ Finset.univ.erase (0 : F),
      quadraticChar F x * (P x + M x) = 0 := by
    simpa only [P, M] using weighted_quadratic_pair_cancel_ne_zero (F := F) hF hcard t
  calc
    ∑ x ∈ Finset.univ.erase (0 : F), (1 + quadraticChar F x) *
        (quadraticChar F ((1 + x) * (1 + t * x)) +
          quadraticChar F ((1 - x) * (1 - t * x))) =
        (∑ x ∈ Finset.univ.erase (0 : F), P x) +
        (∑ x ∈ Finset.univ.erase (0 : F), M x) +
        (∑ x ∈ Finset.univ.erase (0 : F), quadraticChar F x * (P x + M x)) := by
          repeat' rw [← Finset.sum_add_distrib]
          apply sum_congr rfl
          intro x _
          dsimp only [P, M]
          ring
    _ = -4 := by rw [hP, hM, hW]; norm_num

/-- Generator-free form of the core Yamada--Pott identity: the sum of the
two quadratic-character correlations over the nonzero square subgroup is
exactly `-2`.  Indexing that subgroup by powers of a square generator gives
the displayed character sum in Lemma 4.1 of the paper. -/
theorem YamadaPott_square_subgroup_sum (hF : ringChar F ≠ 2)
    (hcard : Fintype.card F % 4 = 3) {t : F}
    (ht0 : t ≠ 0) (ht1 : t ≠ 1) (htsq : quadraticChar F t = 1) :
    ∑ x ∈ (Finset.univ.erase (0 : F)).filter (IsSquare : F → Prop),
        (quadraticChar F ((1 + x) * (1 + t * x)) +
          quadraticChar F ((1 - x) * (1 - t * x))) = -2 := by
  classical
  let f : F → ℤ := fun x ↦
    quadraticChar F ((1 + x) * (1 + t * x)) +
      quadraticChar F ((1 - x) * (1 - t * x))
  have hweight := weighted_square_indicator (F := F) f
  have htotal :
      ∑ x ∈ Finset.univ.erase (0 : F), (1 + quadraticChar F x) * f x = -4 := by
    simpa only [f] using weighted_YamadaPott_pair_sum (F := F) hF hcard ht0 ht1 htsq
  rw [htotal] at hweight
  change (∑ x ∈ (Finset.univ.erase (0 : F)).filter (IsSquare : F → Prop), f x) = -2
  linarith

/-- Translation preserves the complete quadratic-character sum, so the
sum of `χ(1+x)` over the whole field vanishes. -/
theorem sum_quadraticChar_one_add_all (hF : ringChar F ≠ 2) :
    ∑ x : F, quadraticChar F (1 + x) = 0 := by
  calc
    ∑ x : F, quadraticChar F (1 + x) = ∑ x : F, quadraticChar F x := by
      exact Equiv.sum_comp (Equiv.addLeft (1 : F)) (quadraticChar F)
    _ = 0 := quadraticChar_sum_zero hF

/-- The mixed Jacobi sum occurring in the proof that the Yamada--Pott
sequence `u(x)=χ(1+x)` has total sum `-1`. -/
theorem sum_quadraticChar_mul_one_add (hF : ringChar F ≠ 2)
    (hcard : Fintype.card F % 4 = 3) :
    ∑ x : F, quadraticChar F x * quadraticChar F (1 + x) = -1 := by
  have hneg : quadraticChar F (-1) = -1 :=
    quadraticChar_neg_one_of_card_mod_four_eq_three (F := F) hF hcard
  calc
    ∑ x : F, quadraticChar F x * quadraticChar F (1 + x) =
        ∑ y : F, quadraticChar F (-y) * quadraticChar F (1 + (-y)) := by
          symm
          exact Equiv.sum_comp (Equiv.neg F)
            (fun x : F ↦ quadraticChar F x * quadraticChar F (1 + x))
    _ = -jacobiSum (quadraticChar F) (quadraticChar F) := by
          rw [jacobiSum]
          rw [← Finset.sum_neg_distrib]
          apply sum_congr rfl
          intro y _
          rw [show (-y : F) = (-1) * y by ring, map_mul, hneg]
          rw [show (1 + (-1) * y : F) = 1 - y by ring]
          ring
    _ = -1 := by
          rw [jacobiSum_quadraticChar_self (F := F) hF, hneg]
          norm_num

/-- Generator-free form of `∑ u_r=-1`: summing `χ(1+x)` over the
nonzero square subgroup gives `-1`. -/
theorem YamadaPott_u_sum (hF : ringChar F ≠ 2)
    (hcard : Fintype.card F % 4 = 3) :
    ∑ x ∈ (Finset.univ.erase (0 : F)).filter (IsSquare : F → Prop),
      quadraticChar F (1 + x) = -1 := by
  classical
  let f : F → ℤ := fun x ↦ quadraticChar F (1 + x)
  have hall : ∑ x : F, f x = 0 := by
    simpa only [f] using sum_quadraticChar_one_add_all (F := F) hF
  have herase := Finset.sum_erase_add (s := (Finset.univ : Finset F))
    (f := f) (Finset.mem_univ 0)
  have hf0 : f 0 = 1 := by simp only [f, add_zero, map_one]
  rw [hf0, hall] at herase
  have hplain : ∑ x ∈ Finset.univ.erase (0 : F), f x = -1 := by linarith
  have hmixed : ∑ x ∈ Finset.univ.erase (0 : F), quadraticChar F x * f x = -1 := by
    have hfull := sum_quadraticChar_mul_one_add (F := F) hF hcard
    have herase' := Finset.sum_erase_add (s := (Finset.univ : Finset F))
      (f := fun x : F ↦ quadraticChar F x * f x) (Finset.mem_univ 0)
    simp only [quadraticChar_zero, zero_mul, add_zero] at herase'
    simpa only [f] using herase'.trans hfull
  have hweighted :
      ∑ x ∈ Finset.univ.erase (0 : F), (1 + quadraticChar F x) * f x = -2 := by
    calc
      ∑ x ∈ Finset.univ.erase (0 : F), (1 + quadraticChar F x) * f x =
          (∑ x ∈ Finset.univ.erase (0 : F), f x) +
            (∑ x ∈ Finset.univ.erase (0 : F), quadraticChar F x * f x) := by
              rw [← Finset.sum_add_distrib]
              apply sum_congr rfl
              intro x _
              ring
      _ = -2 := by rw [hplain, hmixed]; norm_num
  have hindicator := weighted_square_indicator (F := F) f
  rw [hweighted] at hindicator
  change (∑ x ∈ (Finset.univ.erase (0 : F)).filter (IsSquare : F → Prop), f x) = -1
  linarith

/-- Generator-free form of `u_{-r}=u_r`: inversion in the square subgroup
preserves `χ(1+x)`. -/
theorem YamadaPott_u_inv {x : F} (hx0 : x ≠ 0) (hxsq : IsSquare x) :
    quadraticChar F (1 + x⁻¹) = quadraticChar F (1 + x) := by
  have hinv0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
  have hinvsq : IsSquare x⁻¹ := hxsq.inv
  rw [show (1 + x⁻¹ : F) = x⁻¹ * (1 + x) by (field_simp; ring)]
  rw [map_mul, (quadraticChar_one_iff_isSquare hinv0).mpr hinvsq, one_mul]

/-- Generator-free form of `h_{-r}=-h_r`: when the field order is `3 mod
4`, inversion in the square subgroup negates `χ(1-x)`. -/
theorem YamadaPott_h_inv (hF : ringChar F ≠ 2)
    (hcard : Fintype.card F % 4 = 3) {x : F} (hx0 : x ≠ 0) (hxsq : IsSquare x) :
    quadraticChar F (1 - x⁻¹) = -quadraticChar F (1 - x) := by
  have hinv0 : x⁻¹ ≠ 0 := inv_ne_zero hx0
  have hinvsq : IsSquare x⁻¹ := hxsq.inv
  have hneg : quadraticChar F (-1) = -1 :=
    quadraticChar_neg_one_of_card_mod_four_eq_three (F := F) hF hcard
  rw [show (1 - x⁻¹ : F) = ((-1) * x⁻¹) * (1 - x) by (field_simp; ring)]
  rw [map_mul, map_mul, hneg, (quadraticChar_one_iff_isSquare hinv0).mpr hinvsq]
  ring

/-! ## A concrete generator-free Yamada--Pott source -/

/-- The square subgroup of the unit group.  The concrete finset below is
its image in the field under the units coercion. -/
def YamadaPottSquareSubgroup (F : Type*) [Field F] : Subgroup Fˣ :=
  Subgroup.square Fˣ

/-- Nonzero squares, viewed directly as field elements. -/
def YamadaPottS (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset F :=
  (Finset.univ.erase 0).filter (IsSquare : F → Prop)

/-- The symmetric Yamada--Pott sequence. -/
def YamadaPottU (x : F) : ℤ := quadraticChar F (1 + x)

/-- The skew Yamada--Pott sequence. -/
def YamadaPottH (x : F) : ℤ := quadraticChar F (1 - x)

/-- The positive support of `YamadaPottU` inside the square subgroup. -/
def YamadaPottX (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset F :=
  (YamadaPottS F).filter fun x ↦ YamadaPottU x = 1

@[simp] theorem mem_YamadaPottS {x : F} :
    x ∈ YamadaPottS F ↔ x ≠ 0 ∧ IsSquare x := by
  simp [YamadaPottS, and_comm]

@[simp] theorem mem_YamadaPottX {x : F} :
    x ∈ YamadaPottX F ↔ x ∈ YamadaPottS F ∧ YamadaPottU x = 1 := by
  simp [YamadaPottX]

/-- Inversion symmetry of `U`, stated on the concrete square carrier. -/
theorem YamadaPottU_inv {x : F} (hx : x ∈ YamadaPottS F) :
    YamadaPottU x⁻¹ = YamadaPottU x := by
  rw [YamadaPottU]
  exact YamadaPott_u_inv (mem_YamadaPottS.mp hx).1 (mem_YamadaPottS.mp hx).2

/-- Inversion skew-symmetry of `H`, stated on the concrete square carrier. -/
theorem YamadaPottH_inv (hF : ringChar F ≠ 2)
    (hcard : Fintype.card F % 4 = 3) {x : F} (hx : x ∈ YamadaPottS F) :
    YamadaPottH x⁻¹ = -YamadaPottH x := by
  rw [YamadaPottH]
  exact YamadaPott_h_inv (F := F) hF hcard
    (mem_YamadaPottS.mp hx).1 (mem_YamadaPottS.mp hx).2

private theorem sum_quadraticChar_ne_zero_eq_zero (hF : ringChar F ≠ 2) :
    ∑ x ∈ Finset.univ.erase (0 : F), quadraticChar F x = 0 := by
  have hfull := quadraticChar_sum_zero (F := F) hF
  have herase := Finset.sum_erase_add (s := (Finset.univ : Finset F))
    (f := quadraticChar F) (Finset.mem_univ 0)
  rw [quadraticChar_zero, add_zero, hfull] at herase
  exact herase

/-- If `#F=4r+3`, the nonzero-square carrier has size `2r+1`. -/
theorem card_YamadaPottS (hF : ringChar F ≠ 2) {r : ℕ}
    (hcard : Fintype.card F = 4 * r + 3) : (YamadaPottS F).card = 2 * r + 1 := by
  have hweight := weighted_square_indicator (F := F) (fun _ ↦ (1 : ℤ))
  have hchi := sum_quadraticChar_ne_zero_eq_zero (F := F) hF
  have hzero : (0 : F) ∈ (Finset.univ : Finset F) := Finset.mem_univ 0
  have herasecard : (Finset.univ.erase (0 : F)).card = Fintype.card F - 1 := by
    rw [Finset.card_erase_of_mem hzero, Finset.card_univ]
  simp only [mul_one, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul] at hweight
  rw [hchi, add_zero] at hweight
  change (YamadaPottS F).card = 2 * r + 1
  rw [← Int.ofNat_inj]
  have hcardInt : ((Fintype.card F : ℕ) : ℤ) = 4 * (r : ℤ) + 3 := by omega
  have heraseInt : (((Finset.univ.erase (0 : F)).card : ℕ) : ℤ) =
      (Fintype.card F : ℤ) - 1 := by omega
  change (((YamadaPottS F).card : ℕ) : ℤ) = ((2 * r + 1 : ℕ) : ℤ)
  change (((Finset.univ.erase (0 : F)).card : ℕ) : ℤ) =
      2 * (((YamadaPottS F).card : ℕ) : ℤ) at hweight
  norm_num at hweight ⊢
  omega

private theorem YamadaPott_one_add_ne_zero (hF : ringChar F ≠ 2)
    (hcard : Fintype.card F % 4 = 3) {x : F} (hx : x ∈ YamadaPottS F) :
    1 + x ≠ 0 := by
  intro hxzero
  have hxneg : x = -1 := eq_neg_of_add_eq_zero_right hxzero
  have hxsq := (mem_YamadaPottS.mp hx).2
  have hx0 := (mem_YamadaPottS.mp hx).1
  have hchar : quadraticChar F x = 1 :=
    (quadraticChar_one_iff_isSquare hx0).mpr hxsq
  have hneg := quadraticChar_neg_one_of_card_mod_four_eq_three (F := F) hF hcard
  rw [hxneg, hneg] at hchar
  norm_num at hchar

private theorem YamadaPottU_ne_zero (hF : ringChar F ≠ 2)
    (hcard : Fintype.card F % 4 = 3) {x : F} (hx : x ∈ YamadaPottS F) :
    YamadaPottU x ≠ 0 := by
  rw [YamadaPottU]
  exact (quadraticChar_eq_zero_iff.not).mpr
    (YamadaPott_one_add_ne_zero (F := F) hF hcard hx)

private theorem YamadaPottU_dichotomy (hF : ringChar F ≠ 2)
    (hcard : Fintype.card F % 4 = 3) {x : F} (hx : x ∈ YamadaPottS F) :
    YamadaPottU x = 1 ∨ YamadaPottU x = -1 := by
  rw [YamadaPottU]
  exact quadraticChar_dichotomy (YamadaPott_one_add_ne_zero (F := F) hF hcard hx)

/-- The positive support `X` has size `r` when `#F=4r+3`; equivalently,
`|X|=(m-1)/2` for `m=(#F-1)/2=2r+1`. -/
theorem card_YamadaPottX (hF : ringChar F ≠ 2) {r : ℕ}
    (hcard : Fintype.card F = 4 * r + 3) : (YamadaPottX F).card = r := by
  have hmod : Fintype.card F % 4 = 3 := by omega
  have hS := card_YamadaPottS (F := F) hF hcard
  have hu : ∑ x ∈ YamadaPottS F, YamadaPottU x = -1 := by
    simpa only [YamadaPottS, YamadaPottU] using YamadaPott_u_sum (F := F) hF hmod
  have hindicator :
      ∑ x ∈ YamadaPottS F, (if YamadaPottU x = 1 then (1 : ℤ) else 0) =
        ((YamadaPottX F).card : ℤ) := by
    rw [← Finset.sum_filter]
    simp only [YamadaPottX, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hpoint (x : F) (hx : x ∈ YamadaPottS F) :
      YamadaPottU x = 2 * (if YamadaPottU x = 1 then (1 : ℤ) else 0) - 1 := by
    rcases YamadaPottU_dichotomy (F := F) hF hmod hx with hp | hn
    · rw [hp, if_pos rfl]
      norm_num
    · rw [hn, if_neg (by norm_num)]
      norm_num
  have hsum :
      (∑ x ∈ YamadaPottS F, YamadaPottU x) =
        2 * ((YamadaPottX F).card : ℤ) - ((YamadaPottS F).card : ℤ) := by
    calc
      ∑ x ∈ YamadaPottS F, YamadaPottU x =
          ∑ x ∈ YamadaPottS F,
            (2 * (if YamadaPottU x = 1 then (1 : ℤ) else 0) - 1) := by
              apply sum_congr rfl
              exact hpoint
      _ = 2 * (∑ x ∈ YamadaPottS F,
            (if YamadaPottU x = 1 then (1 : ℤ) else 0)) -
            ((YamadaPottS F).card : ℤ) := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
              simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ = _ := by rw [hindicator]
  rw [hu, hS] at hsum
  rw [← Int.ofNat_inj]
  norm_num at hsum ⊢
  omega

/-- Multiplication closes the nonzero-square carrier. -/
theorem YamadaPottS_mul_mem {x y : F} (hx : x ∈ YamadaPottS F)
    (hy : y ∈ YamadaPottS F) : x * y ∈ YamadaPottS F := by
  rw [mem_YamadaPottS] at hx hy ⊢
  exact ⟨mul_ne_zero hx.1 hy.1, hx.2.mul hy.2⟩

private theorem sum_YamadaPottU_mul (hF : ringChar F ≠ 2)
    (hcard : Fintype.card F % 4 = 3) {t : F} (ht : t ∈ YamadaPottS F) :
    ∑ x ∈ YamadaPottS F, YamadaPottU (t * x) = -1 := by
  let T := {x : F // x ∈ YamadaPottS F}
  let e : T → T := fun x ↦ ⟨t * x.1, YamadaPottS_mul_mem ht x.2⟩
  have ht0 : t ≠ 0 := (mem_YamadaPottS.mp ht).1
  have he : Function.Bijective e := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      dsimp only [e] at hxy
      exact mul_left_cancel₀ ht0 (congrArg Subtype.val hxy)
    · intro y
      have htinv : t⁻¹ ∈ YamadaPottS F := by
        rw [mem_YamadaPottS]
        exact ⟨inv_ne_zero ht0, (mem_YamadaPottS.mp ht).2.inv⟩
      refine ⟨⟨t⁻¹ * y.1, YamadaPottS_mul_mem htinv y.2⟩, ?_⟩
      apply Subtype.ext
      dsimp only [e]
      field_simp
  calc
    ∑ x ∈ YamadaPottS F, YamadaPottU (t * x) =
        ∑ x : T, YamadaPottU (t * x.1) :=
          Finset.sum_subtype (YamadaPottS F) (fun _ ↦ Iff.rfl) _
    _ = ∑ x : T, YamadaPottU x.1 := by
          exact Fintype.sum_bijective e he
            (fun x : T ↦ YamadaPottU (t * x.1))
            (fun x : T ↦ YamadaPottU x.1) (fun _ ↦ rfl)
    _ = ∑ x ∈ YamadaPottS F, YamadaPottU x :=
          (Finset.sum_subtype (YamadaPottS F) (fun _ ↦ Iff.rfl) _).symm
    _ = -1 := by
          simpa only [YamadaPottS, YamadaPottU] using YamadaPott_u_sum (F := F) hF hcard

/-- The overlap `K(t)` of the positive support with its multiplicative
translate. -/
def YamadaPottK (F : Type*) [Field F] [Fintype F] [DecidableEq F] (t : F) : Finset F :=
  (YamadaPottS F).filter fun x ↦ YamadaPottU x = 1 ∧ YamadaPottU (t * x) = 1

/-- Autocorrelation of the skew sequence. -/
def YamadaPottCorrH (F : Type*) [Field F] [Fintype F] [DecidableEq F] (t : F) : ℤ :=
  ∑ x ∈ YamadaPottS F, YamadaPottH x * YamadaPottH (t * x)

private theorem YamadaPottU_corr (hF : ringChar F ≠ 2) {r : ℕ}
    (hcard : Fintype.card F = 4 * r + 3) {t : F}
    (ht : t ∈ YamadaPottS F) :
    ∑ x ∈ YamadaPottS F, YamadaPottU x * YamadaPottU (t * x) =
      4 * ((YamadaPottK F t).card : ℤ) + 1 - 2 * r := by
  have hmod : Fintype.card F % 4 = 3 := by omega
  have hS := card_YamadaPottS (F := F) hF hcard
  have hX := card_YamadaPottX (F := F) hF hcard
  have hshift := sum_YamadaPottU_mul (F := F) hF hmod ht
  let i : F → ℤ := fun x ↦ if YamadaPottU x = 1 then 1 else 0
  let j : F → ℤ := fun x ↦ if YamadaPottU (t * x) = 1 then 1 else 0
  have hi : ∑ x ∈ YamadaPottS F, i x = r := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    change ((YamadaPottX F).card : ℤ) = (r : ℤ)
    exact_mod_cast hX
  have hpointi (x : F) (hx : x ∈ YamadaPottS F) :
      YamadaPottU x = 2 * i x - 1 := by
    rcases YamadaPottU_dichotomy (F := F) hF hmod hx with hp | hn
    · simp [i, hp]
    · simp [i, hn]
  have hpointj (x : F) (hx : x ∈ YamadaPottS F) :
      YamadaPottU (t * x) = 2 * j x - 1 := by
    have htx := YamadaPottS_mul_mem ht hx
    rcases YamadaPottU_dichotomy (F := F) hF hmod htx with hp | hn
    · simp [j, hp]
    · simp [j, hn]
  have hj : ∑ x ∈ YamadaPottS F, j x = r := by
    have hrewrite :
        (∑ x ∈ YamadaPottS F, YamadaPottU (t * x)) =
          2 * (∑ x ∈ YamadaPottS F, j x) - ((YamadaPottS F).card : ℤ) := by
      calc
        ∑ x ∈ YamadaPottS F, YamadaPottU (t * x) =
            ∑ x ∈ YamadaPottS F, (2 * j x - 1) := by
              apply sum_congr rfl
              exact hpointj
        _ = _ := by
              rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
              simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hshift, hS] at hrewrite
    norm_num at hrewrite ⊢
    omega
  have hij : ∑ x ∈ YamadaPottS F, i x * j x = ((YamadaPottK F t).card : ℤ) := by
    calc
      ∑ x ∈ YamadaPottS F, i x * j x =
          ∑ x ∈ YamadaPottS F,
            if YamadaPottU x = 1 ∧ YamadaPottU (t * x) = 1 then (1 : ℤ) else 0 := by
              apply sum_congr rfl
              intro x _
              by_cases hp : YamadaPottU x = 1 <;>
                by_cases hq : YamadaPottU (t * x) = 1 <;> simp [i, j, hp, hq]
      _ = ((YamadaPottK F t).card : ℤ) := by
              rw [← Finset.sum_filter]
              simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
              rfl
  calc
    ∑ x ∈ YamadaPottS F, YamadaPottU x * YamadaPottU (t * x) =
        ∑ x ∈ YamadaPottS F, (2 * i x - 1) * (2 * j x - 1) := by
          apply sum_congr rfl
          intro x hx
          rw [hpointi x hx, hpointj x hx]
    _ = ∑ x ∈ YamadaPottS F,
          (4 * (i x * j x) - 2 * i x - 2 * j x + 1) := by
          apply sum_congr rfl
          intro x _
          ring
    _ = 4 * (∑ x ∈ YamadaPottS F, i x * j x) -
          2 * (∑ x ∈ YamadaPottS F, i x) -
          2 * (∑ x ∈ YamadaPottS F, j x) + ((YamadaPottS F).card : ℤ) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
          simp only [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = _ := by rw [hi, hj, hij, hS]; push_cast; ring

/-- The Yamada--Pott correlation identity `H(t)+4K(t)=m-4`, written with
`m=2r+1` and hence right-hand side `2r-3`. -/
theorem YamadaPott_correlation_identity (hF : ringChar F ≠ 2) {r : ℕ}
    (hcard : Fintype.card F = 4 * r + 3) {t : F}
    (ht : t ∈ YamadaPottS F) (ht1 : t ≠ 1) :
    YamadaPottCorrH F t + 4 * ((YamadaPottK F t).card : ℤ) = 2 * r - 3 := by
  have hmod : Fintype.card F % 4 = 3 := by omega
  have ht0 : t ≠ 0 := (mem_YamadaPottS.mp ht).1
  have htsq : quadraticChar F t = 1 :=
    (quadraticChar_one_iff_isSquare ht0).mpr (mem_YamadaPottS.mp ht).2
  have hpair := YamadaPott_square_subgroup_sum (F := F) hF hmod ht0 ht1 htsq
  have hpair' :
      (∑ x ∈ YamadaPottS F,
        (YamadaPottU x * YamadaPottU (t * x) +
          YamadaPottH x * YamadaPottH (t * x))) = -2 := by
    simpa only [YamadaPottS, YamadaPottU, YamadaPottH, map_mul] using hpair
  rw [Finset.sum_add_distrib] at hpair'
  have hu := YamadaPottU_corr (F := F) hF hcard ht
  rw [hu] at hpair'
  rw [YamadaPottCorrH]
  linarith

/-- The auxiliary set `E={0}∪ X∪(-X)`. -/
def YamadaPottE (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset F :=
  insert 0 (YamadaPottX F ∪ (YamadaPottX F).image Neg.neg)

/-- The complementary Yamada--Pott difference set. -/
def YamadaPottD (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset F :=
  Finset.univ \ YamadaPottE F

private theorem neg_not_mem_YamadaPottS (hF : ringChar F ≠ 2)
    (hcard : Fintype.card F % 4 = 3) {x : F} (hx : x ∈ YamadaPottS F) :
    -x ∉ YamadaPottS F := by
  intro hnx
  have hx0 := (mem_YamadaPottS.mp hx).1
  have hnx0 := (mem_YamadaPottS.mp hnx).1
  have hcx : quadraticChar F x = 1 :=
    (quadraticChar_one_iff_isSquare hx0).mpr (mem_YamadaPottS.mp hx).2
  have hcnx : quadraticChar F (-x) = 1 :=
    (quadraticChar_one_iff_isSquare hnx0).mpr (mem_YamadaPottS.mp hnx).2
  have hcneg := quadraticChar_neg_one_of_card_mod_four_eq_three (F := F) hF hcard
  rw [show (-x : F) = (-1) * x by ring, map_mul, hcneg, hcx] at hcnx
  norm_num at hcnx

/-- The auxiliary set has size `m=2r+1`. -/
theorem card_YamadaPottE (hF : ringChar F ≠ 2) {r : ℕ}
    (hcard : Fintype.card F = 4 * r + 3) : (YamadaPottE F).card = 2 * r + 1 := by
  have hmod : Fintype.card F % 4 = 3 := by omega
  have hX := card_YamadaPottX (F := F) hF hcard
  have hzeroX : (0 : F) ∉ YamadaPottX F := by simp
  have hzeroNeg : (0 : F) ∉ (YamadaPottX F).image Neg.neg := by simp
  have hdisj : Disjoint (YamadaPottX F) ((YamadaPottX F).image Neg.neg) := by
    rw [Finset.disjoint_left]
    intro x hxX hxNeg
    rw [Finset.mem_image] at hxNeg
    obtain ⟨y, hyX, hy⟩ := hxNeg
    have hyS := (mem_YamadaPottX.mp hyX).1
    have hnot := neg_not_mem_YamadaPottS (F := F) hF hmod hyS
    apply hnot
    rw [hy]
    exact (mem_YamadaPottX.mp hxX).1
  rw [YamadaPottE, Finset.card_insert_of_notMem]
  · rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ neg_injective, hX]
    omega
  · simp only [Finset.mem_union, hzeroX, hzeroNeg, or_self, not_false_eq_true]

/-- The complementary set has size `m+1=2r+2`. -/
theorem card_YamadaPottD (hF : ringChar F ≠ 2) {r : ℕ}
    (hcard : Fintype.card F = 4 * r + 3) : (YamadaPottD F).card = 2 * r + 2 := by
  rw [YamadaPottD, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    card_YamadaPottE (F := F) hF hcard, hcard]
  omega

/-- Multiplicative overlap of `E`. -/
def YamadaPottEOverlap (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (t : F) : Finset F :=
  (YamadaPottE F).filter fun x ↦ t * x ∈ YamadaPottE F

/-- Multiplicative overlap `I(t)=|D∩t⁻¹D|`. -/
def YamadaPottI (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (t : F) : ℕ :=
  ((YamadaPottD F).filter fun x ↦ t * x ∈ YamadaPottD F).card

@[simp] theorem mem_YamadaPottE {x : F} :
    x ∈ YamadaPottE F ↔ x = 0 ∨ x ∈ YamadaPottX F ∨ -x ∈ YamadaPottX F := by
  rw [YamadaPottE, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro (hx0 | hxX | ⟨a, haX, hax⟩)
    · exact Or.inl hx0
    · exact Or.inr (Or.inl hxX)
    · right; right
      have : -x = a := by rw [← hax, neg_neg]
      rwa [this]
  · rintro (hx0 | hxX | hnxX)
    · exact Or.inl hx0
    · exact Or.inr (Or.inl hxX)
    · right; right
      exact ⟨-x, hnxX, neg_neg x⟩

private theorem YamadaPottEOverlap_eq (hF : ringChar F ≠ 2)
    (hcard : Fintype.card F % 4 = 3) {t : F} (ht : t ∈ YamadaPottS F) :
    YamadaPottEOverlap F t =
      insert 0 (YamadaPottK F t ∪ (YamadaPottK F t).image Neg.neg) := by
  ext x
  simp only [YamadaPottEOverlap, Finset.mem_filter, mem_YamadaPottE,
    Finset.mem_insert, Finset.mem_union, Finset.mem_image, YamadaPottK,
    mem_YamadaPottX, and_assoc]
  have hnegS : ∀ {z : F}, z ∈ YamadaPottS F → -z ∉ YamadaPottS F :=
    fun {_} hz ↦ neg_not_mem_YamadaPottS (F := F) hF hcard hz
  constructor
  · rintro ⟨hxE, htxE⟩
    rcases hxE with hx0 | hxpos | hxneg
    · exact Or.inl hx0
    · rcases htxE with htx0 | htxpos | htxneg
      · exfalso
        apply (mem_YamadaPottS.mp hxpos.1).1
        apply mul_left_cancel₀ (mem_YamadaPottS.mp ht).1
        simp [htx0]
      · exact Or.inr (Or.inl ⟨hxpos.1, hxpos.2, htxpos.2⟩)
      · exfalso
        have htxS := YamadaPottS_mul_mem ht hxpos.1
        exact hnegS htxS htxneg.1
    · rcases htxE with htx0 | htxpos | htxneg
      · exfalso
        have hnx0 := (mem_YamadaPottS.mp hxneg.1).1
        apply hnx0
        apply mul_left_cancel₀ (mem_YamadaPottS.mp ht).1
        simp [htx0]
      · exfalso
        have hn_tx_S := YamadaPottS_mul_mem ht hxneg.1
        have heq : t * (-x) = -(t * x) := by ring
        rw [heq] at hn_tx_S
        exact hnegS htxpos.1 hn_tx_S
      · have hut : YamadaPottU (t * (-x)) = 1 := by
          have heq : t * (-x) = -(t * x) := by ring
          rw [heq]
          exact htxneg.2
        exact Or.inr (Or.inr ⟨-x, hxneg.1, hxneg.2, hut, neg_neg x⟩)
  · rintro (hx0 | ⟨hxS, hux, hutx⟩ | ⟨y, hyS, huy, huty, hy⟩)
    · subst x
      simp
    · exact ⟨Or.inr (Or.inl ⟨hxS, hux⟩),
        Or.inr (Or.inl ⟨YamadaPottS_mul_mem ht hxS, hutx⟩)⟩
    · subst x
      constructor
      · exact Or.inr (Or.inr ⟨by simpa using hyS, by simpa using huy⟩)
      · right; right
        have heq : -(t * -y) = t * y := by ring
        rw [heq]
        exact ⟨YamadaPottS_mul_mem ht hyS, huty⟩

/-- The `E` overlap is `1+2K(t)`. -/
theorem card_YamadaPottEOverlap (hF : ringChar F ≠ 2)
    (hcard : Fintype.card F % 4 = 3) {t : F} (ht : t ∈ YamadaPottS F) :
    (YamadaPottEOverlap F t).card = 1 + 2 * (YamadaPottK F t).card := by
  have hzero : (0 : F) ∉ YamadaPottK F t := by simp [YamadaPottK]
  have hzeroNeg : (0 : F) ∉ (YamadaPottK F t).image Neg.neg := by
    simpa using hzero
  have hdisj : Disjoint (YamadaPottK F t) ((YamadaPottK F t).image Neg.neg) := by
    rw [Finset.disjoint_left]
    intro x hxK hxNeg
    rw [Finset.mem_image] at hxNeg
    obtain ⟨y, hyK, hy⟩ := hxNeg
    have hxS : x ∈ YamadaPottS F := (Finset.mem_filter.mp hxK).1
    have hyS : y ∈ YamadaPottS F := (Finset.mem_filter.mp hyK).1
    have hnot := neg_not_mem_YamadaPottS (F := F) hF hcard hyS
    apply hnot
    rw [hy]
    exact hxS
  rw [YamadaPottEOverlap_eq (F := F) hF hcard ht, Finset.card_insert_of_notMem]
  · rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ neg_injective]
    omega
  · simp only [Finset.mem_union, hzero, hzeroNeg, or_self, not_false_eq_true]

/-- Inclusion--exclusion for the complement gives `I(t)=2+2K(t)`. -/
theorem YamadaPott_I_eq (hF : ringChar F ≠ 2) {r : ℕ}
    (hcard : Fintype.card F = 4 * r + 3) {t : F} (ht : t ∈ YamadaPottS F) :
    YamadaPottI F t = 2 + 2 * (YamadaPottK F t).card := by
  let P : Finset F := Finset.univ.filter fun x ↦ t * x ∈ YamadaPottE F
  have ht0 : t ≠ 0 := (mem_YamadaPottS.mp ht).1
  have hPcard : P.card = (YamadaPottE F).card := by
    apply Finset.card_equiv (Equiv.mulLeft₀ t ht0)
    intro x
    simp only [P, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.mulLeft₀_apply]
  have hinter : YamadaPottE F ∩ P = YamadaPottEOverlap F t := by
    ext x
    simp only [Finset.mem_inter, P, Finset.mem_filter, Finset.mem_univ, true_and,
      YamadaPottEOverlap]
  have hfilter :
      (YamadaPottD F).filter (fun x ↦ t * x ∈ YamadaPottD F) =
        Finset.univ \ (YamadaPottE F ∪ P) := by
    ext x
    simp only [YamadaPottD, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_union, P]
    aesop
  have hunion := Finset.card_union_add_card_inter (YamadaPottE F) P
  rw [hinter, hPcard] at hunion
  have hmod : Fintype.card F % 4 = 3 := by omega
  have hE := card_YamadaPottE (F := F) hF hcard
  have hEO := card_YamadaPottEOverlap (F := F) hF hmod ht
  rw [YamadaPottI, hfilter, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, hcard]
  omega

/-- Final source identity in the form used by the difference lift:
`H(t)+2I(t)=m`, with `m=2r+1`. -/
theorem YamadaPott_H_add_two_I (hF : ringChar F ≠ 2) {r : ℕ}
    (hcard : Fintype.card F = 4 * r + 3) {t : F}
    (ht : t ∈ YamadaPottS F) (ht1 : t ≠ 1) :
    YamadaPottCorrH F t + 2 * (YamadaPottI F t : ℤ) = 2 * r + 1 := by
  have hc := YamadaPott_correlation_identity (F := F) hF hcard ht ht1
  have hi := YamadaPott_I_eq (F := F) hF hcard ht
  rw [hi]
  push_cast
  linarith

end QuadraticCharacter

end BookS3
