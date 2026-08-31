import FiniteKakeyaS3.Selector
import FiniteKakeyaS3.MixedSums

/-!
# The square-footprint overlap

This file carries out the exact three-indicator expansion in the proof of
Spotlight 3 and derives the uniform coarse estimate for the overlap of the
non-pole line union with the scaled square footprint.
-/

namespace FiniteKakeyaS3

open scoped BigOperators
open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- For nonzero `lambda`, membership in `lambda Q` is detected by whether
`x / lambda` is a square. -/
theorem mem_scaledSquareSet_iff_isSquare_div {lambda x : F}
    (hlambda : lambda ≠ 0) :
    x ∈ scaledSquareSet lambda ↔ IsSquare (x / lambda) := by
  rw [mem_scaledSquareSet]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t, ?_⟩
    field_simp
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    calc
      lambda * t ^ 2 = lambda * (t * t) := by rw [pow_two]
      _ = lambda * (x / lambda) := by rw [ht]
      _ = x := mul_div_cancel₀ x hlambda

private theorem zeroIndicator_div (hlambda : lambda ≠ 0) (x : F) :
    zeroIndicator (x / lambda) = zeroIndicator x := by
  by_cases hx : x = 0
  · simp [zeroIndicator, hx]
  · have hd : x / lambda ≠ 0 := div_ne_zero hx hlambda
    simp [zeroIndicator, hx, hd]

/-- The exact three-square indicator expansion for the selector overlap
`O* = |selector ∩ (lambda Q)²|`. -/
theorem selector_overlap_indicator_expansion (lambda A B r : F)
    (hlambda : lambda ≠ 0) :
    8 * (((selector A B r ∩ scaledSquareFootprint lambda).card : ℤ)) =
      ∑ y : F, ∑ z : F,
        (1 + yChar F lambda y + zeroIndicator y) *
        (1 + zChar F lambda z + zeroIndicator z) *
        (1 + xChar F A B r y z +
          zeroIndicator (selectorDiscriminant A B r y z)) := by
  have hinter :
      selector A B r ∩ scaledSquareFootprint lambda =
        (univ : Finset (F × F)).filter fun q ↦
          IsSquare (q.1 / lambda) ∧ IsSquare (q.2 / lambda) ∧
            IsSquare (selectorDiscriminant A B r q.1 q.2) := by
    ext q
    simp only [mem_inter, mem_selector, scaledSquareFootprint, mem_product,
      mem_filter, mem_univ, true_and]
    rw [mem_scaledSquareSet_iff_isSquare_div hlambda,
      mem_scaledSquareSet_iff_isSquare_div hlambda]
    tauto
  rw [hinter, card_filter]
  push_cast
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro z _
  rw [show 1 + yChar F lambda y + zeroIndicator y =
      2 * squareIndicator (y / lambda) by
        simpa [yChar, zeroIndicator_div hlambda] using
          (two_mul_squareIndicator (F := F) (y / lambda)).symm,
    show 1 + zChar F lambda z + zeroIndicator z =
      2 * squareIndicator (z / lambda) by
        simpa [zChar, zeroIndicator_div hlambda] using
          (two_mul_squareIndicator (F := F) (z / lambda)).symm,
    show 1 + xChar F A B r y z +
        zeroIndicator (selectorDiscriminant A B r y z) =
      2 * squareIndicator (selectorDiscriminant A B r y z) by
        simpa [xChar] using
          (two_mul_squareIndicator (F := F)
            (selectorDiscriminant A B r y z)).symm]
  by_cases hy : IsSquare (y / lambda) <;>
    by_cases hz : IsSquare (z / lambda) <;>
      by_cases hD : IsSquare (selectorDiscriminant A B r y z) <;>
        simp [squareIndicator, hy, hz, hD]

private theorem abs_quadraticChar_le_one (x : F) :
    |quadraticChar F x| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · rcases quadraticChar_dichotomy (F := F) hx with h | h <;> simp [h]

private theorem coordinate_factor_nonneg (lambda x : F) :
    0 ≤ 1 + quadraticChar F (x / lambda) + zeroIndicator x := by
  by_cases hx : x / lambda = 0
  · rw [(quadraticChar_eq_zero_iff (F := F)).2 hx]
    by_cases hzero : x = 0 <;> simp [zeroIndicator, hzero]
  · rcases quadraticChar_dichotomy (F := F) hx with h | h <;>
      rw [h] <;> by_cases hzero : x = 0 <;> simp [zeroIndicator, hzero]

private theorem sum_char_div_eq_zero (hchar : ringChar F ≠ 2)
    {lambda : F} (hlambda : lambda ≠ 0) :
    (∑ x : F, quadraticChar F (x / lambda)) = 0 := by
  simpa [div_eq_mul_inv, mul_comm] using
    sum_quadratic_affine F hchar lambda⁻¹ 0 (inv_ne_zero hlambda)

private theorem sum_zeroIndicator :
    (∑ x : F, zeroIndicator x) = 1 := by
  simp [zeroIndicator]

private theorem sum_coordinate_factor (hchar : ringChar F ≠ 2)
    {lambda : F} (hlambda : lambda ≠ 0) :
    (∑ x : F, (1 + quadraticChar F (x / lambda) + zeroIndicator x)) =
      (Fintype.card F : ℤ) + 1 := by
  rw [sum_add_distrib, sum_add_distrib, sum_char_div_eq_zero hchar hlambda,
    sum_zeroIndicator]
  simp

private theorem sum_one_add_char_div (hchar : ringChar F ≠ 2)
    {lambda : F} (hlambda : lambda ≠ 0) :
    (∑ x : F, (1 + quadraticChar F (x / lambda))) =
      (Fintype.card F : ℤ) := by
  rw [sum_add_distrib, sum_char_div_eq_zero hchar hlambda]
  simp

private theorem abs_sum_coordinate_factor_mul_char_le (hchar : ringChar F ≠ 2)
    {lambda : F} (hlambda : lambda ≠ 0) (f : F → F) :
    |(∑ x : F, (1 + quadraticChar F (x / lambda) + zeroIndicator x) *
        quadraticChar F (f x))| ≤ (Fintype.card F : ℤ) + 1 := by
  calc
    |(∑ x : F, (1 + quadraticChar F (x / lambda) + zeroIndicator x) *
        quadraticChar F (f x))| ≤
        ∑ x : F, |(1 + quadraticChar F (x / lambda) + zeroIndicator x) *
          quadraticChar F (f x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : F, (1 + quadraticChar F (x / lambda) + zeroIndicator x) := by
      apply sum_le_sum
      intro x _
      rw [abs_mul, abs_of_nonneg (coordinate_factor_nonneg lambda x)]
      have h := abs_quadraticChar_le_one (f x)
      have hn := coordinate_factor_nonneg lambda x
      nlinarith
    _ = (Fintype.card F : ℤ) + 1 := sum_coordinate_factor hchar hlambda

private theorem abs_sum_one_add_char_mul_char_le (hchar : ringChar F ≠ 2)
    {lambda : F} (hlambda : lambda ≠ 0) (f : F → F) :
    |(∑ x : F, (1 + quadraticChar F (x / lambda)) *
        quadraticChar F (f x))| ≤ (Fintype.card F : ℤ) := by
  calc
    |(∑ x : F, (1 + quadraticChar F (x / lambda)) *
        quadraticChar F (f x))| ≤
        ∑ x : F, |(1 + quadraticChar F (x / lambda)) *
          quadraticChar F (f x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x : F, (1 + quadraticChar F (x / lambda)) := by
      apply sum_le_sum
      intro x _
      rw [abs_mul]
      have hc := abs_quadraticChar_le_one (x / lambda)
      have hf := abs_quadraticChar_le_one (f x)
      have hc' := (abs_le.mp hc).1
      have hn : 0 ≤ 1 + quadraticChar F (x / lambda) := by omega
      rw [abs_of_nonneg hn]
      nlinarith
    _ = (Fintype.card F : ℤ) := sum_one_add_char_div hchar hlambda

private theorem zero_locus_block_eq_four_mul_card (lambda A B r : F)
    (hlambda : lambda ≠ 0) :
    (∑ y : F, ∑ z : F,
      (1 + yChar F lambda y + zeroIndicator y) *
      (1 + zChar F lambda z + zeroIndicator z) *
      zeroIndicator (selectorDiscriminant A B r y z)) =
      4 * (((selectorZeroLocus A B r ∩ scaledSquareFootprint lambda).card : ℤ)) := by
  have hinter :
      selectorZeroLocus A B r ∩ scaledSquareFootprint lambda =
        (univ : Finset (F × F)).filter fun q ↦
          IsSquare (q.1 / lambda) ∧ IsSquare (q.2 / lambda) ∧
            selectorDiscriminant A B r q.1 q.2 = 0 := by
    ext q
    simp only [selectorZeroLocus, mem_inter, mem_filter, mem_univ, true_and,
      scaledSquareFootprint, mem_product]
    rw [mem_scaledSquareSet_iff_isSquare_div hlambda,
      mem_scaledSquareSet_iff_isSquare_div hlambda]
    tauto
  rw [hinter, card_filter]
  push_cast
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply sum_congr rfl
  intro y _
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro z _
  rw [show 1 + yChar F lambda y + zeroIndicator y =
      2 * squareIndicator (y / lambda) by
        simpa [yChar, zeroIndicator_div hlambda] using
          (two_mul_squareIndicator (F := F) (y / lambda)).symm,
    show 1 + zChar F lambda z + zeroIndicator z =
      2 * squareIndicator (z / lambda) by
        simpa [zChar, zeroIndicator_div hlambda] using
          (two_mul_squareIndicator (F := F) (z / lambda)).symm]
  by_cases hy : IsSquare (y / lambda) <;>
    by_cases hz : IsSquare (z / lambda) <;>
      by_cases hD : selectorDiscriminant A B r y z = 0 <;>
        simp [squareIndicator, zeroIndicator, hy, hz, hD]

/-- The selector version of the overlap differs from `q²/8` by at most the
sum of the base, mixed-character, coordinate, and zero-locus errors. -/
theorem abs_eight_mul_card_selector_overlap_sub_sq_le (hchar : ringChar F ≠ 2)
    {lambda A B r : F} (hlambda : lambda ≠ 0)
    (hD : familyD A B r ≠ 0) :
    |8 * (((selector A B r ∩ scaledSquareFootprint lambda).card : ℤ)) -
        (Fintype.card F : ℤ) ^ 2| ≤
      15 * (Fintype.card F : ℤ) + 2 := by
  let q : ℤ := Fintype.card F
  let Y : F → ℤ := fun y ↦ yChar F lambda y
  let Z : F → ℤ := fun z ↦ zChar F lambda z
  let X : F → F → ℤ := fun y z ↦ xChar F A B r y z
  let ey : F → ℤ := zeroIndicator
  let ed : F → F → ℤ := fun y z ↦
    zeroIndicator (selectorDiscriminant A B r y z)
  let base : ℤ := ∑ y : F, ∑ z : F, (1 + Y y + ey y) * (1 + Z z + ey z)
  let xb : ℤ := ∑ y : F, ∑ z : F,
    (1 + Y y + ey y) * (1 + Z z + ey z) * X y z
  let db : ℤ := ∑ y : F, ∑ z : F,
    (1 + Y y + ey y) * (1 + Z z + ey z) * ed y z
  have hexpand :
      8 * (((selector A B r ∩ scaledSquareFootprint lambda).card : ℤ)) =
        base + xb + db := by
    rw [selector_overlap_indicator_expansion lambda A B r hlambda]
    dsimp [base, xb, db, Y, Z, X, ey, ed]
    rw [show (∑ y : F, ∑ z : F,
        (1 + yChar F lambda y + zeroIndicator y) *
        (1 + zChar F lambda z + zeroIndicator z) *
        (1 + xChar F A B r y z +
          zeroIndicator (selectorDiscriminant A B r y z))) =
      ∑ y : F, ∑ z : F,
        ((1 + yChar F lambda y + zeroIndicator y) *
          (1 + zChar F lambda z + zeroIndicator z) +
         (1 + yChar F lambda y + zeroIndicator y) *
          (1 + zChar F lambda z + zeroIndicator z) * xChar F A B r y z +
         (1 + yChar F lambda y + zeroIndicator y) *
          (1 + zChar F lambda z + zeroIndicator z) *
            zeroIndicator (selectorDiscriminant A B r y z)) by
        apply sum_congr rfl
        intro y _
        apply sum_congr rfl
        intro z _
        ring]
    simp only [sum_add_distrib]
  have hbase : base = (q + 1) ^ 2 := by
    dsimp [base, Y, Z, ey, q, yChar, zChar]
    have hcoord := sum_coordinate_factor (F := F) hchar hlambda
    change (∑ x : F, (1 + quadraticCharFun F (x / lambda) + zeroIndicator x)) =
      (Fintype.card F : ℤ) + 1 at hcoord
    calc
      (∑ y : F, ∑ z : F,
          (1 + quadraticCharFun F (y / lambda) + zeroIndicator y) *
            (1 + quadraticCharFun F (z / lambda) + zeroIndicator z)) =
          ∑ y : F, (1 + quadraticCharFun F (y / lambda) + zeroIndicator y) *
            ((Fintype.card F : ℤ) + 1) := by
        apply sum_congr rfl
        intro y _
        rw [← Finset.mul_sum, hcoord]
      _ = ((Fintype.card F : ℤ) + 1) * ((Fintype.card F : ℤ) + 1) := by
        rw [← Finset.sum_mul, hcoord]
      _ = ((Fintype.card F : ℤ) + 1) ^ 2 := by ring
  have hbasedev : |base - q ^ 2| ≤ 2 * q + 1 := by
    rw [hbase]
    have hq : 0 ≤ q := by dsimp [q]; positivity
    rw [abs_of_nonneg (by nlinarith)]
    ring_nf
    rfl
  let sx : ℤ := ∑ y : F, ∑ z : F, X y z
  let syx : ℤ := ∑ y : F, ∑ z : F, Y y * X y z
  let szx : ℤ := ∑ y : F, ∑ z : F, Z z * X y z
  let syzx : ℤ := ∑ y : F, ∑ z : F, Y y * Z z * X y z
  let srow : ℤ := ∑ z : F, (1 + Z z + ey z) * X 0 z
  let scol : ℤ := ∑ y : F, (1 + Y y) * X y 0
  have hxb : xb = sx + syx + szx + syzx + srow + scol := by
    dsimp [xb, sx, syx, szx, syzx, srow, scol]
    rw [show (∑ y : F, ∑ z : F,
        (1 + Y y + ey y) * (1 + Z z + ey z) * X y z) =
      ∑ y : F, ∑ z : F,
        (X y z + Y y * X y z + Z z * X y z + Y y * Z z * X y z +
          ey y * (1 + Z z + ey z) * X y z +
          ey z * (1 + Y y) * X y z) by
        apply sum_congr rfl
        intro y _
        apply sum_congr rfl
        intro z _
        ring]
    simp only [sum_add_distrib]
    simp [ey, zeroIndicator]
  have hsx : sx = 0 := by
    exact sum_xChar_eq_zero F hchar hD
  have hsyx : syx = 0 := by
    exact sum_yChar_mul_xChar_eq_zero F hchar hlambda hD
  have hszx : |szx| ≤ 3 * q := by
    exact abs_sum_zChar_mul_xChar_le_three_card F hchar hlambda hD
  have hsyzx : |syzx| ≤ 4 * q := by
    exact abs_sum_yChar_mul_zChar_mul_xChar_le_four_card F hchar hlambda hD
  have hsrow : |srow| ≤ q + 1 := by
    dsimp [srow, Z, ey, X, zChar, xChar, q]
    exact abs_sum_coordinate_factor_mul_char_le hchar hlambda
      (fun z ↦ selectorDiscriminant A B r 0 z)
  have hscol : |scol| ≤ q := by
    dsimp [scol, Y, X, yChar, xChar, q]
    exact abs_sum_one_add_char_mul_char_le hchar hlambda
      (fun y ↦ selectorDiscriminant A B r y 0)
  have hxbabs : |xb| ≤ 9 * q + 1 := by
    rw [hxb, hsx, hsyx]
    simp only [zero_add]
    have htri : |szx + syzx + srow + scol| ≤
        |szx| + |syzx| + |srow| + |scol| := by
      calc
        |szx + syzx + srow + scol| ≤ |szx + syzx + srow| + |scol| :=
          abs_add_le _ _
        _ ≤ (|szx + syzx| + |srow|) + |scol| := by
          gcongr
          exact abs_add_le _ _
        _ ≤ (|szx| + |syzx|) + |srow| + |scol| := by
          gcongr
          exact abs_add_le _ _
    omega
  have hdb : 0 ≤ db ∧ db ≤ 4 * q := by
    have heq : db =
        4 * (((selectorZeroLocus A B r ∩ scaledSquareFootprint lambda).card : ℤ)) := by
      exact zero_locus_block_eq_four_mul_card lambda A B r hlambda
    rw [heq]
    constructor
    · positivity
    · have hc := card_le_card
          (inter_subset_left : selectorZeroLocus A B r ∩
            scaledSquareFootprint lambda ⊆ selectorZeroLocus A B r)
      rw [card_selectorZeroLocus hchar A B r hD] at hc
      have hc' : (((selectorZeroLocus A B r ∩
          scaledSquareFootprint lambda).card : ℤ)) ≤ q := by
        dsimp [q]
        exact_mod_cast hc
      nlinarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  rw [hexpand]
  have htri : |base + xb + db - q ^ 2| ≤
      |base - q ^ 2| + |xb| + |db| := by
    rw [show base + xb + db - q ^ 2 = (base - q ^ 2) + xb + db by ring]
    calc
      |base - q ^ 2 + xb + db| ≤ |base - q ^ 2 + xb| + |db| := abs_add_le _ _
      _ ≤ (|base - q ^ 2| + |xb|) + |db| := by
        gcongr
        exact abs_add_le _ _
  rw [abs_of_nonneg hdb.1] at htri
  dsimp [q] at *
  omega

/-- Spotlight 3's coarse overlap estimate for the actual non-pole line union.
The extra constant `8` is precisely the worst-case cost of erasing the
selector's exceptional point `(0,A)`. -/
theorem abs_eight_mul_card_finiteLine_overlap_sub_sq_le
    (hchar : ringChar F ≠ 2) {lambda A B r : F}
    (hlambda : lambda ≠ 0) (hD : familyD A B r ≠ 0) :
    |8 * (((finiteLineUnion A B r ∩ scaledSquareFootprint lambda).card : ℤ)) -
        (Fintype.card F : ℤ) ^ 2| ≤
      15 * (Fintype.card F : ℤ) + 10 := by
  let actual := finiteLineUnion A B r ∩ scaledSquareFootprint lambda
  let selected := selector A B r ∩ scaledSquareFootprint lambda
  let exceptional : F × F := (0, A)
  have herase : actual = selected.erase exceptional := by
    dsimp [actual, selected, exceptional]
    rw [finiteLineUnion_eq_selector_erase hchar A B r hD]
    ext q
    simp only [mem_inter, mem_erase]
    tauto
  have hle : actual.card ≤ selected.card := by
    rw [herase]
    exact card_erase_le
  have hle' : selected.card ≤ actual.card + 1 := by
    rw [herase]
    by_cases hmem : exceptional ∈ selected
    · rw [card_erase_add_one hmem]
    · rw [erase_eq_of_notMem hmem]
      omega
  have hclose :
      |(8 * (actual.card : ℤ) - (Fintype.card F : ℤ) ^ 2) -
        (8 * (selected.card : ℤ) - (Fintype.card F : ℤ) ^ 2)| ≤ 8 := by
    norm_num only [sub_sub_sub_cancel_right]
    push_cast at hle hle'
    rw [abs_le]
    omega
  have hselected :=
    abs_eight_mul_card_selector_overlap_sub_sq_le (F := F) hchar hlambda hD
  change |8 * (actual.card : ℤ) - (Fintype.card F : ℤ) ^ 2| ≤ _
  change |8 * (selected.card : ℤ) - (Fintype.card F : ℤ) ^ 2| ≤ _ at hselected
  have htri :
      |8 * (actual.card : ℤ) - (Fintype.card F : ℤ) ^ 2| ≤
        |8 * (selected.card : ℤ) - (Fintype.card F : ℤ) ^ 2| +
        |(8 * (actual.card : ℤ) - (Fintype.card F : ℤ) ^ 2) -
          (8 * (selected.card : ℤ) - (Fintype.card F : ℤ) ^ 2)| := by
    have := abs_add_le
      (8 * (selected.card : ℤ) - (Fintype.card F : ℤ) ^ 2)
      ((8 * (actual.card : ℤ) - (Fintype.card F : ℤ) ^ 2) -
        (8 * (selected.card : ℤ) - (Fintype.card F : ℤ) ^ 2))
    convert this using 1 <;> ring
  omega

end FiniteKakeyaS3
