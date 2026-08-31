import FiniteKakeyaS3.Definitions

/-!
# Geometry of the finite one-pole part

The main results give the exact discriminant elimination away from `y=0` and
identify the one exceptional point on the zero row.
-/

namespace FiniteKakeyaS3

open Finset

variable {F : Type*} [Fintype F] [Field F] [DecidableEq F]

lemma beta_eq_A_add_div_D (A B r c : F) (hc : c ≠ r) :
    beta A B r c = A + familyD A B r / (c - r) := by
  rw [beta, familyD]
  apply (div_eq_iff (sub_ne_zero.mpr hc)).2
  field_simp [sub_ne_zero.mpr hc]
  ring

/-- Direct elimination: a point on `L_c`, after putting `x=c-r`, satisfies
the quadratic `y x² - (z-A-ry)x + D = 0`. -/
lemma finiteLine_elimination (A B r c y z : F) (hc : c ≠ r)
    (hz : z = c * y + beta A B r c) :
    y * (c - r) ^ 2 - (z - A - r * y) * (c - r) + familyD A B r = 0 := by
  rw [beta_eq_A_add_div_D A B r c hc] at hz
  have hcr : c - r ≠ 0 := sub_ne_zero.mpr hc
  field_simp [hcr] at hz
  simp only [familyD] at hz ⊢
  linear_combination -hz

/-- The elementary quadratic-discriminant criterion in the exact form needed
for the selector. -/
lemma exists_nonzero_root_iff_isSquare_discriminant
    (y t D : F) (hy : y ≠ 0) (hD : D ≠ 0) (h2 : (2 : F) ≠ 0) :
    (∃ x : F, x ≠ 0 ∧ y * x ^ 2 - t * x + D = 0) ↔
      IsSquare (t ^ 2 - 4 * D * y) := by
  constructor
  · rintro ⟨x, hx, hquad⟩
    refine ⟨2 * y * x - t, ?_⟩
    change t ^ 2 - 4 * D * y = (2 * y * x - t) * (2 * y * x - t)
    linear_combination -4 * y * hquad
  · rintro ⟨w, hw⟩
    have hden : 2 * y ≠ 0 := mul_ne_zero h2 hy
    let x : F := (t + w) / (2 * y)
    have hx : x ≠ 0 := by
      intro hx0
      have htw : t + w = 0 := (div_eq_zero_iff).mp hx0 |>.resolve_right hden
      have wy : 4 * D * y = 0 := by
        have hwt : w = -t := by linear_combination htw
        rw [hwt] at hw
        linear_combination -hw
      have h4 : (4 : F) ≠ 0 := by
        convert mul_ne_zero h2 h2 using 1 <;> norm_num
      exact (mul_ne_zero (mul_ne_zero h4 hD) hy) wy
    refine ⟨x, hx, ?_⟩
    dsimp [x]
    field_simp [hden]
    linear_combination -hw

/-- Lemma 4.1's selector statement: off `y=0`, the finite one-pole line union
is exactly the square-discriminant selector. -/
theorem finiteLine_selector_iff (A B r y z : F)
    (hD : familyD A B r ≠ 0) (hy : y ≠ 0) (h2 : (2 : F) ≠ 0) :
    (y, z) ∈ finiteLineUnion A B r ↔
      IsSquare (selectorDiscriminant A B r y z) := by
  rw [mem_finiteLineUnion]
  change (∃ c : F, c ≠ r ∧ z = c * y + beta A B r c) ↔ _
  unfold selectorDiscriminant
  constructor
  · rintro ⟨c, hc, hz⟩
    rw [exists_nonzero_root_iff_isSquare_discriminant y (z - A - r * y)
      (familyD A B r) hy hD h2 |>.symm]
    exact ⟨c - r, sub_ne_zero.mpr hc, finiteLine_elimination A B r c y z hc hz⟩
  · intro hs
    rw [← exists_nonzero_root_iff_isSquare_discriminant y (z - A - r * y)
      (familyD A B r) hy hD h2] at hs
    obtain ⟨x, hx, hquad⟩ := hs
    refine ⟨r + x, by simpa [add_eq_left] using hx, ?_⟩
    rw [beta_eq_A_add_div_D A B r (r + x) (by simpa [add_eq_left] using hx)]
    have hsolve : z = A + r * y + y * x + familyD A B r / x := by
      field_simp [hx]
      linear_combination -hquad
    rw [hsolve]
    field_simp [hx]
    ring

/-- On `y=0`, the intercept map omits exactly `A`. -/
theorem zero_row_mem_finiteLineUnion_iff (A B r z : F)
    (hD : familyD A B r ≠ 0) :
    (0, z) ∈ finiteLineUnion A B r ↔ z ≠ A := by
  rw [mem_finiteLineUnion]
  constructor
  · rintro ⟨c, hc, hz⟩ hza
    rw [Prod.snd, Prod.fst, mul_zero, zero_add, beta_eq_A_add_div_D A B r c hc] at hz
    rw [hza] at hz
    have hzero : familyD A B r / (c - r) = 0 := by linear_combination -hz
    rcases div_eq_zero_iff.mp hzero with h | h
    · exact hD h
    · exact hc (sub_eq_zero.mp h)
  · intro hzA
    let x : F := familyD A B r / (z - A)
    have hx : x ≠ 0 := div_ne_zero hD (sub_ne_zero.mpr hzA)
    refine ⟨r + x, by simpa [add_eq_left] using hx, ?_⟩
    rw [Prod.snd, Prod.fst, mul_zero, zero_add,
      beta_eq_A_add_div_D A B r (r + x) (by simpa [add_eq_left] using hx)]
    dsimp [x]
    field_simp [hD, sub_ne_zero.mpr hzA]
    ring

end FiniteKakeyaS3
