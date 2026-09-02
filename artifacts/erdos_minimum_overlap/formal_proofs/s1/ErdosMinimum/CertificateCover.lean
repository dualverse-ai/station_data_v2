import ErdosMinimum.Problem

/-!
# Exact aggregation of the Erdős minimum-overlap lower-bound certificate

This file formalizes the last, exact-rational part of Theorem 2.1 in the
paper's verification notebook.  The analytic/directed-interval verifier
supplies four quadratic lower bounds, according to the first moment `m`.
The theorem below checks that they cover `|m| ≤ 1` and all lie strictly above
`0.380552`.
-/

namespace ErdosMinimum

noncomputable section

/-- The decimal lower bound claimed in the paper, interpreted exactly. -/
def claimedLower : ℝ := 380552 / 1000000

/-- A concave quadratic written in the certificate's normalization. -/
def quadratic (c0 a1 a2 m : ℝ) : ℝ := c0 + a1 * m + a2 * m ^ 2 / 2

/-- Exact data printed with outward rounding by the directed MPFI checker. -/
structure VerifiedRow where
  lo : ℝ
  hi : ℝ
  c0 : ℝ
  a1 : ℝ
  a2 : ℝ

/-- What the analytic part of one certificate row establishes for an overlap. -/
def RowApplies (row : VerifiedRow) (M m : ℝ) : Prop :=
  row.lo ≤ m → m ≤ row.hi → quadratic row.c0 row.a1 row.a2 m ≤ M

theorem concaveQuadratic_ge_min_endpoints
    (c0 a1 a2 lo hi m : ℝ)
    (ha2 : a2 ≤ 0) (hlo : lo ≤ m) (hhi : m ≤ hi) :
    min (quadratic c0 a1 a2 lo) (quadratic c0 a1 a2 hi) ≤
      quadratic c0 a1 a2 m := by
  by_cases h : lo = hi
  · subst hi
    have : m = lo := le_antisymm hhi hlo
    subst m
    simp
  · have hlt : lo < hi := lt_of_le_of_ne (le_trans hlo hhi) h
    let t : ℝ := (m - lo) / (hi - lo)
    have hden : 0 < hi - lo := sub_pos.mpr hlt
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hlo) hden.le
    have ht1 : t ≤ 1 := (div_le_one hden).2 (sub_le_sub_right hhi lo)
    have hm : m = (1 - t) * lo + t * hi := by
      dsimp [t]
      field_simp
      ring
    rw [hm]
    have hconcave :
        (1 - t) * quadratic c0 a1 a2 lo + t * quadratic c0 a1 a2 hi ≤
          quadratic c0 a1 a2 ((1 - t) * lo + t * hi) := by
      dsimp [quadratic]
      nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1),
        mul_nonpos_of_nonneg_of_nonpos
          (sq_nonneg (hi - lo)) ha2]
    have hminlo : min (quadratic c0 a1 a2 lo) (quadratic c0 a1 a2 hi) ≤
        quadratic c0 a1 a2 lo := min_le_left _ _
    have hminhi : min (quadratic c0 a1 a2 lo) (quadratic c0 a1 a2 hi) ≤
        quadratic c0 a1 a2 hi := min_le_right _ _
    calc
      min (quadratic c0 a1 a2 lo) (quadratic c0 a1 a2 hi)
          ≤ (1 - t) * quadratic c0 a1 a2 lo + t * quadratic c0 a1 a2 hi := by
            nlinarith
      _ ≤ quadratic c0 a1 a2 ((1 - t) * lo + t * hi) := hconcave

/-- A generic, kernel-checked four-row cover theorem.  The premises are the
four analytic row inequalities; the conclusion is the paper's numerical
lower bound for the overlap represented by `(M,m)`. -/
theorem four_row_cover
    (M m : ℝ)
    (rows : Fin 4 → VerifiedRow)
    (hcover : ∀ x : ℝ, 0 ≤ x → x ≤ 1 → ∃ i, (rows i).lo ≤ x ∧ x ≤ (rows i).hi)
    (hfloor : ∀ i, claimedLower <
      min (quadratic (rows i).c0 (rows i).a1 (rows i).a2 (rows i).lo)
          (quadratic (rows i).c0 (rows i).a1 (rows i).a2 (rows i).hi))
    (hconcave : ∀ i, (rows i).a2 ≤ 0)
    (hrows : ∀ i, RowApplies (rows i) M |m|)
    (hm : |m| ≤ 1) :
    claimedLower < M := by
  obtain ⟨i, hlo, hhi⟩ := hcover |m| (abs_nonneg m) hm
  have hq := concaveQuadratic_ge_min_endpoints
    (rows i).c0 (rows i).a1 (rows i).a2 (rows i).lo (rows i).hi |m|
    (hconcave i) hlo hhi
  exact lt_of_lt_of_le (hfloor i) (le_trans hq (hrows i hlo hhi))

/-! ## Concrete outward-rounded rows

The coefficients below are conservative truncations of the lower endpoints
printed by `mpfi_positive_budget.c`.  Decreasing `c0` and `a1` (on the
nonnegative moment range), and making the negative `a2` slightly more
negative, can only weaken a certified row inequality.
-/

def row0 : VerifiedRow where
  lo := 0
  hi := 0.00259038
  c0 := 0.380553385726178104971549433
  a1 := 0
  a2 := -0.336311423213154

def row1 : VerifiedRow where
  lo := 0.00259038
  hi := 0.035
  c0 := 0.380535903684482958019035
  a1 := 0.00674884302286265
  a2 := -0.336302531807290

def row2 : VerifiedRow where
  lo := 0.035
  hi := 0.065
  c0 := 0.380157336168305731734844
  a1 := 0.0174251447311828
  a2 := -0.343300819269616

def row3 : VerifiedRow where
  lo := 0.065
  hi := 1
  c0 := 0.369791719552889297350385
  a1 := 0.192609732008968
  a2 := -0.333057948456492

def concreteRows : Fin 4 → VerifiedRow
  | 0 => row0
  | 1 => row1
  | 2 => row2
  | 3 => row3

theorem concrete_rows_cover (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    ∃ i, (concreteRows i).lo ≤ x ∧ x ≤ (concreteRows i).hi := by
  by_cases h0 : x ≤ 0.00259038
  · exact ⟨0, by simpa [concreteRows, row0] using hx0,
      by simpa [concreteRows, row0] using h0⟩
  by_cases h1 : x ≤ 0.035
  · exact ⟨1, by simpa [concreteRows, row1] using le_of_not_ge h0,
      by simpa [concreteRows, row1] using h1⟩
  by_cases h2 : x ≤ 0.065
  · exact ⟨2, by simpa [concreteRows, row2] using le_of_not_ge h1,
      by simpa [concreteRows, row2] using h2⟩
  · exact ⟨3, by simpa [concreteRows, row3] using le_of_not_ge h2,
      by simpa [concreteRows, row3] using hx1⟩

theorem concrete_rows_concave (i : Fin 4) : (concreteRows i).a2 ≤ 0 := by
  fin_cases i <;> norm_num [concreteRows, row0, row1, row2, row3]

theorem concrete_rows_floor (i : Fin 4) : claimedLower <
    min (quadratic (concreteRows i).c0 (concreteRows i).a1 (concreteRows i).a2
      (concreteRows i).lo)
      (quadratic (concreteRows i).c0 (concreteRows i).a1 (concreteRows i).a2
        (concreteRows i).hi) := by
  fin_cases i <;>
    norm_num [concreteRows, row0, row1, row2, row3, claimedLower, quadratic, min_def]

/-- Every row has the same conservative rational floor used in the `sInf`
argument.  For row 0 the right endpoint is exactly this chosen floor. -/
theorem concrete_rows_safe_floor (i : Fin 4) : certifiedFloor ≤
    min (quadratic (concreteRows i).c0 (concreteRows i).a1 (concreteRows i).a2
      (concreteRows i).lo)
      (quadratic (concreteRows i).c0 (concreteRows i).a1 (concreteRows i).a2
        (concreteRows i).hi) := by
  fin_cases i <;>
    norm_num [concreteRows, row0, row1, row2, row3, certifiedFloor, quadratic, min_def]

/-- The exact-rational certificate aggregation specialized to the paper's
four rows.  This is the public theorem of this file: only the four analytic
row obligations remain as premises. -/
theorem concrete_certificate_cover
    (M m : ℝ)
    (hm : |m| ≤ 1)
    (hrows : ∀ i, RowApplies (concreteRows i) M |m|) :
    claimedLower < M := by
  exact four_row_cover M m concreteRows concrete_rows_cover concrete_rows_floor
    concrete_rows_concave hrows hm

/-- Uniform non-strict form needed before taking an infimum over profiles. -/
theorem concrete_certificate_uniform_floor
    (M m : ℝ)
    (hm : |m| ≤ 1)
    (hrows : ∀ i, RowApplies (concreteRows i) M |m|) :
    certifiedFloor ≤ M := by
  obtain ⟨i, hlo, hhi⟩ := concrete_rows_cover |m| (abs_nonneg m) hm
  have hq := concaveQuadratic_ge_min_endpoints
    (concreteRows i).c0 (concreteRows i).a1 (concreteRows i).a2
    (concreteRows i).lo (concreteRows i).hi |m|
    (concrete_rows_concave i) hlo hhi
  exact le_trans (concrete_rows_safe_floor i) (le_trans hq (hrows i hlo hhi))

end

end ErdosMinimum
