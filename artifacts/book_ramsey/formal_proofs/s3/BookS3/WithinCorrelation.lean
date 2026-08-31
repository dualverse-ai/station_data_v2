import BookS3.YamadaPottConstruction
import BookS3.SourceIdentity
import BookS3.AffineCorrelation
import BookS3.CrossCorrelation
import BookS3.CodegreeArithmetic

/-!
# Within-fibre correlations for the Yamada--Pott lift

This file proves the explicit correlation formulas used for the two
within-fibre codegrees.  It contains no graph-level or codegree-profile
assumptions.
-/

namespace BookS3

open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private noncomputable def ypNormalize : YamadaPottW F ≃ YamadaPottW F where
  toFun p := (p.1, p.2 * (YamadaPott.squareValue p.1)⁻¹)
  invFun p := (p.1, p.2 * YamadaPott.squareValue p.1)
  left_inv p := by
    rcases p with ⟨r, c⟩
    apply Prod.ext
    · rfl
    · dsimp
      field_simp [YamadaPott.squareValue_ne_zero r]
  right_inv p := by
    rcases p with ⟨r, c⟩
    apply Prod.ext
    · rfl
    · dsimp
      field_simp [YamadaPott.squareValue_ne_zero r]

private theorem squareValue_sub
    (r a : Additive (YamadaPottSquareSubgroup F)) :
    YamadaPott.squareValue (r - a) =
      YamadaPott.squareValue r * (YamadaPott.squareValue a)⁻¹ := by
  simp [YamadaPott.squareValue, sub_eq_add_neg]

private theorem squareValue_quadraticChar
    (r : Additive (YamadaPottSquareSubgroup F)) :
    quadraticChar F (YamadaPott.squareValue r) = 1 := by
  exact (quadraticChar_one_iff_isSquare
    (YamadaPott.squareValue_ne_zero r)).mpr
      (YamadaPott.squareValue_isSquare r)

private theorem quadraticChar_inv_eq (x : F) (hx : x ≠ 0) :
    quadraticChar F x⁻¹ = quadraticChar F x := by
  rcases quadraticChar_dichotomy hx with hpos | hneg
  · rw [hpos]
    apply (quadraticChar_one_iff_isSquare (inv_ne_zero hx)).mpr
    exact ((quadraticChar_one_iff_isSquare hx).mp hpos).inv
  · rw [hneg]
    apply quadraticChar_neg_one_iff_not_isSquare.mpr
    intro hs
    have hsx : IsSquare x := by
      simpa using hs.inv
    exact (quadraticChar_neg_one_iff_not_isSquare.mp hneg) hsx

private theorem squareValue_injective :
    Function.Injective
      (YamadaPott.squareValue (F := F) :
        Additive (YamadaPottSquareSubgroup F) → F) := by
  intro r s hrs
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact hrs

private theorem normalized_zero_shift
    (r a : Additive (YamadaPottSquareSubgroup F)) (c : F) :
    c * (YamadaPott.squareValue (r - a))⁻¹ =
      YamadaPott.squareValue a *
        (c * (YamadaPott.squareValue r)⁻¹) := by
  rw [squareValue_sub]
  have hr := YamadaPott.squareValue_ne_zero r
  have ha := YamadaPott.squareValue_ne_zero a
  field_simp

/-- Equation (10), `b=0`, for the cross-set autocorrelation:
`R_C(a,0)=m I(a)`. -/
theorem YamadaPott_C_correlation_zero
    (a : Additive (YamadaPottSquareSubgroup F)) :
    (correlation (YamadaPottC (F := F)) (YamadaPottC (F := F)) (a, 0)).card =
      Fintype.card (YamadaPottSquareSubgroup F) *
        YamadaPottI F (YamadaPott.squareValue a) := by
  let target : Finset (YamadaPottW F) := Finset.univ ×ˢ
    ((YamadaPottD F).filter fun x ↦
      YamadaPott.squareValue a * x ∈ YamadaPottD F)
  have hcard :
      (correlation (YamadaPottC (F := F)) (YamadaPottC (F := F)) (a, 0)).card =
        target.card := by
    apply Finset.card_equiv (ypNormalize (F := F))
    intro p
    rcases p with ⟨r, c⟩
    simp only [correlation, Finset.mem_filter, mem_YamadaPottC,
      Prod.fst_sub, Prod.snd_sub, sub_zero, ypNormalize, target,
      Finset.mem_product, Finset.mem_univ, true_and]
    rw [normalized_zero_shift]
    rfl
  rw [hcard]
  change (Finset.univ ×ˢ
    ((YamadaPottD F).filter fun x ↦
      YamadaPott.squareValue a * x ∈ YamadaPottD F)).card = _
  rw [Finset.card_product, Finset.card_univ]
  rw [Fintype.card_additive]
  rfl

/-- Parameterized form of `R_C(a,0)=mI(a)`, with `m=2r+1`. -/
theorem YamadaPott_C_correlation_zero_at_card (hF : ringChar F ≠ 2) {r : ℕ}
    (hcard : Fintype.card F = 4 * r + 3)
    (a : Additive (YamadaPottSquareSubgroup F)) :
    (correlation (YamadaPottC (F := F)) (YamadaPottC (F := F)) (a, 0)).card =
      (2 * r + 1) * YamadaPottI F (YamadaPott.squareValue a) := by
  rw [YamadaPott_C_correlation_zero,
    YamadaPott.card_squareSubgroup (F := F) hF hcard]

private theorem YamadaPottD_neg_mem (x : F) :
    -x ∈ YamadaPottD F ↔ x ∈ YamadaPottD F := by
  simp only [YamadaPottD, Finset.mem_sdiff, Finset.mem_univ, true_and,
    mem_YamadaPottE]
  constructor
  · intro h hxE
    apply h
    rcases hxE with hx0 | hxX | hnxX
    · exact Or.inl (by rw [hx0, neg_zero])
    · exact Or.inr (Or.inr (by simpa using hxX))
    · exact Or.inr (Or.inl (by simpa using hnxX))
  · intro h hxE
    apply h
    rcases hxE with hx0 | hxX | hnxX
    · exact Or.inl (neg_eq_zero.mp hx0)
    · exact Or.inr (Or.inr (by simpa using hxX))
    · exact Or.inr (Or.inl (by simpa using hnxX))

/-- Pairs in `D²` in the quadratic-character coset selected by `b`. -/
private def ypAffineCharacterPairs (t b : F) : Finset (F × F) :=
  ((YamadaPottD F) ×ˢ (YamadaPottD F)).filter fun p ↦
    quadraticChar F (t * p.2 - p.1) = quadraticChar F b

private theorem two_mul_card_ypAffineCharacterPairs
    (hmod : Fintype.card F % 4 = 3) {t b : F}
    (htsq : quadraticChar F t = 1) (hb : b ≠ 0) :
    2 * (ypAffineCharacterPairs (F := F) t b).card =
      (YamadaPottD F).card * (YamadaPottD F).card - YamadaPottI F t := by
  have hbchi := quadraticChar_dichotomy (F := F) hb
  rcases hbchi with hbpos | hbneg
  · have heq : ypAffineCharacterPairs (F := F) t b =
        affinePositivePairs t (YamadaPottD F) := by
      ext p
      simp [ypAffineCharacterPairs, affinePositivePairs, hbpos]
    rw [heq]
    exact two_mul_card_affinePositive_filter (YamadaPottD F)
      (YamadaPottD_neg_mem (F := F)) htsq hmod
  · have heq : ypAffineCharacterPairs (F := F) t b =
        affineNegativePairs t (YamadaPottD F) := by
      ext p
      simp [ypAffineCharacterPairs, affineNegativePairs, hbneg]
    rw [heq]
    exact two_mul_card_affineNegative_filter (YamadaPottD F)
      (YamadaPottD_neg_mem (F := F)) htsq hmod

/-- For a nonzero additive shift, normalization in each cyclic row identifies
the `C` autocorrelation with the affine character-pair set of equation (9). -/
private theorem card_YamadaPott_C_correlation_eq_affinePairs
    (a : Additive (YamadaPottSquareSubgroup F)) {b : F} (hb : b ≠ 0) :
    (correlation (YamadaPottC (F := F)) (YamadaPottC (F := F)) (a, b)).card =
      (ypAffineCharacterPairs (F := F) (YamadaPott.squareValue a) b).card := by
  let t := YamadaPott.squareValue a
  let φ : YamadaPottW F → F × F := fun p =>
    (t * (p.2 - b) * (YamadaPott.squareValue p.1)⁻¹,
      p.2 * (YamadaPott.squareValue p.1)⁻¹)
  apply Finset.card_bij (fun p _ ↦ φ p)
  · intro p hp
    rcases p with ⟨r, c⟩
    simp only [correlation, Finset.mem_filter, mem_YamadaPottC,
      Prod.fst_sub, Prod.snd_sub] at hp
    have hfirst :
        t * (c - b) * (YamadaPott.squareValue r)⁻¹ ∈ YamadaPottD F := by
      change YamadaPott.squareValue a * (c - b) *
          (YamadaPott.squareValue r)⁻¹ ∈ YamadaPottD F
      rw [mul_assoc, ← normalized_zero_shift r a (c - b)]
      exact hp.2
    have htchi : quadraticChar F t = 1 :=
      squareValue_quadraticChar (F := F) a
    have hrchi : quadraticChar F (YamadaPott.squareValue r) = 1 :=
      squareValue_quadraticChar (F := F) r
    have hchar :
        quadraticChar F
            (t * (c * (YamadaPott.squareValue r)⁻¹) -
              t * (c - b) * (YamadaPott.squareValue r)⁻¹) =
          quadraticChar F b := by
      have heq :
          t * (c * (YamadaPott.squareValue r)⁻¹) -
              t * (c - b) * (YamadaPott.squareValue r)⁻¹ =
            t * b * (YamadaPott.squareValue r)⁻¹ := by ring
      rw [heq, map_mul, map_mul,
        quadraticChar_inv_eq _ (YamadaPott.squareValue_ne_zero r),
        htchi, hrchi]
      norm_num
    simp only [ypAffineCharacterPairs, Finset.mem_filter, Finset.mem_product,
      φ, Prod.fst, Prod.snd]
    exact ⟨⟨hfirst, hp.1⟩, hchar⟩
  · intro p hp q hq hpq
    rcases p with ⟨r, c⟩
    rcases q with ⟨s, d⟩
    have hpair1 := congrArg Prod.fst hpq
    have hpair2 := congrArg Prod.snd hpq
    have ht0 : t ≠ 0 := YamadaPott.squareValue_ne_zero a
    have hfirst :
        (c - b) * (YamadaPott.squareValue r)⁻¹ =
          (d - b) * (YamadaPott.squareValue s)⁻¹ := by
      apply mul_left_cancel₀ ht0
      simpa [φ, mul_assoc] using hpair1
    have hsecond :
        c * (YamadaPott.squareValue r)⁻¹ =
          d * (YamadaPott.squareValue s)⁻¹ := by
      simpa [φ] using hpair2
    have hdiff :
        b * (YamadaPott.squareValue r)⁻¹ =
          b * (YamadaPott.squareValue s)⁻¹ := by
      linear_combination hsecond - hfirst
    have hinv : (YamadaPott.squareValue r)⁻¹ =
        (YamadaPott.squareValue s)⁻¹ := mul_left_cancel₀ hb hdiff
    have huv : YamadaPott.squareValue r = YamadaPott.squareValue s :=
      inv_injective hinv
    have hrs : r = s := squareValue_injective (F := F) huv
    subst s
    have hcd : c = d := by
      apply mul_right_cancel₀ (inv_ne_zero (YamadaPott.squareValue_ne_zero r))
      exact hsecond
    subst d
    rfl
  · intro p hp
    rcases p with ⟨y, x⟩
    simp only [ypAffineCharacterPairs, Finset.mem_filter, Finset.mem_product,
      Prod.fst, Prod.snd] at hp
    let δ : F := t * x - y
    have hchar : quadraticChar F δ = quadraticChar F b := by
      simpa [δ, t] using hp.2
    have hbchi0 : quadraticChar F b ≠ 0 := by
      rw [ne_eq, quadraticChar_eq_zero_iff]
      exact hb
    have hδ0 : δ ≠ 0 := by
      intro hzero
      have : quadraticChar F b = 0 := by
        rw [← hchar, hzero, quadraticChar_zero]
      exact hbchi0 this
    let u : F := t * b * δ⁻¹
    have ht0 : t ≠ 0 := YamadaPott.squareValue_ne_zero a
    have hu0 : u ≠ 0 := mul_ne_zero (mul_ne_zero ht0 hb) (inv_ne_zero hδ0)
    have htchi : quadraticChar F t = 1 :=
      squareValue_quadraticChar (F := F) a
    have huchi : quadraticChar F u = 1 := by
      rw [show u = t * b * δ⁻¹ by rfl, map_mul, map_mul,
        quadraticChar_inv_eq δ hδ0, htchi, hchar]
      have := quadraticChar_sq_one hb
      simpa [pow_two] using this
    have huS : u ∈ YamadaPottS F := by
      rw [mem_YamadaPottS]
      exact ⟨hu0, (quadraticChar_one_iff_isSquare hu0).mp huchi⟩
    let su : {z // z ∈ YamadaPottS F} := ⟨u, huS⟩
    let r : Additive (YamadaPottSquareSubgroup F) :=
      Additive.ofMul ((YamadaPott.squareSubgroupEquivS (F := F)).symm su)
    have hru : YamadaPott.squareValue r = u := by
      have he := (YamadaPott.squareSubgroupEquivS (F := F)).apply_symm_apply su
      exact congrArg Subtype.val he
    let c : F := u * x
    refine ⟨(r, c), ?_, ?_⟩
    · simp only [correlation, Finset.mem_filter, mem_YamadaPottC,
        Prod.fst_sub, Prod.snd_sub]
      constructor
      · have heq : c * (YamadaPott.squareValue r)⁻¹ = x := by
          rw [hru]
          dsimp [c]
          field_simp
        rw [heq]
        exact hp.1.2
      · rw [normalized_zero_shift r a (c - b)]
        have heq : t * ((c - b) * (YamadaPott.squareValue r)⁻¹) = y := by
          rw [hru]
          dsimp [c, u]
          field_simp [hδ0]
          ring
        rw [heq]
        exact hp.1.1
    · apply Prod.ext
      · dsimp [φ]
        rw [hru]
        have heq : t * (c - b) * u⁻¹ = y := by
          dsimp [c, u]
          field_simp [hδ0]
          ring
        exact heq
      · dsimp [φ, c]
        rw [hru]
        field_simp

/-- Equation (9): the cross-set autocorrelation at a nonzero additive shift,
in its exact division-free form. -/
theorem YamadaPott_C_correlation_nonzero
    (hmod : Fintype.card F % 4 = 3)
    (a : Additive (YamadaPottSquareSubgroup F)) {b : F} (hb : b ≠ 0) :
    2 * (correlation (YamadaPottC (F := F)) (YamadaPottC (F := F)) (a, b)).card =
      (YamadaPottD F).card * (YamadaPottD F).card -
        YamadaPottI F (YamadaPott.squareValue a) := by
  rw [card_YamadaPott_C_correlation_eq_affinePairs a hb]
  exact two_mul_card_ypAffineCharacterPairs hmod
    (squareValue_quadraticChar (F := F) a) hb

/-- Parameterized form of equation (9), where `|D|=2r+2`. -/
theorem YamadaPott_C_correlation_nonzero_at_card
    (hF : ringChar F ≠ 2) {r : ℕ}
    (hcard : Fintype.card F = 4 * r + 3)
    (a : Additive (YamadaPottSquareSubgroup F)) {b : F} (hb : b ≠ 0) :
    2 * (correlation (YamadaPottC (F := F)) (YamadaPottC (F := F)) (a, b)).card =
      (2 * r + 2) ^ 2 - YamadaPottI F (YamadaPott.squareValue a) := by
  have hmod : Fintype.card F % 4 = 3 := by omega
  rw [YamadaPott_C_correlation_nonzero hmod a hb,
    card_YamadaPottD (F := F) hF hcard]
  ring

/-- The `a=0`, `b≠0` line of equation (10): `2R_C=m(m+1)`. -/
theorem YamadaPott_C_correlation_first_zero
    (hF : ringChar F ≠ 2) {r : ℕ}
    (hcard : Fintype.card F = 4 * r + 3) {b : F} (hb : b ≠ 0) :
    2 * (correlation (YamadaPottC (F := F)) (YamadaPottC (F := F)) (0, b)).card =
      (2 * r + 1) * (2 * r + 2) := by
  have h := YamadaPott_C_correlation_nonzero_at_card
    (F := F) hF hcard (0 : Additive (YamadaPottSquareSubgroup F)) hb
  simp only [YamadaPott.squareValue_zero, YamadaPottI, one_mul,
    Finset.filter_mem_eq_inter] at h
  simp only [Finset.inter_self] at h
  rw [card_YamadaPottD (F := F) hF hcard] at h
  have hle : 2 * r + 2 ≤ (2 * r + 2) ^ 2 := by nlinarith
  have harith : (2 * r + 2) ^ 2 - (2 * r + 2) =
      (2 * r + 1) * (2 * r + 2) := by
    rw [Nat.sub_eq_iff_eq_add hle]
    ring
  rwa [harith] at h

private def ypSignedRow (z : ℤ) : Finset F :=
  Finset.univ.filter fun c ↦ c = 0 ∨ z * quadraticChar F c = 1

private theorem four_mul_card_ypSignedRow_correlation
    (hF : ringChar F ≠ 2) (hmod : Fintype.card F % 4 = 3)
    {z w : ℤ} (hz : z = -1 ∨ z = 1) (hw : w = -1 ∨ w = 1)
    {b : F} (hb : b ≠ 0) :
    4 * (((ypSignedRow (F := F) z).filter fun c ↦
      c - b ∈ ypSignedRow (F := F) w).card : ℤ) =
      (Fintype.card F : ℤ) + 2 - z * w +
        (z - w) * quadraticChar F b := by
  have hneg : quadraticChar F (-1) = -1 :=
    quadraticChar_neg_one_of_card_three (F := F) hmod
  have hindicator : ∀ (v : ℤ), (v = -1 ∨ v = 1) → ∀ c : F,
      2 * (if c = 0 ∨ v * quadraticChar F c = 1 then (1 : ℤ) else 0) =
        1 + v * quadraticChar F c + (if c = 0 then 1 else 0) := by
    intro v hv c
    rcases hv with rfl | rfl
    · by_cases hc : c = 0
      · subst c; simp
      · rcases quadraticChar_dichotomy hc with hpos | hneg'
        · simp [hc, hpos]
        · simp [hc, hneg']
    · by_cases hc : c = 0
      · subst c; simp
      · rcases quadraticChar_dichotomy hc with hpos | hneg'
        · simp [hc, hpos]
        · simp [hc, hneg']
  have hpoint : ∀ c : F,
      4 * (if (c = 0 ∨ z * quadraticChar F c = 1) ∧
          (c - b = 0 ∨ w * quadraticChar F (c - b) = 1)
        then (1 : ℤ) else 0) =
        (1 + z * quadraticChar F c + (if c = 0 then 1 else 0)) *
          (1 + w * quadraticChar F (c - b) +
            (if c - b = 0 then 1 else 0)) := by
    intro c
    let P : Prop := c = 0 ∨ z * quadraticChar F c = 1
    let Q : Prop := c - b = 0 ∨ w * quadraticChar F (c - b) = 1
    have hand : (if P ∧ Q then (1 : ℤ) else 0) =
        (if P then 1 else 0) * (if Q then 1 else 0) := by
      by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]
    rw [hand]
    calc
      4 * ((if P then (1 : ℤ) else 0) * (if Q then 1 else 0)) =
          (2 * (if P then (1 : ℤ) else 0)) *
            (2 * (if Q then (1 : ℤ) else 0)) := by ring
      _ = _ := by
        rw [hindicator z hz c, hindicator w hw (c - b)]
  have hshift : ∑ c : F, quadraticChar F (c - b) = 0 := by
    rw [← quadraticChar_sum_zero (F := F) hF]
    exact (Equiv.subRight b).sum_comp (quadraticChar F)
  have hdelta0 : ∑ c : F, (if c = 0 then (1 : ℤ) else 0) = 1 := by simp
  have hdeltab : ∑ c : F, (if c - b = 0 then (1 : ℤ) else 0) = 1 := by
    simp [sub_eq_zero]
  have hchidelta :
      ∑ c : F, quadraticChar F c * (if c - b = 0 then (1 : ℤ) else 0) =
        quadraticChar F b := by
    simp [sub_eq_zero]
  have hdeltachi :
      ∑ c : F, (if c = 0 then (1 : ℤ) else 0) *
          quadraticChar F (c - b) = -quadraticChar F b := by
    have hchneg : quadraticChar F (-b) = -quadraticChar F b := by
      rw [show -b = (-1 : F) * b by ring, map_mul, hneg]
      ring
    simp only [ite_mul, one_mul, zero_mul]
    simp
    exact hchneg
  have hsumShiftCoeff :
      ∑ c : F, w * quadraticChar F (c - b) = 0 := by
    rw [← Finset.mul_sum, hshift, mul_zero]
  have hsumCoeff : ∑ c : F, z * quadraticChar F c = 0 := by
    rw [← Finset.mul_sum, quadraticChar_sum_zero (F := F) hF, mul_zero]
  have hsumProduct :
      ∑ c : F, w * z * quadraticChar F c * quadraticChar F (c - b) =
        -(w * z) := by
    rw [show (∑ c : F, w * z * quadraticChar F c * quadraticChar F (c - b)) =
        w * z * (∑ c : F, quadraticChar F c * quadraticChar F (c - b)) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c _
          ring,
      sum_quadraticChar_mul_shift (F := F) hF hb]
    ring
  have hsumChiDeltaCoeff :
      ∑ c : F, z * quadraticChar F c *
          (if c - b = 0 then (1 : ℤ) else 0) = z * quadraticChar F b := by
    rw [show (∑ c : F, z * quadraticChar F c *
        (if c - b = 0 then (1 : ℤ) else 0)) = z *
          (∑ c : F, quadraticChar F c *
            (if c - b = 0 then (1 : ℤ) else 0)) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c _
          ring,
      hchidelta]
  have hsumDeltaChiCoeff :
      ∑ c : F, (w * (if c = 0 then (1 : ℤ) else 0)) *
          quadraticChar F (c - b) = -w * quadraticChar F b := by
    rw [show (∑ c : F, (w * (if c = 0 then (1 : ℤ) else 0)) *
        quadraticChar F (c - b)) = w *
          (∑ c : F, (if c = 0 then (1 : ℤ) else 0) *
            quadraticChar F (c - b)) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro c _
          ring,
      hdeltachi]
    ring
  have hsumDeltaDelta :
      ∑ c : F, (if c = 0 then (1 : ℤ) else 0) *
          (if c - b = 0 then (1 : ℤ) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro c _
    by_cases hcb : c - b = 0
    · have hc : c = b := sub_eq_zero.mp hcb
      simp [hcb, hc, hb]
    · simp [hcb]
  have hsumProduct' :
      ∑ c : F, z * quadraticChar F c * w * quadraticChar F (c - b) =
        -(z * w) := by
    calc
      _ = ∑ c : F, w * z * quadraticChar F c *
          quadraticChar F (c - b) := by
            apply Finset.sum_congr rfl
            intro c _
            ring
      _ = -(w * z) := hsumProduct
      _ = -(z * w) := by ring
  have hsumDeltaChiCoeff' :
      ∑ c : F, (w * (if c = 0 then (1 : ℤ) else 0)) *
          quadraticChar F (-b + c) = -w * quadraticChar F b := by
    simpa only [sub_eq_add_neg, add_comm] using hsumDeltaChiCoeff
  have hsumProduct'' :
      ∑ c : F, z * quadraticChar F c *
          (w * quadraticChar F (c - b)) = -(z * w) := by
    calc
      _ = ∑ c : F, z * quadraticChar F c * w *
          quadraticChar F (c - b) := by
            apply Finset.sum_congr rfl
            intro c _
            ring
      _ = _ := hsumProduct'
  have hsumDeltaChiCoeff'' :
      ∑ c : F, (if c = 0 then (1 : ℤ) else 0) *
          (w * quadraticChar F (c - b)) = -w * quadraticChar F b := by
    calc
      _ = ∑ c : F, (w * (if c = 0 then (1 : ℤ) else 0)) *
          quadraticChar F (c - b) := by
            apply Finset.sum_congr rfl
            intro c _
            ring
      _ = _ := hsumDeltaChiCoeff
  simp only [ypSignedRow, Finset.filter_filter, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [int_card_filter_eq_sum_indicator]
  rw [Finset.mul_sum]
  calc
    ∑ c : F, 4 *
        (if (c = 0 ∨ z * quadraticChar F c = 1) ∧
            (c - b = 0 ∨ w * quadraticChar F (c - b) = 1)
          then (1 : ℤ) else 0) =
        ∑ c : F,
          (1 + z * quadraticChar F c + (if c = 0 then 1 else 0)) *
            (1 + w * quadraticChar F (c - b) +
              (if c - b = 0 then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro c _
          exact hpoint c
    _ = (Fintype.card F : ℤ) + 2 - z * w +
          (z - w) * quadraticChar F b := by
      simp_rw [add_mul, mul_add]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one, one_mul, hsumShiftCoeff, hsumCoeff,
        hsumProduct, hsumProduct', hdelta0, hdeltab, hsumChiDeltaCoeff,
        hsumDeltaChiCoeff, hsumDeltaChiCoeff', hsumDeltaDelta]
      rw [hsumProduct'', hsumDeltaChiCoeff'']
      ring

private noncomputable def ypNonexceptionalRows
    (a : Additive (YamadaPottSquareSubgroup F)) :
    Finset (Additive (YamadaPottSquareSubgroup F)) :=
  (Finset.univ.erase 0).erase a

private theorem card_YamadaPott_A_correlation_eq_row_sum
    (a : Additive (YamadaPottSquareSubgroup F)) (b : F) :
    (correlation (YamadaPottA (F := F)) (YamadaPottA (F := F)) (a, b)).card =
      ∑ r ∈ ypNonexceptionalRows (F := F) a,
        ((ypSignedRow (F := F) (YamadaPott.skew r)).filter fun c ↦
          c - b ∈ ypSignedRow (F := F) (YamadaPott.skew (r - a))).card := by
  let fibers : Additive (YamadaPottSquareSubgroup F) → Finset (YamadaPottW F) :=
    fun r ↦ ({r} : Finset (Additive (YamadaPottSquareSubgroup F))) ×ˢ
      ((ypSignedRow (F := F) (YamadaPott.skew r)).filter fun c ↦
        c - b ∈ ypSignedRow (F := F) (YamadaPott.skew (r - a)))
  have hdisj : ((ypNonexceptionalRows (F := F) a : Finset _) : Set _).PairwiseDisjoint
      fibers := by
    intro r hr s hs hrs
    change Disjoint (fibers r) (fibers s)
    dsimp only [fibers]
    rw [Finset.disjoint_product]
    left
    simp only [Finset.disjoint_singleton]
    exact hrs
  have heq :
      correlation (YamadaPottA (F := F)) (YamadaPottA (F := F)) (a, b) =
        (ypNonexceptionalRows (F := F) a).biUnion fibers := by
    ext p
    rcases p with ⟨r, c⟩
    simp only [correlation, Finset.mem_filter, mem_YamadaPottA,
      Prod.fst_sub, Prod.snd_sub, ypNonexceptionalRows, Finset.mem_biUnion,
      Finset.mem_erase, Finset.mem_univ, and_true, fibers,
      Finset.mem_product, Finset.mem_singleton, ypSignedRow]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hr0, hc⟩, hra0, hcb⟩
      exact ⟨r, ⟨(sub_ne_zero.mp hra0), hr0⟩, rfl, hc, hcb⟩
    · rintro ⟨s, ⟨hsa, hs0⟩, hsr, hc, hcb⟩
      subst s
      exact ⟨⟨hs0, hc⟩, sub_ne_zero.mpr hsa, hcb⟩
  rw [heq, Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro r hr
  simp [fibers]

private theorem card_YamadaPott_B_correlation_eq_row_sum
    (a : Additive (YamadaPottSquareSubgroup F)) (b : F) :
    (correlation (YamadaPottB (F := F)) (YamadaPottB (F := F)) (a, b)).card =
      ∑ r ∈ ypNonexceptionalRows (F := F) a,
        ((ypSignedRow (F := F) (-YamadaPott.skew r)).filter fun c ↦
          c - b ∈ ypSignedRow (F := F) (-YamadaPott.skew (r - a))).card := by
  let fibers : Additive (YamadaPottSquareSubgroup F) → Finset (YamadaPottW F) :=
    fun r ↦ ({r} : Finset (Additive (YamadaPottSquareSubgroup F))) ×ˢ
      ((ypSignedRow (F := F) (-YamadaPott.skew r)).filter fun c ↦
        c - b ∈ ypSignedRow (F := F) (-YamadaPott.skew (r - a)))
  have hdisj : ((ypNonexceptionalRows (F := F) a : Finset _) : Set _).PairwiseDisjoint
      fibers := by
    intro r hr s hs hrs
    change Disjoint (fibers r) (fibers s)
    dsimp only [fibers]
    rw [Finset.disjoint_product]
    left
    simp only [Finset.disjoint_singleton]
    exact hrs
  have heq :
      correlation (YamadaPottB (F := F)) (YamadaPottB (F := F)) (a, b) =
        (ypNonexceptionalRows (F := F) a).biUnion fibers := by
    ext p
    rcases p with ⟨r, c⟩
    simp only [correlation, Finset.mem_filter, mem_YamadaPottB,
      Prod.fst_sub, Prod.snd_sub, ypNonexceptionalRows, Finset.mem_biUnion,
      Finset.mem_erase, Finset.mem_univ, and_true, fibers,
      Finset.mem_product, Finset.mem_singleton, ypSignedRow]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hr0, hc⟩, hra0, hcb⟩
      refine ⟨r, ⟨sub_ne_zero.mp hra0, hr0⟩, rfl, ?_, ?_⟩
      · rcases hc with hc0 | hc
        · exact Or.inl hc0
        · exact Or.inr (by calc
            (-YamadaPott.skew r) * quadraticChar F c =
                -(YamadaPott.skew r * quadraticChar F c) := by ring
            _ = 1 := by rw [hc]; norm_num)
      · rcases hcb with hcb0 | hcb
        · exact Or.inl hcb0
        · exact Or.inr (by calc
            (-YamadaPott.skew (r - a)) * quadraticChar F (c - b) =
                -(YamadaPott.skew (r - a) * quadraticChar F (c - b)) := by ring
            _ = 1 := by rw [hcb]; norm_num)
    · rintro ⟨s, ⟨hsa0, hs0⟩, hsr, hc, hcb⟩
      subst s
      refine ⟨⟨hs0, ?_⟩, sub_ne_zero.mpr hsa0, ?_⟩
      · rcases hc with hc0 | hc
        · exact Or.inl hc0
        · exact Or.inr (by
            have := congrArg Neg.neg hc
            norm_num at this
            simpa only [neg_mul] using this)
      · rcases hcb with hcb0 | hcb
        · exact Or.inl hcb0
        · exact Or.inr (by
            have := congrArg Neg.neg hcb
            norm_num at this
            simpa only [neg_mul] using this)
  rw [heq, Finset.card_biUnion hdisj]
  apply Finset.sum_congr rfl
  intro r hr
  simp [fibers]

@[simp] private theorem YamadaPott_skew_zero :
    YamadaPott.skew (0 : Additive (YamadaPottSquareSubgroup F)) = 0 := by
  simp [YamadaPott.skew, YamadaPottH]

private theorem YamadaPott_skew_sign
    {r : Additive (YamadaPottSquareSubgroup F)} (hr : r ≠ 0) :
    YamadaPott.skew r = -1 ∨ YamadaPott.skew r = 1 := by
  have hx : 1 - YamadaPott.squareValue r ≠ 0 := by
    intro h
    apply hr
    rw [← YamadaPott.squareValue_eq_one_iff]
    exact (sub_eq_zero.mp h).symm
  rcases quadraticChar_dichotomy hx with h | h
  · exact Or.inr (by simpa [YamadaPott.skew, YamadaPottH] using h)
  · exact Or.inl (by simpa [YamadaPott.skew, YamadaPottH] using h)

private theorem card_ypNonexceptionalRows (hF : ringChar F ≠ 2) {t : ℕ}
    (hcard : Fintype.card F = 4 * t + 3)
    {a : Additive (YamadaPottSquareSubgroup F)} (ha : a ≠ 0) :
    (ypNonexceptionalRows (F := F) a).card = 2 * t - 1 := by
  rw [ypNonexceptionalRows,
    Finset.card_erase_of_mem (by simp [ha] : a ∈
      (Finset.univ.erase (0 : Additive (YamadaPottSquareSubgroup F)))),
    Finset.card_erase_of_mem (Finset.mem_univ
      (0 : Additive (YamadaPottSquareSubgroup F))),
    Finset.card_univ, Fintype.card_additive,
    YamadaPott.card_squareSubgroup (F := F) hF hcard]
  omega

private theorem YamadaPott_parameter_pos (hF : ringChar F ≠ 2) {t : ℕ}
    (hcard : Fintype.card F = 4 * t + 3)
    {a : Additive (YamadaPottSquareSubgroup F)} (ha : a ≠ 0) : 1 ≤ t := by
  have hc := YamadaPott.card_squareSubgroup (F := F) hF hcard
  by_contra ht
  have ht0 : t = 0 := by omega
  have hle : Fintype.card (Additive (YamadaPottSquareSubgroup F)) ≤ 1 := by
    rw [Fintype.card_additive, hc, ht0]
  have hs : Subsingleton (Additive (YamadaPottSquareSubgroup F)) :=
    Fintype.card_le_one_iff_subsingleton.mp hle
  exact ha (hs.elim a 0)

private theorem sum_ypRows_skew_product
    {a : Additive (YamadaPottSquareSubgroup F)} (ha : a ≠ 0) :
    ∑ r ∈ ypNonexceptionalRows (F := F) a,
        YamadaPott.skew r * YamadaPott.skew (r - a) =
      YamadaPottCorrH F (YamadaPott.squareValue a) := by
  let R := Additive (YamadaPottSquareSubgroup F)
  let e : R ≃ {x // x ∈ YamadaPottS F} :=
    Additive.toMul.trans (YamadaPott.squareSubgroupEquivS (F := F))
  have hfull :
      ∑ r : R, YamadaPott.skew r * YamadaPott.skew (r - a) =
        YamadaPottCorrH F (YamadaPott.squareValue a) := by
    calc
      ∑ r : R, YamadaPott.skew r * YamadaPott.skew (r - a) =
          ∑ s : R, YamadaPott.skew (s + a) * YamadaPott.skew s := by
            apply Fintype.sum_equiv (Equiv.subRight a)
            intro r
            simp
      _ = ∑ x : {x // x ∈ YamadaPottS F},
          YamadaPottH (YamadaPott.squareValue a * x.1) * YamadaPottH x.1 := by
            apply Fintype.sum_equiv e
            intro s
            simp only [YamadaPott.skew]
            have hs : YamadaPott.squareValue (s + a) =
                YamadaPott.squareValue a * (e s).1 := by
              change YamadaPott.squareValue (s + a) =
                YamadaPott.squareValue a * YamadaPott.squareValue s
              simp [YamadaPott.squareValue]
              ac_rfl
            rw [hs]
            rfl
      _ = ∑ x ∈ YamadaPottS F,
          YamadaPottH (YamadaPott.squareValue a * x) * YamadaPottH x :=
            by
              simpa only using
                (Finset.sum_subtype (YamadaPottS F) (fun _ ↦ Iff.rfl)
                  (fun x ↦ YamadaPottH (YamadaPott.squareValue a * x) *
                    YamadaPottH x)).symm
      _ = YamadaPottCorrH F (YamadaPott.squareValue a) := by
            rw [YamadaPottCorrH]
            apply Finset.sum_congr rfl
            intro x hx
            ring
  rw [← hfull]
  simp only [ypNonexceptionalRows]
  rw [Finset.sum_erase ((Finset.univ : Finset R).erase 0)
      (f := fun r : R ↦ YamadaPott.skew r * YamadaPott.skew (r - a)) (a := a)
      (show YamadaPott.skew a * YamadaPott.skew (a - a) = 0 by simp),
    Finset.sum_erase (Finset.univ : Finset R)
      (f := fun r : R ↦ YamadaPott.skew r * YamadaPott.skew (r - a)) (a := 0)
      (show YamadaPott.skew (0 : Additive (YamadaPottSquareSubgroup F)) *
          YamadaPott.skew (0 - a) = 0 by simp)]

private theorem YamadaPott_skew_neg (hF : ringChar F ≠ 2)
    (hmod : Fintype.card F % 4 = 3)
    (a : Additive (YamadaPottSquareSubgroup F)) :
    YamadaPott.skew (-a) = -YamadaPott.skew a := by
  simpa [YamadaPott.skew, YamadaPott.squareValue_neg] using
    (YamadaPottH_inv (F := F) hF hmod (YamadaPott.squareValue_mem_S a))

private theorem sum_ypRows_skew_difference
    (hF : ringChar F ≠ 2) (hmod : Fintype.card F % 4 = 3)
    {a : Additive (YamadaPottSquareSubgroup F)} (ha : a ≠ 0) :
    ∑ r ∈ ypNonexceptionalRows (F := F) a,
        (YamadaPott.skew r - YamadaPott.skew (r - a)) =
      -2 * YamadaPott.skew a := by
  let R := Additive (YamadaPottSquareSubgroup F)
  let f : R → ℤ := fun r ↦ YamadaPott.skew r - YamadaPott.skew (r - a)
  have hshift : ∑ r : R, YamadaPott.skew (r - a) = ∑ r : R, YamadaPott.skew r :=
    (Equiv.subRight a).sum_comp YamadaPott.skew
  have hfull : ∑ r : R, f r = 0 := by
    simp only [f, Finset.sum_sub_distrib]
    rw [hshift]
    ring
  have hfa : f a = YamadaPott.skew a := by simp [f]
  have hf0 : f 0 = YamadaPott.skew a := by
    simp [f, YamadaPott_skew_neg (F := F) hF hmod]
  have haMem : a ∈ (Finset.univ : Finset R).erase 0 := by simp [ha]
  have h1 := Finset.sum_erase_add ((Finset.univ : Finset R).erase 0) f haMem
  have h2 := Finset.sum_erase_add (Finset.univ : Finset R) f (Finset.mem_univ 0)
  simp only [ypNonexceptionalRows]
  rw [hfa] at h1
  rw [hf0, hfull] at h2
  linarith

/-- Equation (8), first line: exact `A` correlation for `a≠0`, `b≠0`. -/
theorem YamadaPott_A_correlation_nonzero
    (hF : ringChar F ≠ 2) {t : ℕ}
    (hcard : Fintype.card F = 4 * t + 3)
    {a : Additive (YamadaPottSquareSubgroup F)} (ha : a ≠ 0)
    {b : F} (hb : b ≠ 0) :
    4 * ((correlation (YamadaPottA (F := F)) (YamadaPottA (F := F))
      (a, b)).card : ℤ) =
      ((2 * t + 1 : ℤ) - 2) * (2 * (2 * t + 1 : ℤ) + 3) -
        YamadaPottCorrH F (YamadaPott.squareValue a) -
          2 * YamadaPott.skew a * quadraticChar F b := by
  have hmod : Fintype.card F % 4 = 3 := by omega
  have htpos := YamadaPott_parameter_pos (F := F) hF hcard ha
  have hdecomp := congrArg (fun n : ℕ ↦ (n : ℤ))
    (card_YamadaPott_A_correlation_eq_row_sum (F := F) a b)
  push_cast at hdecomp
  have hrow : ∀ r ∈ ypNonexceptionalRows (F := F) a,
      4 * ((((ypSignedRow (F := F) (YamadaPott.skew r)).filter fun c ↦
        c - b ∈ ypSignedRow (F := F) (YamadaPott.skew (r - a))).card : ℕ) : ℤ) =
        (Fintype.card F : ℤ) + 2 -
          YamadaPott.skew r * YamadaPott.skew (r - a) +
          (YamadaPott.skew r - YamadaPott.skew (r - a)) *
            quadraticChar F b := by
    intro r hr
    have hr0 : r ≠ 0 := (Finset.mem_erase.mp
      (Finset.mem_erase.mp hr).2).1
    have hra : r - a ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hr).1
    exact four_mul_card_ypSignedRow_correlation hF hmod
      (YamadaPott_skew_sign hr0) (YamadaPott_skew_sign hra) hb
  calc
    4 * ((correlation (YamadaPottA (F := F)) (YamadaPottA (F := F))
        (a, b)).card : ℤ) =
        ∑ r ∈ ypNonexceptionalRows (F := F) a,
          4 * ((((ypSignedRow (F := F) (YamadaPott.skew r)).filter fun c ↦
            c - b ∈ ypSignedRow (F := F) (YamadaPott.skew (r - a))).card : ℕ) : ℤ) := by
      rw [hdecomp, Finset.mul_sum]
    _ = ∑ r ∈ ypNonexceptionalRows (F := F) a,
        ((Fintype.card F : ℤ) + 2 -
          YamadaPott.skew r * YamadaPott.skew (r - a) +
          (YamadaPott.skew r - YamadaPott.skew (r - a)) *
            quadraticChar F b) := Finset.sum_congr rfl hrow
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul, sum_ypRows_skew_product (F := F) ha,
        sum_ypRows_skew_difference (F := F) hF hmod ha]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [card_ypNonexceptionalRows (F := F) hF hcard ha, hcard]
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * t)]
      push_cast
      ring

/-- Equation (8), second line: exact `B` correlation for `a≠0`, `b≠0`. -/
theorem YamadaPott_B_correlation_nonzero
    (hF : ringChar F ≠ 2) {t : ℕ}
    (hcard : Fintype.card F = 4 * t + 3)
    {a : Additive (YamadaPottSquareSubgroup F)} (ha : a ≠ 0)
    {b : F} (hb : b ≠ 0) :
    4 * ((correlation (YamadaPottB (F := F)) (YamadaPottB (F := F))
      (a, b)).card : ℤ) =
      ((2 * t + 1 : ℤ) - 2) * (2 * (2 * t + 1 : ℤ) + 3) -
        YamadaPottCorrH F (YamadaPott.squareValue a) +
          2 * YamadaPott.skew a * quadraticChar F b := by
  have hmod : Fintype.card F % 4 = 3 := by omega
  have htpos := YamadaPott_parameter_pos (F := F) hF hcard ha
  have hdecomp := congrArg (fun n : ℕ ↦ (n : ℤ))
    (card_YamadaPott_B_correlation_eq_row_sum (F := F) a b)
  push_cast at hdecomp
  have hrow : ∀ r ∈ ypNonexceptionalRows (F := F) a,
      4 * ((((ypSignedRow (F := F) (-YamadaPott.skew r)).filter fun c ↦
        c - b ∈ ypSignedRow (F := F) (-YamadaPott.skew (r - a))).card : ℕ) : ℤ) =
        (Fintype.card F : ℤ) + 2 -
          YamadaPott.skew r * YamadaPott.skew (r - a) -
          (YamadaPott.skew r - YamadaPott.skew (r - a)) *
            quadraticChar F b := by
    intro r hr
    have hr0 : r ≠ 0 := (Finset.mem_erase.mp
      (Finset.mem_erase.mp hr).2).1
    have hra : r - a ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hr).1
    have hz := YamadaPott_skew_sign (F := F) hr0
    have hw := YamadaPott_skew_sign (F := F) hra
    have hz' : -YamadaPott.skew r = -1 ∨ -YamadaPott.skew r = 1 := by
      rcases hz with h | h <;> simp [h]
    have hw' : -YamadaPott.skew (r - a) = -1 ∨
        -YamadaPott.skew (r - a) = 1 := by
      rcases hw with h | h <;> simp [h]
    have h := four_mul_card_ypSignedRow_correlation
      (F := F) hF hmod hz' hw' hb
    nlinarith
  calc
    4 * ((correlation (YamadaPottB (F := F)) (YamadaPottB (F := F))
        (a, b)).card : ℤ) =
        ∑ r ∈ ypNonexceptionalRows (F := F) a,
          4 * ((((ypSignedRow (F := F) (-YamadaPott.skew r)).filter fun c ↦
            c - b ∈ ypSignedRow (F := F) (-YamadaPott.skew (r - a))).card : ℕ) : ℤ) := by
      rw [hdecomp, Finset.mul_sum]
    _ = ∑ r ∈ ypNonexceptionalRows (F := F) a,
        ((Fintype.card F : ℤ) + 2 -
          YamadaPott.skew r * YamadaPott.skew (r - a) -
          (YamadaPott.skew r - YamadaPott.skew (r - a)) *
            quadraticChar F b) := Finset.sum_congr rfl hrow
    _ = _ := by
      simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, sum_ypRows_skew_product (F := F) ha,
        sum_ypRows_skew_difference (F := F) hF hmod ha]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [card_ypNonexceptionalRows (F := F) hF hcard ha, hcard]
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * t)]
      push_cast
      ring

private theorem card_ypNonexceptionalRows_zero (hF : ringChar F ≠ 2) {t : ℕ}
    (hcard : Fintype.card F = 4 * t + 3) :
    (ypNonexceptionalRows (F := F)
      (0 : Additive (YamadaPottSquareSubgroup F))).card = 2 * t := by
  simp only [ypNonexceptionalRows, Finset.erase_idem]
  rw [Finset.card_erase_of_mem (Finset.mem_univ
    (0 : Additive (YamadaPottSquareSubgroup F))), Finset.card_univ,
    Fintype.card_additive, YamadaPott.card_squareSubgroup (F := F) hF hcard]
  omega

/-- The `a=0`, `b≠0` line of equation (10) for `A`. -/
theorem YamadaPott_A_correlation_first_zero
    (hF : ringChar F ≠ 2) {t : ℕ}
    (hcard : Fintype.card F = 4 * t + 3) {b : F} (hb : b ≠ 0) :
    2 * ((correlation (YamadaPottA (F := F)) (YamadaPottA (F := F))
      (0, b)).card : ℤ) = (2 * t + 1 : ℤ) ^ 2 - 1 := by
  have hmod : Fintype.card F % 4 = 3 := by omega
  have hdecomp := congrArg (fun n : ℕ ↦ (n : ℤ))
    (card_YamadaPott_A_correlation_eq_row_sum (F := F)
      (0 : Additive (YamadaPottSquareSubgroup F)) b)
  push_cast at hdecomp
  have hrow : ∀ r ∈ ypNonexceptionalRows (F := F)
      (0 : Additive (YamadaPottSquareSubgroup F)),
      4 * ((((ypSignedRow (F := F) (YamadaPott.skew r)).filter fun c ↦
        c - b ∈ ypSignedRow (F := F) (YamadaPott.skew (r - 0))).card : ℕ) : ℤ) =
        (Fintype.card F : ℤ) + 1 := by
    intro r hr
    have hr0 : r ≠ 0 := (Finset.mem_erase.mp
      (Finset.mem_erase.mp hr).2).1
    have hs := YamadaPott_skew_sign (F := F) hr0
    have h := four_mul_card_ypSignedRow_correlation
      (F := F) hF hmod hs (by simpa using hs) hb
    rcases hs with hs | hs <;> simp [hs] at h ⊢ <;> linarith
  have hfour :
      4 * ((correlation (YamadaPottA (F := F)) (YamadaPottA (F := F))
        (0, b)).card : ℤ) =
        ((2 * t : ℕ) : ℤ) * ((Fintype.card F : ℤ) + 1) := by
    rw [hdecomp, Finset.mul_sum]
    calc
      _ = ∑ r ∈ ypNonexceptionalRows (F := F)
          (0 : Additive (YamadaPottSquareSubgroup F)),
          ((Fintype.card F : ℤ) + 1) := Finset.sum_congr rfl hrow
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [card_ypNonexceptionalRows_zero (F := F) hF hcard]
  rw [hcard] at hfour
  push_cast at hfour
  nlinarith

/-- The `a=0`, `b≠0` line of equation (10) for `B`. -/
theorem YamadaPott_B_correlation_first_zero
    (hF : ringChar F ≠ 2) {t : ℕ}
    (hcard : Fintype.card F = 4 * t + 3) {b : F} (hb : b ≠ 0) :
    2 * ((correlation (YamadaPottB (F := F)) (YamadaPottB (F := F))
      (0, b)).card : ℤ) = (2 * t + 1 : ℤ) ^ 2 - 1 := by
  have hmod : Fintype.card F % 4 = 3 := by omega
  have hdecomp := congrArg (fun n : ℕ ↦ (n : ℤ))
    (card_YamadaPott_B_correlation_eq_row_sum (F := F)
      (0 : Additive (YamadaPottSquareSubgroup F)) b)
  push_cast at hdecomp
  have hrow : ∀ r ∈ ypNonexceptionalRows (F := F)
      (0 : Additive (YamadaPottSquareSubgroup F)),
      4 * ((((ypSignedRow (F := F) (-YamadaPott.skew r)).filter fun c ↦
        c - b ∈ ypSignedRow (F := F) (-YamadaPott.skew (r - 0))).card : ℕ) : ℤ) =
        (Fintype.card F : ℤ) + 1 := by
    intro r hr
    have hr0 : r ≠ 0 := (Finset.mem_erase.mp
      (Finset.mem_erase.mp hr).2).1
    have hs := YamadaPott_skew_sign (F := F) hr0
    have hns : -YamadaPott.skew r = -1 ∨ -YamadaPott.skew r = 1 := by
      rcases hs with hs | hs <;> simp [hs]
    have hns2 : -YamadaPott.skew (r - 0) = -1 ∨
        -YamadaPott.skew (r - 0) = 1 := by
      simpa only [sub_zero] using hns
    have h := four_mul_card_ypSignedRow_correlation
      (F := F) hF hmod hns hns2 hb
    rcases hns with hs | hs <;> simp [hs] at h ⊢ <;> linarith
  have hfour :
      4 * ((correlation (YamadaPottB (F := F)) (YamadaPottB (F := F))
        (0, b)).card : ℤ) =
        ((2 * t : ℕ) : ℤ) * ((Fintype.card F : ℤ) + 1) := by
    rw [hdecomp, Finset.mul_sum]
    calc
      _ = ∑ r ∈ ypNonexceptionalRows (F := F)
          (0 : Additive (YamadaPottSquareSubgroup F)),
          ((Fintype.card F : ℤ) + 1) := Finset.sum_congr rfl hrow
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [card_ypNonexceptionalRows_zero (F := F) hF hcard]
  rw [hcard] at hfour
  push_cast at hfour
  nlinarith

private theorem two_mul_card_ypSignedRow_zero_correlation
    (hF : ringChar F ≠ 2) {t : ℕ}
    (hcard : Fintype.card F = 4 * t + 3)
    {z w : ℤ} (hz : z = -1 ∨ z = 1) (hw : w = -1 ∨ w = 1) :
    2 * (((ypSignedRow (F := F) z).filter fun c ↦
      c ∈ ypSignedRow (F := F) w).card : ℤ) =
      (2 * t + 1 : ℤ) + 2 + (2 * t + 1 : ℤ) * z * w := by
  have hq : Fintype.card F = 2 * (2 * t + 1) + 1 := by omega
  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
  · have heq : ((ypSignedRow (F := F) (-1)).filter fun c ↦
        c ∈ ypSignedRow (F := F) (-1)) = insert 0 (quadraticNegative F) := by
      ext c
      simp only [ypSignedRow, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, mem_quadraticNegative]
      constructor
      · rintro ⟨hc, _⟩
        rcases hc with hc | hc
        · exact Or.inl hc
        · exact Or.inr (by omega)
      · intro hc
        rcases hc with hc | hc
        · subst c; simp
        · exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
    rw [heq, Finset.card_insert_of_notMem (by simp),
      card_quadraticNegative_of_card_eq (F := F) hF hq]
    push_cast
    ring
  · have heq : ((ypSignedRow (F := F) (-1)).filter fun c ↦
        c ∈ ypSignedRow (F := F) 1) = {0} := by
      ext c
      simp only [ypSignedRow, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hc, hc'⟩
        rcases hc with hc | hc
        · exact hc
        · rcases hc' with hc' | hc'
          · exact hc'
          · exfalso; omega
      · rintro rfl
        simp
    rw [heq, Finset.card_singleton]
    ring
  · have heq : ((ypSignedRow (F := F) 1).filter fun c ↦
        c ∈ ypSignedRow (F := F) (-1)) = {0} := by
      ext c
      simp only [ypSignedRow, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · rintro ⟨hc, hc'⟩
        rcases hc with hc | hc
        · exact hc
        · rcases hc' with hc' | hc'
          · exact hc'
          · exfalso; omega
      · rintro rfl
        simp
    rw [heq, Finset.card_singleton]
    ring
  · have heq : ((ypSignedRow (F := F) 1).filter fun c ↦
        c ∈ ypSignedRow (F := F) 1) = insert 0 (quadraticPositive F) := by
      ext c
      simp only [ypSignedRow, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, mem_quadraticPositive, one_mul]
      constructor
      · rintro ⟨hc, _⟩
        exact hc
      · intro hc
        exact ⟨hc, hc⟩
    rw [heq, Finset.card_insert_of_notMem (by simp),
      card_quadraticPositive_of_card_eq (F := F) hF hq]
    push_cast
    ring

/-- The `a≠0`, `b=0` line of equation (10) for `A`. -/
theorem YamadaPott_A_correlation_second_zero
    (hF : ringChar F ≠ 2) {t : ℕ}
    (hcard : Fintype.card F = 4 * t + 3)
    {a : Additive (YamadaPottSquareSubgroup F)} (ha : a ≠ 0) :
    2 * ((correlation (YamadaPottA (F := F)) (YamadaPottA (F := F))
      (a, 0)).card : ℤ) =
      (2 * t + 1 : ℤ) ^ 2 - 4 +
        (2 * t + 1 : ℤ) * YamadaPottCorrH F (YamadaPott.squareValue a) := by
  have htpos := YamadaPott_parameter_pos (F := F) hF hcard ha
  have hdecomp := congrArg (fun n : ℕ ↦ (n : ℤ))
    (card_YamadaPott_A_correlation_eq_row_sum (F := F) a 0)
  push_cast at hdecomp
  have hrow : ∀ r ∈ ypNonexceptionalRows (F := F) a,
      2 * ((((ypSignedRow (F := F) (YamadaPott.skew r)).filter fun c ↦
        c - 0 ∈ ypSignedRow (F := F) (YamadaPott.skew (r - a))).card : ℕ) : ℤ) =
        (2 * t + 1 : ℤ) + 2 +
          (2 * t + 1 : ℤ) * YamadaPott.skew r * YamadaPott.skew (r - a) := by
    intro r hr
    have hr0 : r ≠ 0 := (Finset.mem_erase.mp
      (Finset.mem_erase.mp hr).2).1
    have hra : r - a ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hr).1
    simpa only [sub_zero] using
      (two_mul_card_ypSignedRow_zero_correlation (F := F) hF hcard
        (YamadaPott_skew_sign hr0) (YamadaPott_skew_sign hra))
  calc
    2 * ((correlation (YamadaPottA (F := F)) (YamadaPottA (F := F))
        (a, 0)).card : ℤ) =
        ∑ r ∈ ypNonexceptionalRows (F := F) a,
          2 * ((((ypSignedRow (F := F) (YamadaPott.skew r)).filter fun c ↦
            c - 0 ∈ ypSignedRow (F := F) (YamadaPott.skew (r - a))).card : ℕ) : ℤ) := by
      rw [hdecomp, Finset.mul_sum]
    _ = ∑ r ∈ ypNonexceptionalRows (F := F) a,
        ((2 * t + 1 : ℤ) + 2 +
          (2 * t + 1 : ℤ) * YamadaPott.skew r *
            YamadaPott.skew (r - a)) := Finset.sum_congr rfl hrow
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      rw [show (∑ r ∈ ypNonexceptionalRows (F := F) a,
          (2 * t + 1 : ℤ) * YamadaPott.skew r * YamadaPott.skew (r - a)) =
          (2 * t + 1 : ℤ) *
            (∑ r ∈ ypNonexceptionalRows (F := F) a,
              YamadaPott.skew r * YamadaPott.skew (r - a)) by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r _
              ring,
        sum_ypRows_skew_product (F := F) ha]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [card_ypNonexceptionalRows (F := F) hF hcard ha,
        Nat.cast_sub (by omega : 1 ≤ 2 * t)]
      push_cast
      ring

/-- The `a≠0`, `b=0` line of equation (10) for `B`. -/
theorem YamadaPott_B_correlation_second_zero
    (hF : ringChar F ≠ 2) {t : ℕ}
    (hcard : Fintype.card F = 4 * t + 3)
    {a : Additive (YamadaPottSquareSubgroup F)} (ha : a ≠ 0) :
    2 * ((correlation (YamadaPottB (F := F)) (YamadaPottB (F := F))
      (a, 0)).card : ℤ) =
      (2 * t + 1 : ℤ) ^ 2 - 4 +
        (2 * t + 1 : ℤ) * YamadaPottCorrH F (YamadaPott.squareValue a) := by
  have htpos := YamadaPott_parameter_pos (F := F) hF hcard ha
  have hdecomp := congrArg (fun n : ℕ ↦ (n : ℤ))
    (card_YamadaPott_B_correlation_eq_row_sum (F := F) a 0)
  push_cast at hdecomp
  have hrow : ∀ r ∈ ypNonexceptionalRows (F := F) a,
      2 * ((((ypSignedRow (F := F) (-YamadaPott.skew r)).filter fun c ↦
        c - 0 ∈ ypSignedRow (F := F) (-YamadaPott.skew (r - a))).card : ℕ) : ℤ) =
        (2 * t + 1 : ℤ) + 2 +
          (2 * t + 1 : ℤ) * YamadaPott.skew r * YamadaPott.skew (r - a) := by
    intro r hr
    have hr0 : r ≠ 0 := (Finset.mem_erase.mp
      (Finset.mem_erase.mp hr).2).1
    have hra : r - a ≠ 0 := sub_ne_zero.mpr (Finset.mem_erase.mp hr).1
    have hz := YamadaPott_skew_sign (F := F) hr0
    have hw := YamadaPott_skew_sign (F := F) hra
    have hz' : -YamadaPott.skew r = -1 ∨ -YamadaPott.skew r = 1 := by
      rcases hz with h | h <;> simp [h]
    have hw' : -YamadaPott.skew (r - a) = -1 ∨
        -YamadaPott.skew (r - a) = 1 := by
      rcases hw with h | h <;> simp [h]
    have h := two_mul_card_ypSignedRow_zero_correlation
      (F := F) hF hcard hz' hw'
    simp only [sub_zero] at h ⊢
    nlinarith
  calc
    2 * ((correlation (YamadaPottB (F := F)) (YamadaPottB (F := F))
        (a, 0)).card : ℤ) =
        ∑ r ∈ ypNonexceptionalRows (F := F) a,
          2 * ((((ypSignedRow (F := F) (-YamadaPott.skew r)).filter fun c ↦
            c - 0 ∈ ypSignedRow (F := F) (-YamadaPott.skew (r - a))).card : ℕ) : ℤ) := by
      rw [hdecomp, Finset.mul_sum]
    _ = ∑ r ∈ ypNonexceptionalRows (F := F) a,
        ((2 * t + 1 : ℤ) + 2 +
          (2 * t + 1 : ℤ) * YamadaPott.skew r *
            YamadaPott.skew (r - a)) := Finset.sum_congr rfl hrow
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      rw [show (∑ r ∈ ypNonexceptionalRows (F := F) a,
          (2 * t + 1 : ℤ) * YamadaPott.skew r * YamadaPott.skew (r - a)) =
          (2 * t + 1 : ℤ) *
            (∑ r ∈ ypNonexceptionalRows (F := F) a,
              YamadaPott.skew r * YamadaPott.skew (r - a)) by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro r _
              ring,
        sum_ypRows_skew_product (F := F) ha]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [card_ypNonexceptionalRows (F := F) hF hcard ha,
        Nat.cast_sub (by omega : 1 ≤ 2 * t)]
      push_cast
      ring
end BookS3
