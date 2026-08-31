import BookS3.DifferenceLift
import BookS3.SourceIdentity
import BookS3.CodegreeArithmetic
import BookS3.AffineCorrelation

/-!
# The concrete Yamada--Pott difference sets

The cyclic coordinate of the notebook is represented without choosing a
generator: it is the square subgroup of `Fˣ`, written additively.  Consequently
subtraction in the first coordinate is multiplicative division, exactly as in
the notebook's powers `g^(s-r)`.
-/

namespace BookS3

open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- A field of cardinality `4t+3` automatically has odd characteristic. -/
theorem YamadaPott.ringChar_ne_two {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3) : ringChar F ≠ 2 := by
  intro hchar
  have hdvdChar : 2 ∣ ringChar F := by simp [hchar]
  have hdvdCard : 2 ∣ Fintype.card F :=
    (prime_dvd_char_iff_dvd_card (R := F) 2).mp hdvdChar
  rw [hcard] at hdvdCard
  omega

/-- The generator-free version of `Z_m × F`: the square subgroup is written
additively so the whole carrier is an additive commutative group. -/
abbrev YamadaPottW (F : Type*) [Field F] :=
  Additive (YamadaPottSquareSubgroup F) × F

/-- The field value represented by a point of the additive square subgroup. -/
def YamadaPott.squareValue
    (r : Additive (YamadaPottSquareSubgroup F)) : F :=
  ((Additive.toMul r : YamadaPottSquareSubgroup F) : Fˣ)

omit [Fintype F] [DecidableEq F] in
@[simp] theorem YamadaPott.squareValue_zero :
    YamadaPott.squareValue (F := F) 0 = 1 := rfl

omit [Fintype F] [DecidableEq F] in
@[simp] theorem YamadaPott.squareValue_neg
    (r : Additive (YamadaPottSquareSubgroup F)) :
    YamadaPott.squareValue (-r) = (YamadaPott.squareValue r)⁻¹ := by
  simp [YamadaPott.squareValue]

omit [Fintype F] [DecidableEq F] in
theorem YamadaPott.squareValue_ne_zero
    (r : Additive (YamadaPottSquareSubgroup F)) :
    YamadaPott.squareValue r ≠ 0 := Units.ne_zero _

omit [Fintype F] [DecidableEq F] in
theorem YamadaPott.squareValue_isSquare
    (r : Additive (YamadaPottSquareSubgroup F)) :
    IsSquare (YamadaPott.squareValue r) := by
  rcases (Additive.toMul r).property with ⟨u, hu⟩
  refine ⟨((u : Fˣ) : F), ?_⟩
  have hv := congrArg (fun z : Fˣ => (z : F)) hu
  simpa [YamadaPott.squareValue] using hv

theorem YamadaPott.squareValue_mem_S
    (r : Additive (YamadaPottSquareSubgroup F)) :
    YamadaPott.squareValue r ∈ YamadaPottS F := by
  exact mem_YamadaPottS.mpr
    ⟨YamadaPott.squareValue_ne_zero r, YamadaPott.squareValue_isSquare r⟩

/-- Coercion identifies the abstract square subgroup with the concrete finset
of nonzero field squares used by the source identities. -/
noncomputable def YamadaPott.squareSubgroupEquivS :
    YamadaPottSquareSubgroup F ≃ {x // x ∈ YamadaPottS F} where
  toFun r := ⟨((r : Fˣ) : F), by
    rw [mem_YamadaPottS]
    constructor
    · exact Units.ne_zero _
    · rcases r.property with ⟨u, hu⟩
      refine ⟨((u : Fˣ) : F), ?_⟩
      have hv := congrArg (fun z : Fˣ => (z : F)) hu
      simpa using hv⟩
  invFun x := ⟨Units.mk0 x.1 (mem_YamadaPottS.mp x.2).1, by
    rcases (mem_YamadaPottS.mp x.2).2 with ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      intro hz
      rw [hz, zero_mul] at hy
      exact (mem_YamadaPottS.mp x.2).1 hy
    refine ⟨Units.mk0 y hy0, ?_⟩
    apply Units.ext
    simpa using hy⟩
  left_inv r := by
    apply Subtype.ext
    apply Units.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl

theorem YamadaPott.card_squareSubgroup (hF : ringChar F ≠ 2) {r : Nat}
    (hcard : Fintype.card F = 4 * r + 3) :
    Fintype.card (YamadaPottSquareSubgroup F) = 2 * r + 1 := by
  rw [Fintype.card_congr YamadaPott.squareSubgroupEquivS]
  rw [Fintype.card_coe, card_YamadaPottS (F := F) hF hcard]

theorem YamadaPott.card_W (hF : ringChar F ≠ 2) {r : Nat}
    (hcard : Fintype.card F = 4 * r + 3) :
    Fintype.card (YamadaPottW F) = (2 * r + 1) * (4 * r + 3) := by
  rw [Fintype.card_prod, hcard]
  rw [Fintype.card_additive]
  rw [YamadaPott.card_squareSubgroup hF hcard]

/-- The skew sequence `h_r=χ(1-g^r)` on the generator-free square subgroup. -/
def YamadaPott.skew
    (r : Additive (YamadaPottSquareSubgroup F)) : ℤ :=
  YamadaPottH (YamadaPott.squareValue r)

private noncomputable def YamadaPott.crossNormalize : YamadaPottW F ≃ YamadaPottW F where
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

omit [Fintype F] [DecidableEq F] in
@[simp] theorem YamadaPott.squareValue_eq_one_iff
    (r : Additive (YamadaPottSquareSubgroup F)) :
    YamadaPott.squareValue r = 1 ↔ r = 0 := by
  constructor
  · intro h
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    simpa [YamadaPott.squareValue] using h
  · rintro rfl
    exact YamadaPott.squareValue_zero

private theorem YamadaPott.skew_dichotomy
    (r : Additive (YamadaPottSquareSubgroup F)) (hr : r ≠ 0) :
    YamadaPott.skew r = -1 ∨ YamadaPott.skew r = 1 := by
  have hs : 1 - YamadaPott.squareValue r ≠ 0 := by
    intro h
    have : YamadaPott.squareValue r = 1 := (sub_eq_zero.mp h).symm
    exact hr (YamadaPott.squareValue_eq_one_iff r |>.mp this)
  rcases quadraticChar_dichotomy hs with hpos | hneg
  · exact Or.inr (by simpa [YamadaPott.skew, YamadaPottH] using hpos)
  · exact Or.inl (by simpa [YamadaPott.skew, YamadaPottH] using hneg)

private noncomputable def YamadaPott.ARow
    (r : Additive (YamadaPottSquareSubgroup F)) : Finset F :=
  Finset.univ.filter fun c =>
    c = 0 ∨ YamadaPott.skew r * quadraticChar F c = 1

private noncomputable def YamadaPott.BRow
    (r : Additive (YamadaPottSquareSubgroup F)) : Finset F :=
  Finset.univ.filter fun c =>
    c = 0 ∨ YamadaPott.skew r * quadraticChar F c = -1

private theorem YamadaPott.card_ARow (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    (r : Additive (YamadaPottSquareSubgroup F)) (hr : r ≠ 0) :
    (YamadaPott.ARow r).card = 2 * t + 2 := by
  have hq : Fintype.card F = 2 * (2 * t + 1) + 1 := by omega
  rcases YamadaPott.skew_dichotomy r hr with hneg | hpos
  · have hrow : YamadaPott.ARow r = insert 0 (quadraticNegative F) := by
      ext c
      simp only [YamadaPott.ARow, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, mem_quadraticNegative, hneg]
      constructor <;> intro h
      · rcases h with hzero | hprod
        · exact Or.inl hzero
        · exact Or.inr (by omega)
      · rcases h with hzero | hchi
        · exact Or.inl hzero
        · exact Or.inr (by omega)
    rw [hrow, Finset.card_insert_of_notMem]
    · rw [card_quadraticNegative_of_card_eq hF hq]
    · simp
  · have hrow : YamadaPott.ARow r = insert 0 (quadraticPositive F) := by
      ext c
      simp [YamadaPott.ARow, hpos]
    rw [hrow, Finset.card_insert_of_notMem]
    · rw [card_quadraticPositive_of_card_eq hF hq]
    · simp

private theorem YamadaPott.card_BRow (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    (r : Additive (YamadaPottSquareSubgroup F)) (hr : r ≠ 0) :
    (YamadaPott.BRow r).card = 2 * t + 2 := by
  have hq : Fintype.card F = 2 * (2 * t + 1) + 1 := by omega
  rcases YamadaPott.skew_dichotomy r hr with hneg | hpos
  · have hrow : YamadaPott.BRow r = insert 0 (quadraticPositive F) := by
      ext c
      simp only [YamadaPott.BRow, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, mem_quadraticPositive, hneg]
      constructor <;> intro h
      · rcases h with hzero | hprod
        · exact Or.inl hzero
        · exact Or.inr (by omega)
      · rcases h with hzero | hchi
        · exact Or.inl hzero
        · exact Or.inr (by omega)
    rw [hrow, Finset.card_insert_of_notMem]
    · rw [card_quadraticPositive_of_card_eq hF hq]
    · simp
  · have hrow : YamadaPott.BRow r = insert 0 (quadraticNegative F) := by
      ext c
      simp only [YamadaPott.BRow, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_insert, mem_quadraticNegative, hpos]
      constructor <;> intro h
      · rcases h with hzero | hprod
        · exact Or.inl hzero
        · exact Or.inr (by omega)
      · rcases h with hzero | hchi
        · exact Or.inl hzero
        · exact Or.inr (by omega)
    rw [hrow, Finset.card_insert_of_notMem]
    · rw [card_quadraticNegative_of_card_eq hF hq]
    · simp

/-- Notebook equation (7), first within-fibre connection set. -/
noncomputable def YamadaPottA : Finset (YamadaPottW F) :=
  Finset.univ.filter fun p =>
    p.1 ≠ 0 ∧
      (p.2 = 0 ∨ YamadaPott.skew p.1 * quadraticChar F p.2 = 1)

/-- Notebook equation (7), second within-fibre connection set. -/
noncomputable def YamadaPottB : Finset (YamadaPottW F) :=
  Finset.univ.filter fun p =>
    p.1 ≠ 0 ∧
      (p.2 = 0 ∨ YamadaPott.skew p.1 * quadraticChar F p.2 = -1)

/-- Notebook equation (7), oriented cross-fibre connection set.  The expression
`c * squareValue(r)⁻¹` is exactly `c g⁻ʳ`. -/
noncomputable def YamadaPottC : Finset (YamadaPottW F) :=
  Finset.univ.filter fun p =>
    p.2 * (YamadaPott.squareValue p.1)⁻¹ ∈ YamadaPottD F

@[simp] theorem mem_YamadaPottA {p : YamadaPottW F} :
    p ∈ YamadaPottA ↔
      p.1 ≠ 0 ∧
        (p.2 = 0 ∨ YamadaPott.skew p.1 * quadraticChar F p.2 = 1) := by
  simp [YamadaPottA]

@[simp] theorem mem_YamadaPottB {p : YamadaPottW F} :
    p ∈ YamadaPottB ↔
      p.1 ≠ 0 ∧
        (p.2 = 0 ∨ YamadaPott.skew p.1 * quadraticChar F p.2 = -1) := by
  simp [YamadaPottB]

@[simp] theorem mem_YamadaPottC {p : YamadaPottW F} :
    p ∈ YamadaPottC ↔
      p.2 * (YamadaPott.squareValue p.1)⁻¹ ∈ YamadaPottD F := by
  simp [YamadaPottC]

theorem YamadaPott.card_C (hF : ringChar F ≠ 2) {r : Nat}
    (hcard : Fintype.card F = 4 * r + 3) :
    (YamadaPottC (F := F)).card = (2 * r + 1) * (2 * r + 2) := by
  classical
  let target : Finset (YamadaPottW F) :=
    Finset.univ ×ˢ YamadaPottD F
  have hcardEq : (YamadaPottC (F := F)).card = target.card := by
    apply Finset.card_equiv (YamadaPott.crossNormalize (F := F))
    intro p
    simp [target, YamadaPott.crossNormalize, YamadaPottC]
  rw [hcardEq]
  change (Finset.univ ×ˢ YamadaPottD F).card = _
  rw [Finset.card_product, Finset.card_univ, Fintype.card_additive,
    YamadaPott.card_squareSubgroup hF hcard, card_YamadaPottD (F := F) hF hcard]

theorem YamadaPott.card_A (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3) :
    (YamadaPottA (F := F)).card = (2 * t + 1) ^ 2 - 1 := by
  classical
  let R := Additive (YamadaPottSquareSubgroup F)
  let rows : R → Finset (YamadaPottW F) := fun r =>
    ({r} : Finset R) ×ˢ YamadaPott.ARow r
  have hdisj : ((Finset.univ.erase (0 : R) : Finset R) : Set R).PairwiseDisjoint rows := by
    intro r hr s hs hrs
    change Disjoint (rows r) (rows s)
    dsimp only [rows]
    rw [Finset.disjoint_product]
    left
    simp only [Finset.disjoint_singleton]
    exact hrs
  have hA : YamadaPottA (F := F) =
      (Finset.univ.erase (0 : R)).biUnion rows := by
    ext p
    simp only [YamadaPottA, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.mem_erase, rows, Finset.mem_product,
      Finset.mem_singleton, YamadaPott.ARow]
    aesop
  rw [hA, Finset.card_biUnion hdisj]
  have hsubcard := YamadaPott.card_squareSubgroup (F := F) hF hcard
  simp only [rows, Finset.card_product, Finset.card_singleton, one_mul]
  have hrow : ∀ r ∈ (Finset.univ.erase (0 : R)),
      (YamadaPott.ARow r).card = 2 * t + 2 := by
    intro r hr
    exact YamadaPott.card_ARow hF hcard r (Finset.mem_erase.mp hr).1
  rw [Finset.sum_congr rfl hrow]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ (0 : R)),
    Finset.card_univ, Fintype.card_additive, hsubcard]
  simp only [nsmul_eq_mul]
  rw [show 2 * t + 1 - 1 = 2 * t by omega]
  have hpos : 1 ≤ (2 * t + 1) ^ 2 := Nat.one_le_pow 2 (2 * t + 1) (by omega)
  symm
  apply (Nat.sub_eq_iff_eq_add hpos).2
  simp only [Nat.cast_id]
  ring

theorem YamadaPott.card_B (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3) :
    (YamadaPottB (F := F)).card = (2 * t + 1) ^ 2 - 1 := by
  classical
  let R := Additive (YamadaPottSquareSubgroup F)
  let rows : R → Finset (YamadaPottW F) := fun r =>
    ({r} : Finset R) ×ˢ YamadaPott.BRow r
  have hdisj : ((Finset.univ.erase (0 : R) : Finset R) : Set R).PairwiseDisjoint rows := by
    intro r hr s hs hrs
    change Disjoint (rows r) (rows s)
    dsimp only [rows]
    rw [Finset.disjoint_product]
    left
    simp only [Finset.disjoint_singleton]
    exact hrs
  have hB : YamadaPottB (F := F) =
      (Finset.univ.erase (0 : R)).biUnion rows := by
    ext p
    simp only [YamadaPottB, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_biUnion, Finset.mem_erase, rows, Finset.mem_product,
      Finset.mem_singleton, YamadaPott.BRow]
    aesop
  rw [hB, Finset.card_biUnion hdisj]
  have hsubcard := YamadaPott.card_squareSubgroup (F := F) hF hcard
  simp only [rows, Finset.card_product, Finset.card_singleton, one_mul]
  have hrow : ∀ r ∈ (Finset.univ.erase (0 : R)),
      (YamadaPott.BRow r).card = 2 * t + 2 := by
    intro r hr
    exact YamadaPott.card_BRow hF hcard r (Finset.mem_erase.mp hr).1
  rw [Finset.sum_congr rfl hrow]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ (0 : R)),
    Finset.card_univ, Fintype.card_additive, hsubcard]
  simp only [nsmul_eq_mul]
  rw [show 2 * t + 1 - 1 = 2 * t by omega]
  have hpos : 1 ≤ (2 * t + 1) ^ 2 := Nat.one_le_pow 2 (2 * t + 1) (by omega)
  symm
  apply (Nat.sub_eq_iff_eq_add hpos).2
  simp only [Nat.cast_id]
  ring

private theorem YamadaPott.skew_neg
    (hF : ringChar F ≠ 2) (hmod : Fintype.card F % 4 = 3)
    (r : Additive (YamadaPottSquareSubgroup F)) :
    YamadaPott.skew (-r) = -YamadaPott.skew r := by
  simpa [YamadaPott.skew, YamadaPott.squareValue_neg] using
    YamadaPottH_inv (F := F) hF hmod (YamadaPott.squareValue_mem_S r)

private theorem quadraticChar_neg_apply
    (hF : ringChar F ≠ 2) (hmod : Fintype.card F % 4 = 3) (c : F) :
    quadraticChar F (-c) = -quadraticChar F c := by
  have hneg := quadraticChar_neg_one_of_card_mod_four_eq_three (F := F) hF hmod
  rw [show -c = (-1 : F) * c by ring, map_mul, hneg]
  ring

theorem YamadaPottA_neg_mem
    (hF : ringChar F ≠ 2) (hmod : Fintype.card F % 4 = 3)
    (p : YamadaPottW F) : -p ∈ YamadaPottA ↔ p ∈ YamadaPottA := by
  rcases p with ⟨r, c⟩
  have hh := YamadaPott.skew_neg (F := F) hF hmod r
  have hc := quadraticChar_neg_apply (F := F) hF hmod c
  simp only [mem_YamadaPottA, Prod.fst_neg, Prod.snd_neg, neg_ne_zero,
    neg_eq_zero, hh, hc]
  constructor <;> rintro ⟨hr, hc0 | hp⟩
  · exact ⟨hr, Or.inl hc0⟩
  · refine ⟨hr, Or.inr ?_⟩
    nlinarith
  · exact ⟨hr, Or.inl hc0⟩
  · refine ⟨hr, Or.inr ?_⟩
    nlinarith

theorem YamadaPottB_neg_mem
    (hF : ringChar F ≠ 2) (hmod : Fintype.card F % 4 = 3)
    (p : YamadaPottW F) : -p ∈ YamadaPottB ↔ p ∈ YamadaPottB := by
  rcases p with ⟨r, c⟩
  have hh := YamadaPott.skew_neg (F := F) hF hmod r
  have hc := quadraticChar_neg_apply (F := F) hF hmod c
  simp only [mem_YamadaPottB, Prod.fst_neg, Prod.snd_neg, neg_ne_zero,
    neg_eq_zero, hh, hc]
  constructor <;> rintro ⟨hr, hc0 | hp⟩
  · exact ⟨hr, Or.inl hc0⟩
  · refine ⟨hr, Or.inr ?_⟩
    nlinarith
  · exact ⟨hr, Or.inl hc0⟩
  · refine ⟨hr, Or.inr ?_⟩
    nlinarith

theorem zero_not_mem_YamadaPottA : (0 : YamadaPottW F) ∉ YamadaPottA := by
  simp

theorem zero_not_mem_YamadaPottB : (0 : YamadaPottW F) ∉ YamadaPottB := by
  simp

/-- The concrete difference data underlying the Yamada--Pott lift. -/
noncomputable def YamadaPottDifferenceData
    (hF : ringChar F ≠ 2) (hmod : Fintype.card F % 4 = 3) :
    DifferenceData (YamadaPottW F) where
  A := YamadaPottA
  B := YamadaPottB
  C := YamadaPottC
  A_neg := YamadaPottA_neg_mem hF hmod
  B_neg := YamadaPottB_neg_mem hF hmod
  zero_not_mem_A := zero_not_mem_YamadaPottA
  zero_not_mem_B := zero_not_mem_YamadaPottB

/-- The Ramsey parameter `n=m²+(m+1)/2` with `m=2t+1`. -/
def YamadaPottN (t : Nat) : Nat :=
  CodegreeArithmetic.bookParameter (2 * t + 1)

theorem YamadaPottN_eq (t : Nat) :
    YamadaPottN t = 4 * t ^ 2 + 5 * t + 2 := by
  simp [YamadaPottN, CodegreeArithmetic.bookParameter]
  rw [show (2 * t + 2) / 2 = t + 1 by omega]
  ring

theorem YamadaPott.profile_vertex_count
    (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3) :
    2 * Fintype.card (YamadaPottW F) = 4 * YamadaPottN t - 2 := by
  rw [YamadaPott.card_W hF hcard, YamadaPottN_eq]
  symm
  apply (Nat.sub_eq_iff_eq_add (by omega)).2
  ring

theorem YamadaPott.profile_degree_A
    (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3) :
    (YamadaPottA (F := F)).card + (YamadaPottC (F := F)).card =
      2 * YamadaPottN t - 2 := by
  rw [YamadaPott.card_A hF hcard, YamadaPott.card_C hF hcard, YamadaPottN_eq]
  have hsq : (2 * t + 1) ^ 2 - 1 = 4 * t ^ 2 + 4 * t := by
    apply (Nat.sub_eq_iff_eq_add (Nat.one_le_pow 2 (2 * t + 1) (by omega))).2
    ring
  have hn : 2 * (4 * t ^ 2 + 5 * t + 2) - 2 = 8 * t ^ 2 + 10 * t + 2 := by
    apply (Nat.sub_eq_iff_eq_add (by omega)).2
    ring
  rw [hsq, hn]
  ring

theorem YamadaPott.profile_degree_B
    (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3) :
    (YamadaPottB (F := F)).card + (YamadaPottC (F := F)).card =
      2 * YamadaPottN t - 2 := by
  rw [YamadaPott.card_B hF hcard, YamadaPott.card_C hF hcard, YamadaPottN_eq]
  have hsq : (2 * t + 1) ^ 2 - 1 = 4 * t ^ 2 + 4 * t := by
    apply (Nat.sub_eq_iff_eq_add (Nat.one_le_pow 2 (2 * t + 1) (by omega))).2
    ring
  have hn : 2 * (4 * t ^ 2 + 5 * t + 2) - 2 = 8 * t ^ 2 + 10 * t + 2 := by
    apply (Nat.sub_eq_iff_eq_add (by omega)).2
    ring
  rw [hsq, hn]
  ring

end BookS3
