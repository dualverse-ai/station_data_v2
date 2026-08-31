import BookS3.DifferenceLift
import BookS3.AffineCorrelation
import BookS3.YamadaPottConstruction

/-!
# The mixed cross-fibre correlation

This file proves the remaining convolution identity used for cross-fibre
common-neighbor counts.  Its assumptions are pointwise membership and explicit
row/column cardinalities of finite connection sets; it assumes no graph
codegree or book-freeness conclusion.
-/

namespace BookS3

open scoped Classical

section Generic

variable {R K : Type*} [AddCommGroup R] [Fintype R] [DecidableEq R]
  [AddCommGroup K] [Fintype K] [DecidableEq K]

/-- The `0/1` membership indicator of a finset. -/
noncomputable def memIndicator (S : Finset (R × K)) (x : R × K) : Nat :=
  if x ∈ S then 1 else 0

/-- A fixed first-coordinate row of a connection set. -/
noncomputable def firstRow (C : Finset (R × K)) (a : R) : Finset (R × K) :=
  C.filter fun x => x.1 = a

/-- A fixed field-coordinate column of a connection set. -/
noncomputable def secondColumn (C : Finset (R × K)) (b : K) : Finset (R × K) :=
  C.filter fun x => x.2 = b

/-- The baseline term selected by `r ≠ 0` after convolving the pointwise
`A+B` identity with `C`. -/
noncomputable def mixedBaseline (C : Finset (R × K)) (d : R × K) :
    Finset (R × K) :=
  Finset.univ.filter fun x => x.1 ≠ 0 ∧ d - x ∈ C

/-- The extra term selected by `r ≠ 0, c = 0`. -/
noncomputable def mixedExtra (C : Finset (R × K)) (d : R × K) :
    Finset (R × K) :=
  Finset.univ.filter fun x => x.1 ≠ 0 ∧ x.2 = 0 ∧ d - x ∈ C

/-- Negation symmetry converts the second correlation into a convolution. -/
theorem correlation_card_eq_convolution_card_of_neg
    (B C : Finset (R × K)) (hBneg : ∀ x, -x ∈ B ↔ x ∈ B) (d : R × K) :
    (correlation C B d).card = (convolution B C d).card := by
  classical
  apply Finset.card_equiv (Equiv.subLeft d)
  intro x
  simp only [correlation, convolution, Finset.mem_filter, Equiv.subLeft_apply]
  constructor
  · rintro ⟨hxC, hxdB⟩
    refine ⟨?_, ?_⟩
    · have : -(x - d) ∈ B := (hBneg (x - d)).2 hxdB
      simpa only [neg_sub] using this
    · simpa only [sub_sub_cancel]
  · rintro ⟨hdxB, hC⟩
    refine ⟨?_, ?_⟩
    · simpa only [sub_sub_cancel] using hC
    · have : -(d - x) ∈ B := (hBneg (d - x)).2 hdxB
      simpa only [neg_sub] using this

/-- The pointwise `A+B` identity turns the mixed convolution into the sum of
the baseline and exceptional finite sets. -/
theorem convolution_add_correlation_eq_baseline_add_extra
    (A B C : Finset (R × K))
    (hBneg : ∀ x, -x ∈ B ↔ x ∈ B)
    (hAB : ∀ x,
      memIndicator A x + memIndicator B x =
        if x.1 ≠ 0 then 1 + (if x.2 = 0 then 1 else 0) else 0)
    (d : R × K) :
    (convolution A C d).card + (correlation C B d).card =
      (mixedBaseline C d).card + (mixedExtra C d).card := by
  classical
  rw [correlation_card_eq_convolution_card_of_neg B C hBneg d]
  have hsum (X : Finset (R × K)) :
      (convolution X C d).card =
        ∑ x : R × K, memIndicator X x * memIndicator C (d - x) := by
    calc
      (convolution X C d).card =
          (Finset.univ.filter fun x : R × K => x ∈ X ∧ d - x ∈ C).card := by
            congr 1
            ext x
            simp [convolution]
      _ = ∑ x ∈ (Finset.univ : Finset (R × K)),
          if x ∈ X ∧ d - x ∈ C then 1 else 0 :=
            card_filter_eq_sum_indicator _ _
      _ = ∑ x : R × K, memIndicator X x * memIndicator C (d - x) := by
            apply Finset.sum_congr rfl
            intro x hx
            by_cases hX : x ∈ X <;> by_cases hC : d - x ∈ C <;>
              simp [memIndicator, hX, hC]
  rw [hsum A, hsum B, ← Finset.sum_add_distrib]
  simp only [mixedBaseline, mixedExtra, Finset.card_filter]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  have hab := hAB x
  by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;>
    by_cases hC : d - x ∈ C <;> by_cases hr : x.1 = 0 <;>
    by_cases hc : x.2 = 0 <;> simp [hA, hB, hC, hr, hc, memIndicator] at hab ⊢

/-- Translating by `x ↦ d-x` identifies the baseline with all of `C` except
the row having first coordinate `d.1`. -/
theorem card_mixedBaseline
    (C : Finset (R × K)) (d : R × K) :
    (mixedBaseline C d).card = C.card - (firstRow C d.1).card := by
  classical
  let target := C.filter fun y => y.1 ≠ d.1
  have hcard : (mixedBaseline C d).card = target.card := by
    apply Finset.card_equiv (Equiv.subLeft d)
    intro x
    rcases d with ⟨a, b⟩
    rcases x with ⟨r, c⟩
    simp only [mixedBaseline, target, Finset.mem_filter, Finset.mem_univ,
      true_and, Equiv.subLeft_apply, Prod.fst_sub]
    constructor
    · rintro ⟨hr, hC⟩
      exact ⟨hC, fun h => hr (sub_eq_self.mp h)⟩
    · rintro ⟨hC, har⟩
      exact ⟨fun hr => har (by simp [hr]), hC⟩
  rw [hcard]
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := C) (fun y : R × K => y.1 = d.1)
  change (firstRow C d.1).card + target.card = C.card at hsplit
  omega

/-- Translating the exceptional term identifies it with the relevant second
column of `C`, with the point `d` erased. -/
theorem card_mixedExtra
    (C : Finset (R × K)) (d : R × K) :
    (mixedExtra C d).card = ((secondColumn C d.2).erase d).card := by
  classical
  apply Finset.card_equiv (Equiv.subLeft d)
  intro x
  rcases d with ⟨a, b⟩
  rcases x with ⟨r, c⟩
  simp only [mixedExtra, secondColumn, Finset.mem_filter, Finset.mem_univ,
    true_and, Equiv.subLeft_apply, Finset.mem_erase, Prod.fst_sub, Prod.snd_sub]
  constructor
  · rintro ⟨hr, hc, hC⟩
    subst c
    refine ⟨?_, hC, by simp⟩
    intro h
    have : a - r = a := congrArg Prod.fst h
    exact hr (sub_eq_self.mp this)
  · rintro ⟨hne, hC, hcol⟩
    have hc : c = 0 := sub_eq_self.mp hcol
    subst c
    refine ⟨?_, rfl, hC⟩
    intro hr
    subst r
    exact hne (by simp)

/-- Erasing `d` from its own second-coordinate column subtracts precisely its
`C`-membership indicator. -/
theorem card_secondColumn_erase
    (C : Finset (R × K)) (d : R × K) :
    ((secondColumn C d.2).erase d).card + memIndicator C d =
      (secondColumn C d.2).card := by
  classical
  by_cases hd : d ∈ C
  · have hdcol : d ∈ secondColumn C d.2 := by simp [secondColumn, hd]
    have hpos : 0 < (secondColumn C d.2).card := Finset.card_pos.mpr ⟨d, hdcol⟩
    rw [Finset.card_erase_of_mem hdcol]
    simp [memIndicator, hd]
    omega
  · have hdcol : d ∉ secondColumn C d.2 := by simp [secondColumn, hd]
    rw [Finset.erase_eq_of_notMem hdcol]
    simp [memIndicator, hd]

/-- The generic cross-fibre convolution count.  The row hypothesis is the
transparent ingredient giving the baseline `m²-1`; the zero/nonzero column
hypotheses give the exceptional term. -/
theorem mixedCorrelation_count
    (A B C : Finset (R × K))
    (hBneg : ∀ x, -x ∈ B ↔ x ∈ B)
    (hAB : ∀ x,
      memIndicator A x + memIndicator B x =
        if x.1 ≠ 0 then 1 + (if x.2 = 0 then 1 else 0) else 0)
    (m half : Nat)
    (hCcard : C.card = m * (m + 1))
    (hCrow : ∀ a, (firstRow C a).card = m + 1)
    (hCzero : (secondColumn C 0).card = 0)
    (hCnonzero : ∀ b, b ≠ 0 → (secondColumn C b).card = half)
    (d : R × K) :
    (convolution A C d).card + (correlation C B d).card =
      m ^ 2 - 1 +
        if d.2 = 0 then 0 else half - memIndicator C d := by
  rw [convolution_add_correlation_eq_baseline_add_extra A B C hBneg hAB d,
    card_mixedBaseline C d, card_mixedExtra C d]
  have herase := card_secondColumn_erase C d
  rw [hCcard, hCrow]
  have hbase : m * (m + 1) - (m + 1) = m ^ 2 - 1 := by
    cases m with
    | zero => norm_num
    | succ k =>
        ring_nf
        omega
  rw [hbase]
  by_cases hb : d.2 = 0
  · rw [if_pos hb]
    have hcol : (secondColumn C d.2).card = 0 := by simpa [hb] using hCzero
    rw [hcol] at herase
    have hextra : ((secondColumn C d.2).erase d).card = 0 := by
      exact Nat.eq_zero_of_le_zero (by omega)
    rw [hextra]
  · rw [if_neg hb]
    rw [hCnonzero d.2 hb] at herase
    have hextra : ((secondColumn C d.2).erase d).card =
        half - memIndicator C d := by omega
    rw [hextra]

/-- The preceding result with the paper's nonzero-column size `(m+1)/2`
substituted explicitly. -/
theorem mixedCorrelation_count_paper
    (A B C : Finset (R × K))
    (hBneg : ∀ x, -x ∈ B ↔ x ∈ B)
    (hAB : ∀ x,
      memIndicator A x + memIndicator B x =
        if x.1 ≠ 0 then 1 + (if x.2 = 0 then 1 else 0) else 0)
    (m : Nat)
    (hCcard : C.card = m * (m + 1))
    (hCrow : ∀ a, (firstRow C a).card = m + 1)
    (hCzero : (secondColumn C 0).card = 0)
    (hCnonzero : ∀ b, b ≠ 0 →
      (secondColumn C b).card = (m + 1) / 2)
    (d : R × K) :
    (convolution A C d).card + (correlation C B d).card =
      m ^ 2 - 1 + if d.2 = 0 then 0
        else (m + 1) / 2 - memIndicator C d := by
  exact mixedCorrelation_count A B C hBneg hAB m ((m + 1) / 2)
    hCcard hCrow hCzero hCnonzero d

end Generic

section ConcreteAB

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The concrete `A` and `B` from equation (7) satisfy the exact pointwise
indicator identity consumed by `mixedCorrelation_count`. -/
theorem YamadaPott_indicator_A_add_B (p : YamadaPottW F) :
    memIndicator (YamadaPottA (F := F)) p +
        memIndicator (YamadaPottB (F := F)) p =
      if p.1 ≠ 0 then 1 + (if p.2 = 0 then 1 else 0) else 0 := by
  classical
  rcases p with ⟨r, c⟩
  by_cases hr : r = 0
  · simp [hr, memIndicator]
  by_cases hc : c = 0
  · simp [hr, hc, memIndicator]
  have hs0 : 1 - YamadaPott.squareValue r ≠ 0 := by
    intro h
    have hs : YamadaPott.squareValue r = 1 := (sub_eq_zero.mp h).symm
    exact hr ((YamadaPott.squareValue_eq_one_iff r).mp hs)
  rcases quadraticChar_dichotomy hs0 with hh | hh <;>
    rcases quadraticChar_dichotomy hc with hchi | hchi <;>
    simp [memIndicator, hr, hc, YamadaPott.skew, YamadaPottH, hh, hchi]

/-- The concrete source complement is stable under negation. -/
theorem YamadaPottD_neg_mem (x : F) :
    -x ∈ YamadaPottD F ↔ x ∈ YamadaPottD F := by
  simp only [YamadaPottD, Finset.mem_sdiff, Finset.mem_univ, true_and,
    mem_YamadaPottE]
  constructor
  · intro h hxE
    apply h
    rcases hxE with rfl | hx | hx
    · exact Or.inl neg_zero
    · exact Or.inr (Or.inr (by simpa using hx))
    · exact Or.inr (Or.inl (by simpa using hx))
  · intro h hxE
    apply h
    rcases hxE with hx | hx | hx
    · exact Or.inl (neg_eq_zero.mp hx)
    · exact Or.inr (Or.inr (by simpa using hx))
    · exact Or.inr (Or.inl (by simpa using hx))

theorem zero_not_mem_YamadaPottD : (0 : F) ∉ YamadaPottD F := by
  simp [YamadaPottD, YamadaPottE]

private noncomputable def charPositiveIn (D : Finset F) : Finset F :=
  D.filter fun x => quadraticChar F x = 1

private noncomputable def charNegativeIn (D : Finset F) : Finset F :=
  D.filter fun x => quadraticChar F x = -1

private theorem card_charPositiveIn_eq_negativeIn
    (hF : ringChar F ≠ 2) (hmod : Fintype.card F % 4 = 3)
    (D : Finset F) (hDneg : ∀ x, -x ∈ D ↔ x ∈ D) :
    (charPositiveIn D).card = (charNegativeIn D).card := by
  have hneg := quadraticChar_neg_one_of_card_mod_four_eq_three (F := F) hF hmod
  apply Finset.card_equiv (Equiv.neg F)
  intro x
  simp only [charPositiveIn, charNegativeIn, Finset.mem_filter, Equiv.neg_apply]
  constructor
  · rintro ⟨hxD, hx⟩
    refine ⟨(hDneg x).2 hxD, ?_⟩
    rw [show -x = (-1 : F) * x by ring, map_mul, hneg, hx]
    norm_num
  · rintro ⟨hxD, hx⟩
    refine ⟨(hDneg x).1 hxD, ?_⟩
    rw [show -x = (-1 : F) * x by ring, map_mul, hneg] at hx
    norm_num at hx ⊢
    omega

private theorem charPositiveIn_union_negativeIn
    (D : Finset F) (hD0 : (0 : F) ∉ D) :
    charPositiveIn D ∪ charNegativeIn D = D := by
  ext x
  simp only [Finset.mem_union, charPositiveIn, charNegativeIn, Finset.mem_filter]
  constructor
  · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
  · intro hx
    have hx0 : x ≠ 0 := fun h => hD0 (h ▸ hx)
    rcases quadraticChar_dichotomy hx0 with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩

private theorem charPositiveIn_disjoint_negativeIn (D : Finset F) :
    Disjoint (charPositiveIn D) (charNegativeIn D) := by
  rw [Finset.disjoint_left]
  intro x hp hn
  simp only [charPositiveIn, charNegativeIn, Finset.mem_filter] at hp hn
  omega

/-- A negation-stable, zero-free set of size `2(t+1)` has `t+1` elements
in each quadratic-character coset. -/
theorem card_charPositiveIn_of_neg_stable
    (hF : ringChar F ≠ 2) (hmod : Fintype.card F % 4 = 3)
    (D : Finset F) (hDneg : ∀ x, -x ∈ D ↔ x ∈ D)
    (hD0 : (0 : F) ∉ D) {t : Nat} (hDcard : D.card = 2 * t + 2) :
    (charPositiveIn D).card = t + 1 := by
  have hu := congrArg Finset.card (charPositiveIn_union_negativeIn D hD0)
  rw [Finset.card_union_of_disjoint (charPositiveIn_disjoint_negativeIn D)] at hu
  rw [← card_charPositiveIn_eq_negativeIn hF hmod D hDneg, hDcard] at hu
  omega

theorem card_charNegativeIn_of_neg_stable
    (hF : ringChar F ≠ 2) (hmod : Fintype.card F % 4 = 3)
    (D : Finset F) (hDneg : ∀ x, -x ∈ D ↔ x ∈ D)
    (hD0 : (0 : F) ∉ D) {t : Nat} (hDcard : D.card = 2 * t + 2) :
    (charNegativeIn D).card = t + 1 := by
  rw [← card_charPositiveIn_eq_negativeIn hF hmod D hDneg]
  exact card_charPositiveIn_of_neg_stable hF hmod D hDneg hD0 hDcard

/-- Every fixed first-coordinate row of the concrete `C` has `|D|=m+1`
entries. -/
theorem YamadaPott_firstRow_C_card
    (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    (a : Additive (YamadaPottSquareSubgroup F)) :
    (firstRow (YamadaPottC (F := F)) a).card = 2 * t + 2 := by
  classical
  let s := YamadaPott.squareValue a
  have hs0 : s ≠ 0 := YamadaPott.squareValue_ne_zero a
  have hrow : (firstRow (YamadaPottC (F := F)) a).card =
      (YamadaPottD F).card := by
    apply Finset.card_bij (fun p _ => p.2 * s⁻¹)
    · intro p hp
      simp only [firstRow, Finset.mem_filter] at hp
      simpa [s, hp.2] using hp.1
    · intro p hp q hq heq
      simp only [firstRow, Finset.mem_filter] at hp hq
      apply Prod.ext
      · exact hp.2.trans hq.2.symm
      · apply (mul_right_cancel₀ (inv_ne_zero hs0))
        exact heq
    · intro z hz
      refine ⟨(a, z * s), ?_, ?_⟩
      · simp only [firstRow, Finset.mem_filter]
        constructor
        · simpa [YamadaPottC, s, hs0] using hz
        · trivial
      · dsimp
        field_simp
  rw [hrow]
  exact card_YamadaPottD (F := F) hF hcard

/-- The zero field-coordinate column of `C` is empty. -/
theorem YamadaPott_secondColumn_C_zero :
    (secondColumn (YamadaPottC (F := F)) 0).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_not_mem.mpr
  intro p hp
  simp only [secondColumn, Finset.mem_filter] at hp
  have hpC := hp.1
  rw [mem_YamadaPottC, hp.2, zero_mul] at hpC
  exact zero_not_mem_YamadaPottD hpC

private theorem squareValue_injective : Function.Injective
    (YamadaPott.squareValue :
      Additive (YamadaPottSquareSubgroup F) → F) := by
  intro r s hrs
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  exact hrs

private theorem quadraticChar_squareValue_inv
    (r : Additive (YamadaPottSquareSubgroup F)) :
    quadraticChar F (YamadaPott.squareValue r)⁻¹ = 1 := by
  apply (quadraticChar_one_iff_isSquare
    (inv_ne_zero (YamadaPott.squareValue_ne_zero r))).2
  exact (YamadaPott.squareValue_isSquare r).inv

private noncomputable def squareIndexOfRatio {b z : F} (hb : b ≠ 0) (hz : z ≠ 0)
    (hsq : IsSquare (b * z⁻¹)) : Additive (YamadaPottSquareSubgroup F) := by
  let u : Fˣ := Units.mk0 (b * z⁻¹) (mul_ne_zero hb (inv_ne_zero hz))
  have huSq : IsSquare u := by
    rcases hsq with ⟨w, hw⟩
    have hw0 : w ≠ 0 := by
      intro hwz
      rw [hwz, zero_mul] at hw
      exact (mul_ne_zero hb (inv_ne_zero hz)) hw
    refine ⟨Units.mk0 w hw0, ?_⟩
    apply Units.ext
    simpa [u] using hw
  exact Additive.ofMul ⟨u, (Subgroup.mem_square.mpr huSq)⟩

private theorem squareValue_squareIndexOfRatio {b z : F} (hb : b ≠ 0) (hz : z ≠ 0)
    (hsq : IsSquare (b * z⁻¹)) :
    YamadaPott.squareValue (squareIndexOfRatio hb hz hsq) = b * z⁻¹ := rfl

/-- Every nonzero field-coordinate column of the concrete `C` has `t+1`,
equivalently `(m+1)/2`, entries. -/
theorem YamadaPott_secondColumn_C_nonzero_card
    (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    (b : F) (hb : b ≠ 0) :
    (secondColumn (YamadaPottC (F := F)) b).card = t + 1 := by
  classical
  let target := (YamadaPottD F).filter fun z =>
    quadraticChar F z = quadraticChar F b
  have hcolTarget : (secondColumn (YamadaPottC (F := F)) b).card = target.card := by
    apply Finset.card_bij (fun p _ => p.2 * (YamadaPott.squareValue p.1)⁻¹)
    · intro p hp
      simp only [secondColumn, Finset.mem_filter] at hp
      have hpC := hp.1
      have hpb := hp.2
      rw [mem_YamadaPottC] at hpC
      dsimp [target]
      simp only [Finset.mem_filter]
      change p.2 * (YamadaPott.squareValue p.1)⁻¹ ∈ YamadaPottD F ∧
        quadraticChar F (p.2 * (YamadaPott.squareValue p.1)⁻¹) =
          quadraticChar F b
      refine ⟨hpC, ?_⟩
      rw [hpb, map_mul, quadraticChar_squareValue_inv, mul_one]
    · intro p hp q hq heq
      simp only [secondColumn, Finset.mem_filter] at hp hq
      apply Prod.ext
      · apply squareValue_injective
        apply inv_injective
        apply mul_left_cancel₀ hb
        simpa [hp.2, hq.2] using heq
      · exact hp.2.trans hq.2.symm
    · intro z hz
      dsimp [target] at hz
      simp only [Finset.mem_filter] at hz
      change z ∈ YamadaPottD F ∧ quadraticChar F z = quadraticChar F b at hz
      have hzD : z ∈ YamadaPottD F := hz.1
      have hz0 : z ≠ 0 := fun h => zero_not_mem_YamadaPottD (h ▸ hzD)
      have hratioChar : quadraticChar F (b * z⁻¹) = 1 := by
        rw [map_mul]
        have hzsq := quadraticChar_sq_one hz0
        have hzinv : quadraticChar F z⁻¹ = quadraticChar F z := by
          have hmul : quadraticChar F z * quadraticChar F z⁻¹ = 1 := by
            rw [← map_mul, mul_inv_cancel₀ hz0, map_one]
          rcases quadraticChar_dichotomy hz0 with h | h <;> rw [h] at hmul ⊢ <;>
            norm_num at hmul ⊢ <;> omega
        rw [hzinv, hz.2]
        simpa [pow_two] using quadraticChar_sq_one (F := F) hb
      have hratio0 : b * z⁻¹ ≠ 0 := mul_ne_zero hb (inv_ne_zero hz0)
      have hratioSq : IsSquare (b * z⁻¹) :=
        (quadraticChar_one_iff_isSquare hratio0).1 hratioChar
      let r := squareIndexOfRatio hb hz0 hratioSq
      refine ⟨(r, b), ?_, ?_⟩
      · simp only [secondColumn, Finset.mem_filter]
        constructor
        · rw [mem_YamadaPottC]
          have hrval := squareValue_squareIndexOfRatio hb hz0 hratioSq
          dsimp only [r]
          rw [hrval]
          field_simp
          exact hzD
        · trivial
      · dsimp
        have hrval := squareValue_squareIndexOfRatio hb hz0 hratioSq
        dsimp only [r]
        rw [hrval]
        field_simp
  rw [hcolTarget]
  have hmod : Fintype.card F % 4 = 3 := by omega
  have hDcard := card_YamadaPottD (F := F) hF hcard
  rcases quadraticChar_dichotomy hb with hbpos | hbneg
  · have htarget : target = charPositiveIn (YamadaPottD F) := by
      ext z
      simp [target, charPositiveIn, hbpos]
    rw [htarget]
    exact card_charPositiveIn_of_neg_stable hF hmod _
      (YamadaPottD_neg_mem (F := F)) zero_not_mem_YamadaPottD hDcard
  · have htarget : target = charNegativeIn (YamadaPottD F) := by
      ext z
      simp [target, charNegativeIn, hbneg]
    rw [htarget]
    exact card_charNegativeIn_of_neg_stable hF hmod _
      (YamadaPottD_neg_mem (F := F)) zero_not_mem_YamadaPottD hDcard

/-- The paper's mixed cross-fibre common-red count for the concrete
Yamada--Pott connection sets. -/
theorem YamadaPott_mixedCorrelation_count
    (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    (d : YamadaPottW F) :
    (convolution (YamadaPottA (F := F)) (YamadaPottC (F := F)) d).card +
        (correlation (YamadaPottC (F := F)) (YamadaPottB (F := F)) d).card =
      (2 * t + 1) ^ 2 - 1 +
        if d.2 = 0 then 0
        else t + 1 - memIndicator (YamadaPottC (F := F)) d := by
  classical
  have hmod : Fintype.card F % 4 = 3 := by omega
  have hCcard : (YamadaPottC (F := F)).card =
      (2 * t + 1) * (2 * t + 1 + 1) := by
    simpa only [Nat.add_assoc, Nat.add_left_inj] using
      YamadaPott.card_C (F := F) hF hcard
  have hCrow : ∀ a, (firstRow (YamadaPottC (F := F)) a).card =
      2 * t + 1 + 1 := by
    intro a
    simpa only [Nat.add_assoc, Nat.add_left_inj] using
      YamadaPott_firstRow_C_card (F := F) hF hcard a
  have hAB : ∀ x : YamadaPottW F,
      memIndicator (YamadaPottA (F := F)) x +
          memIndicator (YamadaPottB (F := F)) x =
        if x.1 ≠ 0 then 1 + (if x.2 = 0 then 1 else 0) else 0 := by
    intro x
    exact YamadaPott_indicator_A_add_B x
  have hmain := mixedCorrelation_count
    (YamadaPottA (F := F)) (YamadaPottB (F := F)) (YamadaPottC (F := F))
    (fun x => YamadaPottB_neg_mem hF hmod x)
    hAB (2 * t + 1) (t + 1)
    hCcard hCrow (YamadaPott_secondColumn_C_zero (F := F))
    (YamadaPott_secondColumn_C_nonzero_card (F := F) hF hcard) d
  exact hmain

/-- On a concrete cross edge, the mixed count is exactly `n-2`. -/
theorem YamadaPott_mixedCorrelation_edge
    (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    (d : YamadaPottW F) (hd : d ∈ YamadaPottC (F := F)) :
    (convolution (YamadaPottA (F := F)) (YamadaPottC (F := F)) d).card +
        (correlation (YamadaPottC (F := F)) (YamadaPottB (F := F)) d).card =
      4 * t ^ 2 + 5 * t := by
  rw [YamadaPott_mixedCorrelation_count hF hcard d]
  have hb : d.2 ≠ 0 := by
    intro hb
    have hdc := hd
    rw [mem_YamadaPottC, hb, zero_mul] at hdc
    exact zero_not_mem_YamadaPottD hdc
  rw [if_neg hb]
  simp [memIndicator, hd]
  ring_nf
  omega

/-- Off the concrete cross connection set, the mixed count is at most
`n-1`. -/
theorem YamadaPott_mixedCorrelation_nonedge
    (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    (d : YamadaPottW F) (hd : d ∉ YamadaPottC (F := F)) :
    (convolution (YamadaPottA (F := F)) (YamadaPottC (F := F)) d).card +
        (correlation (YamadaPottC (F := F)) (YamadaPottB (F := F)) d).card ≤
      4 * t ^ 2 + 5 * t + 1 := by
  rw [YamadaPott_mixedCorrelation_count hF hcard d]
  by_cases hb : d.2 = 0
  · rw [if_pos hb]
    ring_nf
    omega
  · rw [if_neg hb]
    simp [memIndicator, hd]
    ring_nf
    omega

/-- Card-order-only form of the concrete row count. -/
theorem YamadaPott_firstRow_C_card_of_card {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    (a : Additive (YamadaPottSquareSubgroup F)) :
    (firstRow (YamadaPottC (F := F)) a).card = 2 * t + 2 := by
  exact YamadaPott_firstRow_C_card (YamadaPott.ringChar_ne_two hcard) hcard a

/-- Card-order-only form of the concrete nonzero-column count. -/
theorem YamadaPott_secondColumn_C_nonzero_card_of_card {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    (b : F) (hb : b ≠ 0) :
    (secondColumn (YamadaPottC (F := F)) b).card = t + 1 := by
  exact YamadaPott_secondColumn_C_nonzero_card
    (YamadaPott.ringChar_ne_two hcard) hcard b hb

/-- Card-order-only exact mixed-correlation formula. -/
theorem YamadaPott_mixedCorrelation_count_of_card {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    (d : YamadaPottW F) :
    (convolution (YamadaPottA (F := F)) (YamadaPottC (F := F)) d).card +
        (correlation (YamadaPottC (F := F)) (YamadaPottB (F := F)) d).card =
      (2 * t + 1) ^ 2 - 1 +
        if d.2 = 0 then 0
        else t + 1 - memIndicator (YamadaPottC (F := F)) d := by
  exact YamadaPott_mixedCorrelation_count
    (YamadaPott.ringChar_ne_two hcard) hcard d

/-- Card-order-only cross-edge value `n-2`. -/
theorem YamadaPott_mixedCorrelation_edge_of_card {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    (d : YamadaPottW F) (hd : d ∈ YamadaPottC (F := F)) :
    (convolution (YamadaPottA (F := F)) (YamadaPottC (F := F)) d).card +
        (correlation (YamadaPottC (F := F)) (YamadaPottB (F := F)) d).card =
      4 * t ^ 2 + 5 * t := by
  exact YamadaPott_mixedCorrelation_edge
    (YamadaPott.ringChar_ne_two hcard) hcard d hd

/-- Card-order-only cross-nonedge bound `n-1`. -/
theorem YamadaPott_mixedCorrelation_nonedge_of_card {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    (d : YamadaPottW F) (hd : d ∉ YamadaPottC (F := F)) :
    (convolution (YamadaPottA (F := F)) (YamadaPottC (F := F)) d).card +
        (correlation (YamadaPottC (F := F)) (YamadaPottB (F := F)) d).card ≤
      4 * t ^ 2 + 5 * t + 1 := by
  exact YamadaPott_mixedCorrelation_nonedge
    (YamadaPott.ringChar_ne_two hcard) hcard d hd

end ConcreteAB

end BookS3
