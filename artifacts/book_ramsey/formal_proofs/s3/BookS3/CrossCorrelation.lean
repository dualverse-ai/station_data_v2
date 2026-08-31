import BookS3.AffineCorrelation
import BookS3.SourceIdentity

/-!
# The sign-reversing pair count behind equation (9)

For a negation-stable subset `D` of a finite field, simultaneous negation of
`(x,y) ∈ D × D` changes the sign of the quadratic character of `t*y-x` when
the field cardinality is `3 mod 4`.  Away from `t*y=x`, this pairs the two
quadratic-character classes.  The lemmas below make that involution and its
exact finite-cardinality consequence explicit, without mentioning graphs or
codegrees.
-/

namespace BookS3

open scoped BigOperators

section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Multiplicatively scale a finite subset of a field. -/
def scaledFinset (t : F) (D : Finset F) : Finset F :=
  D.image fun y => t * y

/-- `D ∩ tD`, the overlap that appears as `I(a)` in the paper. -/
def scaledOverlap (t : F) (D : Finset F) : Finset F :=
  D ∩ scaledFinset t D

/-- Pairs in `D²` for which the affine difference `t*y-x` vanishes. -/
def affineDiagonalPairs (t : F) (D : Finset F) : Finset (F × F) :=
  (D ×ˢ D).filter fun p => t * p.2 - p.1 = 0

/-- Pairs in `D²` away from the affine diagonal `x=t*y`. -/
def affineOffDiagonalPairs (t : F) (D : Finset F) : Finset (F × F) :=
  (D ×ˢ D).filter fun p => t * p.2 - p.1 ≠ 0

/-- The positive quadratic-character class among the affine differences. -/
def affinePositivePairs (t : F) (D : Finset F) : Finset (F × F) :=
  (D ×ˢ D).filter fun p => quadraticChar F (t * p.2 - p.1) = 1

/-- The negative quadratic-character class among the affine differences. -/
def affineNegativePairs (t : F) (D : Finset F) : Finset (F × F) :=
  (D ×ˢ D).filter fun p => quadraticChar F (t * p.2 - p.1) = -1

@[simp] theorem mem_scaledFinset {t x : F} {D : Finset F} :
    x ∈ scaledFinset t D ↔ ∃ y ∈ D, t * y = x := by
  simp [scaledFinset]

@[simp] theorem mem_scaledOverlap {t x : F} {D : Finset F} :
    x ∈ scaledOverlap t D ↔ x ∈ D ∧ ∃ y ∈ D, t * y = x := by
  simp [scaledOverlap]

/-- The affine diagonal is in bijection with `D ∩ tD`. -/
theorem card_affineDiagonalPairs (D : Finset F) {t : F} (ht : t ≠ 0) :
    (affineDiagonalPairs t D).card = (scaledOverlap t D).card := by
  classical
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    rcases p with ⟨x, y⟩
    simp only [affineDiagonalPairs, Finset.mem_filter, Finset.mem_product,
      Prod.fst, Prod.snd] at hp
    rw [mem_scaledOverlap]
    refine ⟨hp.1.1, y, hp.1.2, ?_⟩
    exact sub_eq_zero.mp hp.2
  · intro p hp q hq hpq
    rcases p with ⟨x, y⟩
    rcases q with ⟨x', y'⟩
    simp only [affineDiagonalPairs, Finset.mem_filter, Finset.mem_product,
      Prod.fst, Prod.snd] at hp hq hpq
    have hxy : t * y = x := sub_eq_zero.mp hp.2
    have hxy' : t * y' = x' := sub_eq_zero.mp hq.2
    have hyy : y = y' := by
      apply mul_left_cancel₀ ht
      rw [hxy, hxy', hpq]
    simp [hpq, hyy]
  · intro x hx
    rw [mem_scaledOverlap] at hx
    rcases hx with ⟨hxD, y, hyD, hty⟩
    refine ⟨(x, y), ?_, rfl⟩
    simp [affineDiagonalPairs, hxD, hyD, hty]

/-- A filter form of `|D ∩ tD|`, matching the definition of `YamadaPottI`. -/
theorem card_scaledOverlap_eq_filter_mul_mem
    (D : Finset F) {t : F} (ht : t ≠ 0) :
    (scaledOverlap t D).card = (D.filter fun y => t * y ∈ D).card := by
  classical
  symm
  apply Finset.card_bij (fun y _ => t * y)
  · intro y hy
    simp only [Finset.mem_filter] at hy
    rw [mem_scaledOverlap]
    exact ⟨hy.2, y, hy.1, rfl⟩
  · intro y hy z hz hyz
    exact mul_left_cancel₀ ht hyz
  · intro x hx
    rw [mem_scaledOverlap] at hx
    rcases hx with ⟨hxD, y, hyD, hty⟩
    refine ⟨y, ?_, hty⟩
    simp [hyD, hxD, hty]

/-- Diagonal and off-diagonal pairs partition `D²`. -/
theorem card_affineDiagonal_add_offDiagonal (t : F) (D : Finset F) :
    (affineDiagonalPairs t D).card + (affineOffDiagonalPairs t D).card =
      D.card * D.card := by
  have h := Finset.filter_card_add_filter_neg_card_eq_card
    (s := D ×ˢ D) (fun p : F × F => t * p.2 - p.1 = 0)
  simpa only [affineDiagonalPairs, affineOffDiagonalPairs,
    Finset.card_product] using h

/-- Under `|F| ≡ 3 (mod 4)`, the quadratic character of `-1` is `-1`.
The characteristic hypothesis is derived rather than assumed. -/
theorem quadraticChar_neg_one_of_card_three
    (hcard : Fintype.card F % 4 = 3) :
    quadraticChar F (-1) = -1 := by
  have hF : ringChar F ≠ 2 := by
    intro hchar
    have heven := FiniteField.even_card_of_char_two (F := F) hchar
    omega
  exact quadraticChar_neg_one_of_card_mod_four_eq_three (F := F) hF hcard

/-- Simultaneous negation bijects the positive and negative affine-difference
classes.  `htsq` records that `t` is a nonzero square, as in equation (9). -/
theorem card_affinePositive_eq_negative
    (D : Finset F) (hDneg : ∀ x, -x ∈ D ↔ x ∈ D)
    (t : F)
    (hcard : Fintype.card F % 4 = 3) :
    (affinePositivePairs t D).card = (affineNegativePairs t D).card := by
  have hneg := quadraticChar_neg_one_of_card_three (F := F) hcard
  apply Finset.card_equiv (Equiv.neg (F × F))
  intro p
  rcases p with ⟨x, y⟩
  simp only [affinePositivePairs, affineNegativePairs, Finset.mem_filter,
    Finset.mem_product, Equiv.neg_apply, Prod.fst, Prod.snd,
    Prod.fst_neg, Prod.snd_neg]
  constructor
  · rintro ⟨⟨hx, hy⟩, hchi⟩
    refine ⟨⟨(hDneg x).2 hx, (hDneg y).2 hy⟩, ?_⟩
    have heq : t * -y - -x = -(t * y - x) := by ring
    rw [heq, show -(t * y - x) = (-1) * (t * y - x) by ring,
      map_mul, hneg, hchi]
    norm_num
  · rintro ⟨⟨hx, hy⟩, hchi⟩
    refine ⟨⟨(hDneg x).1 hx, (hDneg y).1 hy⟩, ?_⟩
    have heq : t * -y - -x = -(t * y - x) := by ring
    rw [heq, show -(t * y - x) = (-1) * (t * y - x) by ring,
      map_mul, hneg] at hchi
    norm_num at hchi ⊢
    omega

/-- The two nonzero sign classes partition the off-diagonal pairs. -/
theorem affinePositive_union_negative
    (t : F) (D : Finset F) :
    affinePositivePairs t D ∪ affineNegativePairs t D =
      affineOffDiagonalPairs t D := by
  ext p
  rcases p with ⟨x, y⟩
  simp only [Finset.mem_union, affinePositivePairs, affineNegativePairs,
    affineOffDiagonalPairs, Finset.mem_filter, Finset.mem_product,
    Prod.fst, Prod.snd]
  constructor
  · rintro (⟨hmem, h⟩ | ⟨hmem, h⟩)
    · exact ⟨hmem, fun hz => by rw [hz, quadraticChar_zero] at h; omega⟩
    · exact ⟨hmem, fun hz => by rw [hz, quadraticChar_zero] at h; omega⟩
  · rintro ⟨hmem, hne⟩
    rcases quadraticChar_dichotomy hne with h | h
    · exact Or.inl ⟨hmem, h⟩
    · exact Or.inr ⟨hmem, h⟩

theorem affinePositive_disjoint_negative (t : F) (D : Finset F) :
    Disjoint (affinePositivePairs t D) (affineNegativePairs t D) := by
  rw [Finset.disjoint_left]
  intro p hp hn
  simp only [affinePositivePairs, affineNegativePairs, Finset.mem_filter] at hp hn
  omega

/-- Exact equation (9) in a division-free finite-cardinality form. -/
theorem two_mul_card_affinePositive
    (D : Finset F) (hDneg : ∀ x, -x ∈ D ↔ x ∈ D)
    {t : F} (htsq : quadraticChar F t = 1)
    (hcard : Fintype.card F % 4 = 3) :
    2 * (affinePositivePairs t D).card =
      D.card * D.card - (scaledOverlap t D).card := by
  have ht : t ≠ 0 := by
    intro hzero
    subst t
    simp at htsq
  have hsign := congrArg Finset.card (affinePositive_union_negative t D)
  rw [Finset.card_union_of_disjoint (affinePositive_disjoint_negative t D)] at hsign
  rw [← card_affinePositive_eq_negative D hDneg t hcard] at hsign
  have hpartition := card_affineDiagonal_add_offDiagonal t D
  rw [card_affineDiagonalPairs D ht] at hpartition
  omega

theorem two_mul_card_affineNegative
    (D : Finset F) (hDneg : ∀ x, -x ∈ D ↔ x ∈ D)
    {t : F} (htsq : quadraticChar F t = 1)
    (hcard : Fintype.card F % 4 = 3) :
    2 * (affineNegativePairs t D).card =
      D.card * D.card - (scaledOverlap t D).card := by
  rw [← card_affinePositive_eq_negative D hDneg t hcard]
  exact two_mul_card_affinePositive D hDneg htsq hcard

/-- Equation (9), with the overlap written exactly as the multiplicative
filter used by the concrete Yamada--Pott source. -/
theorem two_mul_card_affinePositive_filter
    (D : Finset F) (hDneg : ∀ x, -x ∈ D ↔ x ∈ D)
    {t : F} (htsq : quadraticChar F t = 1)
    (hcard : Fintype.card F % 4 = 3) :
    2 * (affinePositivePairs t D).card =
      D.card * D.card - (D.filter fun y => t * y ∈ D).card := by
  have ht : t ≠ 0 := by
    intro hzero
    subst t
    simp at htsq
  rw [← card_scaledOverlap_eq_filter_mul_mem D ht]
  exact two_mul_card_affinePositive D hDneg htsq hcard

theorem two_mul_card_affineNegative_filter
    (D : Finset F) (hDneg : ∀ x, -x ∈ D ↔ x ∈ D)
    {t : F} (htsq : quadraticChar F t = 1)
    (hcard : Fintype.card F % 4 = 3) :
    2 * (affineNegativePairs t D).card =
      D.card * D.card - (D.filter fun y => t * y ∈ D).card := by
  rw [← card_affinePositive_eq_negative D hDneg t hcard]
  exact two_mul_card_affinePositive_filter D hDneg htsq hcard

/-- Equation (9) in the paper's divided form for the positive coset. -/
theorem card_affinePositive
    (D : Finset F) (hDneg : ∀ x, -x ∈ D ↔ x ∈ D)
    {t : F} (htsq : quadraticChar F t = 1)
    (hcard : Fintype.card F % 4 = 3) :
    (affinePositivePairs t D).card =
      (D.card * D.card - (scaledOverlap t D).card) / 2 := by
  have h := two_mul_card_affinePositive D hDneg htsq hcard
  omega

/-- Equation (9) in the paper's divided form for the negative coset. -/
theorem card_affineNegative
    (D : Finset F) (hDneg : ∀ x, -x ∈ D ↔ x ∈ D)
    {t : F} (htsq : quadraticChar F t = 1)
    (hcard : Fintype.card F % 4 = 3) :
    (affineNegativePairs t D).card =
      (D.card * D.card - (scaledOverlap t D).card) / 2 := by
  have h := two_mul_card_affineNegative D hDneg htsq hcard
  omega

end

end BookS3
