import BookS3.SourceIdentity

/-!
# Finite-field counting for the affine Yamada--Pott lift

These lemmas are the unconditional finite-field ingredients used when the
indicator functions in equations (8)--(10) are expanded.  No graph,
correlation-profile, codegree, or book-freeness hypothesis occurs here.
-/

open scoped BigOperators

namespace BookS3

section Indicators

variable {α : Type*}

/-- A finset cardinality as a sum of `ℕ`-valued indicators. -/
theorem card_filter_eq_sum_indicator (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (s.filter p).card = ∑ x ∈ s, if p x then 1 else 0 := by
  exact Finset.card_filter p s

/-- A finset cardinality as a sum of `ℤ`-valued indicators. -/
theorem int_card_filter_eq_sum_indicator (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    ((s.filter p).card : ℤ) = ∑ x ∈ s, if p x then (1 : ℤ) else 0 := by
  simp

/-- The positive-sign indicator, in the polynomial form used in correlation
expansions. -/
theorem two_mul_indicator_eq_one {z : ℤ}
    (hz : z = -1 ∨ z = 0 ∨ z = 1) :
    2 * (if z = 1 then (1 : ℤ) else 0) = z ^ 2 + z := by
  rcases hz with rfl | rfl | rfl <;> norm_num

/-- The negative-sign indicator, in the polynomial form used in correlation
expansions. -/
theorem two_mul_indicator_eq_neg_one {z : ℤ}
    (hz : z = -1 ∨ z = 0 ∨ z = 1) :
    2 * (if z = -1 then (1 : ℤ) else 0) = z ^ 2 - z := by
  rcases hz with rfl | rfl | rfl <;> norm_num

/-- Convert a sum of a three-valued sign function to the difference of its
positive and negative level-set cardinalities. -/
theorem sum_eq_card_pos_sub_card_neg (s : Finset α) (f : α → ℤ)
    (hf : ∀ x ∈ s, f x = -1 ∨ f x = 0 ∨ f x = 1) :
    ∑ x ∈ s, f x =
      ((s.filter fun x => f x = 1).card : ℤ) -
        ((s.filter fun x => f x = -1).card : ℤ) := by
  rw [int_card_filter_eq_sum_indicator, int_card_filter_eq_sum_indicator]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rcases hf x hx with h | h | h <;> simp [h]

/-- Indicator product sums count simultaneous membership. -/
theorem sum_indicator_mul_indicator (s : Finset α) (p q : α → Prop)
    [DecidablePred p] [DecidablePred q] :
    (∑ x ∈ s, (if p x then (1 : ℕ) else 0) *
      (if q x then 1 else 0)) = (s.filter fun x => p x ∧ q x).card := by
  rw [card_filter_eq_sum_indicator]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hp : p x <;> by_cases hq : q x <;> simp [hp, hq]

end Indicators

section QuadraticCharacter

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The elements on which the quadratic character is positive. -/
def quadraticPositive (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset F :=
  Finset.univ.filter fun x => quadraticChar F x = 1

/-- The elements on which the quadratic character is negative. -/
def quadraticNegative (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset F :=
  Finset.univ.filter fun x => quadraticChar F x = -1

@[simp] theorem mem_quadraticPositive (x : F) :
    x ∈ quadraticPositive F ↔ quadraticChar F x = 1 := by
  simp [quadraticPositive]

@[simp] theorem mem_quadraticNegative (x : F) :
    x ∈ quadraticNegative F ↔ quadraticChar F x = -1 := by
  simp [quadraticNegative]

/-- The quadratic character takes only the values `-1`, `0`, and `1`. -/
theorem quadraticChar_trichotomy (x : F) :
    quadraticChar F x = -1 ∨ quadraticChar F x = 0 ∨ quadraticChar F x = 1 := by
  by_cases hx : x = 0
  · subst x
    simp
  · rcases quadraticChar_dichotomy hx with h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inl h

/-- The shifted quadratic-character autocorrelation used in (8) and (10). -/
theorem sum_quadraticChar_mul_shift (hF : ringChar F ≠ 2) {b : F} (hb : b ≠ 0) :
    ∑ c : F, quadraticChar F c * quadraticChar F (c - b) = -1 := by
  have h := sum_quadraticChar_two_roots (F := F) hF (a := 0) (b := b) hb.symm
  simpa only [zero_sub, sub_zero, map_mul] using h

/-- Multiplication by a nonsquare exchanges the positive and negative
quadratic-character classes. -/
theorem card_quadraticPositive_eq_card_quadraticNegative
    (hF : ringChar F ≠ 2) :
    (quadraticPositive F).card = (quadraticNegative F).card := by
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := F) hF
  have ha0 : a ≠ 0 := by
    intro haz
    subst a
    simp at ha
  apply Finset.card_equiv (Equiv.mulLeft₀ a ha0)
  intro x
  simp only [mem_quadraticPositive, mem_quadraticNegative, Equiv.mulLeft₀_apply,
    map_mul, ha, neg_one_mul]
  omega

/-- The positive and negative classes partition the nonzero field elements. -/
theorem quadraticPositive_union_quadraticNegative :
    quadraticPositive F ∪ quadraticNegative F = Finset.univ.erase 0 := by
  ext x
  simp only [Finset.mem_union, mem_quadraticPositive, mem_quadraticNegative,
    Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro (h | h) <;> intro hx <;> subst x <;> norm_num at h
  · intro hx
    rcases quadraticChar_dichotomy hx with h | h
    · exact Or.inl h
    · exact Or.inr h

theorem quadraticPositive_disjoint_quadraticNegative :
    Disjoint (quadraticPositive F) (quadraticNegative F) := by
  rw [Finset.disjoint_left]
  intro x hp hn
  rw [mem_quadraticPositive] at hp
  rw [mem_quadraticNegative] at hn
  omega

/-- Twice the size of either nonzero character class is `|F|-1`. -/
theorem two_mul_card_quadraticPositive (hF : ringChar F ≠ 2) :
    2 * (quadraticPositive F).card = Fintype.card F - 1 := by
  have hunion := congrArg Finset.card
    (quadraticPositive_union_quadraticNegative (F := F))
  rw [Finset.card_union_of_disjoint quadraticPositive_disjoint_quadraticNegative] at hunion
  rw [Finset.card_erase_of_mem (Finset.mem_univ (0 : F))] at hunion
  rw [← card_quadraticPositive_eq_card_quadraticNegative hF] at hunion
  simpa only [Finset.card_univ, two_mul] using hunion

theorem two_mul_card_quadraticNegative (hF : ringChar F ≠ 2) :
    2 * (quadraticNegative F).card = Fintype.card F - 1 := by
  rw [← card_quadraticPositive_eq_card_quadraticNegative hF]
  exact two_mul_card_quadraticPositive hF

/-- Each sign occurs `(q-1)/2` times in a finite field of odd characteristic. -/
theorem card_quadraticPositive (hF : ringChar F ≠ 2) :
    (quadraticPositive F).card = (Fintype.card F - 1) / 2 := by
  have h := two_mul_card_quadraticPositive (F := F) hF
  omega

theorem card_quadraticNegative (hF : ringChar F ≠ 2) :
    (quadraticNegative F).card = (Fintype.card F - 1) / 2 := by
  rw [← card_quadraticPositive_eq_card_quadraticNegative hF]
  exact card_quadraticPositive hF

theorem card_quadraticPositive_of_card_eq {m : Nat} (hF : ringChar F ≠ 2)
    (hcard : Fintype.card F = 2 * m + 1) :
    (quadraticPositive F).card = m := by
  rw [card_quadraticPositive hF, hcard]
  omega

theorem card_quadraticNegative_of_card_eq {m : Nat} (hF : ringChar F ≠ 2)
    (hcard : Fintype.card F = 2 * m + 1) :
    (quadraticNegative F).card = m := by
  rw [card_quadraticNegative hF, hcard]
  omega

end QuadraticCharacter

end BookS3
