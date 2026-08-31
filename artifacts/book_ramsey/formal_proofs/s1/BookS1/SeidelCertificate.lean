import BookS1.ConferenceLift

/-!
# The Seidel certificate

This file proves the notebook's Lemma 1.1 in graph language.  It converts a
row-sum and square-sign certificate into literal exclusion of red and blue
books.
-/

namespace BookS1

open scoped BigOperators
open Finset

universe u

variable {V : Type u}

def indicator (p : Prop) [Decidable p] : ℤ := if p then 1 else 0

theorem sum_indicator [Fintype V] (p : V → Prop) [DecidablePred p] :
    ∑ x, indicator (p x) = ((Finset.univ.filter p).card : ℤ) := by
  simp [indicator]

theorem sum_adj_indicator [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V) :
    ∑ z, indicator (G.Adj x z) = (G.degree x : ℤ) := by
  rw [sum_indicator]
  have heq : (Finset.univ.filter fun z => G.Adj x z) = G.neighborFinset x := by
    ext z
    simp [SimpleGraph.mem_neighborFinset]
  rw [heq]
  simp only [SimpleGraph.card_neighborFinset_eq_degree]

theorem sum_common_indicator [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x y : V) :
    ∑ z, indicator (G.Adj x z) * indicator (G.Adj z y) =
      (Fintype.card (G.commonNeighbors x y) : ℤ) := by
  classical
  calc
    _ = ∑ z, indicator (G.Adj x z ∧ G.Adj y z) := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hx : G.Adj x z <;> by_cases hy : G.Adj y z <;>
        simp [indicator, hx, hy, G.adj_comm]
    _ = ((Finset.univ.filter fun z => G.Adj x z ∧ G.Adj y z).card : ℤ) :=
      sum_indicator _
    _ = (Fintype.card (G.commonNeighbors x y) : ℤ) := by
      rw [← Set.toFinset_card]
      congr 2
      ext z
      simp [SimpleGraph.commonNeighbors]

theorem sum_eq_indicator [Fintype V] [DecidableEq V] (x : V) :
    ∑ z, indicator (x = z) = 1 := by simp [indicator]

theorem sum_indicator_mul_eq [Fintype V] [DecidableEq V]
    (p : V → Prop) [DecidablePred p] (x : V) :
    ∑ z, indicator (p z) * indicator (z = x) = indicator (p x) := by
  by_cases hp : p x <;> simp [indicator, hp, eq_comm]

theorem sum_eq_mul_indicator [Fintype V] [DecidableEq V]
    (p : V → Prop) [DecidablePred p] (x : V) :
    ∑ z, indicator (x = z) * indicator (p z) = indicator (p x) := by
  calc
    _ = ∑ z, indicator (p z) * indicator (z = x) := by
      apply Finset.sum_congr rfl
      intro z hz
      by_cases hx : x = z
      · subst z
        simp [indicator]
      · have hzx : z ≠ x := Ne.symm hx
        simp [indicator, hx, hzx]
    _ = _ := sum_indicator_mul_eq p x

theorem sum_eq_mul_eq [Fintype V] [DecidableEq V]
    {x y : V} (hxy : x ≠ y) :
    ∑ z, indicator (x = z) * indicator (z = y) = 0 := by
  simp [indicator, hxy]

theorem sum_eq_mul_eq_general [Fintype V] [DecidableEq V] (x y : V) :
    ∑ z, indicator (x = z) * indicator (z = y) = indicator (x = y) := by
  by_cases hxy : x = y
  · subst y
    simp [indicator]
  · rw [sum_eq_mul_eq hxy]
    simp [indicator, hxy]

/-- A Seidel sign matrix on `4q+2` vertices with the certificate properties
used in the paper. -/
structure IsSeidelCertificate [Fintype V] [DecidableEq V]
    (S : V → V → ℤ) (q : ℕ) : Prop where
  card : Fintype.card V = 4 * q + 2
  symm : ∀ x y, S x y = S y x
  diag : ∀ x, S x x = 0
  offdiag : ∀ ⦃x y⦄, x ≠ y → S x y = 1 ∨ S x y = -1
  rowSum : ∀ x, ∑ y, S x y = -1
  square_nonpos : ∀ ⦃x y⦄, x ≠ y → ∑ z, S x z * S z y ≤ 0

namespace IsSeidelCertificate

variable [Fintype V] [DecidableEq V] {S : V → V → ℤ} {q : ℕ}

/-- The graph whose edges are the `+1` entries of a Seidel certificate. -/
def graph (h : IsSeidelCertificate S q) : SimpleGraph V where
  Adj x y := S x y = 1
  symm x y hxy := by simpa [h.symm x y] using hxy
  loopless x := by simp [h.diag]

@[simp] theorem graph_adj (h : IsSeidelCertificate S q) (x y : V) :
    h.graph.Adj x y ↔ S x y = 1 := Iff.rfl

instance (h : IsSeidelCertificate S q) : DecidableRel h.graph.Adj :=
  fun x y => inferInstanceAs (Decidable (S x y = 1))

private theorem sign_eq (h : IsSeidelCertificate S q) (x y : V) :
    S x y = 2 * indicator (h.graph.Adj x y) + indicator (x = y) - 1 := by
  by_cases hxy : x = y
  · subst y
    simp [indicator, h.diag]
  · rcases h.offdiag hxy with hs | hs
    · simp [indicator, hxy, hs]
    · simp [indicator, hxy, hs, graph]

theorem degree_eq (h : IsSeidelCertificate S q) (x : V) :
    h.graph.degree x = 2 * q := by
  have hrs := h.rowSum x
  simp_rw [h.sign_eq] at hrs
  rw [sum_sub_distrib, sum_add_distrib, ← Finset.mul_sum, sum_adj_indicator,
    sum_eq_indicator] at hrs
  simp [h.card] at hrs
  omega

theorem square_eq (h : IsSeidelCertificate S q) {x y : V} (hxy : x ≠ y) :
    ∑ z, S x z * S z y =
      4 * (Fintype.card (h.graph.commonNeighbors x y) : ℤ) +
        4 * indicator (h.graph.Adj x y) - 4 * q := by
  simp_rw [h.sign_eq]
  have hdy : h.graph.degree y = 2 * q := h.degree_eq y
  have hdx : h.graph.degree x = 2 * q := h.degree_eq x
  calc
    _ = ∑ z, (4 * (indicator (h.graph.Adj x z) * indicator (h.graph.Adj z y)) +
          2 * (indicator (h.graph.Adj x z) * indicator (z = y)) +
          2 * (indicator (x = z) * indicator (h.graph.Adj z y)) -
          2 * indicator (h.graph.Adj x z) -
          2 * indicator (h.graph.Adj z y) +
          indicator (x = z) * indicator (z = y) -
          indicator (x = z) - indicator (z = y) + 1) := by
        apply Finset.sum_congr rfl
        intro z hz
        ring
    _ = 4 * (∑ z, indicator (h.graph.Adj x z) * indicator (h.graph.Adj z y)) +
          2 * (∑ z, indicator (h.graph.Adj x z) * indicator (z = y)) +
          2 * (∑ z, indicator (x = z) * indicator (h.graph.Adj z y)) -
          2 * (∑ z, indicator (h.graph.Adj x z)) -
          2 * (∑ z, indicator (h.graph.Adj z y)) +
          (∑ z, indicator (x = z) * indicator (z = y)) -
          (∑ z, indicator (x = z)) - (∑ z, indicator (z = y)) +
          (Fintype.card V : ℤ) := by
        simp only [sum_add_distrib, sum_sub_distrib, mul_sum, sum_const,
          card_univ, nsmul_eq_mul, mul_one]
    _ = _ := by
      rw [sum_common_indicator, sum_indicator_mul_eq,
        sum_eq_mul_indicator, sum_adj_indicator,
        sum_eq_mul_eq hxy, sum_eq_indicator]
      have hsumy : (∑ z, indicator (h.graph.Adj z y)) =
          (h.graph.degree y : ℤ) := by
        calc
          _ = ∑ z, indicator (h.graph.Adj y z) := by
            apply Finset.sum_congr rfl
            intro z hz
            change (if S z y = 1 then 1 else 0) = (if S y z = 1 then 1 else 0)
            rw [h.symm z y]
          _ = _ := sum_adj_indicator h.graph y
      rw [hsumy]
      rw [show (∑ z, indicator (z = y)) = 1 by
        simpa [eq_comm] using sum_eq_indicator y]
      simp only [hdx, hdy, h.card]
      push_cast
      ring

theorem red_commonNeighbors_lt (h : IsSeidelCertificate S q) {x y : V}
    (hxy : h.graph.Adj x y) :
    Fintype.card (h.graph.commonNeighbors x y) < q := by
  have hne : x ≠ y := h.graph.ne_of_adj hxy
  have hs := h.square_nonpos hne
  rw [h.square_eq hne] at hs
  rw [show indicator (h.graph.Adj x y) = 1 by rw [indicator, if_pos hxy]] at hs
  omega

theorem nonedge_commonNeighbors_lt (h : IsSeidelCertificate S q) {x y : V}
    (hne : x ≠ y) (hxy : ¬h.graph.Adj x y) :
    Fintype.card (h.graph.commonNeighbors x y) < q + 1 := by
  have hs := h.square_nonpos hne
  rw [h.square_eq hne] at hs
  rw [show indicator (h.graph.Adj x y) = 0 by rw [indicator, if_neg hxy]] at hs
  omega

end IsSeidelCertificate

end BookS1
