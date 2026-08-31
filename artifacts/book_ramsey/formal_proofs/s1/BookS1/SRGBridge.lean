import BookS1.SeidelCertificate

/-!
# From a strongly regular conference graph to the matrix identities

This is the audit-critical bridge: the lift is not assumed to start from an
opaque matrix certificate.  The exact strongly regular graph parameters in the
paper imply both conference-sign identities.
-/

namespace BookS1

open scoped BigOperators
open Finset

universe u

variable {V : Type u}

private theorem conferenceSign_eq_indicator [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    conferenceSign G x y =
      2 * indicator (G.Adj x y) + indicator (x = y) - 1 := by
  by_cases hxy : x = y
  · subst y
    simp [conferenceSign, indicator]
  · by_cases ha : G.Adj x y
    · simp [conferenceSign, indicator, hxy, ha]
    · simp [conferenceSign, indicator, hxy, ha]

private theorem conferenceSign_square [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    ∑ z, conferenceSign G x z * conferenceSign G z y =
      4 * (Fintype.card (G.commonNeighbors x y) : ℤ) +
        4 * indicator (G.Adj x y) - 2 * (G.degree x : ℤ) -
        2 * (G.degree y : ℤ) + (Fintype.card V : ℤ) - 2 +
        indicator (x = y) := by
  simp_rw [conferenceSign_eq_indicator]
  calc
    _ = ∑ z, (4 * (indicator (G.Adj x z) * indicator (G.Adj z y)) +
          2 * (indicator (G.Adj x z) * indicator (z = y)) +
          2 * (indicator (x = z) * indicator (G.Adj z y)) -
          2 * indicator (G.Adj x z) - 2 * indicator (G.Adj z y) +
          indicator (x = z) * indicator (z = y) -
          indicator (x = z) - indicator (z = y) + 1) := by
        apply Finset.sum_congr rfl
        intro z hz
        ring
    _ = 4 * (∑ z, indicator (G.Adj x z) * indicator (G.Adj z y)) +
          2 * (∑ z, indicator (G.Adj x z) * indicator (z = y)) +
          2 * (∑ z, indicator (x = z) * indicator (G.Adj z y)) -
          2 * (∑ z, indicator (G.Adj x z)) -
          2 * (∑ z, indicator (G.Adj z y)) +
          (∑ z, indicator (x = z) * indicator (z = y)) -
          (∑ z, indicator (x = z)) - (∑ z, indicator (z = y)) +
          (Fintype.card V : ℤ) := by
        simp only [sum_add_distrib, sum_sub_distrib, mul_sum, sum_const,
          card_univ, nsmul_eq_mul, mul_one]
    _ = _ := by
      rw [sum_common_indicator, sum_indicator_mul_eq, sum_eq_mul_indicator,
        sum_adj_indicator, sum_eq_mul_eq_general, sum_eq_indicator]
      have hsumy : (∑ z, indicator (G.Adj z y)) = (G.degree y : ℤ) := by
        calc
          _ = ∑ z, indicator (G.Adj y z) := by
            apply Finset.sum_congr rfl
            intro z hz
            by_cases ha : G.Adj z y
            · have hb : G.Adj y z := G.symm ha
              simp [indicator, ha, hb]
            · have hb : ¬G.Adj y z := fun h' => ha (G.symm h')
              simp [indicator, ha, hb]
          _ = _ := sum_adj_indicator G y
      rw [hsumy]
      rw [show (∑ z, indicator (z = y)) = 1 by
        simpa [eq_comm] using sum_eq_indicator y]
      ring

/-- Division-free form of the paper's conference-graph hypothesis:
`q = 4r+1`, degree `2r`, adjacent codegree `r-1`, and nonadjacent codegree `r`.
It implies `C1=0` and `C²=qI-J` for the edge-positive sign matrix. -/
theorem conferenceSign_of_isSRGWith [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (hr : 1 ≤ r)
    (hG : G.IsSRGWith (4 * r + 1) (2 * r) (r - 1) r) :
    IsConferenceSign (conferenceSign G) (4 * r + 1) where
  card := hG.card
  symm := conferenceSign_symm G
  diag := conferenceSign_self G
  offdiag := by
    intro x y hxy
    by_cases ha : G.Adj x y
    · left
      exact (conferenceSign_eq_one_iff G).2 ha
    · right
      exact conferenceSign_eq_neg_one_of_ne G hxy ha
  rowSum := by
    intro x
    simp_rw [conferenceSign_eq_indicator]
    rw [sum_sub_distrib, sum_add_distrib, ← Finset.mul_sum,
      sum_adj_indicator, sum_eq_indicator]
    simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
    simp only [hG.regular.degree_eq, hG.card]
    push_cast
    ring
  mulSum := by
    intro x y
    rw [conferenceSign_square]
    simp only [hG.regular.degree_eq, hG.card]
    by_cases hxy : x = y
    · subst y
      have hcn : Fintype.card (G.commonNeighbors x x) = 2 * r := by
        rw [← Set.toFinset_card]
        simpa [SimpleGraph.commonNeighbors, ← SimpleGraph.neighborFinset_def] using
          hG.regular.degree_eq x
      rw [hcn]
      simp [indicator]
      ring
    · by_cases ha : G.Adj x y
      · rw [hG.of_adj x y ha]
        simp [indicator, hxy, ha]
        omega
      · rw [hG.of_not_adj hxy ha]
        simp [indicator, hxy, ha]
        ring

end BookS1
