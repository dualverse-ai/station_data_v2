import Mathlib

/-!
# Seidel certificates for two-coloured complete graphs

This file isolates the finite counting argument used by the second book-Ramsey
construction.  A Seidel matrix uses `1` for red and `-1` for blue.  The
certificate theorem turns three readily checkable matrix identities into the
two required book-free bounds.
-/

namespace BookS2

open scoped BigOperators

/-- An (undirected, loopless) adjacency relation on `V`. -/
structure GraphAdjacency (V : Type*) where
  adj : V → V → Prop
  symm : ∀ {u v}, adj u v → adj v u
  loopless : ∀ v, ¬ adj v v

/-- The common neighbours of `u` and `v` in an adjacency relation. -/
noncomputable def commonNeighbors {V : Type*} [Fintype V] (adj : V → V → Prop)
    (u v : V) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun w ↦ adj u w ∧ adj v w

/-- The number of common neighbours of `u` and `v`. -/
noncomputable def commonNeighborCount {V : Type*} [Fintype V] (adj : V → V → Prop)
    (u v : V) : ℕ :=
  (commonNeighbors adj u v).card

/-- A literal copy of the book `B_k`: an edge together with a `k`-element
finset of distinct common neighbours (the pages of the book). -/
def ContainsBook {V : Type*} [Fintype V] (adj : V → V → Prop) (k : ℕ) : Prop :=
  ∃ u v, adj u v ∧ ∃ pages : Finset V,
    pages.card = k ∧ pages ⊆ commonNeighbors adj u v

/-- An adjacency relation is `B_k`-free when it contains no literal `B_k`. -/
def BookFree {V : Type*} [Fintype V] (adj : V → V → Prop) (k : ℕ) : Prop :=
  ¬ ContainsBook adj k

/-- Literal book exclusion is equivalent to the usual common-neighbour count
bound. -/
theorem bookFree_iff_commonNeighborCount {V : Type*} [Fintype V]
    (adj : V → V → Prop) (k : ℕ) :
    BookFree adj k ↔ ∀ u v, adj u v → commonNeighborCount adj u v < k := by
  classical
  constructor
  · intro hfree u v huv
    by_contra hnot
    have hk : k ≤ commonNeighborCount adj u v := by omega
    obtain ⟨pages, hsub, hcard⟩ := Finset.exists_subset_card_eq hk
    exact hfree ⟨u, v, huv, pages, hcard, hsub⟩
  · rintro hbound ⟨u, v, huv, pages, hcard, hsub⟩
    have hle := Finset.card_le_card hsub
    have hlt := hbound u v huv
    simp only [commonNeighborCount] at hlt
    omega

/-- Red adjacency encoded by a Seidel matrix. -/
def redAdj {V : Type*} (S : V → V → ℤ) (u v : V) : Prop :=
  u ≠ v ∧ S u v = 1

/-- Blue adjacency encoded by a Seidel matrix. -/
def blueAdj {V : Type*} (S : V → V → ℤ) (u v : V) : Prop :=
  u ≠ v ∧ S u v = -1

/-- Off the diagonal, the red and blue relations encoded by a `±1` matrix
partition the pairs of vertices. -/
theorem redAdj_or_blueAdj {V : Type*} (S : V → V → ℤ)
    (hpm : ∀ u v, u ≠ v → S u v = 1 ∨ S u v = -1)
    {u v : V} (huv : u ≠ v) : redAdj S u v ∨ blueAdj S u v := by
  rcases hpm u v huv with h | h
  · exact Or.inl ⟨huv, h⟩
  · exact Or.inr ⟨huv, h⟩

private lemma sum_two_indicator {V : Type*} [Fintype V]
    (P : V → Prop) [DecidablePred P] :
    (∑ x : V, if P x then (2 : ℤ) else 0) =
      2 * ((Finset.univ.filter P).card : ℤ) := by
  rw [← Finset.sum_boole P Finset.univ]
  rw [Finset.mul_sum]
  simp

/-- The red graph attached to a symmetric, zero-diagonal Seidel matrix. -/
def redGraph {V : Type*} (S : V → V → ℤ)
    (hS : ∀ u v, S u v = S v u) (_hdiag : ∀ v, S v v = 0) : GraphAdjacency V where
  adj := redAdj S
  symm := by
    rintro u v ⟨huv, h⟩
    exact ⟨Ne.symm huv, by simpa [hS v u] using h⟩
  loopless := by simp [redAdj]

/-- The blue graph attached to a symmetric, zero-diagonal Seidel matrix. -/
def blueGraph {V : Type*} (S : V → V → ℤ)
    (hS : ∀ u v, S u v = S v u) (_hdiag : ∀ v, S v v = 0) : GraphAdjacency V where
  adj := blueAdj S
  symm := by
    rintro u v ⟨huv, h⟩
    exact ⟨Ne.symm huv, by simpa [hS v u] using h⟩
  loopless := by simp [blueAdj]

private lemma row_pair_identity {V : Type*} [Fintype V] [DecidableEq V]
    (S : V → V → ℤ)
    (hS : ∀ u v, S u v = S v u)
    (hdiag : ∀ v, S v v = 0)
    (hpm : ∀ u v, u ≠ v → S u v = 1 ∨ S u v = -1)
    (hrow : ∀ u, ∑ v, S u v = -1)
    {u v : V} (huv : u ≠ v) :
    (-2 : ℤ) =
      2 * (commonNeighborCount (redAdj S) u v : ℤ) -
      2 * (commonNeighborCount (blueAdj S) u v : ℤ) + 2 * S u v := by
  classical
  have hpoint : ∀ x : V,
      S u x + S v x =
        (if redAdj S u x ∧ redAdj S v x then (2 : ℤ) else 0) -
        (if blueAdj S u x ∧ blueAdj S v x then (2 : ℤ) else 0) +
        (if x = u then S u v else 0) +
        (if x = v then S u v else 0) := by
    intro x
    by_cases hxu : x = u
    · subst x
      simp [redAdj, blueAdj, hdiag, hS, huv]
    by_cases hxv : x = v
    · subst x
      simp [redAdj, blueAdj, hdiag, huv, hxu]
    rcases hpm u x (Ne.symm hxu) with hux | hux <;>
      rcases hpm v x (Ne.symm hxv) with hvx | hvx <;>
      simp [redAdj, blueAdj, hxu, hxv, Ne.symm hxu, Ne.symm hxv, hux, hvx]
  calc
    (-2 : ℤ) = (∑ x, S u x) + ∑ x, S v x := by rw [hrow u, hrow v]; norm_num
    _ = ∑ x, (S u x + S v x) := by rw [Finset.sum_add_distrib]
    _ = ∑ x, ((if redAdj S u x ∧ redAdj S v x then (2 : ℤ) else 0) -
          (if blueAdj S u x ∧ blueAdj S v x then (2 : ℤ) else 0) +
          (if x = u then S u v else 0) +
          (if x = v then S u v else 0)) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hpoint x
    _ = 2 * (commonNeighborCount (redAdj S) u v : ℤ) -
        2 * (commonNeighborCount (blueAdj S) u v : ℤ) + 2 * S u v := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          rw [sum_two_indicator, sum_two_indicator]
          simp [commonNeighborCount, commonNeighbors]
          ring

private lemma square_count_identity {V : Type*} [Fintype V] [DecidableEq V]
    (S : V → V → ℤ)
    (hS : ∀ u v, S u v = S v u)
    (hdiag : ∀ v, S v v = 0)
    (hpm : ∀ u v, u ≠ v → S u v = 1 ∨ S u v = -1)
    {u v : V} (huv : u ≠ v) :
    (∑ x, S u x * S x v) =
      2 * (commonNeighborCount (redAdj S) u v : ℤ) +
      2 * (commonNeighborCount (blueAdj S) u v : ℤ) -
      (Fintype.card V : ℤ) + 2 := by
  classical
  have hpoint : ∀ x : V,
      S u x * S x v =
        (if redAdj S u x ∧ redAdj S v x then (2 : ℤ) else 0) +
        (if blueAdj S u x ∧ blueAdj S v x then (2 : ℤ) else 0) - 1 +
        (if x = u then (1 : ℤ) else 0) +
        (if x = v then (1 : ℤ) else 0) := by
    intro x
    by_cases hxu : x = u
    · subst x
      simp [redAdj, blueAdj, hdiag, hS, huv]
    by_cases hxv : x = v
    · subst x
      simp [redAdj, blueAdj, hdiag, huv, hxu]
    rcases hpm u x (Ne.symm hxu) with hux | hux <;>
      rcases hpm v x (Ne.symm hxv) with hvx | hvx <;>
      simp [redAdj, blueAdj, hS x v, hxu, hxv, Ne.symm hxu, Ne.symm hxv, hux, hvx]
  calc
    (∑ x, S u x * S x v) =
        ∑ x, ((if redAdj S u x ∧ redAdj S v x then (2 : ℤ) else 0) +
          (if blueAdj S u x ∧ blueAdj S v x then (2 : ℤ) else 0) - 1 +
          (if x = u then (1 : ℤ) else 0) +
          (if x = v then (1 : ℤ) else 0)) := by
            apply Finset.sum_congr rfl
            intro x hx
            exact hpoint x
    _ = 2 * (commonNeighborCount (redAdj S) u v : ℤ) +
        2 * (commonNeighborCount (blueAdj S) u v : ℤ) -
        (Fintype.card V : ℤ) + 2 := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
          rw [sum_two_indicator, sum_two_indicator]
          simp [commonNeighborCount, commonNeighbors]
          ring

/-- **Generic Seidel certificate theorem.**

On `4n - 2` vertices, a symmetric zero-diagonal `±1` Seidel matrix whose
row sums are `-1` and whose off-diagonal square entries are nonpositive colors
the complete graph with no red `B_(n-1)` and no blue `B_n`.
-/
theorem seidel_certificate {V : Type*} [Fintype V] [DecidableEq V]
    (n : ℕ) (S : V → V → ℤ)
    (hcard : Fintype.card V = 4 * n - 2)
    (hS : ∀ u v, S u v = S v u)
    (hdiag : ∀ v, S v v = 0)
    (hpm : ∀ u v, u ≠ v → S u v = 1 ∨ S u v = -1)
    (hrow : ∀ u, ∑ v, S u v = -1)
    (hsquare : ∀ u v, u ≠ v → ∑ x, S u x * S x v ≤ 0) :
    BookFree (redAdj S) (n - 1) ∧ BookFree (blueAdj S) n := by
  constructor
  · rw [bookFree_iff_commonNeighborCount]
    rintro u v ⟨huv, huvRed⟩
    have hrows := row_pair_identity S hS hdiag hpm hrow huv
    have hsquares := square_count_identity S hS hdiag hpm huv
    have hsquare_le := hsquare u v huv
    rw [hcard] at hsquares
    simp only [huvRed] at hrows
    have hcard_ge : 2 ≤ Fintype.card V := by
      simpa [huv] using Finset.card_le_card (Finset.subset_univ ({u, v} : Finset V))
    rw [hcard] at hcard_ge
    omega
  · rw [bookFree_iff_commonNeighborCount]
    rintro u v ⟨huv, huvBlue⟩
    have hrows := row_pair_identity S hS hdiag hpm hrow huv
    have hsquares := square_count_identity S hS hdiag hpm huv
    have hsquare_le := hsquare u v huv
    rw [hcard] at hsquares
    simp only [huvBlue] at hrows
    have hcard_ge : 2 ≤ Fintype.card V := by
      simpa [huv] using Finset.card_le_card (Finset.subset_univ ({u, v} : Finset V))
    rw [hcard] at hcard_ge
    omega

/-- A bundled form of all hypotheses checked by a concrete Seidel
construction. -/
structure SeidelCertificate (V : Type*) [Fintype V] [DecidableEq V] (n : ℕ) where
  matrix : V → V → ℤ
  card_eq : Fintype.card V = 4 * n - 2
  symmetric : ∀ u v, matrix u v = matrix v u
  diagonal : ∀ v, matrix v v = 0
  offDiagonal : ∀ u v, u ≠ v → matrix u v = 1 ∨ matrix u v = -1
  rowSum : ∀ u, ∑ v, matrix u v = -1
  squareNonpositive : ∀ u v, u ≠ v → ∑ x, matrix u x * matrix x v ≤ 0

/-- The reusable book-freeness conclusion of a bundled certificate. -/
theorem SeidelCertificate.bookFree {V : Type*} [Fintype V] [DecidableEq V]
    {n : ℕ} (C : SeidelCertificate V n) :
    BookFree (redAdj C.matrix) (n - 1) ∧ BookFree (blueAdj C.matrix) n :=
  seidel_certificate n C.matrix C.card_eq C.symmetric C.diagonal C.offDiagonal
    C.rowSum C.squareNonpositive

end BookS2
