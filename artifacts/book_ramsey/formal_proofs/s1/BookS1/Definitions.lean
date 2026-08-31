import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
# Book graphs and lower-bound witnesses

This file gives the graph-theoretic statement used by the conference lift.  A
copy of the book `B k` is represented without choosing an arbitrary labelled
graph: it is a spine edge together with `k` distinct common neighbours.  This
is exactly the usual graph-theoretic definition of `k` triangles sharing one
edge.
-/

namespace BookS1

open Function

universe u

/-- `G` contains a `k`-page book: an edge with `k` distinct common neighbours. -/
def ContainsBook {V : Type u} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ v w : V, G.Adj v w ∧
    ∃ page : Fin k → V, Injective page ∧
      ∀ i, G.Adj v (page i) ∧ G.Adj w (page i)

/-- The assertion that `G` has no copy of the book `B k`. -/
def BookFree {V : Type u} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ¬ContainsBook G k

/-- A red/blue lower-bound witness for `R(B r, B b)` on a fixed vertex type.
The graph gives the red edges and its complement gives the blue edges. -/
def IsBookRamseyWitness {V : Type u} (G : SimpleGraph V) (r b : ℕ) : Prop :=
  BookFree G r ∧ BookFree Gᶜ b

theorem bookFree_of_commonNeighbors_lt {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (h : ∀ ⦃v w : V⦄, G.Adj v w → Fintype.card (G.commonNeighbors v w) < k) :
    BookFree G k := by
  classical
  rintro ⟨v, w, hvw, page, hpage, hp⟩
  let f : Fin k → G.commonNeighbors v w := fun i =>
    ⟨page i, (hp i).1, (hp i).2⟩
  have hf : Injective f := fun i j hij => hpage (Subtype.ext_iff.mp hij)
  have hle : k ≤ Fintype.card (G.commonNeighbors v w) := by
    simpa using Fintype.card_le_of_injective f hf
  exact (Nat.not_le_of_lt (h hvw)) hle

/-- The vertex type of the conference lift: four source chambers and two endpoints. -/
abbrev LiftVertex (V : Type u) := (Fin 4 × V) ⊕ Fin 2

@[simp] theorem card_liftVertex (V : Type u) [Fintype V] :
    Fintype.card (LiftVertex V) = 4 * Fintype.card V + 2 := by
  simp [LiftVertex]

end BookS1
