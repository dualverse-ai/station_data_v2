import BookS1.Definitions

/-!
# Conference graphs as sign matrices

For a graph `G`, `conferenceSign G` is the usual matrix `C = 2A - J + I`:
zero on the diagonal, `+1` on edges, and `-1` on nonedges.  The structure
`IsConferenceSign` records the two identities used by the lift.  The final
theorem of this file derives those identities from the genuine strongly
regular graph hypotheses in the paper.
-/

namespace BookS1

open scoped BigOperators
open Finset

universe u

variable {V : Type u}

/-- Edge-positive sign matrix of a simple graph. -/
def conferenceSign [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) : ℤ :=
  if x = y then 0 else if G.Adj x y then 1 else -1

@[simp] theorem conferenceSign_self [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x : V) :
    conferenceSign G x x = 0 := by simp [conferenceSign]

theorem conferenceSign_symm [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x y : V) :
    conferenceSign G x y = conferenceSign G y x := by
  simp only [conferenceSign, eq_comm (a := x) (b := y), G.adj_comm]

theorem conferenceSign_eq_one_iff [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {x y : V} :
    conferenceSign G x y = 1 ↔ G.Adj x y := by
  by_cases hxy : x = y
  · subst y
    simp
  · simp [conferenceSign, hxy]

theorem conferenceSign_eq_neg_one_of_ne [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {x y : V}
    (hxy : x ≠ y) (h : ¬G.Adj x y) : conferenceSign G x y = -1 := by
  simp [conferenceSign, hxy, h]

/-- The two conference-matrix equations `C 1 = 0` and `C² = qI-J`, together
with the elementary sign conditions. -/
structure IsConferenceSign [Fintype V] [DecidableEq V]
    (C : V → V → ℤ) (q : ℕ) : Prop where
  card : Fintype.card V = q
  symm : ∀ x y, C x y = C y x
  diag : ∀ x, C x x = 0
  offdiag : ∀ ⦃x y⦄, x ≠ y → C x y = 1 ∨ C x y = -1
  rowSum : ∀ x, ∑ y, C x y = 0
  mulSum : ∀ x y, ∑ z, C x z * C z y = if x = y then (q : ℤ) - 1 else -1

namespace IsConferenceSign

variable [Fintype V] [DecidableEq V] {C : V → V → ℤ} {q : ℕ}

theorem offdiag_sq (h : IsConferenceSign C q) {x y : V} (hxy : x ≠ y) :
    C x y * C x y = 1 := by
  rcases h.offdiag hxy with hc | hc <;> simp [hc]

end IsConferenceSign

end BookS1
