import BookS1.SRGBridge

/-!
# Conference-graph lower bound for book Ramsey numbers

The exported theorem is the lower-bound side of S1 in the paper.  The known
universal upper bound is intentionally not imported.
-/

namespace BookS1

open Finset

universe u

variable {V : Type u}

/-- The conference lift satisfies the complete Seidel certificate. -/
theorem conferenceLift_isSeidelCertificate [Fintype V] [DecidableEq V]
    {C : V → V → ℤ} {q : ℕ} (h : IsConferenceSign C q) :
    IsSeidelCertificate (liftSign C) q where
  card := by simp [h.card]
  symm := liftSign_symm h.symm
  diag := liftSign_diag h.diag
  offdiag := by
    intro x y hxy
    exact liftSign_offdiag h.diag h.offdiag (x := x) (y := y) hxy
  rowSum := liftSign_rowSum h
  square_nonpos := by
    intro x y hxy
    exact liftSign_mulSum_nonpos h (x := x) (y := y) hxy

private theorem card_neighbor_union [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {d : ℕ} (hreg : G.IsRegularOfDegree d) (v w : V) :
    #(G.neighborFinset v ∪ G.neighborFinset w) =
      2 * d - Fintype.card (G.commonNeighbors v w) := by
  have hinter : G.neighborFinset v ∩ G.neighborFinset w =
      (G.commonNeighbors v w).toFinset := by
    ext z
    simp [SimpleGraph.commonNeighbors]
  have hi := Finset.card_union_add_card_inter (G.neighborFinset v) (G.neighborFinset w)
  rw [hinter, Set.toFinset_card, SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.card_neighborFinset_eq_degree, hreg.degree_eq, hreg.degree_eq] at hi
  have hle := G.card_commonNeighbors_le_degree_left v w
  rw [hreg.degree_eq] at hle
  omega

/-- In the balanced order/degree situation of the lift, a nonedge has the same
number of common red neighbours as common blue neighbours. -/
theorem card_compl_commonNeighbors_eq [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ)
    (hcard : Fintype.card V = 4 * q + 2)
    (hreg : G.IsRegularOfDegree (2 * q)) {v w : V}
    (ha : Gᶜ.Adj v w) :
    Fintype.card (Gᶜ.commonNeighbors v w) =
      Fintype.card (G.commonNeighbors v w) := by
  let a := Fintype.card (G.commonNeighbors v w)
  have hunion := card_neighbor_union G hreg v w
  have hne : v ≠ w := Gᶜ.ne_of_adj ha
  have hna : ¬G.Adj v w := ((SimpleGraph.compl_adj G v w).mp ha).2
  have hnaw : ¬G.Adj w v := fun h => hna (G.symm h)
  have hv_not : v ∉ G.neighborFinset v ∪ G.neighborFinset w := by
    simp [SimpleGraph.mem_neighborFinset, hnaw]
  have hw_not : w ∉ insert v (G.neighborFinset v ∪ G.neighborFinset w) := by
    simp [hne.symm, SimpleGraph.mem_neighborFinset, hna]
  have hset : (Gᶜ.commonNeighbors v w).toFinset =
      (Finset.univ \ insert w (insert v (G.neighborFinset v ∪ G.neighborFinset w))) := by
    ext z
    simp only [Set.mem_toFinset, SimpleGraph.mem_commonNeighbors,
      SimpleGraph.compl_adj, mem_sdiff, mem_univ, true_and, mem_insert,
      mem_union, SimpleGraph.mem_neighborFinset, not_or]
    constructor
    · rintro ⟨⟨hzv, hnzv⟩, hzw, hnzw⟩
      exact ⟨(fun h => hzw h.symm), (fun h => hzv h.symm), hnzv, hnzw⟩
    · rintro ⟨hzw, hzv, hnzv, hnzw⟩
      exact ⟨⟨(fun h => hzv h.symm), hnzv⟩, (fun h => hzw h.symm), hnzw⟩
  rw [← Set.toFinset_card, hset]
  rw [card_sdiff_of_subset (by simp), card_univ]
  rw [card_insert_of_notMem hw_not, card_insert_of_notMem hv_not, hunion, hcard]
  have hale := G.card_commonNeighbors_le_degree_left v w
  rw [hreg.degree_eq] at hale
  omega

/-- **Conference-graph book-Ramsey lower bound (S1).**

Writing `q = 4r+1`, a strongly regular graph with conference parameters
`(q, 2r, r-1, r)` explicitly produces a red/blue coloring of `K_(4q+2)`
containing neither a red `B_q` nor a blue `B_(q+1)`.
-/
theorem conference_graph_lower_bound [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : ℕ) (hr : 1 ≤ r)
    (hG : G.IsSRGWith (4 * r + 1) (2 * r) (r - 1) r) :
    ∃ R : SimpleGraph (LiftVertex V),
      Fintype.card (LiftVertex V) = 4 * (4 * r + 1) + 2 ∧
      IsBookRamseyWitness R (4 * r + 1) (4 * r + 2) := by
  let C := conferenceSign G
  have hC : IsConferenceSign C (4 * r + 1) :=
    conferenceSign_of_isSRGWith G r hr hG
  let cert : IsSeidelCertificate (liftSign C) (4 * r + 1) :=
    conferenceLift_isSeidelCertificate hC
  let R := cert.graph
  refine ⟨R, ?_, ?_, ?_⟩
  · simp [hG.card]
  · apply bookFree_of_commonNeighbors_lt R (4 * r + 1)
    intro v w hvw
    exact cert.red_commonNeighbors_lt hvw
  · apply bookFree_of_commonNeighbors_lt Rᶜ (4 * r + 2)
    intro v w hvw
    rw [card_compl_commonNeighbors_eq R (4 * r + 1) cert.card cert.degree_eq hvw]
    have hne : v ≠ w := Rᶜ.ne_of_adj hvw
    have hnot : ¬R.Adj v w := ((SimpleGraph.compl_adj R v w).mp hvw).2
    exact cert.nonedge_commonNeighbors_lt hne hnot

end BookS1
