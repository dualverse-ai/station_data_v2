import Mathlib

/-!
# Finite certificates for lower bounds on book Ramsey numbers

A book with `k` pages is represented by an edge having at least `k` common
neighbors.  Thus this file does not need to choose a separate graph model for
the book graph itself.
-/

namespace BookS3

open scoped Classical

variable {V : Type*} [Fintype V]

/-- The common neighbors of `u` and `v`, as a finite set. -/
noncomputable def commonNeighbors (G : SimpleGraph V) (u v : V) : Finset V :=
  Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w

/-- The degree of a vertex, expressed without any local-finiteness wrapper. -/
noncomputable def degree (G : SimpleGraph V) (u : V) : Nat :=
  (Finset.univ.filter fun w => G.Adj u w).card

/-- `G` contains a book with `k` pages if some edge has at least `k` common
neighbors. -/
def ContainsBook (G : SimpleGraph V) (k : Nat) : Prop :=
  ∃ u v, G.Adj u v ∧ k ≤ (commonNeighbors G u v).card

/-- `G` has no book with `k` pages. -/
def BookFree (G : SimpleGraph V) (k : Nat) : Prop :=
  ¬ContainsBook G k

/-- The proposition certified by a red graph on `Fin N`: the red graph avoids
the first book and its blue complement avoids the second. -/
def LowerBoundCertificate (N redPages bluePages : Nat)
    (red : SimpleGraph (Fin N)) : Prop :=
  BookFree red redPages ∧ BookFree redᶜ bluePages

/-- Reindexing a graph along an equivalence preserves the number of common
neighbors of each corresponding pair. -/
theorem commonNeighbors_card_comap_equiv
    {W : Type*} [Fintype W] (G : SimpleGraph V) (e : W ≃ V) (u v : W) :
    (commonNeighbors (G.comap e) u v).card =
      (commonNeighbors G (e u) (e v)).card := by
  classical
  apply Finset.card_equiv e
  intro w
  simp [commonNeighbors]

/-- Book-freeness is invariant under a relabeling of the vertex type. -/
theorem bookFree_comap_equiv
    {W : Type*} [Fintype W] (G : SimpleGraph V) (e : W ≃ V) (k : Nat) :
    BookFree (G.comap e) k ↔ BookFree G k := by
  constructor
  · intro hW hG
    rcases hG with ⟨u, v, huv, hk⟩
    apply hW
    refine ⟨e.symm u, e.symm v, ?_, ?_⟩
    · simpa using huv
    · rw [commonNeighbors_card_comap_equiv]
      simpa using hk
  · intro hG hW
    rcases hW with ⟨u, v, huv, hk⟩
    apply hG
    refine ⟨e u, e v, ?_, ?_⟩
    · simpa using huv
    · simpa [commonNeighbors_card_comap_equiv] using hk

/-- Any finite graph certificate can be relabeled onto the canonical type
`Fin N` used by `LowerBoundCertificate`. -/
theorem exists_lowerBoundCertificate_of_card
    {N redPages bluePages : Nat} (G : SimpleGraph V)
    (hcard : Fintype.card V = N)
    (hbooks : BookFree G redPages ∧ BookFree Gᶜ bluePages) :
    ∃ red : SimpleGraph (Fin N),
      LowerBoundCertificate N redPages bluePages red := by
  classical
  let e : Fin N ≃ V := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨G.comap e, ?_⟩
  constructor
  · exact (bookFree_comap_equiv G e redPages).2 hbooks.1
  · have hcompl : (G.comap e)ᶜ = Gᶜ.comap e := by
      ext u v
      simp
    rw [hcompl]
    exact (bookFree_comap_equiv Gᶜ e bluePages).2 hbooks.2

private noncomputable def neitherNeighbors (G : SimpleGraph V) (u v : V) : Finset V :=
  Finset.univ.filter fun w => ¬G.Adj u w ∧ ¬G.Adj v w

private noncomputable def leftOnlyNeighbors (G : SimpleGraph V) (u v : V) : Finset V :=
  Finset.univ.filter fun w => G.Adj u w ∧ ¬G.Adj v w

private noncomputable def rightOnlyNeighbors (G : SimpleGraph V) (u v : V) : Finset V :=
  Finset.univ.filter fun w => ¬G.Adj u w ∧ G.Adj v w

private theorem complement_commonNeighbors_eq_erase
    [DecidableEq V] (G : SimpleGraph V) (u v : V) :
    commonNeighbors Gᶜ u v = ((neitherNeighbors G u v).erase u).erase v := by
  ext w
  simp only [commonNeighbors, neitherNeighbors, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_erase, SimpleGraph.compl_adj]
  constructor
  · rintro ⟨⟨hwu, hGu⟩, hwv, hGv⟩
    exact ⟨Ne.symm hwv, Ne.symm hwu, hGu, hGv⟩
  · rintro ⟨hwv, hwu, hGu, hGv⟩
    exact ⟨⟨Ne.symm hwu, hGu⟩, Ne.symm hwv, hGv⟩

private theorem complement_commonNeighbors_card_add_two
    [DecidableEq V] (G : SimpleGraph V) {u v : V} (huv : u ≠ v)
    (hnot : ¬G.Adj u v) :
    (commonNeighbors Gᶜ u v).card + 2 = (neitherNeighbors G u v).card := by
  have hnot' : ¬G.Adj v u := by
    simpa [G.adj_comm] using hnot
  have hu_mem : u ∈ neitherNeighbors G u v := by
    simp [neitherNeighbors, hnot']
  have hv_mem : v ∈ (neitherNeighbors G u v).erase u := by
    simp [neitherNeighbors, Ne.symm huv, hnot]
  have herase_u := Finset.card_erase_of_mem hu_mem
  have herase_v := Finset.card_erase_of_mem hv_mem
  rw [complement_commonNeighbors_eq_erase G u v]
  have hpos : 0 < ((neitherNeighbors G u v).erase u).card :=
    Finset.card_pos.mpr ⟨v, hv_mem⟩
  omega

private theorem four_cells_card
    (G : SimpleGraph V) (u v : V) :
    (commonNeighbors G u v).card + (leftOnlyNeighbors G u v).card +
        (rightOnlyNeighbors G u v).card + (neitherNeighbors G u v).card =
      Fintype.card V := by
  classical
  let Au := Finset.univ.filter fun w : V => G.Adj u w
  let nAu := Finset.univ.filter fun w : V => ¬G.Adj u w
  have hsplitU := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset V)) (fun w => G.Adj u w)
  have hsplitA := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Au) (fun w => G.Adj v w)
  have hsplitNA := Finset.filter_card_add_filter_neg_card_eq_card
    (s := nAu) (fun w => G.Adj v w)
  have hcommon :
      (Au.filter fun w => G.Adj v w) = commonNeighbors G u v := by
    ext w
    simp [Au, commonNeighbors]
  have hleft :
      (Au.filter fun w => ¬G.Adj v w) = leftOnlyNeighbors G u v := by
    ext w
    simp [Au, leftOnlyNeighbors]
  have hright :
      (nAu.filter fun w => G.Adj v w) = rightOnlyNeighbors G u v := by
    ext w
    simp [nAu, rightOnlyNeighbors]
  have hneither :
      (nAu.filter fun w => ¬G.Adj v w) = neitherNeighbors G u v := by
    ext w
    simp [nAu, neitherNeighbors]
  have hU : Au.card + nAu.card = Fintype.card V := by
    simpa [Au, nAu] using hsplitU
  rw [hcommon, hleft] at hsplitA
  rw [hright, hneither] at hsplitNA
  omega

private theorem degree_eq_common_add_left
    (G : SimpleGraph V) (u v : V) :
    degree G u =
      (commonNeighbors G u v).card + (leftOnlyNeighbors G u v).card := by
  classical
  let Au := Finset.univ.filter fun w : V => G.Adj u w
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Au) (fun w => G.Adj v w)
  have hcommon :
      (Au.filter fun w => G.Adj v w) = commonNeighbors G u v := by
    ext w
    simp [Au, commonNeighbors]
  have hleft :
      (Au.filter fun w => ¬G.Adj v w) = leftOnlyNeighbors G u v := by
    ext w
    simp [Au, leftOnlyNeighbors]
  simpa [degree, Au, hcommon, hleft] using hsplit.symm

private theorem degree_eq_common_add_right
    (G : SimpleGraph V) (u v : V) :
    degree G v =
      (commonNeighbors G u v).card + (rightOnlyNeighbors G u v).card := by
  classical
  let Av := Finset.univ.filter fun w : V => G.Adj v w
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Av) (fun w => G.Adj u w)
  have hcommon :
      (Av.filter fun w => G.Adj u w) = commonNeighbors G u v := by
    ext w
    simp [Av, commonNeighbors, and_comm]
  have hright :
      (Av.filter fun w => ¬G.Adj u w) = rightOnlyNeighbors G u v := by
    ext w
    simp [Av, rightOnlyNeighbors, and_comm]
  simpa [degree, Av, hcommon, hright] using hsplit.symm

/-- In the parameter range of the third-family construction, complement common
neighbor counts agree with red common-neighbor counts on red nonedges. -/
theorem complement_commonNeighbors_card_eq
    {n : Nat} (G : SimpleGraph (Fin (4 * n - 2)))
    (hregular : ∀ u, degree G u = 2 * n - 2)
    {u v : Fin (4 * n - 2)} (huv : u ≠ v) (hnot : ¬G.Adj u v) :
    (commonNeighbors Gᶜ u v).card = (commonNeighbors G u v).card := by
  have hfour := four_cells_card G u v
  have hdu := degree_eq_common_add_left G u v
  have hdv := degree_eq_common_add_right G u v
  have hblue := complement_commonNeighbors_card_add_two G huv hnot
  rw [hregular u] at hdu
  rw [hregular v] at hdv
  simp only [Fintype.card_fin] at hfour
  omega

/-- The complement-count identity on an arbitrary finite vertex type. -/
theorem complement_commonNeighbors_card_eq_of_card
    {V : Type*} [Fintype V] {n : Nat} (G : SimpleGraph V)
    (hcard : Fintype.card V = 4 * n - 2)
    (hregular : ∀ u, degree G u = 2 * n - 2)
    {u v : V} (huv : u ≠ v) (hnot : ¬G.Adj u v) :
    (commonNeighbors Gᶜ u v).card = (commonNeighbors G u v).card := by
  classical
  have hfour := four_cells_card G u v
  have hdu := degree_eq_common_add_left G u v
  have hdv := degree_eq_common_add_right G u v
  have hblue := complement_commonNeighbors_card_add_two G huv hnot
  rw [hregular u] at hdu
  rw [hregular v] at hdv
  rw [hcard] at hfour
  omega

/-- The regular-graph book criterion on any finite vertex type of the required
cardinality. -/
theorem regularGraphCriterionOfCard
    {V : Type*} [Fintype V] {n : Nat} (hn : 2 ≤ n) (G : SimpleGraph V)
    (hcard : Fintype.card V = 4 * n - 2)
    (hregular : ∀ u, degree G u = 2 * n - 2)
    (hedge : ∀ ⦃u v⦄, G.Adj u v → (commonNeighbors G u v).card ≤ n - 2)
    (hnonedge : ∀ ⦃u v⦄, u ≠ v → ¬G.Adj u v →
      (commonNeighbors G u v).card ≤ n - 1) :
    BookFree G (n - 1) ∧ BookFree Gᶜ n := by
  constructor
  · rintro ⟨u, v, huv, hbook⟩
    have hsmall := hedge huv
    omega
  · rintro ⟨u, v, huv, hbook⟩
    have hne : u ≠ v := ((G.compl_adj u v).mp huv).1
    have hnot : ¬G.Adj u v := ((G.compl_adj u v).mp huv).2
    have hsmall := hnonedge hne hnot
    rw [complement_commonNeighbors_card_eq_of_card G hcard hregular hne hnot] at hbook
    omega

/-- The generic regular-graph criterion underlying the third infinite family.

On `4*n-2` vertices, a `(2*n-2)`-regular red graph is a lower-bound
certificate for red `B_(n-1)` versus blue `B_n` provided red edges have at
most `n-2` red common neighbors and red nonedges have at most `n-1`.
-/
theorem regularGraphCriterion
    {n : Nat} (hn : 2 ≤ n) (G : SimpleGraph (Fin (4 * n - 2)))
    (hregular : ∀ u, degree G u = 2 * n - 2)
    (hedge : ∀ ⦃u v⦄, G.Adj u v → (commonNeighbors G u v).card ≤ n - 2)
    (hnonedge : ∀ ⦃u v⦄, u ≠ v → ¬G.Adj u v →
      (commonNeighbors G u v).card ≤ n - 1) :
    LowerBoundCertificate (4 * n - 2) (n - 1) n G := by
  constructor
  · rintro ⟨u, v, huv, hbook⟩
    have hsmall := hedge huv
    omega
  · rintro ⟨u, v, huv, hbook⟩
    have hne : u ≠ v := ((G.compl_adj u v).mp huv).1
    have hnot : ¬G.Adj u v := ((G.compl_adj u v).mp huv).2
    have hsmall := hnonedge hne hnot
    rw [complement_commonNeighbors_card_eq G hregular hne hnot] at hbook
    omega

end BookS3
