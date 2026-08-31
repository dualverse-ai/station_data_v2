import BookS3.Ramsey

/-!
# A two-fibre difference construction

This file turns finite additive correlation data into a red/blue book-Ramsey
certificate.  The hypotheses in `CorrelationProfile` mention only explicit
finsets in the additive group; in particular, they do not assume graph
codegree bounds or book-freeness.
-/

namespace BookS3

open scoped Classical

variable {W : Type*} [AddCommGroup W] [Fintype W]

/-- Difference sets for the two fibres.  `A` and `B` are symmetric and omit
zero, exactly the conditions needed for the within-fibre Cayley graphs to be
simple.  The oriented cross difference set `C` needs no symmetry condition. -/
structure DifferenceData (W : Type*) [AddCommGroup W] [Fintype W] where
  A : Finset W
  B : Finset W
  C : Finset W
  A_neg : ∀ d, -d ∈ A ↔ d ∈ A
  B_neg : ∀ d, -d ∈ B ↔ d ∈ B
  zero_not_mem_A : 0 ∉ A
  zero_not_mem_B : 0 ∉ B

/-- The explicit adjacency relation before packaging it as a simple graph. -/
def differenceRel (D : DifferenceData W) : Bool × W → Bool × W → Prop
  | (false, x), (false, y) => y - x ∈ D.A
  | (true, x), (true, y) => y - x ∈ D.B
  | (false, x), (true, y) => y - x ∈ D.C
  | (true, x), (false, y) => x - y ∈ D.C

/-- The two-fibre Cayley graph determined by `A`, `B`, and the oriented cross
difference set `C`. -/
def differenceGraph (D : DifferenceData W) : SimpleGraph (Bool × W) where
  Adj := differenceRel D
  symm := by
    rintro ⟨i, x⟩ ⟨j, y⟩
    cases i <;> cases j <;> simp only [differenceRel]
    · intro h
      have := (D.A_neg (y - x)).2 h
      simpa only [neg_sub] using this
    · exact id
    · exact id
    · intro h
      have := (D.B_neg (y - x)).2 h
      simpa only [neg_sub] using this
  loopless := by
    rintro ⟨i, x⟩
    cases i with
    | false => simpa [differenceRel] using D.zero_not_mem_A
    | true => simpa [differenceRel] using D.zero_not_mem_B

@[simp] theorem differenceGraph_adj_ff (D : DifferenceData W) (x y : W) :
    (differenceGraph D).Adj (false, x) (false, y) ↔ y - x ∈ D.A := Iff.rfl

@[simp] theorem differenceGraph_adj_tt (D : DifferenceData W) (x y : W) :
    (differenceGraph D).Adj (true, x) (true, y) ↔ y - x ∈ D.B := Iff.rfl

@[simp] theorem differenceGraph_adj_ft (D : DifferenceData W) (x y : W) :
    (differenceGraph D).Adj (false, x) (true, y) ↔ y - x ∈ D.C := Iff.rfl

@[simp] theorem differenceGraph_adj_tf (D : DifferenceData W) (x y : W) :
    (differenceGraph D).Adj (true, x) (false, y) ↔ x - y ∈ D.C := Iff.rfl

/-- Additive correlation: `t` lies in `X` and `t-d` lies in `Y`. -/
noncomputable def correlation (X Y : Finset W) (d : W) : Finset W :=
  X.filter fun t => t - d ∈ Y

/-- Additive convolution: `t` lies in `X` and `d-t` lies in `Y`. -/
noncomputable def convolution (X Y : Finset W) (d : W) : Finset W :=
  X.filter fun t => d - t ∈ Y

/-- A purely additive profile sufficient for the third-family lift.  Every
codegree hypothesis is a cardinality of an explicit correlation or
convolution of `A`, `B`, and `C`. -/
structure CorrelationProfile (D : DifferenceData W) (n : Nat) : Prop where
  vertex_count : 2 * Fintype.card W = 4 * n - 2
  degree_fibre0 : D.A.card + D.C.card = 2 * n - 2
  degree_fibre1 : D.B.card + D.C.card = 2 * n - 2
  edge_fibre0 : ∀ d ∈ D.A,
    (correlation D.A D.A d).card + (correlation D.C D.C d).card ≤ n - 2
  edge_fibre1 : ∀ d ∈ D.B,
    (correlation D.B D.B d).card + (correlation D.C D.C d).card ≤ n - 2
  edge_cross : ∀ d ∈ D.C,
    (convolution D.A D.C d).card + (correlation D.C D.B d).card ≤ n - 2
  nonedge_fibre0 : ∀ d, d ≠ 0 → d ∉ D.A →
    (correlation D.A D.A d).card + (correlation D.C D.C d).card ≤ n - 1
  nonedge_fibre1 : ∀ d, d ≠ 0 → d ∉ D.B →
    (correlation D.B D.B d).card + (correlation D.C D.C d).card ≤ n - 1
  nonedge_cross : ∀ d, d ∉ D.C →
    (convolution D.A D.C d).card + (correlation D.C D.B d).card ≤ n - 1

omit [AddCommGroup W] in
private theorem card_filter_bool_prod (p : Bool × W → Prop)
    [DecidableEq W] [DecidablePred p] :
    (Finset.univ.filter p).card =
      (Finset.univ.filter fun w : W => p (false, w)).card +
      (Finset.univ.filter fun w : W => p (true, w)).card := by
  simp only [Finset.card_filter]
  rw [← Finset.univ_product_univ]
  rw [Finset.sum_product]
  simp [Nat.add_comm]

private theorem card_sub_sub (X Y : Finset W) (x y : W) :
    (Finset.univ.filter fun w : W => w - x ∈ X ∧ w - y ∈ Y).card =
      (correlation X Y (y - x)).card := by
  classical
  apply Finset.card_equiv (Equiv.subRight x)
  intro w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, correlation]
  constructor
  · rintro ⟨hx, hy⟩
    constructor
    · exact hx
    · rw [Equiv.subRight_apply]
      convert hy using 1
      abel
  · rintro ⟨hx, hy⟩
    constructor
    · exact hx
    · rw [Equiv.subRight_apply] at hy
      convert hy using 1
      abel

private theorem card_sub_reverse (X Y : Finset W) (x y : W) :
    (Finset.univ.filter fun w : W => w - x ∈ X ∧ y - w ∈ Y).card =
      (convolution X Y (y - x)).card := by
  classical
  apply Finset.card_equiv (Equiv.subRight x)
  intro w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, convolution]
  constructor <;> rintro ⟨hx, hy⟩ <;> constructor
  · exact hx
  · rw [Equiv.subRight_apply]
    convert hy using 1
    abel
  · exact hx
  · rw [Equiv.subRight_apply] at hy
    convert hy using 1
    abel

private theorem card_reverse_reverse (X Y : Finset W) (x y : W) :
    (Finset.univ.filter fun w : W => x - w ∈ X ∧ y - w ∈ Y).card =
      (correlation Y X (y - x)).card := by
  classical
  apply Finset.card_equiv (Equiv.subLeft y)
  intro w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, correlation]
  constructor <;> rintro ⟨hx, hy⟩ <;> constructor
  · exact hy
  · rw [Equiv.subLeft_apply]
    convert hx using 1
    abel
  · rw [Equiv.subLeft_apply] at hy
    convert hy using 1
    abel
  · exact hx

private theorem card_single_sub (X : Finset W) (x : W) :
    (Finset.univ.filter fun w : W => w - x ∈ X).card = X.card := by
  classical
  apply Finset.card_equiv (Equiv.subRight x)
  intro w
  simp

private theorem card_single_reverse (X : Finset W) (x : W) :
    (Finset.univ.filter fun w : W => x - w ∈ X).card = X.card := by
  classical
  apply Finset.card_equiv (Equiv.subLeft x)
  intro w
  simp

/-- Exact common-neighbor count for two vertices in fibre zero. -/
theorem commonNeighbors_card_fibre0 (D : DifferenceData W) (x y : W) :
    (commonNeighbors (differenceGraph D) (false, x) (false, y)).card =
      (correlation D.A D.A (y - x)).card +
        (correlation D.C D.C (y - x)).card := by
  classical
  have hcommon : commonNeighbors (differenceGraph D) (false, x) (false, y) =
      Finset.univ.filter (fun w : Bool × W =>
        (differenceGraph D).Adj (false, x) w ∧
          (differenceGraph D).Adj (false, y) w) := by
    ext w
    simp [commonNeighbors]
  rw [hcommon]
  calc
    _ = (Finset.univ.filter fun w : W =>
          (differenceGraph D).Adj (false, x) (false, w) ∧
            (differenceGraph D).Adj (false, y) (false, w)).card +
        (Finset.univ.filter fun w : W =>
          (differenceGraph D).Adj (false, x) (true, w) ∧
            (differenceGraph D).Adj (false, y) (true, w)).card :=
      card_filter_bool_prod (p := fun w : Bool × W =>
        (differenceGraph D).Adj (false, x) w ∧ (differenceGraph D).Adj (false, y) w)
    _ = _ := by
      simp only [differenceGraph_adj_ff, differenceGraph_adj_ft]
      rw [card_sub_sub, card_sub_sub]

/-- Exact common-neighbor count for two vertices in fibre one. -/
theorem commonNeighbors_card_fibre1 (D : DifferenceData W) (x y : W) :
    (commonNeighbors (differenceGraph D) (true, x) (true, y)).card =
      (correlation D.B D.B (y - x)).card +
        (correlation D.C D.C (y - x)).card := by
  classical
  have hcommon : commonNeighbors (differenceGraph D) (true, x) (true, y) =
      Finset.univ.filter (fun w : Bool × W =>
        (differenceGraph D).Adj (true, x) w ∧
          (differenceGraph D).Adj (true, y) w) := by
    ext w
    simp [commonNeighbors]
  rw [hcommon]
  calc
    _ = (Finset.univ.filter fun w : W =>
          (differenceGraph D).Adj (true, x) (false, w) ∧
            (differenceGraph D).Adj (true, y) (false, w)).card +
        (Finset.univ.filter fun w : W =>
          (differenceGraph D).Adj (true, x) (true, w) ∧
            (differenceGraph D).Adj (true, y) (true, w)).card :=
      card_filter_bool_prod (p := fun w : Bool × W =>
        (differenceGraph D).Adj (true, x) w ∧ (differenceGraph D).Adj (true, y) w)
    _ = _ := by
      simp only [differenceGraph_adj_tf, differenceGraph_adj_tt]
      rw [card_reverse_reverse, card_sub_sub]
      omega

/-- Exact common-neighbor count for an oriented cross-fibre pair. -/
theorem commonNeighbors_card_cross (D : DifferenceData W) (x y : W) :
    (commonNeighbors (differenceGraph D) (false, x) (true, y)).card =
      (convolution D.A D.C (y - x)).card +
        (correlation D.C D.B (y - x)).card := by
  classical
  have hcommon : commonNeighbors (differenceGraph D) (false, x) (true, y) =
      Finset.univ.filter (fun w : Bool × W =>
        (differenceGraph D).Adj (false, x) w ∧
          (differenceGraph D).Adj (true, y) w) := by
    ext w
    simp [commonNeighbors]
  rw [hcommon]
  calc
    _ = (Finset.univ.filter fun w : W =>
          (differenceGraph D).Adj (false, x) (false, w) ∧
            (differenceGraph D).Adj (true, y) (false, w)).card +
        (Finset.univ.filter fun w : W =>
          (differenceGraph D).Adj (false, x) (true, w) ∧
            (differenceGraph D).Adj (true, y) (true, w)).card :=
      card_filter_bool_prod (p := fun w : Bool × W =>
        (differenceGraph D).Adj (false, x) w ∧ (differenceGraph D).Adj (true, y) w)
    _ = _ := by
      simp only [differenceGraph_adj_ff, differenceGraph_adj_tf,
        differenceGraph_adj_ft, differenceGraph_adj_tt]
      rw [card_sub_reverse, card_sub_sub]

/-- The same cross-fibre formula with the endpoints presented in the opposite
order. -/
theorem commonNeighbors_card_cross_rev (D : DifferenceData W) (x y : W) :
    (commonNeighbors (differenceGraph D) (true, x) (false, y)).card =
      (convolution D.A D.C (x - y)).card +
        (correlation D.C D.B (x - y)).card := by
  have hcomm :
      commonNeighbors (differenceGraph D) (true, x) (false, y) =
        commonNeighbors (differenceGraph D) (false, y) (true, x) := by
    ext z
    simp [commonNeighbors, and_comm]
  rw [hcomm, commonNeighbors_card_cross]

/-- Exact degree of a vertex in fibre zero. -/
theorem degree_fibre0 (D : DifferenceData W) (x : W) :
    degree (differenceGraph D) (false, x) = D.A.card + D.C.card := by
  rw [degree, card_filter_bool_prod]
  simp only [differenceGraph_adj_ff, differenceGraph_adj_ft]
  rw [card_single_sub, card_single_sub]

/-- Exact degree of a vertex in fibre one. -/
theorem degree_fibre1 (D : DifferenceData W) (x : W) :
    degree (differenceGraph D) (true, x) = D.B.card + D.C.card := by
  rw [degree, card_filter_bool_prod]
  simp only [differenceGraph_adj_tf, differenceGraph_adj_tt]
  rw [card_single_reverse, card_single_sub]
  omega

/-- A correlation profile makes the two-fibre graph regular of the required
degree. -/
theorem CorrelationProfile.regular {D : DifferenceData W} {n : Nat}
    (P : CorrelationProfile D n) (u : Bool × W) :
    degree (differenceGraph D) u = 2 * n - 2 := by
  rcases u with ⟨i, x⟩
  cases i
  · rw [BookS3.degree_fibre0 D x, P.degree_fibre0]
  · rw [BookS3.degree_fibre1 D x, P.degree_fibre1]

/-- A correlation profile gives the required red-edge common-neighbor bound. -/
theorem CorrelationProfile.edge_commonNeighbors_le
    {D : DifferenceData W} {n : Nat} (P : CorrelationProfile D n)
    {u v : Bool × W} (huv : (differenceGraph D).Adj u v) :
    (commonNeighbors (differenceGraph D) u v).card ≤ n - 2 := by
  rcases u with ⟨i, x⟩
  rcases v with ⟨j, y⟩
  cases i <;> cases j
  · rw [commonNeighbors_card_fibre0]
    exact P.edge_fibre0 (y - x) (by simpa using huv)
  · rw [commonNeighbors_card_cross]
    exact P.edge_cross (y - x) (by simpa using huv)
  · rw [commonNeighbors_card_cross_rev]
    exact P.edge_cross (x - y) (by simpa using huv)
  · rw [commonNeighbors_card_fibre1]
    exact P.edge_fibre1 (y - x) (by simpa using huv)

/-- A correlation profile gives the required red-nonedge common-neighbor
bound. -/
theorem CorrelationProfile.nonedge_commonNeighbors_le
    {D : DifferenceData W} {n : Nat} (P : CorrelationProfile D n)
    {u v : Bool × W} (hne : u ≠ v) (huv : ¬(differenceGraph D).Adj u v) :
    (commonNeighbors (differenceGraph D) u v).card ≤ n - 1 := by
  rcases u with ⟨i, x⟩
  rcases v with ⟨j, y⟩
  cases i <;> cases j
  · rw [commonNeighbors_card_fibre0]
    apply P.nonedge_fibre0 (y - x)
    · intro hzero
      apply hne
      simp only [Prod.mk.injEq, true_and]
      exact (sub_eq_zero.mp hzero).symm
    · simpa using huv
  · rw [commonNeighbors_card_cross]
    exact P.nonedge_cross (y - x) (by simpa using huv)
  · rw [commonNeighbors_card_cross_rev]
    exact P.nonedge_cross (x - y) (by simpa using huv)
  · rw [commonNeighbors_card_fibre1]
    apply P.nonedge_fibre1 (y - x)
    · intro hzero
      apply hne
      simp only [Prod.mk.injEq, true_and]
      exact (sub_eq_zero.mp hzero).symm
    · simpa using huv

/-- The headline lift theorem: an entirely additive `CorrelationProfile`
produces the red `B_(n-1)`-free / blue `B_n`-free coloring. -/
theorem correlationProfile_bookFree {D : DifferenceData W} {n : Nat}
    (hn : 2 ≤ n) (P : CorrelationProfile D n) :
    BookFree (differenceGraph D) (n - 1) ∧
      BookFree (differenceGraph D)ᶜ n := by
  apply regularGraphCriterionOfCard hn (differenceGraph D)
  · simpa [Fintype.card_prod, Fintype.card_bool] using P.vertex_count
  · exact P.regular
  · intro u v huv
    exact P.edge_commonNeighbors_le huv
  · intro u v hne huv
    exact P.nonedge_commonNeighbors_le hne huv

end BookS3
