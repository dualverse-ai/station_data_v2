import BookS2.LegendreSource
import BookS2.TwoEndpointLift
import BookS2.Seidel

/-!
# The doubled-Legendre book-Ramsey lower bound

This file composes the finite-field periodic Legendre source, the new
two-endpoint lift, and the generic Seidel counting lemma.  The final theorem is
the lower-bound half of Theorem 3.2 in the accompanying paper.
-/

namespace BookS2

open scoped BigOperators
attribute [local instance] Classical.decEq

/-- Reindex a Seidel certificate along an equivalence of finite vertex types. -/
noncomputable def SeidelCertificate.reindex {V W : Type*}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {n : ℕ} (C : SeidelCertificate V n) (e : V ≃ W) : SeidelCertificate W n where
  matrix u v := C.matrix (e.symm u) (e.symm v)
  card_eq := by
    rw [← Fintype.card_congr e]
    exact C.card_eq
  symmetric u v := C.symmetric _ _
  diagonal v := C.diagonal _
  offDiagonal u v huv := C.offDiagonal _ _ (fun h => huv (e.symm.injective h))
  rowSum u := by
    simpa using (e.symm.sum_comp (fun v => C.matrix (e.symm u) v)).trans (C.rowSum _)
  squareNonpositive u v huv := by
    have hne : e.symm u ≠ e.symm v := fun h => huv (e.symm.injective h)
    rw [e.symm.sum_comp (fun x =>
      C.matrix (e.symm u) x * C.matrix x (e.symm v))]
    exact C.squareNonpositive (e.symm u) (e.symm v) hne

/-- The doubled-Legendre Seidel certificate over an arbitrary finite field of
order `Q > 3`, `Q ≡ 3 (mod 8)`.

Its vertex type is the intrinsic `4 * |K| + 2` type used by the construction,
where `K` is the subgroup of nonzero squares.
-/
noncomputable def doubledLegendreCertificateField
    (F : Type*) [Field F] [Fintype F]
    (hmod : Fintype.card F % 8 = 3) (hlarge : 3 < Fintype.card F) :
    SeidelCertificate (LiftVertex (SquareUnits F)) ((Fintype.card F + 1) / 2) := by
  classical
  let src := finiteFieldSource (F := F) hmod hlarge
  let L := twoEndpointLiftCertificate src
  refine
    { matrix := L.matrix
      card_eq := ?_
      symmetric := fun u v => L.symmetric.apply v u
      diagonal := L.diagonal_zero
      offDiagonal := fun u v h => L.offDiagonal_sign h
      rowSum := L.row_sum_neg_one
      squareNonpositive := ?_ }
  · rw [card_liftVertex, card_squareUnits_of_mod_eight (F := F) hmod]
    omega
  · intro u v huv
    simpa [Matrix.mul_apply] using L.square_offDiagonal_nonpos huv

/-- **Doubled-Legendre lower bound (second infinite family).**

For every prime power `Q > 3` with `Q ≡ 3 (mod 8)`, there is a red/blue
coloring of the edges of `K_(2Q)` with no red book `B_((Q-1)/2)` and no blue
book `B_((Q+1)/2)`.

`BookFree` is defined using a literal spine edge and a finset of distinct
common neighbours, so this conclusion is exactly the lower-bound statement
`R(B_((Q-1)/2), B_((Q+1)/2)) ≥ 2Q+1` (without importing the unrelated
Rousseau--Sheehan upper bound).
-/
theorem doubledLegendre_lowerBound
    (Q : ℕ) (hprimePower : IsPrimePow Q) (hlarge : 3 < Q) (hmod : Q % 8 = 3) :
    ∃ S : Matrix (Fin (2 * Q)) (Fin (2 * Q)) ℤ,
      (∀ u v, S u v = S v u) ∧
      (∀ u, S u u = 0) ∧
      (∀ u v, u ≠ v → redAdj S u v ∨ blueAdj S u v) ∧
      BookFree (redAdj S) ((Q - 1) / 2) ∧
      BookFree (blueAdj S) ((Q + 1) / 2) := by
  rcases hprimePower with ⟨p, k, hp, hk, hpk⟩
  letI : Fact p.Prime := ⟨hp.nat_prime⟩
  let F := GaloisField p k
  letI : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = Q := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p k (Nat.ne_of_gt hk)]
    exact hpk
  have hmodF : Fintype.card F % 8 = 3 := by omega
  have hlargeF : 3 < Fintype.card F := by omega
  let C₀ := doubledLegendreCertificateField F hmodF hlargeF
  have hn : (Fintype.card F + 1) / 2 = (Q + 1) / 2 := by omega
  let C₁ : SeidelCertificate (LiftVertex (SquareUnits F)) ((Q + 1) / 2) := hn ▸ C₀
  have hvertices : Fintype.card (LiftVertex (SquareUnits F)) = 2 * Q := by
    calc
      _ = 4 * ((Q + 1) / 2) - 2 := C₁.card_eq
      _ = 2 * Q := by omega
  let e : LiftVertex (SquareUnits F) ≃ Fin (2 * Q) :=
    Fintype.equivOfCardEq (by simpa using hvertices)
  let C := C₁.reindex e
  refine ⟨C.matrix, C.symmetric, C.diagonal, ?_, ?_⟩
  · intro u v huv
    exact redAdj_or_blueAdj C.matrix C.offDiagonal huv
  · have hbooks := C.bookFree
    have harith : (Q + 1) / 2 - 1 = (Q - 1) / 2 := by omega
    simpa [harith] using hbooks

end BookS2
