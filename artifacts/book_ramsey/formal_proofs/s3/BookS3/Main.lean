import BookS3.YamadaPottProfile
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The Yamada--Pott lower-bound theorem

The paper's third family has `q = 4t+3` and `n = 4t^2+5t+2`.  This module
states both the transparent conditional lift and the unconditional concrete
finite-field certificate.  It neither states nor uses the universal upper
bound for book Ramsey numbers.
-/

namespace BookS3

open scoped Classical

/-- The field-order parameter `q = 4t+3`. -/
def yamadaPottQ (t : Nat) : Nat := 4 * t + 3

/-- The book parameter `n = (q^2-q+2)/4`, written without division. -/
def yamadaPottN (t : Nat) : Nat := 4 * t ^ 2 + 5 * t + 2

/-- The cyclic square-subgroup parameter `m = (q-1)/2`. -/
def yamadaPottM (t : Nat) : Nat := 2 * t + 1

theorem yamadaPottQ_eq_fieldOrder (t : Nat) :
    yamadaPottQ t = CodegreeArithmetic.fieldOrder (yamadaPottM t) := by
  simp [yamadaPottQ, yamadaPottM, CodegreeArithmetic.fieldOrder]
  ring

theorem yamadaPottN_eq_bookParameter (t : Nat) :
    yamadaPottN t = CodegreeArithmetic.bookParameter (yamadaPottM t) := by
  have hhalf : (2 * t + 1 + 1) / 2 = t + 1 := by omega
  simp [yamadaPottN, yamadaPottM, CodegreeArithmetic.bookParameter]
  rw [hhalf]
  ring

/-- The lifted graph has exactly `q^2-q = 4n-2` vertices. -/
theorem yamadaPott_order (t : Nat) :
    yamadaPottQ t * yamadaPottQ t - yamadaPottQ t =
      4 * yamadaPottN t - 2 := by
  have hm : Odd (yamadaPottM t) := by
    exact ⟨t, by simp [yamadaPottM, two_mul]⟩
  have h := CodegreeArithmetic.vertex_count hm
  rw [← yamadaPottQ_eq_fieldOrder, ← yamadaPottN_eq_bookParameter] at h
  rw [Nat.mul_sub_left_distrib, Nat.mul_one] at h
  exact h

/-- The red book has `n-1` pages.  This is the division-free form of
`(q^2-q-2)/4 = n-1`. -/
theorem yamadaPott_red_pages (t : Nat) :
    yamadaPottQ t * yamadaPottQ t - yamadaPottQ t - 2 =
      4 * (yamadaPottN t - 1) := by
  simp [yamadaPottQ, yamadaPottN]
  ring_nf
  omega

theorem yamadaPott_red_pages_div (t : Nat) :
    (yamadaPottQ t * yamadaPottQ t - yamadaPottQ t - 2) / 4 =
      yamadaPottN t - 1 := by
  rw [yamadaPott_red_pages]
  omega

/-- The blue book has `n` pages.  This is the division-free form of
`(q^2-q+2)/4 = n`. -/
theorem yamadaPott_blue_pages (t : Nat) :
    yamadaPottQ t * yamadaPottQ t - yamadaPottQ t + 2 =
      4 * yamadaPottN t := by
  simp [yamadaPottQ, yamadaPottN]
  ring_nf
  omega

theorem yamadaPott_blue_pages_div (t : Nat) :
    (yamadaPottQ t * yamadaPottQ t - yamadaPottQ t + 2) / 4 =
      yamadaPottN t := by
  rw [yamadaPott_blue_pages]
  omega

/-- **Yamada--Pott lower-bound certificate (conditional lift).**

Given exactly the additive correlation profile consumed by the two-fibre
difference lift, its graph has `q^2-q = 4n-2` vertices, contains no red book
with `n-1` pages, and its complement contains no blue book with `n` pages.
Here `q=4t+3` and `n=4t^2+5t+2`.
-/
theorem yamadaPott_lowerBound
    {W : Type*} [AddCommGroup W] [Fintype W]
    (t : Nat) (D : DifferenceData W)
    (P : CorrelationProfile D (yamadaPottN t)) :
    Fintype.card (Bool × W) =
        yamadaPottQ t * yamadaPottQ t - yamadaPottQ t ∧
      BookFree (differenceGraph D) (yamadaPottN t - 1) ∧
      BookFree (differenceGraph D)ᶜ (yamadaPottN t) := by
  have hn : 2 ≤ yamadaPottN t := by
    simp [yamadaPottN]
  have hbooks := correlationProfile_bookFree hn P
  refine ⟨?_, hbooks.1, hbooks.2⟩
  rw [Fintype.card_prod, Fintype.card_bool]
  calc
    2 * Fintype.card W = 4 * yamadaPottN t - 2 := P.vertex_count
    _ = yamadaPottQ t * yamadaPottQ t - yamadaPottQ t :=
      (yamadaPott_order t).symm

/-- **Third-family lower bound over a concrete finite field.**

For every finite field of order `q=4t+3≥7`, there is a red graph on
`q²-q` vertices with no book of `(q²-q-2)/4` pages, whose blue complement
has no book of `(q²-q+2)/4` pages. -/
theorem yamadaPott_finiteField_lowerBound
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {t : Nat} (ht : 1 ≤ t)
    (hcard : Fintype.card F = yamadaPottQ t) :
    ∃ red : SimpleGraph
        (Fin (yamadaPottQ t * yamadaPottQ t - yamadaPottQ t)),
      LowerBoundCertificate
        (yamadaPottQ t * yamadaPottQ t - yamadaPottQ t)
        ((yamadaPottQ t * yamadaPottQ t - yamadaPottQ t - 2) / 4)
        ((yamadaPottQ t * yamadaPottQ t - yamadaPottQ t + 2) / 4)
        red := by
  have hcard' : Fintype.card F = 4 * t + 3 := by
    simpa [yamadaPottQ] using hcard
  have hcert := YamadaPott.lowerBoundCertificate (F := F) ht hcard'
  have hN : YamadaPottN t = yamadaPottN t := by
    simpa [yamadaPottN] using YamadaPottN_eq t
  have hvertices : 4 * YamadaPottN t - 2 =
      yamadaPottQ t * yamadaPottQ t - yamadaPottQ t := by
    rw [hN]
    exact (yamadaPott_order t).symm
  have hred :
      (yamadaPottQ t * yamadaPottQ t - yamadaPottQ t - 2) / 4 =
        YamadaPottN t - 1 := by
    rw [yamadaPott_red_pages_div, hN]
  have hblue :
      (yamadaPottQ t * yamadaPottQ t - yamadaPottQ t + 2) / 4 =
        YamadaPottN t := by
    rw [yamadaPott_blue_pages_div, hN]
  rw [hred, hblue, ← hvertices]
  exact hcert

/-- Prime-power form of the third-family lower bound.  `GaloisField p e`
supplies the field of order `q=p^e`; the displayed arithmetic assumptions say
exactly that `q≥3` is in the paper's congruence class, with `t≥1` giving
`q≥7`. -/
theorem yamadaPott_primePower_lowerBound
    (p e t : Nat) [Fact p.Prime] (he : e ≠ 0) (ht : 1 ≤ t)
    (hq : p ^ e = yamadaPottQ t) :
    ∃ red : SimpleGraph
        (Fin (yamadaPottQ t * yamadaPottQ t - yamadaPottQ t)),
      LowerBoundCertificate
        (yamadaPottQ t * yamadaPottQ t - yamadaPottQ t)
        ((yamadaPottQ t * yamadaPottQ t - yamadaPottQ t - 2) / 4)
        ((yamadaPottQ t * yamadaPottQ t - yamadaPottQ t + 2) / 4)
        red := by
  letI : Fintype (GaloisField p e) := Fintype.ofFinite _
  letI : DecidableEq (GaloisField p e) := Classical.decEq _
  apply yamadaPott_finiteField_lowerBound (F := GaloisField p e) ht
  rw [Fintype.card_eq_nat_card, GaloisField.card p e he, hq]

end BookS3
