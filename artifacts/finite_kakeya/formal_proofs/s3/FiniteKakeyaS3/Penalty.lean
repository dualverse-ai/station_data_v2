import FiniteKakeyaS3.Definitions

/-!
# Cardinality bookkeeping for the full boundary

This module isolates the elementary passage from the non-pole union to the
full `p+1`-line boundary.  It contains no character-sum argument.
-/

namespace FiniteKakeyaS3

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The two lines added after the non-pole family. -/
def addedLines (r u v : F) : Finset (F × F) := poleLine r u ∪ verticalLine v

/-- Points contributed for the first time by the two added lines and lying
outside the square footprint. -/
def extraPoints (lambda A B r u v : F) : Finset (F × F) :=
  addedLines r u v \ (scaledSquareFootprint lambda ∪ finiteLineUnion A B r)

theorem card_affineLine (m b : F) : (affineLine m b).card = Fintype.card F := by
  rw [affineLine, card_image_of_injective, card_univ]
  intro x y h
  exact congrArg Prod.fst h

theorem card_verticalLine (v : F) : (verticalLine v).card = Fintype.card F := by
  rw [verticalLine, card_image_of_injective, card_univ]
  intro x y h
  exact congrArg Prod.snd h

theorem card_addedLines_le (r u v : F) :
    (addedLines r u v).card ≤ 2 * Fintype.card F := by
  calc
    (addedLines r u v).card = (poleLine r u ∪ verticalLine v).card := rfl
    _ ≤ (poleLine r u).card + (verticalLine v).card := card_union_le _ _
    _ = 2 * Fintype.card F := by
      rw [poleLine, card_affineLine, card_verticalLine]
      omega

theorem card_extraPoints_le (lambda A B r u v : F) :
    (extraPoints lambda A B r u v).card ≤ 2 * Fintype.card F := by
  exact (card_le_card sdiff_subset).trans (card_addedLines_le r u v)

/-- The penalty is the old contribution outside the footprint plus exactly
the genuinely new points on the pole and vertical lines. -/
theorem boundaryPenalty_decomposition (lambda A B r u v : F) :
    boundaryPenalty lambda A B r u v =
      (finiteLineUnion A B r \ scaledSquareFootprint lambda).card +
        (extraPoints lambda A B r u v).card := by
  have hunion :
      fullBoundary A B r u v \ scaledSquareFootprint lambda =
        (finiteLineUnion A B r \ scaledSquareFootprint lambda) ∪
          extraPoints lambda A B r u v := by
    ext q
    simp only [fullBoundary, addedLines, extraPoints, mem_sdiff,
      mem_union]
    tauto
  have hdisj : Disjoint
      (finiteLineUnion A B r \ scaledSquareFootprint lambda)
      (extraPoints lambda A B r u v) := by
    rw [Finset.disjoint_left]
    intro q hqold hqfresh
    simp only [mem_sdiff] at hqold
    simp only [extraPoints, mem_sdiff, mem_union] at hqfresh
    exact hqfresh.2 (Or.inr hqold.1)
  rw [boundaryPenalty, hunion, card_union_of_disjoint hdisj]

/-- Addition-only cardinal identity, chosen to avoid casts of natural
subtraction later in the proof. -/
theorem penalty_add_overlap (lambda A B r u v : F) :
    boundaryPenalty lambda A B r u v +
        (finiteLineUnion A B r ∩ scaledSquareFootprint lambda).card =
      (finiteLineUnion A B r).card + (extraPoints lambda A B r u v).card := by
  rw [boundaryPenalty_decomposition]
  have h := card_sdiff_add_card_inter (finiteLineUnion A B r)
    (scaledSquareFootprint lambda)
  omega

end FiniteKakeyaS3
