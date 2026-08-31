import Mathlib

/-!
# The one-pole Kakeya construction

Definitions matching Theorem 2.1 of the paper's finite-field Kakeya section.
-/

namespace FiniteKakeyaInf

/-- A point or direction vector in three-dimensional affine space. -/
abbrev Point (F : Type*) := F × F × F

/-- The affine line with base point `w` and direction vector `v`. -/
def affineLine {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (w v : Point F) : Finset (Point F) :=
  Finset.univ.image fun t : F => w + t • v

/-- A finite set contains a full affine line in every nonzero vector direction. -/
def IsKakeya {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (K : Finset (Point F)) : Prop :=
  ∀ v : Point F, v ≠ 0 → ∃ w : Point F, affineLine w v ⊆ K

/-- The square elements of a finite field, including zero. -/
def squares (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset F :=
  Finset.univ.image fun u : F => u ^ 2

/-- The quadratic-residue body `B_p`. -/
def body (F : Type*) [Field F] [Fintype F] [DecidableEq F] : Finset (Point F) :=
  Finset.univ.filter fun q =>
    q.1 ^ 2 + 4 * q.2.1 ∈ squares F ∧ q.1 ^ 2 + 4 * q.2.2 ∈ squares F

/-- The union of the finite one-pole lines, before the diagonal and vertical lines. -/
def finiteBoundary (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Finset (Point F) :=
  Finset.univ.filter fun q => q.1 = 0 ∧
    ∃ c : F, c ≠ 1 ∧ q.2.2 = c * q.2.1 + c / (c - 1)

/-- The line in the missing slope `(0,1,1)`. -/
def diagonalBoundary (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Finset (Point F) :=
  Finset.univ.filter fun q => q.1 = 0 ∧ q.2.2 = q.2.1

/-- The line in the vertical direction `(0,0,1)`. -/
def verticalBoundary (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Finset (Point F) :=
  Finset.univ.filter fun q => q.1 = 0 ∧ q.2.1 = 0

/-- The complete boundary `U_p` in the plane `x = 0`. -/
def boundary (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Finset (Point F) :=
  finiteBoundary F ∪ diagonalBoundary F ∪ verticalBoundary F

/-- The paper's Kakeya set `K_p = B_p ∪ U_p`. -/
def onePoleKakeya (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Finset (Point F) :=
  body F ∪ boundary F

end FiniteKakeyaInf
