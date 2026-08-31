import Mathlib

/-!
# The one-pole family from finite Kakeya, Spotlight 3

This file records the exact finite-field objects used in Theorem 4.1 of the
verification notebook.  Coordinates are ordered as `(y,z)`.
-/

namespace FiniteKakeyaS3

open Finset

variable {F : Type*} [Fintype F] [Field F] [DecidableEq F]

/-- The square set `Q = {x^2 : x ∈ F}`. -/
def squareSet : Finset F := univ.image fun x : F ↦ x ^ 2

/-- The scaled square set `λ Q`. -/
def scaledSquareSet (lambda : F) : Finset F :=
  univ.image fun x : F ↦ lambda * x ^ 2

/-- The footprint `E₀ = (λ Q)²`, in `(y,z)` coordinates. -/
def scaledSquareFootprint (lambda : F) : Finset (F × F) :=
  scaledSquareSet lambda ×ˢ scaledSquareSet lambda

/-- `D = A r + B`, the nondegeneracy parameter of the family. -/
def familyD (A B r : F) : F := A * r + B

/-- The prescribed intercept `β_c = (Ac+B)/(c-r)`. -/
def beta (A B r c : F) : F := (A * c + B) / (c - r)

/-- An affine line, represented by its finite point set. -/
def affineLine (slope intercept : F) : Finset (F × F) :=
  univ.image fun y : F ↦ (y, slope * y + intercept)

/-- The non-pole line `L_c`, with the paper's intercept `β_c`. -/
def finiteLine (A B r c : F) : Finset (F × F) :=
  affineLine c (beta A B r c)

/-- The union `U_f = ⋃_{c ≠ r} L_c` of all non-pole lines. -/
def finiteLineUnion (A B r : F) : Finset (F × F) :=
  univ.filter fun q ↦ ∃ c : F, c ≠ r ∧ q.2 = c * q.1 + beta A B r c

/-- The separately chosen line in the missing (pole) direction. -/
def poleLine (r u : F) : Finset (F × F) := affineLine r u

/-- The vertical line `L_∞(v) = {(v,z)}`. -/
def verticalLine (v : F) : Finset (F × F) :=
  univ.image fun z : F ↦ (v, z)

/-- The full boundary `U` of all `p+1` chosen directions. -/
def fullBoundary (A B r u v : F) : Finset (F × F) :=
  finiteLineUnion A B r ∪ poleLine r u ∪ verticalLine v

/-- The boundary penalty `|U \ E₀|`. -/
def boundaryPenalty (lambda A B r u v : F) : ℕ :=
  (fullBoundary A B r u v \ scaledSquareFootprint lambda).card

/-- The selector discriminant obtained by eliminating the line parameter. -/
def selectorDiscriminant (A B r y z : F) : F :=
  (z - A - r * y) ^ 2 - 4 * familyD A B r * y

/-- The square-discriminant selector used away from the row `y=0`. -/
def selector (A B r : F) : Finset (F × F) :=
  univ.filter fun q ↦ IsSquare (selectorDiscriminant A B r q.1 q.2)

@[simp] theorem mem_scaledSquareSet {lambda x : F} :
    x ∈ scaledSquareSet lambda ↔ ∃ t : F, lambda * t ^ 2 = x := by
  simp [scaledSquareSet]

@[simp] theorem mem_scaledSquareFootprint {lambda : F} {q : F × F} :
    q ∈ scaledSquareFootprint lambda ↔
      (∃ s : F, lambda * s ^ 2 = q.1) ∧ (∃ t : F, lambda * t ^ 2 = q.2) := by
  simp [scaledSquareFootprint]

@[simp] theorem mem_affineLine {m b : F} {q : F × F} :
    q ∈ affineLine m b ↔ q.2 = m * q.1 + b := by
  constructor
  · simp only [affineLine, mem_image, mem_univ, true_and]
    rintro ⟨y, rfl⟩
    rfl
  · intro h
    simp only [affineLine, mem_image, mem_univ, true_and]
    exact ⟨q.1, Prod.ext rfl h.symm⟩

@[simp] theorem mem_finiteLineUnion {A B r : F} {q : F × F} :
    q ∈ finiteLineUnion A B r ↔
      ∃ c : F, c ≠ r ∧ q.2 = c * q.1 + beta A B r c := by
  simp [finiteLineUnion]

@[simp] theorem mem_poleLine {r u : F} {q : F × F} :
    q ∈ poleLine r u ↔ q.2 = r * q.1 + u := by
  simp [poleLine]

@[simp] theorem mem_verticalLine {v : F} {q : F × F} :
    q ∈ verticalLine v ↔ q.1 = v := by
  constructor
  · simp only [verticalLine, mem_image, mem_univ, true_and]
    rintro ⟨z, rfl⟩
    rfl
  · intro h
    simp only [verticalLine, mem_image, mem_univ, true_and]
    exact ⟨q.2, Prod.ext h.symm rfl⟩

@[simp] theorem mem_selector {A B r : F} {q : F × F} :
    q ∈ selector A B r ↔ IsSquare (selectorDiscriminant A B r q.1 q.2) := by
  simp [selector]

end FiniteKakeyaS3
