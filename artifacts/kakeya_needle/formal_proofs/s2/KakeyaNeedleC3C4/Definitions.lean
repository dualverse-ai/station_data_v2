import Mathlib

/-!
# The finite Kakeya needle problem

We use coordinates `(y, u)` (height first, horizontal coordinate second).
This is the coordinate swap of the paper's `(u, y)` convention and preserves
Lebesgue area.
-/

namespace KakeyaNeedleC3C4

open Set MeasureTheory

noncomputable section

/-- The left endpoint of the `j`th horizontal slice.  A `Fin n` index `j`
corresponds to the paper's one-based index `j + 1`. -/
def leftEndpoint (n : ℕ) (x : Fin n → ℝ) (j : Fin n) (y : ℝ) : ℝ :=
  x j + ((j.1 + 1 : ℕ) : ℝ) / (n : ℝ) * y

/-- The right endpoint of the `j`th horizontal slice. -/
def rightEndpoint (n : ℕ) (x : Fin n → ℝ) (j : Fin n) (y : ℝ) : ℝ :=
  x j + 1 / (n : ℝ) + (j.1 : ℝ) / (n : ℝ) * y

/-- The paper's triangle, after swapping the two coordinates.  Closed rather
than open slices make this literally the convex hull in the paper; the
boundary convention has no effect on Lebesgue area. -/
def triangle (n : ℕ) (x : Fin n → ℝ) (j : Fin n) : Set (ℝ × ℝ) :=
  {p | p.1 ∈ Icc (0 : ℝ) 1 ∧
    p.2 ∈ Icc (leftEndpoint n x j p.1) (rightEndpoint n x j p.1)}

/-- Union of all `n` sliding triangles. -/
def triangleUnion (n : ℕ) (x : Fin n → ℝ) : Set (ℝ × ℝ) :=
  ⋃ j : Fin n, triangle n x j

/-- Ordinary planar Lebesgue area of the triangle union. -/
def unionArea (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  volume.real (triangleUnion n x)

/-- The union of the horizontal slice intervals at height `y`. -/
def sliceUnion (n : ℕ) (x : Fin n → ℝ) (y : ℝ) : Set ℝ :=
  ⋃ j : Fin n, Icc (leftEndpoint n x j y) (rightEndpoint n x j y)

/-- One-dimensional Lebesgue length of the slice union. -/
def sliceLength (n : ℕ) (x : Fin n → ℝ) (y : ℝ) : ℝ :=
  volume.real (sliceUnion n x y)

/-- The exact slice-integral objective used in the paper's certificate. -/
def sliceArea (n : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∫ y in Icc (0 : ℝ) 1, sliceLength n x y

/-- The finite Kakeya triangle constant from the paper. -/
def C_T (n : ℕ) : ℝ :=
  sInf (Set.range (unionArea n))

end

end KakeyaNeedleC3C4
