import JacobianS2.Definitions

/-!
# Constant Jacobian

This file records the actual formal partial derivatives of the displayed coordinate
polynomials and proves that their 3-by-3 determinant is constant.
-/

namespace JacobianS2

section Field

variable {K : Type*} [Field K] [CharZero K]

def Px (a x y z : K) : K := a + 3 * a * x * y + 3 * x ^ 2 * z
def Py (a x y z : K) : K := (3 * a / 2) * x ^ 2
def Pz (_a x _y _z : K) : K := x ^ 3

def Qx (a x y z : K) : K :=
  -2 * a * y ^ 2 + 3 * a * x * y ^ 3 + z - 4 * x * y * z + 3 * x ^ 2 * y ^ 2 * z
def Qy (a x y z : K) : K :=
  a / 6 - 4 * a * x * y + (9 * a / 2) * x ^ 2 * y ^ 2
    - 2 * x ^ 2 * z + 2 * x ^ 3 * y * z
def Qz (_a x y _z : K) : K := x - 2 * x ^ 2 * y + x ^ 3 * y ^ 2

def Rx (a x y z : K) : K :=
  -(7 * a / 2) * y ^ 3 + 3 * a * x * y ^ 4
    + 3 * y * z - 6 * x * y ^ 2 * z + 3 * x ^ 2 * y ^ 3 * z
def Ry (a x y z : K) : K :=
  4 * a * y - (21 * a / 2) * x * y ^ 2 + 6 * a * x ^ 2 * y ^ 3
    + 3 * x * z - 6 * x ^ 2 * y * z + 3 * x ^ 3 * y ^ 2 * z
def Rz (_a x y _z : K) : K :=
  -1 + 3 * x * y - 3 * x ^ 2 * y ^ 2 + x ^ 3 * y ^ 3

/-- Determinant of the matrix of formal partial derivatives of `(P,Q,R)`. -/
def jacobianDet (a x y z : K) : K :=
  Px a x y z * (Qy a x y z * Rz a x y z - Qz a x y z * Ry a x y z)
    - Py a x y z * (Qx a x y z * Rz a x y z - Qz a x y z * Rx a x y z)
    + Pz a x y z * (Qx a x y z * Ry a x y z - Qy a x y z * Rx a x y z)

/-- The whole normalized family has constant Jacobian `-a²/6`. -/
theorem jacobianDet_eq (a x y z : K) : jacobianDet a x y z = -(a ^ 2) / 6 := by
  simp only [jacobianDet, Px, Py, Pz, Qx, Qy, Qz, Rx, Ry, Rz]
  ring

/-- Specialization to the paper's map `F₆`: its Jacobian determinant is `-6`. -/
theorem paper_jacobianDet_eq (x y z : K) :
    jacobianDet (6 : K) x y z = -6 := by
  rw [jacobianDet_eq]
  norm_num

/-- Therefore the paper's map has no affine critical point. -/
theorem paper_no_critical_point (p : Point K) :
    jacobianDet (6 : K) p.x p.y p.z ≠ 0 := by
  rw [paper_jacobianDet_eq]
  norm_num

end Field

end JacobianS2
