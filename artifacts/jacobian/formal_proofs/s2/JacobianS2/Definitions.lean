import Mathlib

/-!
# Jacobian Spotlight 2: definitions

The normalized family `Fₐ` is the one in Section 3.2 of the verification notebook.
The map displayed in the paper is `F₆`.
-/

namespace JacobianS2

structure Point (K : Type*) where
  x : K
  y : K
  z : K
  deriving DecidableEq

namespace Point

@[ext]
theorem ext {K : Type*} {p q : Point K}
    (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) : p = q := by
  cases p
  cases q
  simp_all

end Point

section Field

variable {K : Type*} [Field K]

/-- First coordinate of the normalized Jacobian-counterexample family. -/
def P (a x y z : K) : K :=
  a * x + (3 * a / 2) * x ^ 2 * y + x ^ 3 * z

/-- Second coordinate of the normalized Jacobian-counterexample family. -/
def Q (a x y z : K) : K :=
  a / 6 * y - 2 * a * x * y ^ 2 + (3 * a / 2) * x ^ 2 * y ^ 3
    + x * z - 2 * x ^ 2 * y * z + x ^ 3 * y ^ 2 * z

/-- Third coordinate of the normalized Jacobian-counterexample family. -/
def R (a x y z : K) : K :=
  2 * a * y ^ 2 - (7 * a / 2) * x * y ^ 3 + (3 * a / 2) * x ^ 2 * y ^ 4
    - z + 3 * x * y * z - 3 * x ^ 2 * y ^ 2 * z + x ^ 3 * y ^ 3 * z

/-- The normalized family.  `map 6` is the paper's ruled map. -/
def map (a : K) (p : Point K) : Point K :=
  ⟨P a p.x p.y p.z, Q a p.x p.y p.z, R a p.x p.y p.z⟩

def u (p : Point K) : K := p.x * p.y
def w (p : Point K) : K := p.x ^ 2 * p.z
def A (a : K) (p : Point K) : K := a + (3 * a / 2) * u p + w p
def t (a : K) (p : Point K) : K := A a p * (u p - 1)
def X (a : K) (p : Point K) : K := p.x * A a p
def I (a : K) (p : Point K) : K :=
  t a p ^ 2 + (2 * a / 3) * t a p - a * A a p / 3
def J (a : K) (p : Point K) : K :=
  t a p ^ 3 + a / 2 * t a p ^ 2 - a / 2 * A a p * t a p

/-- The inverse cubic attached to a target `(X,Y,Z)`. -/
def cubic (a : K) (q : Point K) (s : K) : K :=
  s ^ 3 + a * s ^ 2 - 3 * (q.x * q.y) * s + 2 * (q.x ^ 2 * q.z)

/-- Its formal derivative, written as an ordinary polynomial expression. -/
def cubicDeriv (a : K) (q : Point K) (s : K) : K :=
  3 * s ^ 2 + 2 * a * s - 3 * (q.x * q.y)

/-- Explicit inverse formula on the chart where `a`, `q.x`, and `cubicDeriv` are nonzero. -/
noncomputable def recover (a : K) (q : Point K) (s : K) : Point K :=
  let AA := cubicDeriv a q s / a
  let xx := q.x / AA
  let uu := 1 + s / AA
  let yy := uu / xx
  let ww := AA - a - (3 * a / 2) * uu
  let zz := ww / xx ^ 2
  ⟨xx, yy, zz⟩

end Field

end JacobianS2
