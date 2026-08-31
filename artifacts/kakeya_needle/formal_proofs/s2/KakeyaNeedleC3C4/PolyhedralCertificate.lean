import Mathlib

/-!
# Recursive certificates for quadratic minimization on rational polyhedra

This file supplies a reusable, exact certificate layer.  The coefficients of
both the quadratic objective and the affine constraints are rational; only
their evaluation takes place in `ℝ`.

A certificate is a finite face tree.  At a node it proves the desired lower
bound at every stationary point in the relative interior of that face.  For
each constraint which is not already active it contains a certificate for the
face on which that constraint is an equality.  The soundness proof minimizes
the objective on the current compact face.  A minimizer is either relatively
interior (and hence stationary along every locally feasible line), or it lies
on one of the recursively certified boundary faces.

Importantly, `StationaryOnFace` does not assume that the stationary point is
unique.  Thus a singular Hessian, and even a positive-dimensional stationary
affine set, is handled soundly: the node obligation ranges over *all*
stationary points.
-/

namespace KakeyaNeedleC3C4

open Set Filter
open scoped Topology

/-- An affine function with rational coefficients. -/
structure RationalAffine (n : ℕ) where
  constant : ℚ
  linear : Fin n → ℚ
  deriving DecidableEq

namespace RationalAffine

/-- Exact real evaluation of a rational affine function. -/
def eval {n : ℕ} (a : RationalAffine n) (x : Fin n → ℝ) : ℝ :=
  (a.constant : ℝ) + ∑ i, (a.linear i : ℝ) * x i

theorem continuous {n : ℕ} (a : RationalAffine n) : Continuous a.eval := by
  unfold eval
  fun_prop

end RationalAffine

/-- A (not necessarily symmetric) quadratic expression with rational
coefficients.  Not requiring symmetry is convenient for importing generated
certificates; only the represented scalar function matters. -/
structure RationalQuadratic (n : ℕ) where
  constant : ℚ
  linear : Fin n → ℚ
  quadratic : Fin n → Fin n → ℚ
  deriving DecidableEq

namespace RationalQuadratic

/-- Exact real evaluation of a rational quadratic expression. -/
def eval {n : ℕ} (q : RationalQuadratic n) (x : Fin n → ℝ) : ℝ :=
  (q.constant : ℝ) + ∑ i, (q.linear i : ℝ) * x i
    + ∑ i, ∑ j, (q.quadratic i j : ℝ) * x i * x j

theorem continuous {n : ℕ} (q : RationalQuadratic n) : Continuous q.eval := by
  unfold eval
  fun_prop

/-- The exact directional derivative, still assembled from rational
coefficients. -/
def directionalDerivative {n : ℕ} (q : RationalQuadratic n)
    (x d : Fin n → ℝ) : ℝ :=
  ∑ i, (q.linear i : ℝ) * d i
    + ∑ i, ∑ j, (q.quadratic i j : ℝ) * (d i * x j + x i * d j)

/-- Evaluation along a line has the expected exact derivative.  Certificate
generators may therefore replace analytic `deriv` goals by the finite formula
`directionalDerivative`. -/
theorem hasDerivAt_line {n : ℕ} (q : RationalQuadratic n)
    (x d : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ q.eval (x + s • d))
      (q.directionalDerivative (x + t • d) d) t := by
  have hcoord (i : Fin n) :
      HasDerivAt (fun s : ℝ ↦ (x + s • d) i) (d i) t := by
    simpa using ((hasDerivAt_id t).mul_const (d i)).const_add (x i)
  have hlinear : HasDerivAt
      (fun s : ℝ ↦ ∑ i, (q.linear i : ℝ) * (x + s • d) i)
      (∑ i, (q.linear i : ℝ) * d i) t := by
    have h := HasDerivAt.sum (u := Finset.univ) fun i _ ↦
      (hcoord i).const_mul (q.linear i : ℝ)
    convert h using 1
    funext s
    simp only [Finset.sum_apply]
  have hquadratic : HasDerivAt
      (fun s : ℝ ↦ ∑ i, ∑ j,
        (q.quadratic i j : ℝ) * (x + s • d) i * (x + s • d) j)
      (∑ i, ∑ j, (q.quadratic i j : ℝ) *
        (d i * (x + t • d) j + (x + t • d) i * d j)) t := by
    have h := HasDerivAt.sum (u := Finset.univ) fun i _ ↦
      HasDerivAt.sum (u := Finset.univ) fun j _ ↦ by
        simpa only [mul_assoc] using ((hcoord i).mul (hcoord j)).const_mul
          (q.quadratic i j : ℝ)
    convert h using 1
    funext s
    simp only [Finset.sum_apply, Pi.mul_apply, mul_assoc]
  simpa [eval, directionalDerivative] using
    ((hasDerivAt_const t (q.constant : ℝ)).add hlinear).add hquadratic

end RationalQuadratic

/-- A polyhedron presented by finitely many rational affine inequalities
`0 ≤ constraint i x`. -/
structure RationalPolyhedron (n m : ℕ) where
  constraint : Fin m → RationalAffine n

namespace RationalPolyhedron

variable {n m : ℕ}

/-- The set cut out by all inequalities of a rational polyhedron. -/
def carrier (P : RationalPolyhedron n m) : Set (Fin n → ℝ) :=
  {x | ∀ i, 0 ≤ (P.constraint i).eval x}

/-- The face obtained by declaring every constraint in `active` to be an
equality.  Redundant active constraints are allowed. -/
def face (P : RationalPolyhedron n m) (active : Finset (Fin m)) :
    Set (Fin n → ℝ) :=
  {x | x ∈ P.carrier ∧ ∀ i ∈ active, (P.constraint i).eval x = 0}

/-- Relative-interior condition with respect to the presented inequalities.
This is intentionally presentation-relative: inactive redundant constraints
simply cause an immediate descent to another (equal) face. -/
def InPresentedRelativeInterior (P : RationalPolyhedron n m)
    (active : Finset (Fin m)) (x : Fin n → ℝ) : Prop :=
  ∀ i, i ∉ active → 0 < (P.constraint i).eval x

theorem isClosed_carrier (P : RationalPolyhedron n m) : IsClosed P.carrier := by
  simp only [carrier, setOf_forall]
  exact isClosed_iInter fun i ↦ isClosed_Ici.preimage (P.constraint i).continuous

theorem isClosed_face (P : RationalPolyhedron n m) (active : Finset (Fin m)) :
    IsClosed (P.face active) := by
  have hzero : IsClosed (⋂ i ∈ (active : Set (Fin m)),
      {x | (P.constraint i).eval x = 0}) :=
    isClosed_biInter fun i _ ↦
      isClosed_singleton.preimage (P.constraint i).continuous
  have hinter := P.isClosed_carrier.inter hzero
  rw [show P.face active = P.carrier ∩ ⋂ i ∈ (active : Set (Fin m)),
      {x | (P.constraint i).eval x = 0} by
    ext x
    simp [face]]
  exact hinter

theorem face_mono (P : RationalPolyhedron n m) {a b : Finset (Fin m)}
    (hab : a ⊆ b) : P.face b ⊆ P.face a := by
  rintro x ⟨hxP, hxb⟩
  exact ⟨hxP, fun i hi ↦ hxb i (hab hi)⟩

theorem face_insert_subset (P : RationalPolyhedron n m)
    (active : Finset (Fin m)) (i : Fin m) :
    P.face (insert i active) ⊆ P.face active :=
  P.face_mono (Finset.subset_insert i active)

end RationalPolyhedron

section Certificate

variable {n m : ℕ}

/-- A direction is locally feasible in a face when its entire affine line is
in that face for all sufficiently small parameters. -/
def LocallyFeasibleDirection (P : RationalPolyhedron n m)
    (active : Finset (Fin m)) (x d : Fin n → ℝ) : Prop :=
  ∀ᶠ t : ℝ in 𝓝 0, x + t • d ∈ P.face active

/-- Stationarity along the affine hull of the current face, expressed without
any rank or nonsingularity assumption.  This formulation is especially useful
for singular quadratic programs: every locally feasible direction must have
zero directional derivative. -/
def StationaryOnFace (P : RationalPolyhedron n m)
    (q : RationalQuadratic n) (active : Finset (Fin m))
    (x : Fin n → ℝ) : Prop :=
  ∀ d, LocallyFeasibleDirection P active x d →
    deriv (fun t : ℝ ↦ q.eval (x + t • d)) 0 = 0

/-- The stationarity condition is exactly the vanishing of the finite
directional-derivative formula. -/
theorem stationaryOnFace_iff_directionalDerivative
    (P : RationalPolyhedron n m) (q : RationalQuadratic n)
    (active : Finset (Fin m)) (x : Fin n → ℝ) :
    StationaryOnFace P q active x ↔
      ∀ d, LocallyFeasibleDirection P active x d →
        q.directionalDerivative x d = 0 := by
  constructor <;> intro h d hd
  · have hder : deriv (fun t : ℝ ↦ q.eval (x + t • d)) 0 =
        q.directionalDerivative x d := by
      simpa using (q.hasDerivAt_line x d 0).deriv
    exact hder.symm.trans (h d hd)
  · have hder : deriv (fun t : ℝ ↦ q.eval (x + t • d)) 0 =
        q.directionalDerivative x d := by
      simpa using (q.hasDerivAt_line x d 0).deriv
    exact hder.trans (h d hd)

/-- A recursive face certificate.  The node condition checks every stationary
point, rather than solving a linear system and selecting one point; this is
the sound treatment of singular stationary affine sets. -/
inductive FaceCertificate (P : RationalPolyhedron n m)
    (q : RationalQuadratic n) (target : ℚ) : Finset (Fin m) → Type
  | node (active : Finset (Fin m))
      (stationaryLower : ∀ x ∈ P.face active,
        P.InPresentedRelativeInterior active x →
        StationaryOnFace P q active x → (target : ℝ) ≤ q.eval x)
      (boundary : ∀ i, i ∉ active →
        FaceCertificate P q target (insert i active)) :
      FaceCertificate P q target active

namespace FaceCertificate

variable {P : RationalPolyhedron n m} {q : RationalQuadratic n}
  {target : ℚ} {active : Finset (Fin m)}

/-- A global minimum on a face is stationary in the rank-free sense used by
the certificate. -/
theorem stationary_of_isMinOn {x : Fin n → ℝ}
    (hmin : IsMinOn q.eval (P.face active) x) :
    StationaryOnFace P q active x := by
  intro d hd
  have hlocal : IsLocalMin (fun t : ℝ ↦ q.eval (x + t • d)) 0 := by
    have heq : x + (0 : ℝ) • d = x := by simp
    filter_upwards [hd] with t ht
    simpa [heq] using hmin ht
  exact hlocal.deriv_eq_zero

/-- Soundness on an arbitrary face.  Compactness is only required for the
original polyhedron; every presented face is a closed subset of it. -/
theorem sound (cert : FaceCertificate P q target active)
    (hcompact : IsCompact P.carrier) :
    ∀ x ∈ P.face active, (target : ℝ) ≤ q.eval x := by
  induction cert with
  | node active stationaryLower boundary ih =>
      intro x hx
      have hfaceCompact : IsCompact (P.face active) :=
        hcompact.of_isClosed_subset (P.isClosed_face active) fun y hy ↦ hy.1
      obtain ⟨xmin, hxmin, hmin⟩ :=
        hfaceCompact.exists_isMinOn ⟨x, hx⟩ q.continuous.continuousOn
      have hmin_le : q.eval xmin ≤ q.eval x := hmin hx
      suffices (target : ℝ) ≤ q.eval xmin by exact this.trans hmin_le
      by_cases hinterior : P.InPresentedRelativeInterior active xmin
      · exact stationaryLower xmin hxmin hinterior (stationary_of_isMinOn hmin)
      · rw [RationalPolyhedron.InPresentedRelativeInterior] at hinterior
        push_neg at hinterior
        obtain ⟨i, hi_not, hi_nonpos⟩ := hinterior
        have hzero : (P.constraint i).eval xmin = 0 := by
          have hnonneg := hxmin.1 i
          exact le_antisymm hi_nonpos hnonneg
        have hxmin' : xmin ∈ P.face (insert i active) := by
          refine ⟨hxmin.1, ?_⟩
          intro j hj
          simp only [Finset.mem_insert] at hj
          rcases hj with rfl | hj
          · exact hzero
          · exact hxmin.2 j hj
        exact ih i hi_not xmin hxmin'

/-- The root certificate proves the requested lower bound on the whole
polyhedron. -/
theorem sound_root (cert : FaceCertificate P q target ∅)
    (hcompact : IsCompact P.carrier) :
    ∀ x ∈ P.carrier, (target : ℝ) ≤ q.eval x := by
  intro x hx
  exact cert.sound hcompact x ⟨hx, by simp⟩

end FaceCertificate

end Certificate

end KakeyaNeedleC3C4
