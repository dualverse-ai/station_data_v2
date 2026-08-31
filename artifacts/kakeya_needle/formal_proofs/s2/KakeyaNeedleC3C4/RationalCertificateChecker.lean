import KakeyaNeedleC3C4.PolyhedralCertificate

/-!
# Native-checkable rational stationary-point certificates

`PolyhedralCertificate` proves the analytic face-recursion argument.  This
file adds a finite exact replay format for a node's stationary-point
obligation.  Its checker performs only rational arithmetic and equality/order
tests, so generated facts of the form `certificate.check ... = true` can be
proved with `native_decide`.

The key identity is

`q - target = Σ squares + Σ multiplier * stationaryEquation
                    + Σ activeMultiplier * activeConstraint
                    + Σ nonnegativeMultiplier * constraint`.

All terms are rational quadratics.  The listed stationary directions are also
checked to be tangent to the active face.  Consequently the identity applies
to every stationary point, including a positive-dimensional stationary set;
no matrix inversion, rank assumption, or selected stationary solution occurs.
-/

namespace KakeyaNeedleC3C4

open Set Filter
open scoped Topology

namespace RationalAffine

variable {n : ℕ}

/-- Rational evaluation of the linear part on a rational direction. -/
def dot (a : RationalAffine n) (d : Fin n → ℚ) : ℚ :=
  ∑ i, a.linear i * d i

/-- Cast a rational direction to a real direction. -/
def realDirection (d : Fin n → ℚ) : Fin n → ℝ := fun i ↦ (d i : ℝ)

theorem eval_line (a : RationalAffine n) (x : Fin n → ℝ)
    (d : Fin n → ℚ) (t : ℝ) :
    a.eval (x + t • realDirection d) =
      a.eval x + t * (a.dot d : ℝ) := by
  simp only [eval, dot, realDirection, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, Rat.cast_sum, Rat.cast_mul]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  have hz : (∑ i, (a.linear i : ℝ) * (t * (d i : ℝ))) =
      ∑ i, t * ((a.linear i : ℝ) * (d i : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hz]
  ring

end RationalAffine

namespace RationalQuadratic

variable {n : ℕ}

/-- The zero quadratic in the coefficient representation. -/
def zero : RationalQuadratic n where
  constant := 0
  linear := fun _ ↦ 0
  quadratic := fun _ _ ↦ 0

/-- Coefficientwise addition. -/
def add (q r : RationalQuadratic n) : RationalQuadratic n where
  constant := q.constant + r.constant
  linear := fun i ↦ q.linear i + r.linear i
  quadratic := fun i j ↦ q.quadratic i j + r.quadratic i j

/-- Coefficientwise negation. -/
def neg (q : RationalQuadratic n) : RationalQuadratic n where
  constant := -q.constant
  linear := fun i ↦ -q.linear i
  quadratic := fun i j ↦ -q.quadratic i j

/-- A constant rational polynomial. -/
def const (c : ℚ) : RationalQuadratic n where
  constant := c
  linear := fun _ ↦ 0
  quadratic := fun _ _ ↦ 0

/-- Product of two affine polynomials, represented as an ordered quadratic. -/
def mulAffine (a b : RationalAffine n) : RationalQuadratic n where
  constant := a.constant * b.constant
  linear := fun i ↦ a.constant * b.linear i + a.linear i * b.constant
  quadratic := fun i j ↦ a.linear i * b.linear j

/-- A finite sum without relying on any noncomputable polynomial
normalization. -/
def sum : List (RationalQuadratic n) → RationalQuadratic n
  | [] => zero
  | q :: qs => add q (sum qs)

/-- The affine polynomial representing the directional derivative of `q` in
the rational direction `d`. -/
def stationaryEquation (q : RationalQuadratic n) (d : Fin n → ℚ) :
    RationalAffine n where
  constant := ∑ i, q.linear i * d i
  linear := fun k ↦
    (∑ i, q.quadratic i k * d i) + ∑ j, q.quadratic k j * d j

theorem eval_zero (x : Fin n → ℝ) : (zero : RationalQuadratic n).eval x = 0 := by
  simp [zero, eval]

theorem eval_add (q r : RationalQuadratic n) (x : Fin n → ℝ) :
    (add q r).eval x = q.eval x + r.eval x := by
  simp only [add, eval, Rat.cast_add]
  simp_rw [add_mul]
  simp_rw [Finset.sum_add_distrib]
  ring

theorem eval_neg (q : RationalQuadratic n) (x : Fin n → ℝ) :
    (neg q).eval x = -q.eval x := by
  simp only [neg, eval, Rat.cast_neg]
  simp_rw [neg_mul]
  simp_rw [Finset.sum_neg_distrib]
  ring

theorem eval_const (c : ℚ) (x : Fin n → ℝ) :
    (const c : RationalQuadratic n).eval x = (c : ℝ) := by
  simp [const, eval]

theorem eval_mulAffine (a b : RationalAffine n) (x : Fin n → ℝ) :
    (mulAffine a b).eval x = a.eval x * b.eval x := by
  simp only [mulAffine, eval, RationalAffine.eval, Rat.cast_mul, Rat.cast_add]
  have hquadratic :
      (∑ i, ∑ j, (a.linear i : ℝ) * (b.linear j : ℝ) * x i * x j) =
        (∑ i, (a.linear i : ℝ) * x i) *
          ∑ j, (b.linear j : ℝ) * x j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hleft :
      (∑ i, (a.constant : ℝ) * (b.linear i : ℝ) * x i) =
        (a.constant : ℝ) * ∑ i, (b.linear i : ℝ) * x i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hright :
      (∑ i, (a.linear i : ℝ) * (b.constant : ℝ) * x i) =
        (∑ i, (a.linear i : ℝ) * x i) * (b.constant : ℝ) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [hleft, hright, hquadratic]
  ring

theorem eval_sum (qs : List (RationalQuadratic n)) (x : Fin n → ℝ) :
    (sum qs).eval x = (qs.map (fun q ↦ q.eval x)).sum := by
  induction qs with
  | nil => simp [sum, eval_zero]
  | cons q qs ih => simp [sum, eval_add, ih]

theorem eval_stationaryEquation (q : RationalQuadratic n)
    (d : Fin n → ℚ) (x : Fin n → ℝ) :
    (q.stationaryEquation d).eval x =
      q.directionalDerivative x (RationalAffine.realDirection d) := by
  simp only [stationaryEquation, RationalAffine.eval, directionalDerivative,
    RationalAffine.realDirection, Rat.cast_sum, Rat.cast_mul]
  push_cast
  have hfirst :
      (∑ k, (∑ i, (q.quadratic i k : ℝ) * (d i : ℝ)) * x k) =
        ∑ i, ∑ j, (q.quadratic i j : ℝ) * ((d i : ℝ) * x j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsecond :
      (∑ k, (∑ j, (q.quadratic k j : ℝ) * (d j : ℝ)) * x k) =
        ∑ i, ∑ j, (q.quadratic i j : ℝ) * (x i * (d j : ℝ)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hsplit :
      (∑ i, ∑ j, (q.quadratic i j : ℝ) *
        ((d i : ℝ) * x j + x i * (d j : ℝ))) =
      (∑ i, ∑ j, (q.quadratic i j : ℝ) * ((d i : ℝ) * x j)) +
        ∑ i, ∑ j, (q.quadratic i j : ℝ) * (x i * (d j : ℝ)) := by
    simp_rw [mul_add]
    calc
      _ = ∑ i, ((∑ j, (q.quadratic i j : ℝ) * ((d i : ℝ) * x j)) +
          ∑ j, (q.quadratic i j : ℝ) * (x i * (d j : ℝ))) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.sum_add_distrib]
      _ = _ := Finset.sum_add_distrib
  simp_rw [add_mul, Finset.sum_add_distrib]
  rw [hfirst, hsecond, hsplit]

end RationalQuadratic

/-- One stationary equation and its polynomial-identity multiplier. -/
structure RationalStationaryTerm (n : ℕ) where
  direction : Fin n → ℚ
  multiplier : RationalAffine n
  deriving DecidableEq

/-- Finite exact data replayed at one face-tree node. -/
structure RationalNodeCertificate (n m : ℕ) where
  /-- Sum-of-squares affine factors. -/
  squares : List (RationalAffine n)
  /-- Tangent stationary equations and arbitrary affine multipliers. -/
  stationary : List (RationalStationaryTerm n)
  /-- Arbitrary affine multipliers for active equality constraints. -/
  activeMultiplier : Fin m → RationalAffine n
  /-- Nonnegative scalar multipliers for all valid inequalities. -/
  inequalityMultiplier : Fin m → ℚ
  deriving DecidableEq

namespace RationalNodeCertificate

variable {n m : ℕ}

/-- The exact rational quadratic represented by the right side of the
certificate identity. -/
def rhs (c : RationalNodeCertificate n m) (P : RationalPolyhedron n m)
    (q : RationalQuadratic n) (active : Finset (Fin m)) : RationalQuadratic n :=
  RationalQuadratic.sum <|
    (c.squares.map fun a ↦ RationalQuadratic.mulAffine a a) ++
    (c.stationary.map fun s ↦ RationalQuadratic.mulAffine s.multiplier
      (q.stationaryEquation s.direction)) ++
    (List.ofFn fun i ↦ if i ∈ active then
      RationalQuadratic.mulAffine (c.activeMultiplier i) (P.constraint i)
      else RationalQuadratic.zero) ++
    (List.ofFn fun i ↦ RationalQuadratic.mulAffine
      { constant := c.inequalityMultiplier i, linear := fun _ ↦ 0 }
      (P.constraint i))

/-- Left side `q - target` of the certificate identity. -/
def lhs (q : RationalQuadratic n) (target : ℚ) : RationalQuadratic n :=
  q.add (RationalQuadratic.neg (RationalQuadratic.const target))

/-- A purely rational, executable checker. -/
def check (c : RationalNodeCertificate n m) (P : RationalPolyhedron n m)
    (q : RationalQuadratic n) (target : ℚ) (active : Finset (Fin m)) : Bool :=
  decide (
    (∀ s ∈ c.stationary, ∀ i ∈ active,
      (P.constraint i).dot s.direction = 0) ∧
    (∀ i, 0 ≤ c.inequalityMultiplier i) ∧
    lhs q target = c.rhs P q active)

theorem facts_of_check_eq_true {c : RationalNodeCertificate n m}
    {P : RationalPolyhedron n m} {q : RationalQuadratic n}
    {target : ℚ} {active : Finset (Fin m)}
    (h : c.check P q target active = true) :
    (∀ s ∈ c.stationary, ∀ i ∈ active,
      (P.constraint i).dot s.direction = 0) ∧
    (∀ i, 0 ≤ c.inequalityMultiplier i) ∧
    lhs q target = c.rhs P q active := by
  exact of_decide_eq_true h

/-- At a presented relative-interior point, every rational direction which is
checked tangent to all active affine equalities is locally feasible. -/
theorem locallyFeasible_realDirection
    (P : RationalPolyhedron n m) (active : Finset (Fin m))
    {x : Fin n → ℝ} (hx : x ∈ P.face active)
    (hri : P.InPresentedRelativeInterior active x)
    (d : Fin n → ℚ)
    (htangent : ∀ i ∈ active, (P.constraint i).dot d = 0) :
    LocallyFeasibleDirection P active x
      (RationalAffine.realDirection d) := by
  rw [LocallyFeasibleDirection]
  have hall : ∀ᶠ t : ℝ in 𝓝 0,
      ∀ i, 0 ≤ (P.constraint i).eval
        (x + t • RationalAffine.realDirection d) := by
    have hall' : ∀ᶠ t : ℝ in 𝓝 0, ∀ i ∈ (Finset.univ : Finset (Fin m)),
        0 ≤ (P.constraint i).eval
          (x + t • RationalAffine.realDirection d) := by
      rw [Finset.eventually_all]
      intro i _
      by_cases hi : i ∈ active
      · filter_upwards [] with t
        rw [(P.constraint i).eval_line x d t, hx.2 i hi, htangent i hi]
        simp
      · have hpos : 0 < (P.constraint i).eval x := hri i hi
        have hcont : Continuous (fun t : ℝ ↦
            (P.constraint i).eval
              (x + t • RationalAffine.realDirection d)) :=
          (P.constraint i).continuous.comp (by fun_prop)
        have hev : ∀ᶠ t : ℝ in 𝓝 0,
            (P.constraint i).eval
              (x + t • RationalAffine.realDirection d) ∈ Ioi 0 :=
          hcont.continuousAt (isOpen_Ioi.mem_nhds (by simpa using hpos))
        exact hev.mono fun _ ht ↦ le_of_lt ht
    exact hall'.mono fun _ ht i ↦ ht i (Finset.mem_univ i)
  filter_upwards [hall] with t ht
  refine ⟨ht, ?_⟩
  intro i hi
  rw [(P.constraint i).eval_line x d t, hx.2 i hi, htangent i hi]
  simp

/-- Sound replay theorem for a checked rational node.  This is the bridge from
an executable `native_decide` fact to the analytic `stationaryLower` field of
`FaceCertificate.node`. -/
theorem stationaryLower_of_check
    (c : RationalNodeCertificate n m) (P : RationalPolyhedron n m)
    (q : RationalQuadratic n) (target : ℚ) (active : Finset (Fin m))
    (hcheck : c.check P q target active = true) :
    ∀ x ∈ P.face active, P.InPresentedRelativeInterior active x →
      StationaryOnFace P q active x → (target : ℝ) ≤ q.eval x := by
  obtain ⟨htangent, hnonneg, hidentity⟩ := facts_of_check_eq_true hcheck
  intro x hx hri hstationary
  have hstationaryZero : ∀ s ∈ c.stationary,
      (q.stationaryEquation s.direction).eval x = 0 := by
    intro s hs
    have hfeasible := locallyFeasible_realDirection P active hx hri s.direction
      (htangent s hs)
    have hderivative :=
      (stationaryOnFace_iff_directionalDerivative P q active x).mp
        hstationary (RationalAffine.realDirection s.direction) hfeasible
    exact (q.eval_stationaryEquation s.direction x).trans hderivative
  have hsquares : 0 ≤ ((c.squares.map fun a ↦
      RationalQuadratic.mulAffine a a).map fun r ↦ r.eval x).sum := by
    apply List.sum_nonneg
    intro z hz
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hr
    rw [RationalQuadratic.eval_mulAffine]
    exact mul_self_nonneg (a.eval x)
  have hstationaryTerms :
      (((c.stationary.map fun s ↦ RationalQuadratic.mulAffine s.multiplier
        (q.stationaryEquation s.direction)).map fun r ↦ r.eval x).sum) = 0 := by
    apply List.sum_eq_zero
    intro z hz
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hz
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    rw [RationalQuadratic.eval_mulAffine, hstationaryZero s hs, mul_zero]
  have hactiveTerms :
      (((List.ofFn fun i : Fin m ↦ if i ∈ active then
        RationalQuadratic.mulAffine (c.activeMultiplier i) (P.constraint i)
        else RationalQuadratic.zero).map fun r ↦ r.eval x).sum) = 0 := by
    apply List.sum_eq_zero
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    simp only [List.mem_ofFn] at hr
    obtain ⟨i, rfl⟩ := hr
    by_cases hi : i ∈ active
    · simp [hi, RationalQuadratic.eval_mulAffine, hx.2 i hi]
    · simp [hi, RationalQuadratic.eval_zero]
  have hinequalityTerms : 0 ≤
      (((List.ofFn fun i : Fin m ↦ RationalQuadratic.mulAffine
        { constant := c.inequalityMultiplier i, linear := fun _ ↦ 0 }
        (P.constraint i)).map fun r ↦ r.eval x).sum) := by
    apply List.sum_nonneg
    intro z hz
    simp only [List.mem_map] at hz
    obtain ⟨r, hr, rfl⟩ := hz
    simp only [List.mem_ofFn] at hr
    obtain ⟨i, rfl⟩ := hr
    rw [RationalQuadratic.eval_mulAffine]
    simp [RationalAffine.eval]
    exact mul_nonneg (Rat.cast_nonneg.mpr (hnonneg i)) (hx.1 i)
  have hrhs : 0 ≤ (c.rhs P q active).eval x := by
    rw [rhs, RationalQuadratic.eval_sum]
    simp only [List.map_append, List.sum_append]
    exact add_nonneg (add_nonneg (add_nonneg hsquares
      (le_of_eq hstationaryTerms.symm)) (le_of_eq hactiveTerms.symm))
        hinequalityTerms
  have hidEval := congrArg (fun r : RationalQuadratic n ↦ r.eval x) hidentity
  have hlhs : (lhs q target).eval x = q.eval x - (target : ℝ) := by
    simp [lhs, RationalQuadratic.eval_add, RationalQuadratic.eval_neg,
      RationalQuadratic.eval_const, sub_eq_add_neg]
  change (lhs q target).eval x = (c.rhs P q active).eval x at hidEval
  rw [hlhs] at hidEval
  linarith

/-- Assemble a semantic face-tree node from one checked rational identity and
already assembled boundary children. -/
def checkedNode
    (c : RationalNodeCertificate n m) (P : RationalPolyhedron n m)
    (q : RationalQuadratic n) (target : ℚ) (active : Finset (Fin m))
    (hcheck : c.check P q target active = true)
    (boundary : ∀ i, i ∉ active →
      FaceCertificate P q target (insert i active)) :
    FaceCertificate P q target active :=
  .node active (stationaryLower_of_check c P q target active hcheck) boundary

/-- A small executable smoke test.  Real generated certificates use the same
form of theorem, with `native_decide` replaying all rational identities. -/
def nativeReplayExamplePolyhedron : RationalPolyhedron 1 0 where
  constraint := fun i ↦ Fin.elim0 i

def nativeReplayExampleCertificate : RationalNodeCertificate 1 0 where
  squares := []
  stationary := []
  activeMultiplier := fun i ↦ Fin.elim0 i
  inequalityMultiplier := fun i ↦ Fin.elim0 i

theorem nativeReplayExample :
    nativeReplayExampleCertificate.check nativeReplayExamplePolyhedron
      RationalQuadratic.zero 0 ∅ = true := by
  native_decide

end RationalNodeCertificate

end KakeyaNeedleC3C4
