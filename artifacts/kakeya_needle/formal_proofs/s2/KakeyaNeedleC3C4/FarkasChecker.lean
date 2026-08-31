import KakeyaNeedleC3C4.PolyhedralCertificate

/-!
# Exact rational Farkas checkers

This module provides a deliberately small trusted checker for generated
linear certificates.  A certificate is a vector of rational multipliers.
The checker verifies, using exact rational arithmetic, that every multiplier
is nonnegative and that the claimed affine identity holds coefficientwise.
Consequently concrete checks are suitable for `native_decide`.

Two interfaces are supplied:

* `checkImplication` checks `target = ∑ i, λᵢ gᵢ`, proving that the rational
  polyhedron `gᵢ ≥ 0` implies `target ≥ 0` over the reals;
* `checkInfeasible` specializes the target to the constant `-1`, proving that
  the polyhedron is empty.
-/

namespace KakeyaNeedleC3C4

open scoped BigOperators

/-- A dense exact rational Farkas vector.  Generated certificates normally
write this function using `![...]`, so its length is enforced by the type. -/
structure FarkasCertificate (m : ℕ) where
  multiplier : Fin m → ℚ
  deriving DecidableEq, Repr

namespace FarkasCertificate

variable {n m : ℕ}

/-- Constant coefficient of the conic combination represented by `c`. -/
def combinationConstant (c : FarkasCertificate m)
    (P : RationalPolyhedron n m) : ℚ :=
  ∑ i, c.multiplier i * (P.constraint i).constant

/-- One linear coefficient of the conic combination represented by `c`. -/
def combinationLinear (c : FarkasCertificate m)
    (P : RationalPolyhedron n m) (k : Fin n) : ℚ :=
  ∑ i, c.multiplier i * (P.constraint i).linear k

/-- Purely rational executable checker for the identity
`target = ∑ i, λᵢ * P.constraint i`, including `λᵢ ≥ 0`. -/
def checkImplication (c : FarkasCertificate m)
    (P : RationalPolyhedron n m) (target : RationalAffine n) : Bool :=
  decide (
    (∀ i, 0 ≤ c.multiplier i) ∧
    target.constant = c.combinationConstant P ∧
    ∀ k, target.linear k = c.combinationLinear P k)

/-- The affine function which is constantly `-1`. -/
def negativeOneAffine (n : ℕ) : RationalAffine n where
  constant := -1
  linear := fun _ ↦ 0

/-- Purely rational executable checker for the contradiction identity
`-1 = ∑ i, λᵢ * P.constraint i`, with `λᵢ ≥ 0`. -/
def checkInfeasible (c : FarkasCertificate m)
    (P : RationalPolyhedron n m) : Bool :=
  c.checkImplication P (negativeOneAffine n)

private def combinationEval (c : FarkasCertificate m)
    (P : RationalPolyhedron n m) (x : Fin n → ℝ) : ℝ :=
  ∑ i, (c.multiplier i : ℝ) * (P.constraint i).eval x

private theorem combinationEval_eq (c : FarkasCertificate m)
    (P : RationalPolyhedron n m) (x : Fin n → ℝ) :
    c.combinationEval P x =
      (c.combinationConstant P : ℝ) +
        ∑ k, (c.combinationLinear P k : ℝ) * x k := by
  simp only [combinationEval, RationalAffine.eval, combinationConstant,
    combinationLinear]
  push_cast
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  calc
    (∑ i, (c.multiplier i : ℝ) *
        (((P.constraint i).linear k : ℝ) * x k)) =
      ∑ i, ((c.multiplier i : ℝ) *
        ((P.constraint i).linear k : ℝ)) * x k := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ =
      (∑ i, (c.multiplier i : ℝ) *
        ((P.constraint i).linear k : ℝ)) * x k := by
          rw [Finset.sum_mul]
    _ = _ := rfl

private theorem eval_eq_combinationEval
    (c : FarkasCertificate m) (P : RationalPolyhedron n m)
    (target : RationalAffine n)
    (hconstant : target.constant = c.combinationConstant P)
    (hlinear : ∀ k, target.linear k = c.combinationLinear P k)
    (x : Fin n → ℝ) :
    target.eval x = c.combinationEval P x := by
  rw [combinationEval_eq]
  simp only [RationalAffine.eval]
  rw [hconstant]
  apply congrArg (fun z : ℝ ↦ (c.combinationConstant P : ℝ) + z)
  apply Finset.sum_congr rfl
  intro k _
  rw [hlinear k]

/-- An accepted implication certificate is sound over the reals. -/
theorem checkImplication_sound {c : FarkasCertificate m}
    {P : RationalPolyhedron n m} {target : RationalAffine n}
    (hcheck : c.checkImplication P target = true) :
    ∀ x ∈ P.carrier, 0 ≤ target.eval x := by
  have hfacts :
      (∀ i, 0 ≤ c.multiplier i) ∧
      target.constant = c.combinationConstant P ∧
      ∀ k, target.linear k = c.combinationLinear P k :=
    of_decide_eq_true hcheck
  rcases hfacts with ⟨hmultiplier, hconstant, hlinear⟩
  intro x hx
  rw [eval_eq_combinationEval c P target hconstant hlinear x]
  apply Finset.sum_nonneg
  intro i _
  have hlam : (0 : ℝ) ≤ c.multiplier i := by
    exact_mod_cast hmultiplier i
  exact mul_nonneg hlam (hx i)

/-- An accepted `-1` certificate proves that the rational polyhedron has no
real point. -/
theorem checkInfeasible_sound {c : FarkasCertificate m}
    {P : RationalPolyhedron n m}
    (hcheck : c.checkInfeasible P = true) :
    P.carrier = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hnonneg : 0 ≤ (negativeOneAffine n).eval x :=
    checkImplication_sound hcheck x hx
  norm_num [negativeOneAffine, RationalAffine.eval] at hnonneg

/-! The following closed examples are executable regression tests for the
generated-certificate workflow. -/

private def exampleHalfLine : RationalPolyhedron 1 1 where
  constraint := fun _ ↦ { constant := 0, linear := fun _ ↦ 1 }

private def exampleIdentityCertificate : FarkasCertificate 1 where
  multiplier := fun _ ↦ 1

example : exampleIdentityCertificate.checkImplication exampleHalfLine
    (exampleHalfLine.constraint 0) = true := by
  native_decide

private def exampleEmptyPolyhedron : RationalPolyhedron 1 1 where
  constraint := fun _ ↦ { constant := -1, linear := fun _ ↦ 0 }

example : exampleIdentityCertificate.checkInfeasible exampleEmptyPolyhedron = true := by
  native_decide

end FarkasCertificate

/-! ## Sparse certificates

Sparse certificates store only nonzero (or otherwise explicitly requested)
entries.  Repeated indices are allowed: all definitions simply add their
contributions.  This is useful for streaming generators and avoids a dense
vector at every dead branch of a large coverage trie. -/

/-- A sparse exact rational Farkas vector. -/
structure SparseFarkasCertificate (m : ℕ) where
  terms : List (Fin m × ℚ)
  deriving DecidableEq, Repr

namespace SparseFarkasCertificate

variable {n m : ℕ}

private def constantTerms (terms : List (Fin m × ℚ))
    (P : RationalPolyhedron n m) : ℚ :=
  (terms.map fun t ↦ t.2 * (P.constraint t.1).constant).sum

private def linearTerms (terms : List (Fin m × ℚ))
    (P : RationalPolyhedron n m) (k : Fin n) : ℚ :=
  (terms.map fun t ↦ t.2 * (P.constraint t.1).linear k).sum

private def evalTerms (terms : List (Fin m × ℚ))
    (P : RationalPolyhedron n m) (x : Fin n → ℝ) : ℝ :=
  (terms.map fun t ↦ (t.2 : ℝ) * (P.constraint t.1).eval x).sum

def combinationConstant (c : SparseFarkasCertificate m)
    (P : RationalPolyhedron n m) : ℚ := constantTerms c.terms P

def combinationLinear (c : SparseFarkasCertificate m)
    (P : RationalPolyhedron n m) (k : Fin n) : ℚ :=
  linearTerms c.terms P k

private def combinationEval (c : SparseFarkasCertificate m)
    (P : RationalPolyhedron n m) (x : Fin n → ℝ) : ℝ :=
  evalTerms c.terms P x

/-- Exact sparse implication checker. -/
def checkImplication (c : SparseFarkasCertificate m)
    (P : RationalPolyhedron n m) (target : RationalAffine n) : Bool :=
  decide (
    (∀ t ∈ c.terms, 0 ≤ t.2) ∧
    target.constant = c.combinationConstant P ∧
    ∀ k, target.linear k = c.combinationLinear P k)

/-- Exact sparse closed-system infeasibility checker. -/
def checkInfeasible (c : SparseFarkasCertificate m)
    (P : RationalPolyhedron n m) : Bool :=
  c.checkImplication P (FarkasCertificate.negativeOneAffine n)

/-- Exact sparse strict-system infeasibility checker.  It verifies the affine
Gordan certificate: nonnegative nonzero multipliers, zero combined linear
part, and nonpositive combined constant. -/
def checkStrictInfeasible (c : SparseFarkasCertificate m)
    (P : RationalPolyhedron n m) : Bool :=
  decide (
    (∀ t ∈ c.terms, 0 ≤ t.2) ∧
    (∃ t ∈ c.terms, 0 < t.2) ∧
    c.combinationConstant P ≤ 0 ∧
    ∀ k, c.combinationLinear P k = 0)

private theorem evalTerms_eq (terms : List (Fin m × ℚ))
    (P : RationalPolyhedron n m) (x : Fin n → ℝ) :
    evalTerms terms P x =
      (constantTerms terms P : ℝ) +
        ∑ k, (linearTerms terms P k : ℝ) * x k := by
  induction terms with
  | nil => simp [evalTerms, constantTerms, linearTerms]
  | cons t terms ih =>
      rcases t with ⟨i, w⟩
      change
        (w : ℝ) * (P.constraint i).eval x + evalTerms terms P x =
          ((w * (P.constraint i).constant + constantTerms terms P : ℚ) : ℝ) +
            ∑ k, ((w * (P.constraint i).linear k +
              linearTerms terms P k : ℚ) : ℝ) * x k
      rw [ih]
      simp only [RationalAffine.eval]
      push_cast
      rw [mul_add, Finset.mul_sum]
      simp_rw [add_mul, Finset.sum_add_distrib]
      ring_nf

private theorem combinationEval_eq (c : SparseFarkasCertificate m)
    (P : RationalPolyhedron n m) (x : Fin n → ℝ) :
    c.combinationEval P x =
      (c.combinationConstant P : ℝ) +
        ∑ k, (c.combinationLinear P k : ℝ) * x k :=
  evalTerms_eq c.terms P x

private theorem eval_eq_combinationEval
    (c : SparseFarkasCertificate m) (P : RationalPolyhedron n m)
    (target : RationalAffine n)
    (hconstant : target.constant = c.combinationConstant P)
    (hlinear : ∀ k, target.linear k = c.combinationLinear P k)
    (x : Fin n → ℝ) :
    target.eval x = c.combinationEval P x := by
  rw [combinationEval_eq]
  simp only [RationalAffine.eval]
  rw [hconstant]
  apply congrArg (fun z : ℝ ↦ (c.combinationConstant P : ℝ) + z)
  apply Finset.sum_congr rfl
  intro k _
  rw [hlinear k]

private theorem evalTerms_nonneg {terms : List (Fin m × ℚ)}
    {P : RationalPolyhedron n m} {x : Fin n → ℝ}
    (hweight : ∀ t ∈ terms, 0 ≤ t.2)
    (hx : x ∈ P.carrier) : 0 ≤ evalTerms terms P x := by
  induction terms with
  | nil => simp [evalTerms]
  | cons t terms ih =>
      have hhead : 0 ≤ (t.2 : ℝ) * (P.constraint t.1).eval x := by
        apply mul_nonneg
        · exact_mod_cast hweight t (by simp)
        · exact hx t.1
      have htail : 0 ≤ evalTerms terms P x :=
        ih (fun u hu ↦ hweight u (by simp [hu]))
      simpa [evalTerms] using add_nonneg hhead htail

/-- Soundness of an accepted sparse implication certificate. -/
theorem checkImplication_sound {c : SparseFarkasCertificate m}
    {P : RationalPolyhedron n m} {target : RationalAffine n}
    (hcheck : c.checkImplication P target = true) :
    ∀ x ∈ P.carrier, 0 ≤ target.eval x := by
  have hfacts :
      (∀ t ∈ c.terms, 0 ≤ t.2) ∧
      target.constant = c.combinationConstant P ∧
      ∀ k, target.linear k = c.combinationLinear P k :=
    of_decide_eq_true hcheck
  rcases hfacts with ⟨hweight, hconstant, hlinear⟩
  intro x hx
  rw [eval_eq_combinationEval c P target hconstant hlinear x]
  exact evalTerms_nonneg hweight hx

/-- Soundness of an accepted sparse closed-system contradiction. -/
theorem checkInfeasible_sound {c : SparseFarkasCertificate m}
    {P : RationalPolyhedron n m}
    (hcheck : c.checkInfeasible P = true) :
    P.carrier = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hnonneg : 0 ≤ (FarkasCertificate.negativeOneAffine n).eval x :=
    checkImplication_sound hcheck x hx
  norm_num [FarkasCertificate.negativeOneAffine, RationalAffine.eval] at hnonneg

def StrictlySatisfies (P : RationalPolyhedron n m)
    (x : Fin n → ℝ) : Prop :=
  ∀ i, 0 < (P.constraint i).eval x

private theorem evalTerms_pos {terms : List (Fin m × ℚ)}
    {P : RationalPolyhedron n m} {x : Fin n → ℝ}
    (hweight : ∀ t ∈ terms, 0 ≤ t.2)
    (hpositive : ∃ t ∈ terms, 0 < t.2)
    (hx : StrictlySatisfies P x) : 0 < evalTerms terms P x := by
  induction terms with
  | nil => simp at hpositive
  | cons t terms ih =>
      have hhead_nonneg : 0 ≤ (t.2 : ℝ) * (P.constraint t.1).eval x := by
        apply mul_nonneg
        · exact_mod_cast hweight t (by simp)
        · exact (hx t.1).le
      rcases hpositive with ⟨u, hu, hupos⟩
      rcases List.mem_cons.mp hu with rfl | hutail
      · have hhead_pos : 0 < (u.2 : ℝ) * (P.constraint u.1).eval x := by
          exact mul_pos (by exact_mod_cast hupos) (hx u.1)
        have htail_nonneg : 0 ≤ evalTerms terms P x :=
          evalTerms_nonneg (fun v hv ↦ hweight v (by simp [hv]))
            (fun i ↦ (hx i).le)
        simpa [evalTerms] using add_pos_of_pos_of_nonneg hhead_pos htail_nonneg
      · have htail_pos : 0 < evalTerms terms P x :=
          ih (fun v hv ↦ hweight v (by simp [hv])) ⟨u, hutail, hupos⟩

        simpa [evalTerms] using add_pos_of_nonneg_of_pos hhead_nonneg htail_pos

/-- Soundness of sparse strict Farkas infeasibility. -/
theorem checkStrictInfeasible_sound {c : SparseFarkasCertificate m}
    {P : RationalPolyhedron n m}
    (hcheck : c.checkStrictInfeasible P = true) :
    ¬ ∃ x : Fin n → ℝ, StrictlySatisfies P x := by
  have hfacts :
      (∀ t ∈ c.terms, 0 ≤ t.2) ∧
      (∃ t ∈ c.terms, 0 < t.2) ∧
      c.combinationConstant P ≤ 0 ∧
      ∀ k, c.combinationLinear P k = 0 :=
    of_decide_eq_true hcheck
  rcases hfacts with ⟨hweight, hpositive, hconstant, hlinear⟩
  rintro ⟨x, hx⟩
  have hpos : 0 < c.combinationEval P x :=
    evalTerms_pos hweight hpositive hx
  have hnonpos : c.combinationEval P x ≤ 0 := by
    rw [combinationEval_eq]
    have hc : (c.combinationConstant P : ℝ) ≤ 0 := by
      exact_mod_cast hconstant
    simpa [hlinear] using hc
  linarith

/-- Pointwise form of strict infeasibility, convenient at a trie branch. -/
theorem checkStrictInfeasible_sound_at {c : SparseFarkasCertificate m}
    {P : RationalPolyhedron n m}
    (hcheck : c.checkStrictInfeasible P = true) (x : Fin n → ℝ) :
    ¬ ∀ i, 0 < (P.constraint i).eval x := by
  intro hx
  exact checkStrictInfeasible_sound hcheck ⟨x, hx⟩

/-! Executable sparse smoke tests, including repeated indices. -/

private def sparseIdentityCertificate : SparseFarkasCertificate 1 where
  terms := [(0, 1 / 2), (0, 1 / 2)]

example : sparseIdentityCertificate.checkImplication
    FarkasCertificate.exampleHalfLine
    (FarkasCertificate.exampleHalfLine.constraint 0) = true := by
  native_decide

example : sparseIdentityCertificate.checkInfeasible
    FarkasCertificate.exampleEmptyPolyhedron = true := by
  native_decide

private def strictOppositeConstraints : RationalPolyhedron 1 2 where
  constraint
    | 0 => { constant := 0, linear := fun _ ↦ 1 }
    | 1 => { constant := 0, linear := fun _ ↦ -1 }

private def sparseStrictCertificate : SparseFarkasCertificate 2 where
  terms := [(0, 1), (1, 1)]

example : sparseStrictCertificate.checkStrictInfeasible
    strictOppositeConstraints = true := by
  native_decide

/-! ## Boundary-safe oriented strict certificates

At a boundary point, a generic rational direction assigns every constraint a
nonzero directional sign.  Forward-pointing constraints are allowed to be
weak at the point; backward-pointing constraints must already be strict. -/

/-- Exact rational directional derivative of an affine constraint. -/
def directionalDot (g : RationalAffine n) (v : Fin n → ℚ) : ℚ :=
  ∑ k, g.linear k * v k

/-- Executable oriented affine-Gordan contradiction checker.  In addition to
zero combined linear part and nonpositive constant, it verifies that the
routing direction is generic for every presented constraint. -/
def checkOrientedStrictInfeasible (c : SparseFarkasCertificate m)
    (P : RationalPolyhedron n m) (v : Fin n → ℚ) : Bool :=
  decide (
    (∀ t ∈ c.terms, 0 ≤ t.2) ∧
    (∃ t ∈ c.terms, 0 < t.2) ∧
    c.combinationConstant P ≤ 0 ∧
    (∀ k, c.combinationLinear P k = 0) ∧
    ∀ i, directionalDot (P.constraint i) v ≠ 0)

/-- Boundary convention induced by `v`: forward walls are closed and
backward walls are strict. -/
def OrientedSatisfies (P : RationalPolyhedron n m) (v : Fin n → ℚ)
    (x : Fin n → ℝ) : Prop :=
  (∀ i, 0 < directionalDot (P.constraint i) v →
    0 ≤ (P.constraint i).eval x) ∧
  ∀ i, directionalDot (P.constraint i) v < 0 →
    0 < (P.constraint i).eval x

private theorem list_sum_nonneg_of_nonneg
    {α R : Type} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    (l : List α) (f : α → R)
    (hnonneg : ∀ a ∈ l, 0 ≤ f a) : 0 ≤ (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact add_nonneg (hnonneg a List.mem_cons_self)
        (ih (fun b hb ↦ hnonneg b (List.mem_cons_of_mem a hb)))

private theorem list_sum_pos_of_nonneg_of_pos_mem
    {α R : Type} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    [AddLeftStrictMono R]
    (l : List α) (f : α → R)
    (hnonneg : ∀ a ∈ l, 0 ≤ f a)
    (hpos : ∃ a ∈ l, 0 < f a) : 0 < (l.map f).sum := by
  induction l with
  | nil => simp at hpos
  | cons a l ih =>
      rcases hpos with ⟨b, hb, hbpos⟩
      rcases List.mem_cons.mp hb with rfl | hbl
      · have htail : 0 ≤ (l.map f).sum := by
          exact list_sum_nonneg_of_nonneg l f
            (fun d hd ↦ hnonneg d (List.mem_cons_of_mem b hd))
        simpa using add_pos_of_pos_of_nonneg hbpos htail
      · have hhead := hnonneg a List.mem_cons_self
        have htail := ih
          (fun d hd ↦ hnonneg d (List.mem_cons_of_mem a hd))
          ⟨b, hbl, hbpos⟩
        simpa using add_pos_of_nonneg_of_pos hhead htail

private def dotTerms (terms : List (Fin m × ℚ))
    (P : RationalPolyhedron n m) (v : Fin n → ℚ) : ℚ :=
  (terms.map fun t ↦ t.2 * directionalDot (P.constraint t.1) v).sum

private theorem dotTerms_eq (terms : List (Fin m × ℚ))
    (P : RationalPolyhedron n m) (v : Fin n → ℚ) :
    dotTerms terms P v =
      ∑ k, linearTerms terms P k * v k := by
  induction terms with
  | nil => simp [dotTerms, linearTerms]
  | cons t terms ih =>
      rcases t with ⟨i, w⟩
      change w * (∑ k, (P.constraint i).linear k * v k) +
          dotTerms terms P v =
        ∑ k, (w * (P.constraint i).linear k +
          linearTerms terms P k) * v k
      rw [ih, Finset.mul_sum]
      simp_rw [add_mul, Finset.sum_add_distrib]
      ring_nf

/-- Soundness of generic-direction tie routing. -/
theorem checkOrientedStrictInfeasible_sound
    {c : SparseFarkasCertificate m} {P : RationalPolyhedron n m}
    {v : Fin n → ℚ}
    (hcheck : c.checkOrientedStrictInfeasible P v = true) :
    ¬ ∃ x : Fin n → ℝ, OrientedSatisfies P v x := by
  have hfacts :
      (∀ t ∈ c.terms, 0 ≤ t.2) ∧
      (∃ t ∈ c.terms, 0 < t.2) ∧
      c.combinationConstant P ≤ 0 ∧
      (∀ k, c.combinationLinear P k = 0) ∧
      ∀ i, directionalDot (P.constraint i) v ≠ 0 :=
    of_decide_eq_true hcheck
  rcases hfacts with ⟨hweight, hpositive, hconstant, hlinear, hgeneric⟩
  rintro ⟨x, hforward, hbackward⟩
  have heval_nonneg (t : Fin m × ℚ) (ht : t ∈ c.terms) :
      0 ≤ (t.2 : ℝ) * (P.constraint t.1).eval x := by
    have hw : (0 : ℝ) ≤ t.2 := by exact_mod_cast hweight t ht
    have hg : 0 ≤ (P.constraint t.1).eval x := by
      rcases lt_or_gt_of_ne (hgeneric t.1) with hneg | hpos
      · exact (hbackward t.1 hneg).le
      · exact hforward t.1 hpos
    exact mul_nonneg hw hg
  have hcombination_nonpos : c.combinationEval P x ≤ 0 := by
    rw [combinationEval_eq]
    have hc : (c.combinationConstant P : ℝ) ≤ 0 := by
      exact_mod_cast hconstant
    simpa [hlinear] using hc
  by_cases hsupportedBack : ∃ t ∈ c.terms,
      0 < t.2 ∧ directionalDot (P.constraint t.1) v < 0
  · rcases hsupportedBack with ⟨t, ht, htweight, htdot⟩
    have htpos : 0 < (t.2 : ℝ) * (P.constraint t.1).eval x := by
      exact mul_pos (by exact_mod_cast htweight) (hbackward t.1 htdot)
    have hsumpos : 0 < c.combinationEval P x := by
      exact list_sum_pos_of_nonneg_of_pos_mem c.terms
        (fun u ↦ (u.2 : ℝ) * (P.constraint u.1).eval x)
        heval_nonneg ⟨t, ht, htpos⟩
    linarith
  · push_neg at hsupportedBack
    have hdot_nonneg (t : Fin m × ℚ) (ht : t ∈ c.terms) :
        0 ≤ (t.2 * directionalDot (P.constraint t.1) v : ℚ) := by
      by_cases htw : t.2 = 0
      · simp [htw]
      · have htwpos : 0 < t.2 := lt_of_le_of_ne (hweight t ht) (Ne.symm htw)
        have hdotpos : 0 < directionalDot (P.constraint t.1) v := by
          rcases lt_or_gt_of_ne (hgeneric t.1) with hdotneg | hdotpos
          · exact False.elim (not_lt_of_ge (hsupportedBack t ht htwpos) hdotneg)
          · exact hdotpos
        exact mul_nonneg htwpos.le hdotpos.le
    obtain ⟨t, ht, htweight⟩ := hpositive
    have htdotpos : 0 < directionalDot (P.constraint t.1) v := by
      rcases lt_or_gt_of_ne (hgeneric t.1) with hdotneg | hdotpos
      · exact False.elim (not_lt_of_ge (hsupportedBack t ht htweight) hdotneg)
      · exact hdotpos
    have hdotsum_pos : (0 : ℚ) < dotTerms c.terms P v := by
      exact list_sum_pos_of_nonneg_of_pos_mem c.terms
        (fun u ↦ u.2 * directionalDot (P.constraint u.1) v)
        hdot_nonneg ⟨t, ht, mul_pos htweight htdotpos⟩
    have hdotsum_zero : dotTerms c.terms P v = 0 := by
      rw [dotTerms_eq]
      change ∀ k, linearTerms c.terms P k = 0 at hlinear
      simp [hlinear]
    linarith

/-- Pointwise form used directly by a coverage-trie branch. -/
theorem checkOrientedStrictInfeasible_sound_at
    {c : SparseFarkasCertificate m} {P : RationalPolyhedron n m}
    {v : Fin n → ℚ}
    (hcheck : c.checkOrientedStrictInfeasible P v = true)
    (x : Fin n → ℝ) : ¬ OrientedSatisfies P v x := by
  intro hx
  exact checkOrientedStrictInfeasible_sound hcheck ⟨x, hx⟩

private def genericDirection1 : Fin 1 → ℚ := fun _ ↦ 1

example : sparseStrictCertificate.checkOrientedStrictInfeasible
    strictOppositeConstraints genericDirection1 = true := by
  native_decide

example : ¬ ∃ x : Fin 1 → ℝ,
    OrientedSatisfies strictOppositeConstraints genericDirection1 x := by
  exact checkOrientedStrictInfeasible_sound
    (c := sparseStrictCertificate) (P := strictOppositeConstraints)
    (v := genericDirection1) (by native_decide)

end SparseFarkasCertificate

end KakeyaNeedleC3C4
