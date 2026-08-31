import KakeyaNeedleC3C4.RationalCertificateChecker

/-!
# Exact sparse degree-two Handelman checker

The generator family is `g₀ = 1`, followed by the constraints of a
`RationalPolyhedron`.  A sparse term `(i,j,λ)` denotes `λ * gᵢ * gⱼ`.
The checker verifies `λ ≥ 0` and the exact ordered coefficient identity

`q - target = Σ λ * gᵢ * gⱼ`.

`RationalQuadratic` deliberately stores a possibly nonsymmetric coefficient
matrix.  This checker therefore compares every ordered quadratic coefficient;
it never assumes `qᵢⱼ = qⱼᵢ` or discards either entry.  Reversing a generator
pair changes the stored ordered representation but not its real evaluation,
and either orientation is sound when the resulting exact identity passes.
-/

namespace KakeyaNeedleC3C4

open scoped BigOperators

/-- One sparse degree-two Handelman term. -/
structure HandelmanTerm (m : ℕ) where
  left : Fin (m + 1)
  right : Fin (m + 1)
  weight : ℚ
  deriving DecidableEq, Repr

/-- A sparse Handelman identity.  Repeated pairs are permitted. -/
structure HandelmanCertificate (m : ℕ) where
  terms : List (HandelmanTerm m)
  deriving DecidableEq, Repr

namespace HandelmanCertificate

variable {n m : ℕ}

/-- The implicit constant generator `g₀ = 1`. -/
def oneAffine (n : ℕ) : RationalAffine n where
  constant := 1
  linear := fun _ ↦ 0

/-- Generator zero is `1`; generator `i+1` is polyhedral constraint `i`. -/
def generator (P : RationalPolyhedron n m) : Fin (m + 1) → RationalAffine n :=
  Fin.cases (oneAffine n) P.constraint

/-- Rational scaling of an affine form. -/
def scaleAffine (r : ℚ) (a : RationalAffine n) : RationalAffine n where
  constant := r * a.constant
  linear := fun k ↦ r * a.linear k

/-- The ordered quadratic representation of one sparse term. -/
def termQuadratic (P : RationalPolyhedron n m)
    (t : HandelmanTerm m) : RationalQuadratic n :=
  RationalQuadratic.mulAffine
    (scaleAffine t.weight (generator P t.left))
    (generator P t.right)

/-- Quadratic represented by all sparse terms. -/
def rhs (c : HandelmanCertificate m)
    (P : RationalPolyhedron n m) : RationalQuadratic n :=
  RationalQuadratic.sum (c.terms.map (termQuadratic P))

/-- Ordered representation of `q - target`. -/
def lhs (q : RationalQuadratic n) (target : ℚ) : RationalQuadratic n :=
  q.add (RationalQuadratic.neg (RationalQuadratic.const target))

/-- A native-executable checker using only rational equality and order tests.
Every ordered matrix coefficient is checked, so nonsymmetric input is handled
without an implicit symmetry convention. -/
def check (c : HandelmanCertificate m) (P : RationalPolyhedron n m)
    (q : RationalQuadratic n) (target : ℚ) : Bool :=
  let l := lhs q target
  let r := c.rhs P
  decide (
    (∀ t ∈ c.terms, 0 ≤ t.weight) ∧
    l.constant = r.constant ∧
    (∀ i, l.linear i = r.linear i) ∧
    ∀ i j, l.quadratic i j = r.quadratic i j)

/-- Symmetric matrix representative of the same scalar polynomial.  Averaging
with the transpose is important: it preserves evaluation even when the input
`RationalQuadratic` is nonsymmetric. -/
def commutativeNormalize (q : RationalQuadratic n) : RationalQuadratic n where
  constant := q.constant
  linear := q.linear
  quadratic := fun i j ↦ (q.quadratic i j + q.quadratic j i) / 2

/-- Equality of scalar commutative quadratic polynomials in coefficient form:
constant and linear coefficients agree, diagonal coefficients agree, and an
off-diagonal monomial `xᵢxⱼ` compares the sum of both ordered entries. -/
abbrev CommutativeCoefficientsEqual (a b : RationalQuadratic n) : Prop :=
  a.constant = b.constant ∧
  (∀ i, a.linear i = b.linear i) ∧
  (∀ i, a.quadratic i i = b.quadratic i i) ∧
  ∀ i j, i < j →
    a.quadratic i j + a.quadratic j i =
      b.quadratic i j + b.quadratic j i

/-- Native-executable mode for certificates generated in the usual
commutative monomial basis. -/
def checkCommutative (c : HandelmanCertificate m)
    (P : RationalPolyhedron n m) (q : RationalQuadratic n)
    (target : ℚ) : Bool :=
  decide (
    (∀ t ∈ c.terms, 0 ≤ t.weight) ∧
    CommutativeCoefficientsEqual (lhs q target) (c.rhs P))

theorem eval_oneAffine (x : Fin n → ℝ) :
    (oneAffine n).eval x = 1 := by
  simp [oneAffine, RationalAffine.eval]

theorem eval_scaleAffine (r : ℚ) (a : RationalAffine n)
    (x : Fin n → ℝ) :
    (scaleAffine r a).eval x = (r : ℝ) * a.eval x := by
  simp only [scaleAffine, RationalAffine.eval, Rat.cast_mul]
  rw [mul_add, Finset.mul_sum]
  apply congrArg (fun z : ℝ ↦ (r : ℝ) * (a.constant : ℝ) + z)
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem eval_termQuadratic (P : RationalPolyhedron n m)
    (t : HandelmanTerm m) (x : Fin n → ℝ) :
    (termQuadratic P t).eval x =
      (t.weight : ℝ) * (generator P t.left).eval x *
        (generator P t.right).eval x := by
  rw [termQuadratic, RationalQuadratic.eval_mulAffine, eval_scaleAffine]

private theorem quadratic_eq_of_coefficients
    {a b : RationalQuadratic n}
    (hc : a.constant = b.constant)
    (hl : ∀ i, a.linear i = b.linear i)
    (hq : ∀ i j, a.quadratic i j = b.quadratic i j) : a = b := by
  cases a with
  | mk ac al aq =>
      cases b with
      | mk bc bl bq =>
          simp only at hc hl hq
          subst bc
          have hlf : al = bl := funext hl
          subst bl
          have hqf : aq = bq := funext fun i ↦ funext (hq i)
          subst bq
          rfl

/-- Symmetrizing the ordered quadratic coefficient matrix does not change the
represented real scalar polynomial. -/
theorem eval_commutativeNormalize (q : RationalQuadratic n)
    (x : Fin n → ℝ) :
    (commutativeNormalize q).eval x = q.eval x := by
  have htranspose :
      (∑ i, ∑ j, (q.quadratic j i : ℝ) * x i * x j) =
        ∑ i, ∑ j, (q.quadratic i j : ℝ) * x i * x j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [commutativeNormalize, RationalQuadratic.eval]
  push_cast
  have hhalf (f : Fin n → Fin n → ℝ) :
      (∑ i, ∑ j, f i j / 2 * x i * x j) =
        (1 / 2 : ℝ) * ∑ i, ∑ j, f i j * x i * x j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hquadratic :
      (∑ i, ∑ j,
        ((q.quadratic i j : ℝ) + (q.quadratic j i : ℝ)) / 2 * x i * x j) =
      ∑ i, ∑ j, (q.quadratic i j : ℝ) * x i * x j := by
    simp_rw [add_div, add_mul, Finset.sum_add_distrib]
    rw [hhalf (fun i j ↦ (q.quadratic i j : ℝ)),
      hhalf (fun i j ↦ (q.quadratic j i : ℝ)), htranspose]
    ring
  rw [hquadratic]

private theorem normalize_eq_of_commutativeCoefficientsEqual
    {a b : RationalQuadratic n}
    (h : CommutativeCoefficientsEqual a b) :
    commutativeNormalize a = commutativeNormalize b := by
  rcases h with ⟨hc, hl, hd, hoff⟩
  apply quadratic_eq_of_coefficients
      (a := commutativeNormalize a) (b := commutativeNormalize b)
  · exact hc
  · exact hl
  intro i j
  simp only [commutativeNormalize]
  by_cases hij : i = j
  · subst j
    rw [hd i]
  · rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · rw [hoff i j hijlt]
    · rw [add_comm (a.quadratic i j), add_comm (b.quadratic i j),
        hoff j i hjilt]

/-- Scalar-polynomial coefficient equality implies equality of real
evaluation, even for nonsymmetric ordered coefficient matrices. -/
theorem eval_eq_of_commutativeCoefficientsEqual
    {a b : RationalQuadratic n}
    (h : CommutativeCoefficientsEqual a b) (x : Fin n → ℝ) :
    a.eval x = b.eval x := by
  rw [← eval_commutativeNormalize a x, ← eval_commutativeNormalize b x,
    normalize_eq_of_commutativeCoefficientsEqual h]

theorem generator_nonnegative {P : RationalPolyhedron n m}
    {x : Fin n → ℝ} (hx : x ∈ P.carrier) :
    ∀ i, 0 ≤ (generator P i).eval x := by
  intro i
  refine Fin.cases ?_ (fun j ↦ hx j) i
  simp [generator, eval_oneAffine]

private theorem rhs_eval_nonnegative {c : HandelmanCertificate m}
    {P : RationalPolyhedron n m} {x : Fin n → ℝ}
    (hweight : ∀ t ∈ c.terms, 0 ≤ t.weight)
    (hx : x ∈ P.carrier) : 0 ≤ (c.rhs P).eval x := by
  rw [rhs, RationalQuadratic.eval_sum]
  generalize c.terms = terms at hweight ⊢
  revert hweight
  induction terms with
  | nil => simp
  | cons t terms ih =>
      intro hweight
      have hhead : 0 ≤ (termQuadratic P t).eval x := by
        rw [eval_termQuadratic]
        have hw : (0 : ℝ) ≤ t.weight := by
          exact_mod_cast hweight t List.mem_cons_self
        have hl := generator_nonnegative hx t.left
        have hr := generator_nonnegative hx t.right
        positivity
      have htail : 0 ≤
          ((terms.map (termQuadratic P)).map (fun r ↦ r.eval x)).sum := by
        exact ih (fun u hu ↦ hweight u (List.mem_cons_of_mem t hu))
      simpa using add_nonneg hhead htail

/-- Soundness of an accepted sparse Handelman lower-bound certificate. -/
theorem check_sound {c : HandelmanCertificate m}
    {P : RationalPolyhedron n m} {q : RationalQuadratic n} {target : ℚ}
    (hcheck : c.check P q target = true) :
    ∀ x ∈ P.carrier, (target : ℝ) ≤ q.eval x := by
  let l := lhs q target
  let r := c.rhs P
  have hfacts :
      (∀ t ∈ c.terms, 0 ≤ t.weight) ∧
      l.constant = r.constant ∧
      (∀ i, l.linear i = r.linear i) ∧
      ∀ i j, l.quadratic i j = r.quadratic i j :=
    of_decide_eq_true hcheck
  rcases hfacts with ⟨hweight, hc, hl, hq⟩
  have hid : l = r := quadratic_eq_of_coefficients hc hl hq
  intro x hx
  have hrhs : 0 ≤ (c.rhs P).eval x := rhs_eval_nonnegative hweight hx
  have hlhs : (lhs q target).eval x = q.eval x - (target : ℝ) := by
    simp [lhs, RationalQuadratic.eval_add, RationalQuadratic.eval_neg,
      RationalQuadratic.eval_const]
    ring
  change lhs q target = c.rhs P at hid
  rw [← hid, hlhs] at hrhs
  linarith

/-- Soundness of the commutative-monomial checker.  This theorem permits the
generated identity to use either orientation for a cross-product term. -/
theorem checkCommutative_sound {c : HandelmanCertificate m}
    {P : RationalPolyhedron n m} {q : RationalQuadratic n} {target : ℚ}
    (hcheck : c.checkCommutative P q target = true) :
    ∀ x ∈ P.carrier, (target : ℝ) ≤ q.eval x := by
  have hfacts :
      (∀ t ∈ c.terms, 0 ≤ t.weight) ∧
      CommutativeCoefficientsEqual (lhs q target) (c.rhs P) :=
    of_decide_eq_true hcheck
  rcases hfacts with ⟨hweight, hcoeff⟩
  intro x hx
  have hrhs : 0 ≤ (c.rhs P).eval x := rhs_eval_nonnegative hweight hx
  have heval : (lhs q target).eval x = (c.rhs P).eval x :=
    eval_eq_of_commutativeCoefficientsEqual hcoeff x
  have hlhs : (lhs q target).eval x = q.eval x - (target : ℝ) := by
    simp [lhs, RationalQuadratic.eval_add, RationalQuadratic.eval_neg,
      RationalQuadratic.eval_const]
    ring
  rw [← heval, hlhs] at hrhs
  linarith

/-! A closed native-execution smoke test: on `x ≥ 0, 1-x ≥ 0`, the
quadratic `x(1-x)` has the one-term Handelman certificate `g₁g₂`. -/

private def unitInterval : RationalPolyhedron 1 2 where
  constraint
    | 0 => { constant := 0, linear := fun _ ↦ 1 }
    | 1 => { constant := 1, linear := fun _ ↦ -1 }

private def unitIntervalQuadratic : RationalQuadratic 1 :=
  RationalQuadratic.mulAffine
    (unitInterval.constraint 0) (unitInterval.constraint 1)

private def unitIntervalCertificate : HandelmanCertificate 2 where
  terms := [{ left := 1, right := 2, weight := 1 }]

example : unitIntervalCertificate.check unitInterval
    unitIntervalQuadratic 0 = true := by
  native_decide

example : ∀ x ∈ unitInterval.carrier,
    (0 : ℝ) ≤ unitIntervalQuadratic.eval x := by
  simpa using check_sound (c := unitIntervalCertificate) (P := unitInterval)
    (q := unitIntervalQuadratic) (target := 0) (by native_decide)

/-- Reversing the two generators generally changes the ordered coefficient
matrix, but it must pass the commutative checker. -/
private def reversedUnitIntervalCertificate : HandelmanCertificate 2 where
  terms := [{ left := 2, right := 1, weight := 1 }]

example : reversedUnitIntervalCertificate.checkCommutative unitInterval
    unitIntervalQuadratic 0 = true := by
  native_decide

example : ∀ x ∈ unitInterval.carrier,
    (0 : ℝ) ≤ unitIntervalQuadratic.eval x := by
  simpa using checkCommutative_sound (c := reversedUnitIntervalCertificate)
    (P := unitInterval) (q := unitIntervalQuadratic) (target := 0)
    (by native_decide)

/-! A genuinely nonsymmetric cross-term test in two variables. -/

private def positiveQuadrant : RationalPolyhedron 2 2 where
  constraint
    | 0 => { constant := 0, linear := ![1, 0] }
    | 1 => { constant := 0, linear := ![0, 1] }

private def orderedXY : RationalQuadratic 2 :=
  RationalQuadratic.mulAffine
    (positiveQuadrant.constraint 0) (positiveQuadrant.constraint 1)

private def reversedXYCertificate : HandelmanCertificate 2 where
  terms := [{ left := 2, right := 1, weight := 1 }]

example : reversedXYCertificate.checkCommutative positiveQuadrant
    orderedXY 0 = true := by
  native_decide

example : reversedXYCertificate.check positiveQuadrant orderedXY 0 = false := by
  native_decide

end HandelmanCertificate

/-! ## Combined affine-SOS and Handelman certificates -/

/-- One nonnegative rational multiple of an arbitrary affine square. -/
structure WeightedAffineSquare (n : ℕ) where
  weight : ℚ
  affine : RationalAffine n
  deriving DecidableEq

/-- A degree-two lower-bound certificate combining arbitrary affine squares
with the generator products of an ordinary Handelman certificate. -/
structure SOSHandelmanCertificate (n m : ℕ) where
  squares : List (WeightedAffineSquare n)
  products : HandelmanCertificate m
  deriving DecidableEq

namespace SOSHandelmanCertificate

variable {n m : ℕ}

def squareQuadratic (s : WeightedAffineSquare n) : RationalQuadratic n :=
  RationalQuadratic.mulAffine
    (HandelmanCertificate.scaleAffine s.weight s.affine) s.affine

def squaresRhs (c : SOSHandelmanCertificate n m) : RationalQuadratic n :=
  RationalQuadratic.sum (c.squares.map squareQuadratic)

def rhs (c : SOSHandelmanCertificate n m) (P : RationalPolyhedron n m) :
    RationalQuadratic n :=
  (c.squaresRhs).add (c.products.rhs P)

/-- Exact native checker in the scalar commutative monomial basis. -/
def checkCommutative (c : SOSHandelmanCertificate n m)
    (P : RationalPolyhedron n m) (q : RationalQuadratic n)
    (target : ℚ) : Bool :=
  decide (
    (∀ s ∈ c.squares, 0 ≤ s.weight) ∧
    (∀ t ∈ c.products.terms, 0 ≤ t.weight) ∧
    HandelmanCertificate.CommutativeCoefficientsEqual
      (HandelmanCertificate.lhs q target) (c.rhs P))

theorem eval_squareQuadratic (s : WeightedAffineSquare n)
    (x : Fin n → ℝ) :
    (squareQuadratic s).eval x =
      (s.weight : ℝ) * s.affine.eval x ^ 2 := by
  rw [squareQuadratic, RationalQuadratic.eval_mulAffine,
    HandelmanCertificate.eval_scaleAffine]
  ring

private theorem squaresRhs_eval_nonnegative
    {c : SOSHandelmanCertificate n m} {x : Fin n → ℝ}
    (hweight : ∀ s ∈ c.squares, 0 ≤ s.weight) :
    0 ≤ c.squaresRhs.eval x := by
  rw [squaresRhs, RationalQuadratic.eval_sum]
  generalize c.squares = squares at hweight ⊢
  revert hweight
  induction squares with
  | nil => simp
  | cons s squares ih =>
      intro hweight
      have hhead : 0 ≤ (squareQuadratic s).eval x := by
        rw [eval_squareQuadratic]
        have hw : (0 : ℝ) ≤ s.weight := by
          exact_mod_cast hweight s List.mem_cons_self
        positivity
      have htail : 0 ≤
          ((squares.map squareQuadratic).map (fun q ↦ q.eval x)).sum :=
        ih (fun t ht ↦ hweight t (List.mem_cons_of_mem s ht))
      simpa using add_nonneg hhead htail

private theorem handelmanRhs_eval_nonnegative
    {c : HandelmanCertificate m} {P : RationalPolyhedron n m}
    {x : Fin n → ℝ}
    (hweight : ∀ t ∈ c.terms, 0 ≤ t.weight)
    (hx : x ∈ P.carrier) : 0 ≤ (c.rhs P).eval x := by
  rw [HandelmanCertificate.rhs, RationalQuadratic.eval_sum]
  generalize c.terms = terms at hweight ⊢
  revert hweight
  induction terms with
  | nil => simp
  | cons t terms ih =>
      intro hweight
      have hhead : 0 ≤ (HandelmanCertificate.termQuadratic P t).eval x := by
        rw [HandelmanCertificate.eval_termQuadratic]
        have hw : (0 : ℝ) ≤ t.weight := by
          exact_mod_cast hweight t List.mem_cons_self
        have hl := HandelmanCertificate.generator_nonnegative hx t.left
        have hr := HandelmanCertificate.generator_nonnegative hx t.right
        positivity
      have htail : 0 ≤ ((terms.map
          (HandelmanCertificate.termQuadratic P)).map (fun q ↦ q.eval x)).sum :=
        ih (fun u hu ↦ hweight u (List.mem_cons_of_mem t hu))
      simpa using add_nonneg hhead htail

/-- Soundness of an accepted combined SOS+Handelman lower bound. -/
theorem checkCommutative_sound {c : SOSHandelmanCertificate n m}
    {P : RationalPolyhedron n m} {q : RationalQuadratic n} {target : ℚ}
    (hcheck : c.checkCommutative P q target = true) :
    ∀ x ∈ P.carrier, (target : ℝ) ≤ q.eval x := by
  have hfacts :
      (∀ s ∈ c.squares, 0 ≤ s.weight) ∧
      (∀ t ∈ c.products.terms, 0 ≤ t.weight) ∧
      HandelmanCertificate.CommutativeCoefficientsEqual
        (HandelmanCertificate.lhs q target) (c.rhs P) :=
    of_decide_eq_true hcheck
  rcases hfacts with ⟨hsquares, hproducts, hcoeff⟩
  intro x hx
  have hsos : 0 ≤ c.squaresRhs.eval x :=
    squaresRhs_eval_nonnegative hsquares
  have hhand : 0 ≤ (c.products.rhs P).eval x :=
    handelmanRhs_eval_nonnegative hproducts hx
  have hrhs : 0 ≤ (c.rhs P).eval x := by
    rw [rhs, RationalQuadratic.eval_add]
    exact add_nonneg hsos hhand
  have heval : (HandelmanCertificate.lhs q target).eval x =
      (c.rhs P).eval x :=
    HandelmanCertificate.eval_eq_of_commutativeCoefficientsEqual hcoeff x
  have hlhs : (HandelmanCertificate.lhs q target).eval x =
      q.eval x - (target : ℝ) := by
    simp [HandelmanCertificate.lhs, RationalQuadratic.eval_add,
      RationalQuadratic.eval_neg, RationalQuadratic.eval_const]
    ring
  rw [← heval, hlhs] at hrhs
  linarith

/-! Native smoke test: `x²` is certified by one arbitrary affine square and
no polyhedral generator products. -/

private def noConstraints : RationalPolyhedron 1 0 where
  constraint := Fin.elim0

private def xAffine : RationalAffine 1 where
  constant := 0
  linear := fun _ ↦ 1

private def xSquared : RationalQuadratic 1 :=
  RationalQuadratic.mulAffine xAffine xAffine

private def squareOnlyCertificate : SOSHandelmanCertificate 1 0 where
  squares := [{ weight := 1, affine := xAffine }]
  products := { terms := [] }

example : squareOnlyCertificate.checkCommutative noConstraints xSquared 0 = true := by
  native_decide

example : ∀ x ∈ noConstraints.carrier, (0 : ℝ) ≤ xSquared.eval x := by
  simpa using checkCommutative_sound
    (c := squareOnlyCertificate) (P := noConstraints)
    (q := xSquared) (target := 0) (by native_decide)

end SOSHandelmanCertificate

end KakeyaNeedleC3C4
