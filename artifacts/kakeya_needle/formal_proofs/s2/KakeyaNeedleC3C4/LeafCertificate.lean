import KakeyaNeedleC3C4.SweepCertificate
import KakeyaNeedleC3C4.HandelmanChecker

/-!
# Native-checkable generated leaf bundles

A generated arrangement leaf has one of two forms.

* An empty leaf carries a sparse closed Farkas contradiction for its fixed
  rational polyhedron.
* A live leaf carries a checked interval-sweep schedule and a sparse
  commutative Handelman certificate for the schedule's integrated quadratic.

The wrappers below specialize this design to the paper's three- and
four-triangle problems.  `checkAll3` and `checkAll4` allow a generated list of
thousands of leaves to be replayed by one `native_decide`; their extraction
lemmas recover the Boolean fact for any member without rerunning native code.
-/

namespace KakeyaNeedleC3C4

namespace LeafCertificate

/-- One generated leaf for the three-triangle arrangement. -/
inductive Leaf3 (m : ℕ)
  | empty (certificate : SparseFarkasCertificate m)
  | live (sweep : SweepCertificate.Certificate3 m)
      (lower : HandelmanCertificate m)
  | liveSOS (sweep : SweepCertificate.Certificate3 m)
      (lower : SOSHandelmanCertificate 3 m)
  deriving DecidableEq

/-- One generated leaf for the four-triangle arrangement. -/
inductive Leaf4 (m : ℕ)
  | empty (certificate : SparseFarkasCertificate m)
  | live (sweep : SweepCertificate.Certificate4 m)
      (lower : HandelmanCertificate m)
  | liveSOS (sweep : SweepCertificate.Certificate4 m)
      (lower : SOSHandelmanCertificate 4 m)
  deriving DecidableEq

/-- Exact Boolean replay of one three-triangle leaf. -/
def check3 {m : ℕ} (P : RationalPolyhedron 3 m) (target : ℚ) :
    Leaf3 m → Bool
  | .empty certificate => certificate.checkInfeasible P
  | .live sweep lower =>
      SweepCertificate.check3 sweep P &&
      lower.checkCommutative P
        (SweepCertificate.Certificate3.integratedQuadratic sweep) target
  | .liveSOS sweep lower =>
      SweepCertificate.check3 sweep P &&
      lower.checkCommutative P
        (SweepCertificate.Certificate3.integratedQuadratic sweep) target

/-- Exact Boolean replay of one four-triangle leaf. -/
def check4 {m : ℕ} (P : RationalPolyhedron 4 m) (target : ℚ) :
    Leaf4 m → Bool
  | .empty certificate => certificate.checkInfeasible P
  | .live sweep lower =>
      SweepCertificate.check sweep P &&
      lower.checkCommutative P
        (SweepCertificate.integratedQuadratic sweep) target
  | .liveSOS sweep lower =>
      SweepCertificate.check sweep P &&
      lower.checkCommutative P
        (SweepCertificate.integratedQuadratic sweep) target

/-- Soundness of either kind of accepted three-triangle leaf. -/
theorem sound3 {m : ℕ} {P : RationalPolyhedron 3 m} {target : ℚ}
    {leaf : Leaf3 m} (hcheck : check3 P target leaf = true) :
    ∀ p ∈ P.carrier, (target : ℝ) ≤ unionArea 3 p := by
  intro p hp
  cases leaf with
  | empty certificate =>
      have hempty : P.carrier = ∅ :=
        SparseFarkasCertificate.checkInfeasible_sound hcheck
      exfalso
      simp [hempty] at hp
  | live sweep lower =>
      simp only [check3, Bool.and_eq_true] at hcheck
      have hsweep : SweepCertificate.check3 sweep P = true := hcheck.1
      have hlower : lower.checkCommutative P
          (SweepCertificate.Certificate3.integratedQuadratic sweep)
          target = true := hcheck.2
      have hq : (target : ℝ) ≤
          (SweepCertificate.Certificate3.integratedQuadratic sweep).eval p :=
        HandelmanCertificate.checkCommutative_sound hlower p hp
      calc
        (target : ℝ) ≤
            (SweepCertificate.Certificate3.integratedQuadratic sweep).eval p := hq
        _ = sliceArea 3 p :=
          (SweepCertificate.sliceArea_eq_integratedQuadratic_three hsweep hp).symm
        _ = unionArea 3 p := (unionArea_eq_sliceArea 3 p).symm
  | liveSOS sweep lower =>
      simp only [check3, Bool.and_eq_true] at hcheck
      have hsweep : SweepCertificate.check3 sweep P = true := hcheck.1
      have hlower : lower.checkCommutative P
          (SweepCertificate.Certificate3.integratedQuadratic sweep)
          target = true := hcheck.2
      have hq : (target : ℝ) ≤
          (SweepCertificate.Certificate3.integratedQuadratic sweep).eval p :=
        SOSHandelmanCertificate.checkCommutative_sound hlower p hp
      calc
        (target : ℝ) ≤
            (SweepCertificate.Certificate3.integratedQuadratic sweep).eval p := hq
        _ = sliceArea 3 p :=
          (SweepCertificate.sliceArea_eq_integratedQuadratic_three hsweep hp).symm
        _ = unionArea 3 p := (unionArea_eq_sliceArea 3 p).symm

/-- Soundness of either kind of accepted four-triangle leaf. -/
theorem sound4 {m : ℕ} {P : RationalPolyhedron 4 m} {target : ℚ}
    {leaf : Leaf4 m} (hcheck : check4 P target leaf = true) :
    ∀ p ∈ P.carrier, (target : ℝ) ≤ unionArea 4 p := by
  intro p hp
  cases leaf with
  | empty certificate =>
      have hempty : P.carrier = ∅ :=
        SparseFarkasCertificate.checkInfeasible_sound hcheck
      exfalso
      simp [hempty] at hp
  | live sweep lower =>
      simp only [check4, Bool.and_eq_true] at hcheck
      have hsweep : SweepCertificate.check sweep P = true := hcheck.1
      have hlower : lower.checkCommutative P
          (SweepCertificate.integratedQuadratic sweep)
          target = true := hcheck.2
      have hq : (target : ℝ) ≤
          (SweepCertificate.integratedQuadratic sweep).eval p :=
        HandelmanCertificate.checkCommutative_sound hlower p hp
      calc
        (target : ℝ) ≤
            (SweepCertificate.integratedQuadratic sweep).eval p := hq
        _ = sliceArea 4 p :=
          (SweepCertificate.sliceArea_eq_integratedQuadratic_four hsweep hp).symm
        _ = unionArea 4 p := (unionArea_eq_sliceArea 4 p).symm
  | liveSOS sweep lower =>
      simp only [check4, Bool.and_eq_true] at hcheck
      have hsweep : SweepCertificate.check sweep P = true := hcheck.1
      have hlower : lower.checkCommutative P
          (SweepCertificate.integratedQuadratic sweep)
          target = true := hcheck.2
      have hq : (target : ℝ) ≤
          (SweepCertificate.integratedQuadratic sweep).eval p :=
        SOSHandelmanCertificate.checkCommutative_sound hlower p hp
      calc
        (target : ℝ) ≤
            (SweepCertificate.integratedQuadratic sweep).eval p := hq
        _ = sliceArea 4 p :=
          (SweepCertificate.sliceArea_eq_integratedQuadratic_four hsweep hp).symm
        _ = unionArea 4 p := (unionArea_eq_sliceArea 4 p).symm

/-- One Boolean replay for a generated list of three-triangle leaves. -/
def checkAll3 {m : ℕ} (P : RationalPolyhedron 3 m) (target : ℚ)
    (leaves : List (Leaf3 m)) : Bool :=
  leaves.all (check3 P target)

/-- One Boolean replay for a generated list of four-triangle leaves. -/
def checkAll4 {m : ℕ} (P : RationalPolyhedron 4 m) (target : ℚ)
    (leaves : List (Leaf4 m)) : Bool :=
  leaves.all (check4 P target)

/-- Extract an individual accepted leaf from one accepted three-leaf bundle. -/
theorem check3_of_checkAll3 {m : ℕ} {P : RationalPolyhedron 3 m}
    {target : ℚ} {leaves : List (Leaf3 m)}
    (hall : checkAll3 P target leaves = true) {leaf : Leaf3 m}
    (hleaf : leaf ∈ leaves) : check3 P target leaf = true := by
  exact (List.all_eq_true.mp hall) leaf hleaf

/-- Extract an individual accepted leaf from one accepted four-leaf bundle. -/
theorem check4_of_checkAll4 {m : ℕ} {P : RationalPolyhedron 4 m}
    {target : ℚ} {leaves : List (Leaf4 m)}
    (hall : checkAll4 P target leaves = true) {leaf : Leaf4 m}
    (hleaf : leaf ∈ leaves) : check4 P target leaf = true := by
  exact (List.all_eq_true.mp hall) leaf hleaf

/-- Combined extraction and semantic soundness for a member of a checked
three-triangle bundle. -/
theorem sound3_of_checkAll3 {m : ℕ} {P : RationalPolyhedron 3 m}
    {target : ℚ} {leaves : List (Leaf3 m)}
    (hall : checkAll3 P target leaves = true) {leaf : Leaf3 m}
    (hleaf : leaf ∈ leaves) :
    ∀ p ∈ P.carrier, (target : ℝ) ≤ unionArea 3 p :=
  sound3 (check3_of_checkAll3 hall hleaf)

/-- Combined extraction and semantic soundness for a member of a checked
four-triangle bundle. -/
theorem sound4_of_checkAll4 {m : ℕ} {P : RationalPolyhedron 4 m}
    {target : ℚ} {leaves : List (Leaf4 m)}
    (hall : checkAll4 P target leaves = true) {leaf : Leaf4 m}
    (hleaf : leaf ∈ leaves) :
    ∀ p ∈ P.carrier, (target : ℝ) ≤ unionArea 4 p :=
  sound4 (check4_of_checkAll4 hall hleaf)

/-! ## Per-leaf polyhedra and indexed global checks

Generated path polyhedra differ from leaf to leaf, while their padded
constraint count `m` is fixed.  These entry structures are therefore the main
API for generated payloads. -/

structure Entry3 (m : ℕ) where
  poly : RationalPolyhedron 3 m
  leaf : Leaf3 m

structure Entry4 (m : ℕ) where
  poly : RationalPolyhedron 4 m
  leaf : Leaf4 m

def checkEntry3 {m : ℕ} (target : ℚ) (entry : Entry3 m) : Bool :=
  check3 entry.poly target entry.leaf

def checkEntry4 {m : ℕ} (target : ℚ) (entry : Entry4 m) : Bool :=
  check4 entry.poly target entry.leaf

theorem soundEntry3 {m : ℕ} {target : ℚ} {entry : Entry3 m}
    (hcheck : checkEntry3 target entry = true) :
    ∀ p ∈ entry.poly.carrier, (target : ℝ) ≤ unionArea 3 p :=
  sound3 hcheck

theorem soundEntry4 {m : ℕ} {target : ℚ} {entry : Entry4 m}
    (hcheck : checkEntry4 target entry = true) :
    ∀ p ∈ entry.poly.carrier, (target : ℝ) ≤ unionArea 4 p :=
  sound4 hcheck

/-- One native Boolean for an indexed family with distinct three-dimensional
leaf polyhedra. -/
def checkEntries3 {m N : ℕ} (target : ℚ)
    (entries : Fin N → Entry3 m) : Bool :=
  SweepCertificate.finAll (fun i ↦ checkEntry3 target (entries i))

/-- One native Boolean for an indexed family with distinct four-dimensional
leaf polyhedra. -/
def checkEntries4 {m N : ℕ} (target : ℚ)
    (entries : Fin N → Entry4 m) : Bool :=
  SweepCertificate.finAll (fun i ↦ checkEntry4 target (entries i))

theorem checkEntry3_of_checkEntries3 {m N : ℕ} {target : ℚ}
    {entries : Fin N → Entry3 m}
    (hall : checkEntries3 target entries = true) (i : Fin N) :
    checkEntry3 target (entries i) = true :=
  (SweepCertificate.finAll_eq_true.mp hall) i

theorem checkEntry4_of_checkEntries4 {m N : ℕ} {target : ℚ}
    {entries : Fin N → Entry4 m}
    (hall : checkEntries4 target entries = true) (i : Fin N) :
    checkEntry4 target (entries i) = true :=
  (SweepCertificate.finAll_eq_true.mp hall) i

theorem soundEntry3_of_checkEntries3 {m N : ℕ} {target : ℚ}
    {entries : Fin N → Entry3 m}
    (hall : checkEntries3 target entries = true) (i : Fin N) :
    ∀ p ∈ (entries i).poly.carrier,
      (target : ℝ) ≤ unionArea 3 p :=
  soundEntry3 (checkEntry3_of_checkEntries3 hall i)

theorem soundEntry4_of_checkEntries4 {m N : ℕ} {target : ℚ}
    {entries : Fin N → Entry4 m}
    (hall : checkEntries4 target entries = true) (i : Fin N) :
    ∀ p ∈ (entries i).poly.carrier,
      (target : ℝ) ≤ unionArea 4 p :=
  soundEntry4 (checkEntry4_of_checkEntries4 hall i)

/-! ## Direct certified decision trees

This layer avoids an indexed-leaf coverage theorem entirely.  A tree leaf
stores its payload directly.  Both checker and soundness recursion carry the
same root-to-current signed path, and the caller supplies the fixed-size
padded polyhedron constructor used by generated data. -/

/-- `true` selects the wall and `false` selects its negation. -/
abbrev SignedIndex (H : ℕ) := Fin H × Bool

/-- A binary decision tree whose leaves directly contain certificate data. -/
inductive PayloadTree (H : ℕ) (α : Type)
  | leaf (payload : α)
  | branch (wall : Fin H) (pos neg : PayloadTree H α)
  deriving DecidableEq

abbrev Tree3 (H m : ℕ) := PayloadTree H (Leaf3 m)
abbrev Tree4 (H m : ℕ) := PayloadTree H (Leaf4 m)

/-- Semantic sign convention used by routing and generated path constraints. -/
def signedWallEval {n H : ℕ} (walls : Fin H → RationalAffine n)
    (p : Fin n → ℝ) (s : SignedIndex H) : ℝ :=
  if s.2 then (walls s.1).eval p else -(walls s.1).eval p

def PathNonnegative {n H : ℕ} (walls : Fin H → RationalAffine n)
    (p : Fin n → ℝ) (path : List (SignedIndex H)) : Prop :=
  ∀ s ∈ path, 0 ≤ signedWallEval walls p s

private theorem pathNonnegative_append {n H : ℕ}
    {walls : Fin H → RationalAffine n} {p : Fin n → ℝ}
    {path : List (SignedIndex H)} (hpath : PathNonnegative walls p path)
    (s : SignedIndex H) (hs : 0 ≤ signedWallEval walls p s) :
    PathNonnegative walls p (path ++ [s]) := by
  intro t ht
  simp only [List.mem_append, List.mem_singleton] at ht
  rcases ht with ht | rfl
  · exact hpath t ht
  · exact hs

/-- Recursive global checker for three-triangle payload trees.  At a leaf,
`polyForPath current` is exactly the polyhedron checked by both certificates. -/
def checkTreeAux3 {H m : ℕ} (maxDepth : ℕ)
    (polyForPath : List (SignedIndex H) → RationalPolyhedron 3 m)
    (target : ℚ) : List (SignedIndex H) → Tree3 H m → Bool
  | current, .leaf payload =>
      decide (current.length ≤ maxDepth) &&
        check3 (polyForPath current) target payload
  | current, .branch wall pos neg =>
      decide (current.length < maxDepth) &&
        (checkTreeAux3 maxDepth polyForPath target
          (current ++ [(wall, true)]) pos &&
        checkTreeAux3 maxDepth polyForPath target
          (current ++ [(wall, false)]) neg)

/-- Recursive global checker for four-triangle payload trees. -/
def checkTreeAux4 {H m : ℕ} (maxDepth : ℕ)
    (polyForPath : List (SignedIndex H) → RationalPolyhedron 4 m)
    (target : ℚ) : List (SignedIndex H) → Tree4 H m → Bool
  | current, .leaf payload =>
      decide (current.length ≤ maxDepth) &&
        check4 (polyForPath current) target payload
  | current, .branch wall pos neg =>
      decide (current.length < maxDepth) &&
        (checkTreeAux4 maxDepth polyForPath target
          (current ++ [(wall, true)]) pos &&
        checkTreeAux4 maxDepth polyForPath target
          (current ++ [(wall, false)]) neg)

def checkTree3 {H m : ℕ} (maxDepth : ℕ)
    (polyForPath : List (SignedIndex H) → RationalPolyhedron 3 m)
    (target : ℚ) (tree : Tree3 H m) : Bool :=
  checkTreeAux3 maxDepth polyForPath target [] tree

def checkTree4 {H m : ℕ} (maxDepth : ℕ)
    (polyForPath : List (SignedIndex H) → RationalPolyhedron 4 m)
    (target : ℚ) (tree : Tree4 H m) : Bool :=
  checkTreeAux4 maxDepth polyForPath target [] tree

private theorem checkTreeAux3_sound {H m : ℕ} {maxDepth : ℕ}
    {walls : Fin H → RationalAffine 3}
    {polyForPath : List (SignedIndex H) → RationalPolyhedron 3 m}
    {target : ℚ} {Base : (Fin 3 → ℝ) → Prop}
    (hcarrier : ∀ p path, path.length ≤ maxDepth →
      PathNonnegative walls p path → Base p →
      p ∈ (polyForPath path).carrier)
    {current : List (SignedIndex H)} {tree : Tree3 H m}
    (hcheck : checkTreeAux3 maxDepth polyForPath target current tree = true)
    {p : Fin 3 → ℝ} (hpath : PathNonnegative walls p current)
    (hbase : Base p) : (target : ℝ) ≤ unionArea 3 p := by
  induction tree generalizing current with
  | leaf payload =>
      simp only [checkTreeAux3, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      exact sound3 hcheck.2 p (hcarrier p current hcheck.1 hpath hbase)
  | branch wall pos neg ihpos ihneg =>
      simp only [checkTreeAux3, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      by_cases hw : 0 ≤ (walls wall).eval p
      · apply ihpos hcheck.2.1
        apply pathNonnegative_append hpath (wall, true)
        simpa [signedWallEval] using hw
      · apply ihneg hcheck.2.2
        apply pathNonnegative_append hpath (wall, false)
        simp only [signedWallEval, Bool.false_eq_true, ↓reduceIte]
        exact neg_nonneg.mpr (le_of_not_ge hw)

private theorem checkTreeAux4_sound {H m : ℕ} {maxDepth : ℕ}
    {walls : Fin H → RationalAffine 4}
    {polyForPath : List (SignedIndex H) → RationalPolyhedron 4 m}
    {target : ℚ} {Base : (Fin 4 → ℝ) → Prop}
    (hcarrier : ∀ p path, path.length ≤ maxDepth →
      PathNonnegative walls p path → Base p →
      p ∈ (polyForPath path).carrier)
    {current : List (SignedIndex H)} {tree : Tree4 H m}
    (hcheck : checkTreeAux4 maxDepth polyForPath target current tree = true)
    {p : Fin 4 → ℝ} (hpath : PathNonnegative walls p current)
    (hbase : Base p) : (target : ℝ) ≤ unionArea 4 p := by
  induction tree generalizing current with
  | leaf payload =>
      simp only [checkTreeAux4, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      exact sound4 hcheck.2 p (hcarrier p current hcheck.1 hpath hbase)
  | branch wall pos neg ihpos ihneg =>
      simp only [checkTreeAux4, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      by_cases hw : 0 ≤ (walls wall).eval p
      · apply ihpos hcheck.2.1
        apply pathNonnegative_append hpath (wall, true)
        simpa [signedWallEval] using hw
      · apply ihneg hcheck.2.2
        apply pathNonnegative_append hpath (wall, false)
        simp only [signedWallEval, Bool.false_eq_true, ↓reduceIte]
        exact neg_nonneg.mpr (le_of_not_ge hw)

/-- Direct coverage theorem for a globally checked three-triangle tree.
`Base` packages the generated cube and gauge hypotheses; `hcarrier` is the
single generic bridge from those hypotheses and a signed path to the padded
leaf polyhedron. -/
theorem checkTree3_sound {H m : ℕ} {maxDepth : ℕ}
    {walls : Fin H → RationalAffine 3}
    {polyForPath : List (SignedIndex H) → RationalPolyhedron 3 m}
    {target : ℚ} {tree : Tree3 H m} {Base : (Fin 3 → ℝ) → Prop}
    (hcarrier : ∀ p path, path.length ≤ maxDepth →
      PathNonnegative walls p path → Base p →
      p ∈ (polyForPath path).carrier)
    (hcheck : checkTree3 maxDepth polyForPath target tree = true) :
    ∀ p, Base p → (target : ℝ) ≤ unionArea 3 p := by
  intro p hbase
  apply checkTreeAux3_sound hcarrier hcheck (p := p) (hbase := hbase)
  simp [PathNonnegative]

/-- Direct coverage theorem for a globally checked four-triangle tree. -/
theorem checkTree4_sound {H m : ℕ} {maxDepth : ℕ}
    {walls : Fin H → RationalAffine 4}
    {polyForPath : List (SignedIndex H) → RationalPolyhedron 4 m}
    {target : ℚ} {tree : Tree4 H m} {Base : (Fin 4 → ℝ) → Prop}
    (hcarrier : ∀ p path, path.length ≤ maxDepth →
      PathNonnegative walls p path → Base p →
      p ∈ (polyForPath path).carrier)
    (hcheck : checkTree4 maxDepth polyForPath target tree = true) :
    ∀ p, Base p → (target : ℝ) ≤ unionArea 4 p := by
  intro p hbase
  apply checkTreeAux4_sound hcarrier hcheck (p := p) (hbase := hbase)
  simp [PathNonnegative]

/-! A closed `native_decide` smoke test for the empty-leaf path and the
single-global-check extraction interface. -/

private def impossible3 : RationalPolyhedron 3 1 where
  constraint := fun _ ↦ { constant := -1, linear := fun _ ↦ 0 }

private def impossibleCertificate : SparseFarkasCertificate 1 where
  terms := [(0, 1)]

private def impossibleLeaf3 : Leaf3 1 := .empty impossibleCertificate

example : check3 impossible3 (5 / 18) impossibleLeaf3 = true := by
  native_decide

example : checkAll3 impossible3 (5 / 18)
    [impossibleLeaf3, impossibleLeaf3] = true := by
  native_decide

private def impossiblePolyForPath
    (_ : List (SignedIndex 1)) : RationalPolyhedron 3 1 := impossible3

private def impossibleTree3 : Tree3 1 1 :=
  .branch 0 (.leaf impossibleLeaf3) (.leaf impossibleLeaf3)

example : checkTree3 1 impossiblePolyForPath (5 / 18) impossibleTree3 = true := by
  native_decide

end LeafCertificate

end KakeyaNeedleC3C4
