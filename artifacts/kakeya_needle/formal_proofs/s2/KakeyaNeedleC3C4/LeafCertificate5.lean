import KakeyaNeedleC3C4.LeafCertificate
import KakeyaNeedleC3C4.SweepCertificate5

/-!
# Exact lower-bound leaves and decision trees for five intervals

The untrusted generator supplies only rational data.  These definitions reuse
the existing Farkas, Handelman, SOS, and structural-routing soundness layers.
-/

namespace KakeyaNeedleC3C4
namespace LeafCertificate

inductive Leaf5 (m : ℕ)
  | empty (certificate : SparseFarkasCertificate m)
  | live (sweep : SweepCertificate.Certificate5 m)
      (lower : HandelmanCertificate m)
  | liveSOS (sweep : SweepCertificate.Certificate5 m)
      (lower : SOSHandelmanCertificate 5 m)
  deriving DecidableEq

def check5 {m : ℕ} (P : RationalPolyhedron 5 m) (target : ℚ) :
    Leaf5 m → Bool
  | .empty certificate => certificate.checkInfeasible P
  | .live sweep lower =>
      SweepCertificate.check5 sweep P &&
      lower.checkCommutative P
        (SweepCertificate.integratedQuadratic5 sweep) target
  | .liveSOS sweep lower =>
      SweepCertificate.check5 sweep P &&
      lower.checkCommutative P
        (SweepCertificate.integratedQuadratic5 sweep) target

theorem sound5 {m : ℕ} {P : RationalPolyhedron 5 m} {target : ℚ}
    {leaf : Leaf5 m} (hcheck : check5 P target leaf = true) :
    ∀ p ∈ P.carrier, (target : ℝ) ≤ unionArea 5 p := by
  intro p hp
  cases leaf with
  | empty certificate =>
      have hempty : P.carrier = ∅ :=
        SparseFarkasCertificate.checkInfeasible_sound hcheck
      exfalso
      simp [hempty] at hp
  | live sweep lower =>
      simp only [check5, Bool.and_eq_true] at hcheck
      have hq : (target : ℝ) ≤
          (SweepCertificate.integratedQuadratic5 sweep).eval p :=
        HandelmanCertificate.checkCommutative_sound hcheck.2 p hp
      calc
        (target : ℝ) ≤
            (SweepCertificate.integratedQuadratic5 sweep).eval p := hq
        _ = sliceArea 5 p :=
          (SweepCertificate.sliceArea_eq_integratedQuadratic_five
            hcheck.1 hp).symm
        _ = unionArea 5 p := (unionArea_eq_sliceArea 5 p).symm
  | liveSOS sweep lower =>
      simp only [check5, Bool.and_eq_true] at hcheck
      have hq : (target : ℝ) ≤
          (SweepCertificate.integratedQuadratic5 sweep).eval p :=
        SOSHandelmanCertificate.checkCommutative_sound hcheck.2 p hp
      calc
        (target : ℝ) ≤
            (SweepCertificate.integratedQuadratic5 sweep).eval p := hq
        _ = sliceArea 5 p :=
          (SweepCertificate.sliceArea_eq_integratedQuadratic_five
            hcheck.1 hp).symm
        _ = unionArea 5 p := (unionArea_eq_sliceArea 5 p).symm

abbrev Tree5 (H m : ℕ) := PayloadTree H (Leaf5 m)

def checkTreeAux5 {H m : ℕ} (maxDepth : ℕ)
    (polyForPath : List (SignedIndex H) → RationalPolyhedron 5 m)
    (target : ℚ) : List (SignedIndex H) → Tree5 H m → Bool
  | current, .leaf payload =>
      decide (current.length ≤ maxDepth) &&
        check5 (polyForPath current) target payload
  | current, .branch wall pos neg =>
      decide (current.length < maxDepth) &&
        (checkTreeAux5 maxDepth polyForPath target
          (current ++ [(wall, true)]) pos &&
        checkTreeAux5 maxDepth polyForPath target
          (current ++ [(wall, false)]) neg)

def checkTree5 {H m : ℕ} (maxDepth : ℕ)
    (polyForPath : List (SignedIndex H) → RationalPolyhedron 5 m)
    (target : ℚ) (tree : Tree5 H m) : Bool :=
  checkTreeAux5 maxDepth polyForPath target [] tree

private theorem pathNonnegative_append5 {n H : ℕ}
    {walls : Fin H → RationalAffine n} {p : Fin n → ℝ}
    {path : List (SignedIndex H)} (hpath : PathNonnegative walls p path)
    (s : SignedIndex H) (hs : 0 ≤ signedWallEval walls p s) :
    PathNonnegative walls p (path ++ [s]) := by
  intro t ht
  simp only [List.mem_append, List.mem_singleton] at ht
  rcases ht with ht | rfl
  · exact hpath t ht
  · exact hs

private theorem checkTreeAux5_sound {H m : ℕ} {maxDepth : ℕ}
    {walls : Fin H → RationalAffine 5}
    {polyForPath : List (SignedIndex H) → RationalPolyhedron 5 m}
    {target : ℚ} {Base : (Fin 5 → ℝ) → Prop}
    (hcarrier : ∀ p path, path.length ≤ maxDepth →
      PathNonnegative walls p path → Base p →
      p ∈ (polyForPath path).carrier)
    {current : List (SignedIndex H)} {tree : Tree5 H m}
    (hcheck : checkTreeAux5 maxDepth polyForPath target current tree = true)
    {p : Fin 5 → ℝ} (hpath : PathNonnegative walls p current)
    (hbase : Base p) : (target : ℝ) ≤ unionArea 5 p := by
  induction tree generalizing current with
  | leaf payload =>
      simp only [checkTreeAux5, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      exact sound5 hcheck.2 p (hcarrier p current hcheck.1 hpath hbase)
  | branch wall pos neg ihpos ihneg =>
      simp only [checkTreeAux5, Bool.and_eq_true, decide_eq_true_eq] at hcheck
      by_cases hw : 0 ≤ (walls wall).eval p
      · apply ihpos hcheck.2.1
        apply pathNonnegative_append5 hpath (wall, true)
        simpa [signedWallEval] using hw
      · apply ihneg hcheck.2.2
        apply pathNonnegative_append5 hpath (wall, false)
        simp only [signedWallEval, Bool.false_eq_true, ↓reduceIte]
        exact neg_nonneg.mpr (le_of_not_ge hw)

theorem checkTree5_sound {H m : ℕ} {maxDepth : ℕ}
    {walls : Fin H → RationalAffine 5}
    {polyForPath : List (SignedIndex H) → RationalPolyhedron 5 m}
    {target : ℚ} {tree : Tree5 H m} {Base : (Fin 5 → ℝ) → Prop}
    (hcarrier : ∀ p path, path.length ≤ maxDepth →
      PathNonnegative walls p path → Base p →
      p ∈ (polyForPath path).carrier)
    (hcheck : checkTree5 maxDepth polyForPath target tree = true) :
    ∀ p, Base p → (target : ℝ) ≤ unionArea 5 p := by
  intro p hbase
  apply checkTreeAux5_sound hcarrier hcheck (p := p) (hbase := hbase)
  simp [PathNonnegative]

end LeafCertificate
end KakeyaNeedleC3C4
