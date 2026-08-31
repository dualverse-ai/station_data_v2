import KakeyaNeedleC3C4.Generated.DecisionTree3
import KakeyaNeedleC3C4.Generated.DecisionTree4
import KakeyaNeedleC3C4.CompactReduction

/-!
# Assembly of the checked finite lower certificates

The generated decision trees route every real parameter vector by weak affine
wall comparisons.  This file supplies the small handwritten bridge between a
structural tree path and the padded rational polyhedron checked at its leaf.
-/

namespace KakeyaNeedleC3C4

open Generated

namespace CertificateAssembly

/-- The compact-cube and translation-gauge constraints used after reducing
the three-triangle problem to two free parameters. -/
def Base3 (p : Fin 3 → ℝ) : Prop :=
  (∀ i, 0 ≤ (cubeConstraints3 i).eval p) ∧
  ∀ i, 0 ≤ (gaugeConstraints3 i).eval p

theorem mem_polyForPath3 (p : Fin 3 → ℝ)
    (path : List (LeafCertificate.SignedIndex WallCount3))
    (_hdepth : path.length ≤ Depth3)
    (hpath : LeafCertificate.PathNonnegative walls3 p path)
    (hbase : Base3 p) : p ∈ (polyForPath3 path).carrier := by
  intro i
  refine Fin.addCases (m := Depth3) (n := 6) ?_ ?_ i
  · intro i
    simp only [polyForPath3, Fin.append_left]
    rw [pathConstraint3]
    cases hget : path[i.1]? with
    | none =>
        simp [SweepCertificate.affineConst, RationalAffine.eval]
    | some s =>
        obtain ⟨hi, hs⟩ := getElem?_eq_some_iff.mp hget
        have hmem : s ∈ path := by
          rw [← hs]
          exact List.getElem_mem hi
        have hsigned := hpath s hmem
        rcases s with ⟨w, positive⟩
        cases positive <;>
          simpa [signedWall3, LeafCertificate.signedWallEval,
            SweepCertificate.eval_affineNeg] using hsigned
  · intro i
    refine Fin.addCases (m := 4) (n := 2) ?_ ?_ i
    · intro j
      simpa [polyForPath3] using hbase.1 j
    · intro j
      simpa [polyForPath3] using hbase.2 j

/-- The globally checked three-triangle tree gives the exact compact lower
bound for every full offset vector satisfying its cube and gauge constraints. -/
theorem compact_lower_three (p : Fin 3 → ℝ) (hp : Base3 p) :
    (5 : ℝ) / 18 ≤ unionArea 3 p := by
  simpa [target3] using
    LeafCertificate.checkTree3_sound mem_polyForPath3 tree3_verified p hp

theorem base3_offsets3 (p : Fin 2 → ℝ)
    (hcube : ∀ i, -1 ≤ p i ∧ p i ≤ 1) : Base3 (offsets3 p) := by
  have ho0 := offsets3_castSucc p (0 : Fin 2)
  have ho1 := offsets3_castSucc p (1 : Fin 2)
  have ho2 := offsets3_last p
  change offsets3 p (0 : Fin 3) = p 0 at ho0
  change offsets3 p (1 : Fin 3) = p 1 at ho1
  change offsets3 p (2 : Fin 3) = 0 at ho2
  constructor
  · intro i
    fin_cases i <;>
      simp [cubeConstraints3, RationalAffine.eval,
        ho0, ho1,
        Fin.sum_univ_succ] <;>
      linarith [((hcube 0).1), ((hcube 0).2), ((hcube 1).1), ((hcube 1).2)]
  · intro i
    fin_cases i <;>
      simp [gaugeConstraints3, RationalAffine.eval,
        ho0, ho1, ho2,
        Fin.sum_univ_succ]

/-- Exact lower bound for arbitrary (ungauged and unbounded) three-triangle
offsets. -/
theorem unionArea_three_lower (x : Fin 3 → ℝ) :
    (5 : ℝ) / 18 ≤ unionArea 3 x := by
  rw [unionArea_eq_offsets3_gauge]
  let p := gaugeParams3 x
  by_cases hout : ∃ i, p i < -1 ∨ 1 < p i
  · exact unionArea_offsets3_ge_of_outside_cube p hout
  · apply compact_lower_three
    apply base3_offsets3
    intro i
    constructor
    · exact le_of_not_gt (fun hi ↦ hout ⟨i, Or.inl hi⟩)
    · exact le_of_not_gt (fun hi ↦ hout ⟨i, Or.inr hi⟩)

/-- The compact-cube and translation-gauge constraints used after reducing
the four-triangle problem to three free parameters. -/
def Base4 (p : Fin 4 → ℝ) : Prop :=
  (∀ i, 0 ≤ (cubeConstraints4 i).eval p) ∧
  ∀ i, 0 ≤ (gaugeConstraints4 i).eval p

theorem mem_polyForPath4 (p : Fin 4 → ℝ)
    (path : List (LeafCertificate.SignedIndex WallCount4))
    (_hdepth : path.length ≤ Depth4)
    (hpath : LeafCertificate.PathNonnegative walls4 p path)
    (hbase : Base4 p) : p ∈ (polyForPath4 path).carrier := by
  intro i
  refine Fin.addCases (m := Depth4) (n := 8) ?_ ?_ i
  · intro i
    simp only [polyForPath4, Fin.append_left]
    rw [pathConstraint4]
    cases hget : path[i.1]? with
    | none =>
        simp [SweepCertificate.affineConst, RationalAffine.eval]
    | some s =>
        obtain ⟨hi, hs⟩ := getElem?_eq_some_iff.mp hget
        have hmem : s ∈ path := by
          rw [← hs]
          exact List.getElem_mem hi
        have hsigned := hpath s hmem
        rcases s with ⟨w, positive⟩
        cases positive <;>
          simpa [signedWall4, LeafCertificate.signedWallEval,
            SweepCertificate.eval_affineNeg] using hsigned
  · intro i
    refine Fin.addCases (m := 6) (n := 2) ?_ ?_ i
    · intro j
      simpa [polyForPath4] using hbase.1 j
    · intro j
      simpa [polyForPath4] using hbase.2 j

/-- The globally checked four-triangle tree gives the exact compact lower
bound for every full offset vector satisfying its cube and gauge constraints. -/
theorem compact_lower_four (p : Fin 4 → ℝ) (hp : Base4 p) :
    (1 : ℝ) / 4 ≤ unionArea 4 p := by
  simpa [target4] using
    LeafCertificate.checkTree4_sound mem_polyForPath4 tree4_verified p hp

theorem base4_offsets4 (p : Fin 3 → ℝ)
    (hcube : ∀ i, -1 ≤ p i ∧ p i ≤ 1) : Base4 (offsets4 p) := by
  have ho0 := offsets4_castSucc p (0 : Fin 3)
  have ho1 := offsets4_castSucc p (1 : Fin 3)
  have ho2 := offsets4_castSucc p (2 : Fin 3)
  have ho3 := offsets4_last p
  change offsets4 p (0 : Fin 4) = p 0 at ho0
  change offsets4 p (1 : Fin 4) = p 1 at ho1
  change offsets4 p (2 : Fin 4) = p 2 at ho2
  change offsets4 p (3 : Fin 4) = 0 at ho3
  constructor
  · intro i
    fin_cases i <;>
      simp [cubeConstraints4, RationalAffine.eval,
        ho0, ho1, ho2, Fin.sum_univ_succ] <;>
      linarith [((hcube 0).1), ((hcube 0).2), ((hcube 1).1),
        ((hcube 1).2), ((hcube 2).1), ((hcube 2).2)]
  · intro i
    fin_cases i <;>
      simp [gaugeConstraints4, RationalAffine.eval,
        ho0, ho1, ho2, ho3, Fin.sum_univ_succ]

/-- Exact lower bound for arbitrary (ungauged and unbounded) four-triangle
offsets. -/
theorem unionArea_four_lower (x : Fin 4 → ℝ) :
    (1 : ℝ) / 4 ≤ unionArea 4 x := by
  rw [unionArea_eq_offsets4_gauge]
  let p := gaugeParams4 x
  by_cases hout : ∃ i, p i < -1 ∨ 1 < p i
  · exact unionArea_offsets4_ge_of_outside_cube p hout
  · apply compact_lower_four
    apply base4_offsets4
    intro i
    constructor
    · exact le_of_not_gt (fun hi ↦ hout ⟨i, Or.inl hi⟩)
    · exact le_of_not_gt (fun hi ↦ hout ⟨i, Or.inr hi⟩)

end CertificateAssembly

end KakeyaNeedleC3C4
