import KakeyaNeedleC3C4.Generated.DecisionTree5
import KakeyaNeedleC3C4.Generated.WitnessCertificates5
import KakeyaNeedleC3C4.TranslationGauge

/-!
# Reflection symmetry and its first forced breaking at n=5

This module formalizes notebook Theorem 3.5, Proposition 3.6, and Corollary
3.7.  The unrestricted value C_T 5 is deliberately not asserted.
-/

namespace KakeyaNeedleC3C4

open Generated
noncomputable section

/-- The notebook's reflection action specialized to five offsets. -/
def reflectOffsets5 (C : ℝ) (x : Fin 5 → ℝ) (j : Fin 5) : ℝ :=
  C - x j.rev

/-- A configuration is reflection-fixed when all reflected pair sums agree. -/
def ReflectionFixed5 (x : Fin 5 → ℝ) : Prop :=
  ∃ C, ∀ j, x j = reflectOffsets5 C x j

/-- The exact two-parameter fixed locus in the gauge x_5=0. -/
def fixedOffsets5 (p : Fin 2 → ℝ) : Fin 5 → ℝ :=
  ![p 0, p 1, p 0 / 2, p 0 - p 1, 0]

theorem reflectionFixed5_iff_pair_sums (x : Fin 5 → ℝ) :
    ReflectionFixed5 x ↔ ∃ C, ∀ j, x j + x j.rev = C := by
  simp only [ReflectionFixed5, reflectOffsets5]
  constructor
  · rintro ⟨C, h⟩
    exact ⟨C, fun j ↦ by linarith [h j]⟩
  · rintro ⟨C, h⟩
    exact ⟨C, fun j ↦ by linarith [h j]⟩

/-- Every reflection-fixed configuration is a common translate of the
notebook's full unbounded (a,b) parameterization. -/
theorem reflectionFixed5_normal_form {x : Fin 5 → ℝ}
    (hx : ReflectionFixed5 x) :
    ∃ p : Fin 2 → ℝ, x = fun j ↦ fixedOffsets5 p j + x 4 := by
  rcases hx with ⟨C, hx⟩
  let p : Fin 2 → ℝ := ![x 0 - x 4, x 1 - x 4]
  refine ⟨p, funext fun j ↦ ?_⟩
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  fin_cases j <;>
    simp [fixedOffsets5, p, reflectOffsets5] at h0 h1 h2 ⊢ <;>
    linarith

namespace CertificateAssembly5

/-- The six equality inequalities used by every one of the 368 cell leaves. -/
def Base5 (p : Fin 5 → ℝ) : Prop :=
  ∀ i, 0 ≤ (symmetryGaugeConstraints5 i).eval p

theorem mem_polyForPath5 (p : Fin 5 → ℝ)
    (path : List (LeafCertificate.SignedIndex WallCount5))
    (_hdepth : path.length ≤ Depth5)
    (hpath : LeafCertificate.PathNonnegative walls5 p path)
    (hbase : Base5 p) : p ∈ (polyForPath5 path).carrier := by
  intro i
  refine Fin.addCases (m := Depth5) (n := 6) ?_ ?_ i
  · intro j
    simp only [polyForPath5, Fin.append_left]
    rw [pathConstraint5]
    cases hget : path[j.1]? with
    | none =>
        simp [SweepCertificate.affineConst, RationalAffine.eval]
    | some s =>
        obtain ⟨hj, hs⟩ := getElem?_eq_some_iff.mp hget
        have hmem : s ∈ path := by
          rw [← hs]
          exact List.getElem_mem hj
        have hsigned := hpath s hmem
        rcases s with ⟨w, positive⟩
        cases positive <;>
          simpa [signedWall5, LeafCertificate.signedWallEval,
            SweepCertificate.eval_affineNeg] using hsigned
  · intro j
    simpa [polyForPath5] using hbase j

theorem base5_fixedOffsets5 (p : Fin 2 → ℝ) : Base5 (fixedOffsets5 p) := by
  intro i
  fin_cases i <;>
    simp [symmetryGaugeConstraints5, fixedOffsets5,
      RationalAffine.eval, Fin.sum_univ_succ] <;>
    ring_nf
  all_goals exact le_rfl

/-- Semantic lower bound supplied by the decoded 37-wall, 368-cell tree. -/
theorem fixedOffsets5_lower (p : Fin 2 → ℝ) :
    (7 : ℝ) / 30 ≤ unionArea 5 (fixedOffsets5 p) := by
  have hchecked :
      ∀ q, Base5 q → (target5 : ℝ) ≤ unionArea 5 q :=
    CertificateDecoder.checkEncodedTree5_sound mem_polyForPath5
      encodedTree5_verified
  simpa [target5] using hchecked (fixedOffsets5 p) (base5_fixedOffsets5 p)

end CertificateAssembly5

/-- Lower half of notebook Theorem 3.5, covering the entire fixed locus. -/
theorem reflectionFixed5_lower {x : Fin 5 → ℝ} (hx : ReflectionFixed5 x) :
    (7 : ℝ) / 30 ≤ unionArea 5 x := by
  obtain ⟨p, hp⟩ := reflectionFixed5_normal_form hx
  rw [hp, unionArea_add_const]
  exact CertificateAssembly5.fixedOffsets5_lower p

theorem witnessSym5_fixed : ReflectionFixed5 witnessSym5 := by
  refine ⟨(4 : ℝ) / 15, fun j ↦ ?_⟩
  fin_cases j <;>
    norm_num [reflectOffsets5, witnessSym5, witnessSym5Q, Fin.rev]

theorem fixedOffsets5_minimizer :
    witnessSym5 = fixedOffsets5 ![(4 : ℝ) / 15, (1 : ℝ) / 5] := by
  funext j
  fin_cases j <;>
    norm_num [witnessSym5, witnessSym5Q, fixedOffsets5]

/-- The set of all areas attained on the reflection-fixed locus. -/
def reflectionFixedAreas5 : Set ℝ :=
  {A | ∃ x, ReflectionFixed5 x ∧ unionArea 5 x = A}

/-- Notebook Theorem 3.5: the reflection-fixed n=5 minimum is exactly 7/30
and is attained by (4/15,1/5,2/15,1/15,0). -/
theorem theorem_3_5_reflection_fixed_minimum :
    IsLeast reflectionFixedAreas5 ((7 : ℝ) / 30) := by
  constructor
  · exact ⟨witnessSym5, witnessSym5_fixed, unionArea_witnessSym5⟩
  · rintro A ⟨x, hx, rfl⟩
    exact reflectionFixed5_lower hx

theorem witnessAsym5_not_fixed : ¬ ReflectionFixed5 witnessAsym5 := by
  rw [reflectionFixed5_iff_pair_sums]
  rintro ⟨C, hC⟩
  have h0 := hC 0
  have h1 := hC 1
  norm_num [witnessAsym5, witnessAsym5Q, Fin.rev] at h0 h1
  linarith

/-- Notebook Proposition 3.6: the displayed asymmetric configuration has
genuine planar union area exactly 14/61 and is not reflection-fixed. -/
theorem proposition_3_6_asymmetric_witness :
    unionArea 5 witnessAsym5 = (14 : ℝ) / 61 ∧
      ¬ ReflectionFixed5 witnessAsym5 :=
  ⟨unionArea_witnessAsym5, witnessAsym5_not_fixed⟩

/-- A configuration attaining the unrestricted global minimum, without
asserting that such a configuration exists. -/
def IsGlobalMinimizer5 (x : Fin 5 → ℝ) : Prop :=
  ∀ z : Fin 5 → ℝ, unionArea 5 x ≤ unionArea 5 z

/-- Notebook Corollary 3.7: every unrestricted n=5 global minimizer must
break reflection symmetry.  This does not determine C_T 5. -/
theorem corollary_3_7_forced_symmetry_breaking {x : Fin 5 → ℝ}
    (hx : IsGlobalMinimizer5 x) : ¬ ReflectionFixed5 x := by
  intro hfixed
  have hlower := reflectionFixed5_lower hfixed
  have hupper := hx witnessAsym5
  rw [unionArea_witnessAsym5] at hupper
  norm_num at hlower hupper
  linarith

end
end KakeyaNeedleC3C4
