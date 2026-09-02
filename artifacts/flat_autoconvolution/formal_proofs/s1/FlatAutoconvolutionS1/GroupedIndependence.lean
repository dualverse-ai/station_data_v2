import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian

/-!
# Independent functions of disjoint coordinate pairs

Each summand below is a measurable function of two base coordinates.  If the
coordinate blocks are pairwise disjoint, the current summand is independent
of the sum of its predecessors.  This is the independence fact needed for the
anti-diagonal Hoeffding argument; importantly, it does not replace mutual
independence by pairwise independence.
-/

open scoped BigOperators ENNReal
open MeasureTheory

namespace FlatAutoconvolutionS1.GroupedIndependence

open ProbabilityTheory

variable {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι]

/-- The two coordinate indices used by block `j`. -/
def block (left right : ℕ → ι) (j : ℕ) : Finset ι := {left j, right j}

/-- All coordinate indices used by blocks strictly before `n`. -/
def usedBefore (left right : ℕ → ι) (n : ℕ) : Finset ι :=
  (Finset.range n).biUnion (block left right)

/-- A measurable function of the two coordinates in block `j`. -/
def pairVar (X : ι → Ω → ℝ) (left right : ℕ → ι)
    (g : ℕ → ℝ × ℝ → ℝ) (j : ℕ) : Ω → ℝ :=
  fun ω ↦ g j (X (left j) ω, X (right j) ω)

theorem block_disjoint_usedBefore
    (left right : ℕ → ι)
    (hblocks : Pairwise fun j k ↦ Disjoint (block left right j) (block left right k))
    (n : ℕ) :
    Disjoint (block left right n) (usedBefore left right n) := by
  rw [usedBefore, Finset.disjoint_biUnion_right]
  intro j hj
  exact hblocks (Nat.ne_of_gt (Finset.mem_range.mp hj))

/-- A function of the current coordinate pair is independent of the sum of
measurable functions of all earlier, pairwise-disjoint coordinate pairs. -/
theorem pairVar_indep_sum_before
    {μ : Measure Ω} {X : ι → Ω → ℝ}
    (hX : iIndepFun X μ) (hXm : ∀ i, Measurable (X i))
    (left right : ℕ → ι)
    (hblocks : Pairwise fun j k ↦ Disjoint (block left right j) (block left right k))
    (g : ℕ → ℝ × ℝ → ℝ) (hg : ∀ j, Measurable (g j)) (n : ℕ) :
    pairVar X left right g n ⟂ᵢ[μ]
      (fun ω ↦ ∑ j ∈ Finset.range n, pairVar X left right g j ω) := by
  let S := block left right n
  let T := usedBefore left right n
  have hST : Disjoint S T := block_disjoint_usedBefore left right hblocks n
  have hInd := hX.indepFun_finset S T hST hXm

  have hleftS : left n ∈ S := by simp [S, block]
  have hrightS : right n ∈ S := by simp [S, block]
  let currentMap : (S → ℝ) → ℝ := fun z ↦
    g n (z ⟨left n, hleftS⟩, z ⟨right n, hrightS⟩)
  have hCurrentMap : Measurable currentMap := by
    dsimp [currentMap]
    apply (hg n).comp
    exact Measurable.prod
      (show Measurable (fun z : S → ℝ ↦ z (⟨left n, hleftS⟩ : S)) from
        measurable_pi_apply (⟨left n, hleftS⟩ : S))
      (show Measurable (fun z : S → ℝ ↦ z (⟨right n, hrightS⟩ : S)) from
        measurable_pi_apply (⟨right n, hrightS⟩ : S))

  have hleftT (j : ℕ) (hj : j ∈ Finset.range n) : left j ∈ T := by
    simp only [T, usedBefore, Finset.mem_biUnion]
    exact ⟨j, hj, by simp [block]⟩
  have hrightT (j : ℕ) (hj : j ∈ Finset.range n) : right j ∈ T := by
    simp only [T, usedBefore, Finset.mem_biUnion]
    exact ⟨j, hj, by simp [block]⟩
  let previousMap : (T → ℝ) → ℝ := fun z ↦
    ∑ j : Fin n,
      g j (z ⟨left j, hleftT j (Finset.mem_range.mpr j.isLt)⟩,
        z ⟨right j, hrightT j (Finset.mem_range.mpr j.isLt)⟩)
  have hPreviousMap : Measurable previousMap := by
    dsimp [previousMap]
    fun_prop

  have hComp := hInd.comp hCurrentMap hPreviousMap
  have hCurrentEq :
      currentMap ∘ (fun ω (i : S) ↦ X i ω) = pairVar X left right g n := by
    funext ω
    rfl
  have hPreviousEq :
      previousMap ∘ (fun ω (i : T) ↦ X i ω) =
        (fun ω ↦ ∑ j ∈ Finset.range n, pairVar X left right g j ω) := by
    funext ω
    simp only [previousMap, Function.comp_apply, pairVar, Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    simp [Finset.mem_range.mp hj]
  rw [hCurrentEq, hPreviousEq] at hComp
  exact hComp

/-- Additive sub-Gaussian parameter for a finite sum of measurable functions
of pairwise-disjoint coordinate pairs. -/
theorem hasSubgaussianMGF_sum_pairVar_range
    {μ : Measure Ω} {X : ι → Ω → ℝ}
    (hX : iIndepFun X μ) (hXm : ∀ i, Measurable (X i))
    (left right : ℕ → ι)
    (hblocks : Pairwise fun j k ↦ Disjoint (block left right j) (block left right k))
    (g : ℕ → ℝ × ℝ → ℝ) (hg : ∀ j, Measurable (g j))
    (c : ℕ → NNReal)
    (hsubG : ∀ j, HasSubgaussianMGF (pairVar X left right g j) (c j) μ) :
    ∀ n : ℕ,
      HasSubgaussianMGF
        (fun ω ↦ ∑ j ∈ Finset.range n, pairVar X left right g j ω)
        (∑ j ∈ Finset.range n, c j) μ := by
  letI := hX.isProbabilityMeasure
  intro n
  induction n with
  | zero =>
      simpa using (HasSubgaussianMGF.fun_zero (μ := μ))
  | succ n ih =>
      have hind := pairVar_indep_sum_before hX hXm left right hblocks g hg n
      have hadd := ih.add_of_indepFun (hsubG n) hind.symm
      simpa [Finset.sum_range_succ] using hadd

end FlatAutoconvolutionS1.GroupedIndependence
