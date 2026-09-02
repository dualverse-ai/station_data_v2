import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Flat autoconvolution: definitions

Concrete definitions corresponding to Section 2 of the verification notebook.
The ambient measure is Lebesgue measure on `ℝ`; `eLpNorm · ∞ volume` is the
essential-supremum norm, not a pointwise supremum.
-/

open scoped Convolution ENNReal BigOperators
open MeasureTheory Set Filter

namespace FlatAutoconvolutionS1

/-- A (representative of a) real-valued signal. -/
abbrev Signal := ℝ → ℝ

/-- Lebesgue autoconvolution. -/
noncomputable def autoconvolution (f : Signal) : Signal := f ⋆ f

/-- Squared `L²` norm of the autoconvolution (on the admissible domain). -/
noncomputable def convolutionEnergy (f : Signal) : ℝ :=
  ∫ x, (autoconvolution f x) ^ 2

/-- `L¹` norm of the autoconvolution. -/
noncomputable def convolutionMass (f : Signal) : ℝ :=
  ∫ x, |autoconvolution f x|

/-- Essential-supremum norm of the autoconvolution. -/
noncomputable def convolutionPeak (f : Signal) : ℝ :=
  (eLpNorm (autoconvolution f) ⊤ volume).toReal

/-- The flat-autoconvolution score from the paper.

The first two factors are written as Lebesgue integrals and the third is the
essential supremum. On admissible nonnegative functions these are exactly
`‖f*f‖₂²`, `‖f*f‖₁`, and `‖f*f‖∞`.
-/
noncomputable def score (f : Signal) : ℝ :=
  convolutionEnergy f / (convolutionMass f * convolutionPeak f)

/-- The paper's domain: nonnegative, nonzero (modulo a.e. equality), and in
both `L¹(ℝ)` and `L²(ℝ)`. -/
def Admissible (f : Signal) : Prop :=
  (0 ≤ᵐ[volume] f) ∧
  Integrable f ∧
  MemLp f 2 volume ∧
  0 < ∫ x, |f x|

/-- A finite nonnegative equal-grid step function. -/
structure EqualGridStep where
  cells : ℕ
  cells_pos : 0 < cells
  origin : ℝ
  mesh : ℝ
  mesh_pos : 0 < mesh
  weight : Fin cells → ℝ
  weight_nonneg : ∀ i, 0 ≤ weight i
  weight_nonzero : ∃ i, 0 < weight i

/-- The signal represented by a finite equal-grid step function. -/
noncomputable def EqualGridStep.toSignal (g : EqualGridStep) : Signal := fun x =>
  ∑ i : Fin g.cells,
    g.weight i * Set.indicator (Set.Ico
      (g.origin + (i : ℕ) * g.mesh)
      (g.origin + ((i : ℕ) + 1) * g.mesh)) (fun _ : ℝ => (1 : ℝ)) x

/-- A binary equal-grid step is the indicator of finitely many cells of one
grid. `selected_nonempty` excludes the zero function. -/
structure BinaryStep where
  cells : ℕ
  cells_pos : 0 < cells
  origin : ℝ
  mesh : ℝ
  mesh_pos : 0 < mesh
  selected : Fin cells → Bool
  selected_nonempty : ∃ i, selected i = true

/-- The signal represented by a binary equal-grid step. -/
noncomputable def BinaryStep.toSignal (b : BinaryStep) : Signal := fun x =>
  ∑ i : Fin b.cells,
    (if b.selected i then (1 : ℝ) else 0) * Set.indicator (Set.Ico
      (b.origin + (i : ℕ) * b.mesh)
      (b.origin + ((i : ℕ) + 1) * b.mesh)) (fun _ : ℝ => (1 : ℝ)) x

/-- The three score sets whose suprema occur in Theorem 2.1. -/
def unrestrictedScores : Set ℝ := {q | ∃ f, Admissible f ∧ score f = q}

def stepScores : Set ℝ := {q | ∃ g : EqualGridStep, score g.toSignal = q}

def binaryScores : Set ℝ := {q | ∃ b : BinaryStep, score b.toSignal = q}

/-- Supremum constants. -/
noncomputable def C : ℝ := sSup unrestrictedScores
noncomputable def Cstep : ℝ := sSup stepScores
noncomputable def C01 : ℝ := sSup binaryScores

end FlatAutoconvolutionS1
