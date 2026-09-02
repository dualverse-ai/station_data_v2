import FlatAutoconvolutionS1.Definitions

/-!
# Elementary relations between the step classes
-/

open Set

namespace FlatAutoconvolutionS1

/-- Forget that a binary step has only zero-one coefficients. -/
def BinaryStep.toEqualGridStep (b : BinaryStep) : EqualGridStep where
  cells := b.cells
  cells_pos := b.cells_pos
  origin := b.origin
  mesh := b.mesh
  mesh_pos := b.mesh_pos
  weight i := if b.selected i then 1 else 0
  weight_nonneg i := by split <;> simp
  weight_nonzero := by
    obtain ⟨i, hi⟩ := b.selected_nonempty
    exact ⟨i, by simp [hi]⟩

@[simp] theorem BinaryStep.toEqualGridStep_toSignal (b : BinaryStep) :
    b.toEqualGridStep.toSignal = b.toSignal := rfl

theorem binaryScores_subset_stepScores : binaryScores ⊆ stepScores := by
  rintro q ⟨b, rfl⟩
  exact ⟨b.toEqualGridStep, rfl⟩

/-- A concrete one-cell binary step, used to establish nonemptiness without
any supremum-attainment assumption. -/
def unitBinaryStep : BinaryStep where
  cells := 1
  cells_pos := by decide
  origin := 0
  mesh := 1
  mesh_pos := by norm_num
  selected := fun _ => true
  selected_nonempty := ⟨0, rfl⟩

theorem binaryScores_nonempty : binaryScores.Nonempty :=
  ⟨score unitBinaryStep.toSignal, unitBinaryStep, rfl⟩

theorem stepScores_nonempty : stepScores.Nonempty :=
  binaryScores_nonempty.mono binaryScores_subset_stepScores

end FlatAutoconvolutionS1
