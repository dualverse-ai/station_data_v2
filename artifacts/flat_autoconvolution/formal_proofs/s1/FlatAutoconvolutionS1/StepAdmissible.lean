import FlatAutoconvolutionS1.StepBasic

/-!
# Equal-grid steps belong to the unrestricted class
-/

open scoped ENNReal BigOperators
open MeasureTheory Set

namespace FlatAutoconvolutionS1

private def cell (g : EqualGridStep) (i : Fin g.cells) : Set ℝ :=
  Set.Ico (g.origin + (i : ℕ) * g.mesh)
    (g.origin + ((i : ℕ) + 1) * g.mesh)

private noncomputable def cellIndicator (g : EqualGridStep) (i : Fin g.cells) : Signal :=
  Set.indicator (cell g i) (fun _ : ℝ => (1 : ℝ))

private theorem cell_measurable (g : EqualGridStep) (i : Fin g.cells) :
    MeasurableSet (cell g i) := measurableSet_Ico

private theorem cell_measure_ne_top (g : EqualGridStep) (i : Fin g.cells) :
    volume (cell g i) ≠ ∞ := by
  simp [cell, Real.volume_Ico]

private theorem cellIndicator_integrable (g : EqualGridStep) (i : Fin g.cells) :
    Integrable (cellIndicator g i) := by
  exact (integrableOn_const (cell_measure_ne_top g i)).integrable_indicator
    (cell_measurable g i)

private theorem cellIndicator_memLp_two (g : EqualGridStep) (i : Fin g.cells) :
    MemLp (cellIndicator g i) 2 volume := by
  exact memLp_indicator_const 2 (cell_measurable g i) 1
    (Or.inr (cell_measure_ne_top g i))

private theorem integral_cellIndicator (g : EqualGridStep) (i : Fin g.cells) :
    ∫ x, cellIndicator g i x = g.mesh := by
  rw [show cellIndicator g i = (cell g i).indicator (fun _ : ℝ => 1) from rfl]
  rw [integral_indicator (cell_measurable g i)]
  rw [integral_const, measureReal_restrict_apply_univ]
  simp only [smul_eq_mul, mul_one, Measure.real, cell, Real.volume_Ico]
  rw [show g.origin + (↑↑i + 1) * g.mesh - (g.origin + ↑↑i * g.mesh) = g.mesh by ring]
  exact max_eq_left g.mesh_pos.le

theorem EqualGridStep.toSignal_nonneg (g : EqualGridStep) (x : ℝ) :
    0 ≤ g.toSignal x := by
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (g.weight_nonneg i) (Set.indicator_nonneg (fun _ _ => zero_le_one) x)

theorem EqualGridStep.toSignal_integrable (g : EqualGridStep) :
    Integrable g.toSignal := by
  apply integrable_finset_sum
  intro i _
  exact (cellIndicator_integrable g i).const_mul (g.weight i)

theorem EqualGridStep.toSignal_memLp_two (g : EqualGridStep) :
    MemLp g.toSignal 2 volume := by
  apply memLp_finset_sum
  intro i _
  exact (cellIndicator_memLp_two g i).const_mul (g.weight i)

theorem EqualGridStep.integral_abs_toSignal (g : EqualGridStep) :
    (∫ x, |g.toSignal x|) = g.mesh * ∑ i : Fin g.cells, g.weight i := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun x =>
    abs_of_nonneg (g.toSignal_nonneg x))]
  change (∫ x, ∑ i : Fin g.cells, g.weight i * cellIndicator g i x) = _
  rw [integral_finset_sum _ fun i _ =>
    (cellIndicator_integrable g i).const_mul (g.weight i)]
  simp_rw [integral_const_mul, integral_cellIndicator]
  rw [Finset.mul_sum]
  congr 1
  funext i
  ring

theorem EqualGridStep.integral_abs_toSignal_pos (g : EqualGridStep) :
    0 < ∫ x, |g.toSignal x| := by
  rw [g.integral_abs_toSignal]
  apply mul_pos g.mesh_pos
  obtain ⟨i, hi⟩ := g.weight_nonzero
  exact Finset.sum_pos' (fun j _ => g.weight_nonneg j) ⟨i, Finset.mem_univ i, hi⟩

theorem EqualGridStep.admissible (g : EqualGridStep) : Admissible g.toSignal :=
  ⟨Filter.Eventually.of_forall g.toSignal_nonneg, g.toSignal_integrable, g.toSignal_memLp_two,
    g.integral_abs_toSignal_pos⟩

theorem stepScores_subset_unrestrictedScores : stepScores ⊆ unrestrictedScores := by
  rintro q ⟨g, rfl⟩
  exact ⟨g.toSignal, g.admissible, rfl⟩

theorem binaryScores_subset_unrestrictedScores : binaryScores ⊆ unrestrictedScores :=
  binaryScores_subset_stepScores.trans stepScores_subset_unrestrictedScores

theorem unrestrictedScores_nonempty : unrestrictedScores.Nonempty :=
  binaryScores_nonempty.mono binaryScores_subset_unrestrictedScores

end FlatAutoconvolutionS1
