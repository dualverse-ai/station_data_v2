import KakeyaNeedleC3C4.Slices

namespace KakeyaNeedleC3C4

open Set MeasureTheory

noncomputable section

/-- The exact three-triangle minimising configuration from the paper. -/
def witness3 : Fin 3 → ℝ := ![(2 : ℝ) / 9, (1 : ℝ) / 9, 0]

/-- A member of the exact four-triangle optimal family. -/
def witness4 : Fin 4 → ℝ := ![(1 : ℝ) / 4, (1 : ℝ) / 6, (1 : ℝ) / 12, 0]

private theorem sliceLength_le_of_subset {n : ℕ} {x : Fin n → ℝ} {y a b : ℝ}
    (h : sliceUnion n x y ⊆ Icc a b) :
    sliceLength n x y ≤ max (b - a) 0 := by
  unfold sliceLength
  calc
    volume.real (sliceUnion n x y) ≤ volume.real (Icc a b) :=
      measureReal_mono h (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    _ = max (b - a) 0 := by
      rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal']

private theorem sliceLength_le_sum (n : ℕ) (x : Fin n → ℝ) (y : ℝ) :
    sliceLength n x y ≤ ∑ j : Fin n, max (rightEndpoint n x j y -
      leftEndpoint n x j y) 0 := by
  unfold sliceLength sliceUnion
  calc
    volume.real (⋃ j : Fin n, Icc (leftEndpoint n x j y) (rightEndpoint n x j y)) ≤
        ∑ j : Fin n, volume.real (Icc (leftEndpoint n x j y)
          (rightEndpoint n x j y)) :=
      measureReal_iUnion_fintype_le _
    _ = ∑ j : Fin n, max (rightEndpoint n x j y - leftEndpoint n x j y) 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal']

private theorem witness3_first_cover {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 3) :
    sliceUnion 3 witness3 y ⊆ Icc y (5 / 9) := by
  intro u hu
  simp only [sliceUnion, mem_iUnion] at hu
  rcases hu with ⟨j, hj⟩
  fin_cases j <;>
    simp only [mem_Icc] at hj ⊢ <;>
    simp only [witness3, leftEndpoint, rightEndpoint, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue] at hj <;>
    norm_num at hj ⊢ <;> constructor <;> linarith

private theorem witness3_middle_cover {y : ℝ} (hy : 1 / 3 ≤ y) (hy1 : y ≤ 1) :
    sliceUnion 3 witness3 y ⊆ Icc (2 / 9 + y / 3) (1 / 3 + 2 * y / 3) := by
  intro u hu
  simp only [sliceUnion, mem_iUnion] at hu
  rcases hu with ⟨j, hj⟩
  fin_cases j <;>
    simp only [mem_Icc] at hj ⊢ <;>
    simp only [witness3, leftEndpoint, rightEndpoint, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue] at hj <;>
    norm_num at hj ⊢ <;> constructor <;> linarith

private theorem witness4_first_cover {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 3) :
    sliceUnion 4 witness4 y ⊆ Icc y (1 / 2) := by
  intro u hu
  simp only [sliceUnion, mem_iUnion] at hu
  rcases hu with ⟨j, hj⟩
  fin_cases j <;>
    simp only [mem_Icc] at hj ⊢ <;>
    simp only [witness4, leftEndpoint, rightEndpoint, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue] at hj <;>
    norm_num at hj ⊢ <;> constructor <;> linarith

private theorem witness4_middle_cover {y : ℝ} (hy : 1 / 3 ≤ y) (hy1 : y ≤ 1) :
    sliceUnion 4 witness4 y ⊆ Icc (1 / 4 + y / 4) (1 / 4 + 3 * y / 4) := by
  intro u hu
  simp only [sliceUnion, mem_iUnion] at hu
  rcases hu with ⟨j, hj⟩
  fin_cases j <;>
    simp only [mem_Icc] at hj ⊢ <;>
    simp only [witness4, leftEndpoint, rightEndpoint, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue] at hj <;>
    norm_num at hj ⊢ <;> constructor <;> linarith

/-- A piecewise-affine upper envelope for the slices of `witness3`. -/
def witness3Bound (y : ℝ) : ℝ :=
  if y ≤ 1 / 3 then 5 / 9 - y else if y ≤ 2 / 3 then 1 / 9 + y / 3 else 1 - y

/-- A piecewise-affine upper envelope for the slices of `witness4`. -/
def witness4Bound (y : ℝ) : ℝ :=
  if y ≤ 1 / 3 then 1 / 2 - y else if y ≤ 2 / 3 then y / 2 else 1 - y

theorem sliceLength_witness3_le_bound {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    sliceLength 3 witness3 y ≤ witness3Bound y := by
  rcases hy with ⟨hy0, hy1⟩
  rw [witness3Bound]
  by_cases h₁ : y ≤ 1 / 3
  · rw [if_pos h₁]
    have h := sliceLength_le_of_subset (witness3_first_cover hy0 h₁)
    rw [max_eq_left (by linarith : 0 ≤ (5 / 9 : ℝ) - y)] at h
    exact h
  · rw [if_neg h₁]
    have h₁' : 1 / 3 ≤ y := le_of_not_ge h₁
    by_cases h₂ : y ≤ 2 / 3
    · rw [if_pos h₂]
      have h := sliceLength_le_of_subset (witness3_middle_cover h₁' hy1)
      rw [max_eq_left (by linarith : 0 ≤ (1 / 3 + 2 * y / 3) -
        (2 / 9 + y / 3))] at h
      linarith
    · rw [if_neg h₂]
      have h := sliceLength_le_sum 3 witness3 y
      have heq : ∀ j : Fin 3, max (rightEndpoint 3 witness3 j y -
          leftEndpoint 3 witness3 j y) 0 = (1 - y) / 3 := by
        intro j
        rw [max_eq_left]
        · unfold leftEndpoint rightEndpoint
          norm_num
          ring
        · unfold leftEndpoint rightEndpoint
          norm_num
          linarith
      simp_rw [heq] at h
      norm_num at h
      linarith

theorem sliceLength_witness4_le_bound {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    sliceLength 4 witness4 y ≤ witness4Bound y := by
  rcases hy with ⟨hy0, hy1⟩
  rw [witness4Bound]
  by_cases h₁ : y ≤ 1 / 3
  · rw [if_pos h₁]
    have h := sliceLength_le_of_subset (witness4_first_cover hy0 h₁)
    rw [max_eq_left (by linarith : 0 ≤ (1 / 2 : ℝ) - y)] at h
    exact h
  · rw [if_neg h₁]
    have h₁' : 1 / 3 ≤ y := le_of_not_ge h₁
    by_cases h₂ : y ≤ 2 / 3
    · rw [if_pos h₂]
      have h := sliceLength_le_of_subset (witness4_middle_cover h₁' hy1)
      rw [max_eq_left (by linarith : 0 ≤ (1 / 4 + 3 * y / 4) -
        (1 / 4 + y / 4))] at h
      linarith
    · rw [if_neg h₂]
      have h := sliceLength_le_sum 4 witness4 y
      have heq : ∀ j : Fin 4, max (rightEndpoint 4 witness4 j y -
          leftEndpoint 4 witness4 j y) 0 = (1 - y) / 4 := by
        intro j
        rw [max_eq_left]
        · unfold leftEndpoint rightEndpoint
          norm_num
          ring
        · unfold leftEndpoint rightEndpoint
          norm_num
          linarith
      simp_rw [heq] at h
      norm_num at h
      linarith

private theorem continuous_witness3Bound : Continuous witness3Bound := by
  have hinner : Continuous (fun y : ℝ =>
      if y ≤ 2 / 3 then 1 / 9 + y / 3 else 1 - y) := by
    apply continuous_if_le continuous_id continuous_const (by fun_prop) (by fun_prop)
    intro y hy
    norm_num at hy ⊢
    linarith
  unfold witness3Bound
  apply Continuous.if_le (by fun_prop) hinner continuous_id continuous_const
  intro y hy
  norm_num at hy ⊢
  simp [show y ≤ (2 / 3 : ℝ) by linarith]
  linarith

private theorem continuous_witness4Bound : Continuous witness4Bound := by
  have hinner : Continuous (fun y : ℝ =>
      if y ≤ 2 / 3 then y / 2 else 1 - y) := by
    apply continuous_if_le continuous_id continuous_const (by fun_prop) (by fun_prop)
    intro y hy
    norm_num at hy ⊢
    linarith
  unfold witness4Bound
  apply Continuous.if_le (by fun_prop) hinner continuous_id continuous_const
  intro y hy
  norm_num at hy ⊢
  simp [show y ≤ (2 / 3 : ℝ) by linarith]
  linarith

private theorem measurable_indicator_sliceLength (n : ℕ) (x : Fin n → ℝ) :
    Measurable ((Icc (0 : ℝ) 1).indicator (sliceLength n x)) := by
  have hm : Measurable (fun y : ℝ =>
      (volume ((fun u : ℝ => (y, u)) ⁻¹' triangleUnion n x)).toReal) :=
    (measurable_measure_prodMk_left (measurableSet_triangleUnion n x)).ennreal_toReal
  have heq : (Icc (0 : ℝ) 1).indicator (sliceLength n x) = fun y : ℝ =>
      (volume ((fun u : ℝ => (y, u)) ⁻¹' triangleUnion n x)).toReal := by
    funext y
    rw [mk_preimage_triangleUnion]
    by_cases hy : y ∈ Icc (0 : ℝ) 1
    · simp [hy, sliceLength, measureReal_def]
    · simp [hy]
  rw [heq]
  exact hm

private theorem integral_witness3Bound :
    ∫ y in Icc (0 : ℝ) 1, witness3Bound y = 5 / 18 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hi₁ : IntervalIntegrable witness3Bound volume 0 (1 / 3) :=
    continuous_witness3Bound.intervalIntegrable _ _
  have hi₂ : IntervalIntegrable witness3Bound volume (1 / 3) (2 / 3) :=
    continuous_witness3Bound.intervalIntegrable _ _
  have hi₃ : IntervalIntegrable witness3Bound volume (2 / 3) 1 :=
    continuous_witness3Bound.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi₁.trans hi₂) hi₃,
    ← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂]
  have h₁ : (∫ y : ℝ in 0..(1 / 3), witness3Bound y) = 7 / 54 := by
    rw [intervalIntegral.integral_congr (g := fun y : ℝ => 5 / 9 - y) (by
      intro y hy
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 3)] at hy
      rw [witness3Bound, if_pos hy.2])]
    rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id]
    norm_num
  have h₂ : (∫ y : ℝ in (1 / 3)..(2 / 3), witness3Bound y) = 5 / 54 := by
    rw [intervalIntegral.integral_congr (g := fun y : ℝ => 1 / 9 + y / 3) (by
      intro y hy
      rw [uIcc_of_le (by norm_num : (1 / 3 : ℝ) ≤ 2 / 3)] at hy
      by_cases he : y ≤ 1 / 3
      · have : y = 1 / 3 := le_antisymm he hy.1
        subst y
        norm_num [witness3Bound]
      · rw [witness3Bound, if_neg he, if_pos hy.2])]
    norm_num [intervalIntegral.integral_add]
  have h₃ : (∫ y : ℝ in (2 / 3)..1, witness3Bound y) = 1 / 18 := by
    rw [intervalIntegral.integral_congr (g := fun y : ℝ => 1 - y) (by
      intro y hy
      rw [uIcc_of_le (by norm_num : (2 / 3 : ℝ) ≤ 1)] at hy
      by_cases he : y ≤ 2 / 3
      · have : y = 2 / 3 := le_antisymm he hy.1
        subst y
        norm_num [witness3Bound]
      · rw [witness3Bound, if_neg (by linarith : ¬y ≤ (1 / 3 : ℝ)), if_neg he])]
    rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id]
    norm_num
  rw [h₁, h₂, h₃]
  norm_num

private theorem integral_witness4Bound :
    ∫ y in Icc (0 : ℝ) 1, witness4Bound y = 1 / 4 := by
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hi₁ : IntervalIntegrable witness4Bound volume 0 (1 / 3) :=
    continuous_witness4Bound.intervalIntegrable _ _
  have hi₂ : IntervalIntegrable witness4Bound volume (1 / 3) (2 / 3) :=
    continuous_witness4Bound.intervalIntegrable _ _
  have hi₃ : IntervalIntegrable witness4Bound volume (2 / 3) 1 :=
    continuous_witness4Bound.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi₁.trans hi₂) hi₃,
    ← intervalIntegral.integral_add_adjacent_intervals hi₁ hi₂]
  have h₁ : (∫ y : ℝ in 0..(1 / 3), witness4Bound y) = 1 / 9 := by
    rw [intervalIntegral.integral_congr (g := fun y : ℝ => 1 / 2 - y) (by
      intro y hy
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 3)] at hy
      rw [witness4Bound, if_pos hy.2])]
    rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id]
    norm_num
  have h₂ : (∫ y : ℝ in (1 / 3)..(2 / 3), witness4Bound y) = 1 / 12 := by
    rw [intervalIntegral.integral_congr (g := fun y : ℝ => y / 2) (by
      intro y hy
      rw [uIcc_of_le (by norm_num : (1 / 3 : ℝ) ≤ 2 / 3)] at hy
      by_cases he : y ≤ 1 / 3
      · have : y = 1 / 3 := le_antisymm he hy.1
        subst y
        norm_num [witness4Bound]
      · rw [witness4Bound, if_neg he, if_pos hy.2])]
    norm_num
  have h₃ : (∫ y : ℝ in (2 / 3)..1, witness4Bound y) = 1 / 18 := by
    rw [intervalIntegral.integral_congr (g := fun y : ℝ => 1 - y) (by
      intro y hy
      rw [uIcc_of_le (by norm_num : (2 / 3 : ℝ) ≤ 1)] at hy
      by_cases he : y ≤ 2 / 3
      · have : y = 2 / 3 := le_antisymm he hy.1
        subst y
        norm_num [witness4Bound]
      · rw [witness4Bound, if_neg (by linarith : ¬y ≤ (1 / 3 : ℝ)), if_neg he])]
    rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id]
    norm_num
  rw [h₁, h₂, h₃]
  norm_num

private theorem witness3Bound_nonneg {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ witness3Bound y := by
  rcases hy with ⟨hy0, hy1⟩
  rw [witness3Bound]
  split_ifs with h₁ h₂
  · linarith
  · linarith
  · linarith

private theorem witness4Bound_nonneg {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    0 ≤ witness4Bound y := by
  rcases hy with ⟨hy0, hy1⟩
  rw [witness4Bound]
  split_ifs with h₁ h₂
  · linarith
  · linarith
  · linarith

/-- The paper's exact three-triangle configuration has area at most `5/18`. -/
theorem unionArea_witness3_le : unionArea 3 witness3 ≤ 5 / 18 := by
  rw [unionArea_eq_sliceArea, sliceArea]
  have hg : IntegrableOn witness3Bound (Icc (0 : ℝ) 1) :=
    continuous_witness3Bound.integrableOn_Icc
  have hf : IntegrableOn (sliceLength 3 witness3) (Icc (0 : ℝ) 1) := by
    rw [← integrable_indicator_iff measurableSet_Icc]
    refine (hg.integrable_indicator measurableSet_Icc).mono'
      (measurable_indicator_sliceLength 3 witness3).aestronglyMeasurable ?_
    filter_upwards [] with y
    by_cases hy : y ∈ Icc (0 : ℝ) 1
    · simp only [indicator_of_mem hy, Real.norm_eq_abs]
      have hs : 0 ≤ sliceLength 3 witness3 y := by
        unfold sliceLength
        exact measureReal_nonneg
      rw [abs_of_nonneg hs]
      exact sliceLength_witness3_le_bound hy
    · simp [hy]
  calc
    (∫ y in Icc (0 : ℝ) 1, sliceLength 3 witness3 y) ≤
        ∫ y in Icc (0 : ℝ) 1, witness3Bound y := by
      apply integral_mono_ae hf hg
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      exact sliceLength_witness3_le_bound hy
    _ = 5 / 18 := integral_witness3Bound

/-- The paper's exact four-triangle configuration has area at most `1/4`. -/
theorem unionArea_witness4_le : unionArea 4 witness4 ≤ 1 / 4 := by
  rw [unionArea_eq_sliceArea, sliceArea]
  have hg : IntegrableOn witness4Bound (Icc (0 : ℝ) 1) :=
    continuous_witness4Bound.integrableOn_Icc
  have hf : IntegrableOn (sliceLength 4 witness4) (Icc (0 : ℝ) 1) := by
    rw [← integrable_indicator_iff measurableSet_Icc]
    refine (hg.integrable_indicator measurableSet_Icc).mono'
      (measurable_indicator_sliceLength 4 witness4).aestronglyMeasurable ?_
    filter_upwards [] with y
    by_cases hy : y ∈ Icc (0 : ℝ) 1
    · simp only [indicator_of_mem hy, Real.norm_eq_abs]
      have hs : 0 ≤ sliceLength 4 witness4 y := by
        unfold sliceLength
        exact measureReal_nonneg
      rw [abs_of_nonneg hs]
      exact sliceLength_witness4_le_bound hy
    · simp [hy]
  calc
    (∫ y in Icc (0 : ℝ) 1, sliceLength 4 witness4 y) ≤
        ∫ y in Icc (0 : ℝ) 1, witness4Bound y := by
      apply integral_mono_ae hf hg
      filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
      exact sliceLength_witness4_le_bound hy
    _ = 1 / 4 := integral_witness4Bound

end

end KakeyaNeedleC3C4
