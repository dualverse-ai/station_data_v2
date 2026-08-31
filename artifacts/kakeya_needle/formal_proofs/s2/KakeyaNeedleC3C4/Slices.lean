import KakeyaNeedleC3C4.Definitions

namespace KakeyaNeedleC3C4

open Set MeasureTheory
open scoped ENNReal

noncomputable section

theorem leftEndpoint_continuous (n : ℕ) (x : Fin n → ℝ) (j : Fin n) :
    Continuous (leftEndpoint n x j) := by
  unfold leftEndpoint
  fun_prop

theorem rightEndpoint_continuous (n : ℕ) (x : Fin n → ℝ) (j : Fin n) :
    Continuous (rightEndpoint n x j) := by
  unfold rightEndpoint
  fun_prop

theorem measurableSet_triangle (n : ℕ) (x : Fin n → ℝ) (j : Fin n) :
    MeasurableSet (triangle n x j) := by
  unfold triangle
  change MeasurableSet (({p : ℝ × ℝ | (0 : ℝ) ≤ p.1} ∩
    {p | p.1 ≤ (1 : ℝ)}) ∩
    ({p | leftEndpoint n x j p.1 ≤ p.2} ∩
    {p | p.2 ≤ rightEndpoint n x j p.1}))
  exact (measurableSet_le measurable_const measurable_fst |>.inter
    (measurableSet_le measurable_fst measurable_const)).inter
    ((measurableSet_le
      ((leftEndpoint_continuous n x j).measurable.comp measurable_fst)
      measurable_snd).inter
    (measurableSet_le measurable_snd
      ((rightEndpoint_continuous n x j).measurable.comp measurable_fst)))

theorem measurableSet_triangleUnion (n : ℕ) (x : Fin n → ℝ) :
    MeasurableSet (triangleUnion n x) := by
  unfold triangleUnion
  exact MeasurableSet.iUnion fun j => measurableSet_triangle n x j

theorem measurableSet_sliceUnion (n : ℕ) (x : Fin n → ℝ) (y : ℝ) :
    MeasurableSet (sliceUnion n x y) := by
  unfold sliceUnion
  exact MeasurableSet.iUnion fun _ => measurableSet_Icc

/-- The horizontal section of the planar triangle union is exactly the union
of the intervals used by the arrangement certificate. -/
theorem mk_preimage_triangleUnion (n : ℕ) (x : Fin n → ℝ) (y : ℝ) :
    (fun u : ℝ => (y, u)) ⁻¹' triangleUnion n x =
      if y ∈ Icc (0 : ℝ) 1 then sliceUnion n x y else ∅ := by
  by_cases hy : y ∈ Icc (0 : ℝ) 1
  · rw [if_pos hy]
    ext u
    simp only [triangleUnion, triangle, sliceUnion, mem_preimage, mem_iUnion,
      mem_setOf_eq, mem_Icc]
    constructor
    · rintro ⟨j, _hy, hu⟩
      exact ⟨j, hu⟩
    · rintro ⟨j, hu⟩
      exact ⟨j, hy, hu⟩
  · rw [if_neg hy]
    ext u
    simp only [triangleUnion, triangle, mem_preimage, mem_iUnion, mem_setOf_eq,
      mem_Icc, mem_empty_iff_false, iff_false]
    rintro ⟨j, hy', _hu⟩
    exact hy hy'

theorem sliceUnion_volume_lt_top (n : ℕ) (x : Fin n → ℝ) (y : ℝ) :
    volume (sliceUnion n x y) < ∞ := by
  unfold sliceUnion
  calc
    volume (⋃ j : Fin n, Icc (leftEndpoint n x j y) (rightEndpoint n x j y)) ≤
        ∑ j ∈ Finset.univ, volume (Icc (leftEndpoint n x j y)
          (rightEndpoint n x j y)) := by
      simpa using MeasureTheory.measure_biUnion_finset_le (μ := volume) Finset.univ
        (fun j : Fin n => Icc (leftEndpoint n x j y) (rightEndpoint n x j y))
    _ < ∞ := by
      apply ENNReal.sum_lt_top.mpr
      intro j hj
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top

/-- Cavalieri/Fubini bridge: the genuine planar Lebesgue area equals the exact
horizontal-slice integral used in the paper and in the lower certificate. -/
theorem unionArea_eq_sliceArea (n : ℕ) (x : Fin n → ℝ) :
    unionArea n x = sliceArea n x := by
  rw [unionArea, sliceArea, measureReal_def, Measure.volume_eq_prod,
    Measure.prod_apply (measurableSet_triangleUnion n x)]
  let f : ℝ → ℝ≥0∞ :=
    fun y => volume ((fun u : ℝ => (y, u)) ⁻¹' triangleUnion n x)
  have hf_meas : Measurable f :=
    measurable_measure_prodMk_left (measurableSet_triangleUnion n x)
  have hf_top : ∀ y, f y < ∞ := by
    intro y
    rw [show f y = volume ((fun u : ℝ => (y, u)) ⁻¹' triangleUnion n x) by rfl,
      mk_preimage_triangleUnion]
    split_ifs
    · exact sliceUnion_volume_lt_top n x y
    · simp
  rw [← integral_toReal hf_meas.aemeasurable (Filter.Eventually.of_forall hf_top)]
  unfold f
  rw [← integral_indicator measurableSet_Icc]
  change (∫ y : ℝ, (volume ((fun u : ℝ => (y, u)) ⁻¹' triangleUnion n x)).toReal) =
    ∫ y : ℝ, (Icc (0 : ℝ) 1).indicator (sliceLength n x) y
  apply integral_congr_ae
  filter_upwards [] with y
  rw [mk_preimage_triangleUnion]
  by_cases hy : y ∈ Icc (0 : ℝ) 1
  · simp [hy, sliceLength, measureReal_def]
  · simp [hy]

end

end KakeyaNeedleC3C4
