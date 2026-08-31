import KakeyaNeedleC3C4.TranslationGauge

namespace KakeyaNeedleC3C4

open Set MeasureTheory
open scoped ENNReal

noncomputable section

theorem mk_preimage_triangle (n : ℕ) (x : Fin n → ℝ) (j : Fin n) (y : ℝ) :
    (fun u : ℝ => (y, u)) ⁻¹' triangle n x j =
      if y ∈ Icc (0 : ℝ) 1 then
        Icc (leftEndpoint n x j y) (rightEndpoint n x j y) else ∅ := by
  by_cases hy : y ∈ Icc (0 : ℝ) 1
  · rw [if_pos hy]
    ext u
    simp only [triangle, mem_preimage, mem_setOf_eq, mem_Icc]
    exact ⟨fun h => h.2, fun h => ⟨hy, h⟩⟩
  · rw [if_neg hy]
    ext u
    simp only [triangle, mem_preimage, mem_setOf_eq, mem_Icc,
      mem_empty_iff_false, iff_false]
    exact fun h => hy h.1

/-- Every component triangle has the paper's normalized area `1/(2n)`,
independently of its horizontal offset and direction index. -/
theorem triangle_area (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) (j : Fin n) :
    volume.real (triangle n x j) = 1 / (2 * n : ℝ) := by
  rw [measureReal_def, Measure.volume_eq_prod,
    Measure.prod_apply (measurableSet_triangle n x j)]
  let f : ℝ → ℝ≥0∞ :=
    fun y => volume ((fun u : ℝ => (y, u)) ⁻¹' triangle n x j)
  have hf_meas : Measurable f :=
    measurable_measure_prodMk_left (measurableSet_triangle n x j)
  have hf_top : ∀ y, f y < ∞ := by
    intro y
    rw [show f y = volume ((fun u : ℝ => (y, u)) ⁻¹' triangle n x j) by rfl,
      mk_preimage_triangle]
    split_ifs
    · rw [Real.volume_Icc]
      exact ENNReal.ofReal_lt_top
    · simp
  rw [← integral_toReal hf_meas.aemeasurable (Filter.Eventually.of_forall hf_top)]
  unfold f
  calc
    (∫ y : ℝ, (volume ((fun u : ℝ => (y, u)) ⁻¹' triangle n x j)).toReal) =
        ∫ y : ℝ, (Icc (0 : ℝ) 1).indicator (fun y => (1 - y) / n) y := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [mk_preimage_triangle]
      by_cases hy : y ∈ Icc (0 : ℝ) 1
      · simp only [hy, if_true, indicator_of_mem]
        have hdiff : rightEndpoint n x j y - leftEndpoint n x j y =
            (1 - y) / n := by
          unfold leftEndpoint rightEndpoint
          have hn0 : (n : ℝ) ≠ 0 := by positivity
          field_simp
          simp only [Nat.cast_add, Nat.cast_one]
          ring
        rw [Real.volume_Icc, ENNReal.toReal_ofReal]
        · exact hdiff
        · rw [hdiff]
          exact div_nonneg (sub_nonneg.mpr hy.2) (Nat.cast_nonneg n)
      · simp [hy]
    _ = ∫ y in Icc (0 : ℝ) 1, (1 - y) / n :=
      integral_indicator measurableSet_Icc
    _ = 1 / (2 * n : ℝ) := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
      rw [intervalIntegral.integral_div]
      · rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_const
          intervalIntegral.intervalIntegrable_id]
        norm_num
        ring

theorem isClosed_triangle (n : ℕ) (x : Fin n → ℝ) (j : Fin n) :
    IsClosed (triangle n x j) := by
  unfold triangle
  change IsClosed (({p : ℝ × ℝ | (0 : ℝ) ≤ p.1} ∩
    {p | p.1 ≤ (1 : ℝ)}) ∩
    ({p | leftEndpoint n x j p.1 ≤ p.2} ∩
    {p | p.2 ≤ rightEndpoint n x j p.1}))
  exact ((isClosed_le continuous_const continuous_fst).inter
    (isClosed_le continuous_fst continuous_const)).inter
    ((isClosed_le ((leftEndpoint_continuous n x j).comp continuous_fst)
      continuous_snd).inter
    (isClosed_le continuous_snd ((rightEndpoint_continuous n x j).comp continuous_fst)))

theorem triangle_subset_rectangle (n : ℕ) (hn : 0 < n)
    (x : Fin n → ℝ) (j : Fin n) :
    triangle n x j ⊆ Icc (0 : ℝ) 1 ×ˢ Icc (x j - 1) (x j + 2) := by
  intro p hp
  refine ⟨hp.1, ?_⟩
  rcases hp with ⟨hy, hlo, hhi⟩
  constructor
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    unfold leftEndpoint at hlo
    have hcoef : 0 ≤ ((j.1 + 1 : ℕ) : ℝ) / n :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt hnR)
    have : x j ≤ x j + ((j.1 + 1 : ℕ) : ℝ) / n * p.1 :=
      le_add_of_nonneg_right (mul_nonneg hcoef hy.1)
    linarith
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hj : ((j.1 : ℝ) + 1) ≤ n := by exact_mod_cast j.2
    unfold rightEndpoint at hhi
    have hfrac : 1 / (n : ℝ) + (j.1 : ℝ) / n * p.1 ≤ 1 := by
      calc
        1 / (n : ℝ) + (j.1 : ℝ) / n * p.1 ≤
            1 / (n : ℝ) + (j.1 : ℝ) / n := by
              gcongr
              simpa using mul_le_mul_of_nonneg_left hy.2
                (div_nonneg (Nat.cast_nonneg j.1) (le_of_lt hnR))
        _ = ((j.1 : ℝ) + 1) / n := by field_simp; ring
        _ ≤ 1 := (div_le_one hnR).2 hj
    linarith

theorem isCompact_triangle (n : ℕ) (hn : 0 < n)
    (x : Fin n → ℝ) (j : Fin n) : IsCompact (triangle n x j) := by
  apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset (isClosed_triangle n x j)
  exact triangle_subset_rectangle n hn x j

theorem triangle_volume_lt_top (n : ℕ) (hn : 0 < n)
    (x : Fin n → ℝ) (j : Fin n) : volume (triangle n x j) < ∞ :=
  (isCompact_triangle n hn x j).measure_lt_top

end

end KakeyaNeedleC3C4
