import Mathlib
import FlatAutoconvolutionS1.ConvolutionL2
import FlatAutoconvolutionS1.FiniteProfile

open scoped Convolution ENNReal BigOperators
open MeasureTheory Set

noncomputable def unitCell : ℝ → ℝ := Set.indicator (Set.Ico 0 1) (fun _ ↦ 1)

example (t : ℝ) :
    (unitCell ⋆ unitCell) t = ∫ x in Set.Ico 0 1, unitCell (t - x) := by
  rw [MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, unitCell]
  rw [← MeasureTheory.integral_indicator measurableSet_Ico]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Set.Ico (0 : ℝ) 1
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

theorem integral_unitCell_sub_of_mem_Icc_zero_one (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ x in Set.Ico 0 1, unitCell (t - x)) = t := by
  have hx0 : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff, measure_singleton]
  have hxt : ∀ᵐ x : ℝ ∂volume, x ≠ t := by simp [ae_iff, measure_singleton]
  have heq : Set.indicator (Set.Ico 0 1) (fun x : ℝ ↦ unitCell (t - x)) =ᵐ[volume]
      Set.indicator (Set.Ioc 0 t) (fun _ ↦ (1 : ℝ)) := by
    filter_upwards [hx0, hxt] with x hx0' hxt'
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) t
    · rcases hx with ⟨hxpos, hxle⟩
      have hxmem : x ∈ Set.Ioc (0 : ℝ) t := ⟨hxpos, hxle⟩
      have hx_outer : x ∈ Set.Ico (0 : ℝ) 1 := by
        constructor
        · exact hxpos.le
        · by_contra hn
          have : 1 ≤ x := le_of_not_gt hn
          have htx : t ≤ x := by linarith
          exact hxt' (le_antisymm hxle htx)
      have harg : t - x ∈ Set.Ico (0 : ℝ) 1 := by
        constructor <;> linarith
      simp [Set.indicator_of_mem hxmem, Set.indicator_of_mem hx_outer,
        unitCell, Set.indicator_of_mem harg]
    · have hright : Set.indicator (Set.Ioc (0 : ℝ) t) (fun _ ↦ (1 : ℝ)) x = 0 :=
        Set.indicator_of_notMem hx _
      rw [hright]
      by_cases houter : x ∈ Set.Ico (0 : ℝ) 1
      · have hnotarg : t - x ∉ Set.Ico (0 : ℝ) 1 := by
          intro harg
          have hxle : x ≤ t := by linarith [harg.1]
          have hxpos : 0 < x := lt_of_le_of_ne houter.1 (Ne.symm hx0')
          exact hx ⟨hxpos, hxle⟩
        simp [Set.indicator_of_mem houter, unitCell, Set.indicator_of_notMem hnotarg]
      · simp [Set.indicator_of_notMem houter]
  rw [← MeasureTheory.integral_indicator measurableSet_Ico]
  rw [MeasureTheory.integral_congr_ae heq]
  simp [MeasureTheory.integral_indicator_const, ht0]

theorem integral_unitCell_sub_of_mem_Icc_one_two (t : ℝ) (ht1 : 1 ≤ t) (ht2 : t ≤ 2) :
    (∫ x in Set.Ico 0 1, unitCell (t - x)) = 2 - t := by
  have heq : Set.indicator (Set.Ico 0 1) (fun x : ℝ ↦ unitCell (t - x)) =
      Set.indicator (Set.Ioo (t - 1) 1) (fun _ ↦ (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ Set.Ioo (t - 1) 1
    · rcases hx with ⟨hxlo, hxhi⟩
      have hxmem : x ∈ Set.Ioo (t - 1) 1 := ⟨hxlo, hxhi⟩
      have hx_outer : x ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, hxhi⟩
      have harg : t - x ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
      simp [Set.indicator_of_mem hxmem, Set.indicator_of_mem hx_outer,
        unitCell, Set.indicator_of_mem harg]
    · have hright : Set.indicator (Set.Ioo (t - 1) 1) (fun _ ↦ (1 : ℝ)) x = 0 :=
        Set.indicator_of_notMem hx _
      rw [hright]
      by_cases houter : x ∈ Set.Ico (0 : ℝ) 1
      · have hnotarg : t - x ∉ Set.Ico (0 : ℝ) 1 := by
          intro harg
          apply hx
          exact ⟨by linarith [harg.2], houter.2⟩
        simp [Set.indicator_of_mem houter, unitCell, Set.indicator_of_notMem hnotarg]
      · simp [Set.indicator_of_notMem houter]
  rw [← MeasureTheory.integral_indicator measurableSet_Ico]
  rw [heq]
  rw [MeasureTheory.integral_indicator_const (1 : ℝ) measurableSet_Ioo]
  change (volume (Set.Ioo (t - 1) 1)).toReal * 1 = 2 - t
  rw [Real.volume_Ioo]
  rw [ENNReal.toReal_ofReal (by linarith)]
  ring

noncomputable def tent (t : ℝ) : ℝ :=
  if t ≤ 0 then 0 else if t ≤ 1 then t else if t ≤ 2 then 2 - t else 0

theorem unitCell_convolution (t : ℝ) : (unitCell ⋆ unitCell) t = tent t := by
  rw [show (unitCell ⋆ unitCell) t = ∫ x in Set.Ico 0 1, unitCell (t - x) from by
    rw [MeasureTheory.convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, unitCell]
    rw [← MeasureTheory.integral_indicator measurableSet_Ico]
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ Set.Ico (0 : ℝ) 1
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]]
  unfold tent
  split_ifs with h0 h1 h2
  · have hz : (∫ x in Set.Ico 0 1, unitCell (t - x)) = 0 := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ico]
      apply MeasureTheory.integral_eq_zero_of_ae
      have hxzero : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff, measure_singleton]
      filter_upwards [hxzero] with x hxzero'
      by_cases hx : x ∈ Set.Ico (0 : ℝ) 1
      · have harg : t - x ∉ Set.Ico (0 : ℝ) 1 := by
          intro ha
          have : x = 0 := by linarith [hx.1, ha.1]
          exact hxzero' this
        simp [Set.indicator_of_mem hx, unitCell, harg]
      · simp [Set.indicator_of_notMem hx]
    exact hz

  · exact integral_unitCell_sub_of_mem_Icc_zero_one t (lt_of_not_ge h0).le h1
  · exact integral_unitCell_sub_of_mem_Icc_one_two t (lt_of_not_ge h1).le h2
  · have hz : (∫ x in Set.Ico 0 1, unitCell (t - x)) = 0 := by
      rw [← MeasureTheory.integral_indicator measurableSet_Ico]
      apply MeasureTheory.integral_eq_zero_of_ae
      filter_upwards [] with x
      by_cases hx : x ∈ Set.Ico (0 : ℝ) 1
      · have harg : t - x ∉ Set.Ico (0 : ℝ) 1 := by
          intro ha
          linarith [hx.2, ha.2, lt_of_not_ge h2]
        simp [Set.indicator_of_mem hx, unitCell, harg]
      · simp [Set.indicator_of_notMem hx]
    exact hz

namespace FlatAutoconvolutionS1.Bridge

open FlatAutoconvolutionS1.Finite

noncomputable def shiftedUnitCell (i : ℕ) : ℝ → ℝ :=
  fun x ↦ unitCell (x - i)

theorem shiftedUnitCell_convolution (i j : ℕ) (x : ℝ) :
    (shiftedUnitCell i ⋆ shiftedUnitCell j) x = tent (x - i - j) := by
  let H : ℝ → ℝ := fun y ↦ unitCell y * unitCell ((x - i - j) - y)
  change (∫ t, unitCell (t - i) * unitCell (x - t - j)) = _
  calc
    (∫ t, unitCell (t - i) * unitCell (x - t - j)) =
        ∫ t, H (t + (-(i : ℝ))) := by
      apply integral_congr_ae
      filter_upwards [] with t
      dsimp [H]
      congr 2 <;> ring_nf
    _ = ∫ t, H t := integral_add_right_eq_self H (-(i : ℝ))
    _ = (unitCell ⋆ unitCell) (x - i - j) := by rfl
    _ = tent (x - i - j) := unitCell_convolution _

theorem shiftedUnitCell_eq_indicator (i : ℕ) :
    shiftedUnitCell i = Set.indicator (Set.Ico (i : ℝ) (i + 1 : ℝ)) (fun _ ↦ 1) := by
  funext x
  unfold shiftedUnitCell unitCell
  by_cases hx : x ∈ Set.Ico (i : ℝ) (i + 1 : ℝ)
  · have hy : x - (i : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by constructor <;> linarith [hx.1, hx.2]
    simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy]
  · have hy : x - (i : ℝ) ∉ Set.Ico (0 : ℝ) 1 := by
      intro hy
      apply hx
      constructor <;> linarith [hy.1, hy.2]
    simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hy]

theorem shiftedUnitCell_memLp_two (i : ℕ) : MemLp (shiftedUnitCell i) 2 volume := by
  rw [shiftedUnitCell_eq_indicator]
  apply memLp_indicator_const 2 measurableSet_Ico 1
  right
  simp [Real.volume_Ico]

noncomputable def coverSignal (m : ℕ) : ℝ → ℝ := fun x ↦
  ∑ k ∈ Finset.range m, shiftedUnitCell k x

theorem coverSignal_eq_indicator (m : ℕ) :
    coverSignal m = Set.indicator (Set.Ico (0 : ℝ) m) (fun _ ↦ 1) := by
  induction m with
  | zero =>
      funext x
      simp [coverSignal]
  | succ m ih =>
      funext x
      rw [show coverSignal (m + 1) x = coverSignal m x + shiftedUnitCell m x by
        simp [coverSignal, Finset.sum_range_succ]]
      rw [congrFun ih x, shiftedUnitCell_eq_indicator]
      by_cases h0 : 0 ≤ x
      · by_cases hm : x < (m : ℝ)
        · have hleft : x ∈ Set.Ico (0 : ℝ) m := ⟨h0, hm⟩
          have hcell : x ∉ Set.Ico (m : ℝ) (m + 1 : ℝ) := by
            intro hx
            linarith [hx.1]
          have hall : x ∈ Set.Ico (0 : ℝ) (m + 1 : ℝ) := by
            exact ⟨h0, hm.trans_le (by norm_num)⟩
          simp [Set.indicator_of_mem hleft, Set.indicator_of_notMem hcell,
            Set.indicator_of_mem hall]
        · by_cases hnext : x < (m + 1 : ℝ)
          · have hleft : x ∉ Set.Ico (0 : ℝ) m := by
              intro hx
              exact hm hx.2
            have hcell : x ∈ Set.Ico (m : ℝ) (m + 1 : ℝ) :=
              ⟨le_of_not_gt hm, hnext⟩
            have hall : x ∈ Set.Ico (0 : ℝ) (m + 1 : ℝ) := ⟨h0, hnext⟩
            simp [Set.indicator_of_notMem hleft, Set.indicator_of_mem hcell,
              Set.indicator_of_mem hall]
          · have hleft : x ∉ Set.Ico (0 : ℝ) m := by
              intro hx
              exact hm hx.2
            have hcell : x ∉ Set.Ico (m : ℝ) (m + 1 : ℝ) := by
              intro hx
              exact hnext hx.2
            have hall : x ∉ Set.Ico (0 : ℝ) (m + 1 : ℝ) := by
              intro hx
              exact hnext hx.2
            simp [Set.indicator_of_notMem hleft, Set.indicator_of_notMem hcell,
              Set.indicator_of_notMem hall]
      · have hleft : x ∉ Set.Ico (0 : ℝ) m := by
          intro hx
          exact h0 hx.1
        have hcell : x ∉ Set.Ico (m : ℝ) (m + 1 : ℝ) := by
          intro hx
          exact h0 (le_trans (Nat.cast_nonneg m) hx.1)
        have hall : x ∉ Set.Ico (0 : ℝ) (m + 1 : ℝ) := by
          intro hx
          exact h0 hx.1
        simp [Set.indicator_of_notMem hleft, Set.indicator_of_notMem hcell,
          Set.indicator_of_notMem hall]

theorem unitCell_nonneg (x : ℝ) : 0 ≤ unitCell x := by
  unfold unitCell
  by_cases hx : x ∈ Set.Ico (0 : ℝ) 1 <;> simp [hx]

theorem unitCell_integrable : Integrable unitCell volume := by
  rw [unitCell]
  apply (integrable_indicator_iff measurableSet_Ico).2
  exact integrableOn_const (by rw [Real.volume_Ico]; simp)

theorem integral_unitCell : (∫ x, unitCell x) = 1 := by
  rw [unitCell, MeasureTheory.integral_indicator_const (1 : ℝ) measurableSet_Ico]
  norm_num [Real.volume_Ico]

theorem coverSignal_nonneg (m : ℕ) (x : ℝ) : 0 ≤ coverSignal m x := by
  rw [coverSignal_eq_indicator]
  by_cases hx : x ∈ Set.Ico (0 : ℝ) m <;> simp [hx]

theorem coverSignal_le_one (m : ℕ) (x : ℝ) : coverSignal m x ≤ 1 := by
  rw [coverSignal_eq_indicator]
  by_cases hx : x ∈ Set.Ico (0 : ℝ) m <;> simp [hx]

theorem sum_microcells_eq_shiftedUnitCell (T : ℕ) (hT : 0 < T)
    (j : ℕ) (x : ℝ) :
    (∑ r : Fin T, shiftedUnitCell ((r : ℕ) + T * j) (T * x)) =
      shiftedUnitCell j x := by
  rw [Fin.sum_univ_eq_sum_range
    (fun r : ℕ ↦ shiftedUnitCell (r + T * j) (T * x)) T]
  calc
    (∑ r ∈ Finset.range T, shiftedUnitCell (r + T * j) (T * x)) =
        coverSignal T (T * (x - j)) := by
      rw [coverSignal]
      apply Finset.sum_congr rfl
      intro r hr
      unfold shiftedUnitCell
      congr 1
      push_cast
      ring
    _ = Set.indicator (Set.Ico (0 : ℝ) T) (fun _ ↦ 1) (T * (x - j)) := by
      rw [coverSignal_eq_indicator]
    _ = shiftedUnitCell j x := by
      rw [shiftedUnitCell_eq_indicator]
      have hTr : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT
      by_cases hx : x ∈ Set.Ico (j : ℝ) (j + 1 : ℝ)
      · have hscaled : T * (x - j) ∈ Set.Ico (0 : ℝ) T := by
          constructor <;> nlinarith [hTr, hx.1, hx.2]
        simp [Set.indicator_of_mem hx, Set.indicator_of_mem hscaled]
      · have hscaled : T * (x - j) ∉ Set.Ico (0 : ℝ) T := by
          intro hs
          apply hx
          constructor <;> nlinarith [hTr, hs.1, hs.2]
        simp [Set.indicator_of_notMem hx, Set.indicator_of_notMem hscaled]

/-- Repeat every coarse coefficient through a block of `T` microcells. -/
noncomputable def blockProfile {m : ℕ} (T : ℕ) (v : Profile m) : Profile (m * T) :=
  fun i ↦ v (finProdFinEquiv.symm i).1

/-- Integer translates of the triangular tent form a sub-partition of unity
when restricted to any finite consecutive range. -/
theorem sum_tent_range_le_one (m : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range m, tent (x - k)) ≤ 1 := by
  have hterm (k : ℕ) :
      tent (x - k) = ∫ t, unitCell t * shiftedUnitCell k (x - t) := by
    calc
      tent (x - k) = (shiftedUnitCell 0 ⋆ shiftedUnitCell k) x := by
        simpa using (shiftedUnitCell_convolution 0 k x).symm
      _ = ∫ t, unitCell t * shiftedUnitCell k (x - t) := by
        rw [MeasureTheory.convolution_def]
        apply integral_congr_ae
        filter_upwards [] with t
        simp [shiftedUnitCell]
  have hint (k : ℕ) : Integrable (fun t ↦ unitCell t * shiftedUnitCell k (x - t)) := by
    have h := convolutionExistsAt_of_memLp_two
      (shiftedUnitCell 0) (shiftedUnitCell k)
      (shiftedUnitCell_memLp_two 0) (shiftedUnitCell_memLp_two k) x
    exact h.congr (by
      filter_upwards [] with t
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      simp [shiftedUnitCell])
  calc
    (∑ k ∈ Finset.range m, tent (x - k)) =
        ∫ t, ∑ k ∈ Finset.range m, unitCell t * shiftedUnitCell k (x - t) := by
      simp_rw [hterm]
      exact (integral_finset_sum (Finset.range m) fun k _ ↦ hint k).symm
    _ = ∫ t, unitCell t * coverSignal m (x - t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp [coverSignal, Finset.mul_sum]
    _ ≤ ∫ t, unitCell t := by
      apply integral_mono_of_nonneg
      · filter_upwards [] with t
        exact mul_nonneg (unitCell_nonneg t) (coverSignal_nonneg m (x - t))
      · exact unitCell_integrable
      · filter_upwards [] with t
        nlinarith [unitCell_nonneg t, coverSignal_le_one m (x - t)]
    _ = 1 := integral_unitCell

noncomputable def profileSignal {n : ℕ} (w : Profile n) : Signal := fun x ↦
  ∑ i : Fin n, w i * shiftedUnitCell i x

/-- Spatial compression of a unit-grid profile by a positive scale factor. -/
noncomputable def scaledProfileSignal {n : ℕ} (T : ℝ) (w : Profile n) : Signal :=
  fun x ↦ profileSignal w (T * x)

theorem scaledProfileSignal_convolution {n : ℕ} (T : ℝ) (w : Profile n)
    (hT : 0 < T) (x : ℝ) :
    (scaledProfileSignal T w ⋆ scaledProfileSignal T w) x =
      T⁻¹ * (profileSignal w ⋆ profileSignal w) (T * x) := by
  let G : ℝ → ℝ := fun y ↦ profileSignal w y * profileSignal w (T * x - y)
  rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, scaledProfileSignal]
  calc
    (∫ t, profileSignal w (T * t) * profileSignal w (T * (x - t))) =
        ∫ t, G (T * t) := by
      apply integral_congr_ae
      filter_upwards [] with t
      dsimp [G]
      congr 2
      ring
    _ = |T⁻¹| • ∫ y, G y := Measure.integral_comp_mul_left G T
    _ = T⁻¹ * ∫ y, profileSignal w y * profileSignal w (T * x - y) := by
      rw [abs_of_pos (inv_pos.mpr hT)]
      rfl

/-- Repeating coefficients on `T` microcells and then compressing space by `T`
recovers the original coarse unit-grid signal exactly. -/
theorem scaledProfileSignal_blockProfile {m T : ℕ} (hT : 0 < T)
    (v : Profile m) :
    scaledProfileSignal (T : ℝ) (blockProfile T v) = profileSignal v := by
  funext x
  unfold scaledProfileSignal profileSignal blockProfile
  rw [← (finProdFinEquiv : Fin m × Fin T ≃ Fin (m * T)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Equiv.symm_apply_apply]
  calc
    (∑ j : Fin m, ∑ r : Fin T,
        v j * shiftedUnitCell (↑r + T * ↑j) (↑T * x)) =
        ∑ j : Fin m, v j * shiftedUnitCell j x := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.mul_sum, sum_microcells_eq_shiftedUnitCell T hT]
    _ = ∑ j : Fin m, v j * shiftedUnitCell j x := rfl

theorem profileSignal_convolution_pair_expansion {n : ℕ} (w : Profile n) (x : ℝ) :
    (profileSignal w ⋆ profileSignal w) x =
      ∑ i : Fin n, ∑ j : Fin n,
        w i * w j * tent (x - (i : ℕ) - (j : ℕ)) := by
  unfold profileSignal
  rw [MeasureTheory.convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [show (∫ t, (w i * shiftedUnitCell i t) *
          (w j * shiftedUnitCell j (x - t))) =
          w i * w j * ∫ t, shiftedUnitCell i t * shiftedUnitCell j (x - t) by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with t
        ring]
      rw [show (∫ t, shiftedUnitCell i t * shiftedUnitCell j (x - t)) =
          (shiftedUnitCell i ⋆ shiftedUnitCell j) x by rfl]
      rw [shiftedUnitCell_convolution]
    · intro j _
      have hconv := convolutionExistsAt_of_memLp_two
        (shiftedUnitCell i) (shiftedUnitCell j)
        (shiftedUnitCell_memLp_two i) (shiftedUnitCell_memLp_two j) x
      exact hconv.const_mul (w i * w j) |>.congr (by
        filter_upwards [] with t
        simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
        ring)
  · intro i _
    apply integrable_finset_sum
    intro j _
    have hconv := convolutionExistsAt_of_memLp_two
      (shiftedUnitCell i) (shiftedUnitCell j)
      (shiftedUnitCell_memLp_two i) (shiftedUnitCell_memLp_two j) x
    exact hconv.const_mul (w i * w j) |>.congr (by
      filter_upwards [] with t
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      ring)

theorem profileSignal_convolution_expansion {n : ℕ} (w : Profile n) (x : ℝ) :
    (profileSignal w ⋆ profileSignal w) x =
      ∑ k ∈ outputRange n, convCoeff w k * tent (x - k) := by
  rw [profileSignal_convolution_pair_expansion]
  classical
  calc
    (∑ i : Fin n, ∑ j : Fin n,
        w i * w j * tent (x - (i : ℕ) - (j : ℕ))) =
        ∑ p : Fin n × Fin n,
          w p.1 * w p.2 * tent (x - (p.1 : ℕ) - (p.2 : ℕ)) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ k ∈ outputRange n, convCoeff w k * tent (x - k) := by
      simp only [outputRange, convCoeff, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      have hp : (p.1 : ℕ) + (p.2 : ℕ) < 2 * n := by
        have hi := p.1.isLt
        have hj := p.2.isLt
        omega
      rw [Finset.sum_eq_single ((p.1 : ℕ) + (p.2 : ℕ))]
      · simp only [if_true]
        congr 1
        simp only [Nat.cast_add]
        ring_nf
      · intro k hk hne
        simp [hne.symm]
      · simp [hp]

theorem tent_nonneg (t : ℝ) : 0 ≤ tent t := by
  unfold tent
  split_ifs with h0 h1 h2 <;> linarith

theorem tent_le_one (t : ℝ) : tent t ≤ 1 := by
  unfold tent
  split_ifs with h0 h1 h2 <;> linarith

theorem tent_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : tent t = 0 := by
  simp [tent, ht]

theorem tent_eq_zero_of_two_le {t : ℝ} (ht : 2 ≤ t) : tent t = 0 := by
  unfold tent
  split_ifs with h0 h1 h2 <;> linarith

theorem profileSignal_autoconvolution_eq_zero_of_nonpos {n : ℕ}
    (w : Profile n) {x : ℝ} (hx : x ≤ 0) :
    (profileSignal w ⋆ profileSignal w) x = 0 := by
  rw [profileSignal_convolution_expansion]
  apply Finset.sum_eq_zero
  intro k hk
  rw [tent_eq_zero_of_nonpos (by exact sub_nonpos.mpr (hx.trans (Nat.cast_nonneg k)))]
  simp

theorem profileSignal_autoconvolution_eq_zero_of_ge {n : ℕ}
    (w : Profile n) {x : ℝ} (hx : (2 * n : ℝ) + 1 ≤ x) :
    (profileSignal w ⋆ profileSignal w) x = 0 := by
  rw [profileSignal_convolution_expansion]
  apply Finset.sum_eq_zero
  intro k hk
  have hklt : k < 2 * n := by simpa [outputRange] using hk
  have hksucc : k + 1 ≤ 2 * n := Nat.succ_le_iff.mpr hklt
  have hksuccR : (k : ℝ) + 1 ≤ (2 * n : ℝ) := by exact_mod_cast hksucc
  rw [tent_eq_zero_of_two_le (by linarith)]
  simp

/-- Every normalized finite-profile autoconvolution is supported in a fixed
interval depending only on the profile length. -/
theorem profileSignal_autoconvolution_eq_zero_outside {n : ℕ}
    (w : Profile n) {x : ℝ} (hx : x ∉ Set.Ioo (0 : ℝ) ((2 * n : ℝ) + 1)) :
    (profileSignal w ⋆ profileSignal w) x = 0 := by
  by_cases h0 : 0 < x
  · apply profileSignal_autoconvolution_eq_zero_of_ge w
    exact le_of_not_gt (fun hright ↦ hx ⟨h0, hright⟩)
  · exact profileSignal_autoconvolution_eq_zero_of_nonpos w (le_of_not_gt h0)

/-- A uniform anti-diagonal coefficient estimate transfers to a uniform estimate
for the autoconvolutions of the corresponding unit-grid step profiles. -/
theorem profileSignal_autoconvolution_sub_le {n : ℕ} (u v : Profile n) (E : ℝ)
    (hE : 0 ≤ E)
    (hcoeff : ∀ k ∈ outputRange n, |convCoeff u k - convCoeff v k| ≤ E) (x : ℝ) :
    |(profileSignal u ⋆ profileSignal u) x - (profileSignal v ⋆ profileSignal v) x| ≤
      E := by
  rw [profileSignal_convolution_expansion, profileSignal_convolution_expansion,
    ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ outputRange n,
        (convCoeff u k * tent (x - k) - convCoeff v k * tent (x - k))| ≤
        ∑ k ∈ outputRange n,
          |convCoeff u k * tent (x - k) - convCoeff v k * tent (x - k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ outputRange n, E * tent (x - k) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [← sub_mul, abs_mul, abs_of_nonneg (tent_nonneg _)]
      exact mul_le_mul_of_nonneg_right (hcoeff k hk) (tent_nonneg _)
    _ = E * ∑ k ∈ outputRange n, tent (x - k) := by
      rw [Finset.mul_sum]
    _ ≤ E * 1 := by
      apply mul_le_mul_of_nonneg_left _ hE
      simpa [outputRange] using sum_tent_range_le_one (2 * n) x
    _ = E := mul_one E

/-- The same transfer estimate, stated as an essential-supremum (`L∞`) bound. -/
theorem eLpNorm_top_profileSignal_autoconvolution_sub_le {n : ℕ}
    (u v : Profile n) (E : ℝ)
    (hE : 0 ≤ E)
    (hcoeff : ∀ k ∈ outputRange n, |convCoeff u k - convCoeff v k| ≤ E) :
    eLpNorm
        (fun x ↦ (profileSignal u ⋆ profileSignal u) x -
          (profileSignal v ⋆ profileSignal v) x)
        ⊤ volume ≤ ENNReal.ofReal E := by
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  exact profileSignal_autoconvolution_sub_le u v E hE hcoeff x

/-- A fixed-support `L¹` consequence of the coefficient sup-error estimate. -/
theorem integral_abs_profileSignal_autoconvolution_sub_le {n : ℕ}
    (u v : Profile n) (E : ℝ) (hE : 0 ≤ E)
    (hcoeff : ∀ k ∈ outputRange n, |convCoeff u k - convCoeff v k| ≤ E) :
    (∫ x, |(profileSignal u ⋆ profileSignal u) x -
      (profileSignal v ⋆ profileSignal v) x|) ≤ ((2 * n : ℝ) + 1) * E := by
  let I : Set ℝ := Set.Ioo (0 : ℝ) ((2 * n : ℝ) + 1)
  let majorant : ℝ → ℝ := I.indicator (fun _ ↦ E)
  have hmajorant_integrable : Integrable majorant volume := by
    apply (integrable_indicator_iff measurableSet_Ioo).2
    exact integrableOn_const (by
      dsimp [I]
      rw [Real.volume_Ioo]
      simp)
  calc
    (∫ x, |(profileSignal u ⋆ profileSignal u) x -
        (profileSignal v ⋆ profileSignal v) x|) ≤ ∫ x, majorant x := by
      apply integral_mono_of_nonneg
      · filter_upwards [] with x
        exact abs_nonneg _
      · exact hmajorant_integrable
      · filter_upwards [] with x
        by_cases hx : x ∈ I
        · rw [show majorant x = E by simp [majorant, hx]]
          exact profileSignal_autoconvolution_sub_le u v E hE hcoeff x
        · have hu := profileSignal_autoconvolution_eq_zero_outside u hx
          have hv := profileSignal_autoconvolution_eq_zero_outside v hx
          simp [majorant, hx, hu, hv]
    _ = ((2 * n : ℝ) + 1) * E := by
      rw [show majorant = I.indicator (fun _ ↦ E) from rfl,
        MeasureTheory.integral_indicator_const E measurableSet_Ioo]
      dsimp [I]
      rw [Real.volume_real_Ioo_of_le (by positivity)]
      ring

/-- After compressing the common grid by `T`, coefficient error `E` becomes
pointwise output error `E / T`. -/
theorem scaledProfileSignal_autoconvolution_sub_le {n : ℕ}
    (T : ℝ) (hT : 0 < T) (u v : Profile n) (E : ℝ) (hE : 0 ≤ E)
    (hcoeff : ∀ k ∈ outputRange n, |convCoeff u k - convCoeff v k| ≤ E)
    (x : ℝ) :
    |(scaledProfileSignal T u ⋆ scaledProfileSignal T u) x -
      (scaledProfileSignal T v ⋆ scaledProfileSignal T v) x| ≤ T⁻¹ * E := by
  rw [scaledProfileSignal_convolution T u hT,
    scaledProfileSignal_convolution T v hT, ← mul_sub, abs_mul,
    abs_of_pos (inv_pos.mpr hT)]
  exact mul_le_mul_of_nonneg_left
    (profileSignal_autoconvolution_sub_le u v E hE hcoeff (T * x))
    (inv_nonneg.mpr hT.le)

/-- Essential-supremum version of the positive-grid scaling estimate. -/
theorem eLpNorm_top_scaledProfileSignal_autoconvolution_sub_le {n : ℕ}
    (T : ℝ) (hT : 0 < T) (u v : Profile n) (E : ℝ) (hE : 0 ≤ E)
    (hcoeff : ∀ k ∈ outputRange n, |convCoeff u k - convCoeff v k| ≤ E) :
    eLpNorm
        (fun x ↦ (scaledProfileSignal T u ⋆ scaledProfileSignal T u) x -
          (scaledProfileSignal T v ⋆ scaledProfileSignal T v) x)
        ⊤ volume ≤ ENNReal.ofReal (T⁻¹ * E) := by
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_bound
  filter_upwards [] with x
  rw [Real.norm_eq_abs]
  exact scaledProfileSignal_autoconvolution_sub_le T hT u v E hE hcoeff x

end FlatAutoconvolutionS1.Bridge
