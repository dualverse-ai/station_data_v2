import FlatAutoconvolutionS1.StepAdmissible
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Order.Interval.Set.Union

open scoped ENNReal BigOperators
open MeasureTheory Set Filter Metric

namespace FlatAutoconvolutionS1



private def gridCell (a h : ℝ) (i : ℕ) : Set ℝ :=
  Ico (a + i * h) (a + (i + 1) * h)

private lemma grid_cells_disjoint {a h : ℝ} (hh : 0 < h) {i j : ℕ}
    (hij : i ≠ j) : Disjoint (gridCell a h i) (gridCell a h j) := by
  rw [Set.disjoint_left]
  intro x hxi hxj
  simp only [gridCell, mem_Ico] at hxi hxj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hn : i + 1 ≤ j := by omega
    have hc : ((i + 1 : ℕ) : ℝ) * h ≤ (j : ℝ) * h := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hh.le
    norm_num [Nat.cast_add] at hc
    linarith
  · have hn : j + 1 ≤ i := by omega
    have hc : ((j + 1 : ℕ) : ℝ) * h ≤ (i : ℝ) * h := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hh.le
    norm_num [Nat.cast_add] at hc
    linarith

private lemma grid_cover {a h : ℝ} (n : ℕ) :
    Ico a (a + n * h) ⊆ ⋃ i ∈ Finset.range n, gridCell a h i := by
  have hc := Ico_subset_biUnion_Ico n (fun i : ℕ => a + i * h)
  simpa only [gridCell, Nat.cast_zero, zero_mul, add_zero, Nat.cast_add,
    Nat.cast_one] using hc

private lemma toSignal_eq_weight_of_mem
    (s : EqualGridStep) (i : Fin s.cells)
    (hx : x ∈ Ico (s.origin + (i : ℕ) * s.mesh)
      (s.origin + ((i : ℕ) + 1) * s.mesh)) :
    s.toSignal x = s.weight i := by
  classical
  rw [EqualGridStep.toSignal]
  calc
    (∑ j : Fin s.cells,
        s.weight j * indicator
          (Ico (s.origin + (j : ℕ) * s.mesh)
            (s.origin + ((j : ℕ) + 1) * s.mesh))
          (fun _ : ℝ => (1 : ℝ)) x)
        = ∑ j : Fin s.cells, if j = i then s.weight i else 0 := by
          apply Finset.sum_congr rfl
          intro j _
          by_cases hji : j = i
          · subst j
            simp [hx]
          · have hji' : ((j : Fin s.cells) : ℕ) ≠ (i : ℕ) := by
              intro h
              exact hji (Fin.ext h)
            have hd := grid_cells_disjoint (a := s.origin) s.mesh_pos hji'
            have hnot : x ∉ Ico (s.origin + (j : ℕ) * s.mesh)
                (s.origin + ((j : ℕ) + 1) * s.mesh) := by
              intro hxj
              exact Set.disjoint_left.1 hd hxj hx
            simp [hji, hnot]
    _ = s.weight i := by simp

private lemma toSignal_eq_zero_of_outside
    (s : EqualGridStep) {x : ℝ}
    (hx : x ∉ Ico s.origin (s.origin + s.cells * s.mesh)) :
    s.toSignal x = 0 := by
  classical
  rw [EqualGridStep.toSignal]
  apply Finset.sum_eq_zero
  intro i _
  have hnot : x ∉ Ico (s.origin + (i : ℕ) * s.mesh)
      (s.origin + ((i : ℕ) + 1) * s.mesh) := by
    intro hxi
    apply hx
    constructor
    · have hc : s.origin ≤ s.origin + (i : ℕ) * s.mesh := by
        exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) s.mesh_pos.le)
      exact hc.trans hxi.1
    · have hi : (i : ℕ) + 1 ≤ s.cells := Nat.succ_le_iff.2 i.isLt
      have hc : (((i : ℕ) + 1 : ℕ) : ℝ) * s.mesh ≤ (s.cells : ℝ) * s.mesh := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hi) s.mesh_pos.le
      norm_num [Nat.cast_add] at hc
      exact hxi.2.trans_le (by simpa [add_comm] using add_le_add_left hc s.origin)
  simp [hnot]

private theorem exists_step_uniform_of_support_ball
    {g : Signal} (hgcont : Continuous g) (hgcomp : HasCompactSupport g)
    (hgnonneg : ∀ x, 0 ≤ g x) {R : ℝ} (hRpos : 0 < R)
    (hR : tsupport g ⊆ ball 0 R) {eta : ℝ} (heta : 0 < eta) :
    ∃ s : EqualGridStep,
      (∀ x, |g x - s.toSignal x| < eta) ∧
      Function.support (g - s.toSignal) ⊆ Ico (-R) R ∧
      HasCompactSupport (g - s.toSignal) := by
  have huc : UniformContinuous g := hgcomp.uniformContinuous_of_continuous hgcont
  obtain ⟨delta, hdelta, hmod⟩ := (Metric.uniformContinuous_iff.1 huc) (eta / 2) (half_pos heta)
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * R / delta)
  have hnpos : 0 < n := by
    by_contra hn0
    have : n = 0 := Nat.eq_zero_of_not_pos hn0
    subst n
    have hquot : 0 < 2 * R / delta := div_pos (mul_pos two_pos hRpos) hdelta
    norm_num at hn
    linarith
  let mesh : ℝ := 2 * R / n
  have hmeshpos : 0 < mesh := by positivity
  have hmeshdelta : mesh < delta := by
    dsimp [mesh]
    rw [div_lt_iff₀ (by exact_mod_cast hnpos)]
    simpa [mul_comm] using (div_lt_iff₀ hdelta).1 hn
  let s : EqualGridStep :=
    { cells := n
      cells_pos := hnpos
      origin := -R
      mesh := mesh
      mesh_pos := hmeshpos
      weight := fun i => g (-R + (i : ℕ) * mesh) + eta / 2
      weight_nonneg := fun i => add_nonneg (hgnonneg _) (half_pos heta).le
      weight_nonzero := ⟨⟨0, hnpos⟩,
        by simpa using add_pos_of_nonneg_of_pos (hgnonneg (-R)) (half_pos heta)⟩ }
  have hunif : ∀ x, |g x - s.toSignal x| < eta := by
    intro x
    by_cases hx : x ∈ Ico (-R) R
    · have hend : -R + n * mesh = R := by
        dsimp [mesh]
        field_simp
        ring
      have hxcov : x ∈ ⋃ i ∈ Finset.range n, gridCell (-R) mesh i := by
        apply grid_cover n
        simpa [hend] using hx
      simp only [mem_iUnion] at hxcov
      obtain ⟨i, hi, hxi⟩ := hxcov
      have hiN : i < n := Finset.mem_range.1 hi
      let fi : Fin n := ⟨i, hiN⟩
      have hsig : s.toSignal x = g (-R + i * mesh) + eta / 2 := by
        apply toSignal_eq_weight_of_mem s fi
        simpa [s, gridCell, fi] using hxi
      have hdist : dist x (-R + i * mesh) < delta := by
        rw [Real.dist_eq]
        have hnonneg : 0 ≤ x - (-R + i * mesh) := by linarith [hxi.1]
        rw [abs_of_nonneg hnonneg]
        have := hxi.2
        linarith
      have hgclose : dist (g x) (g (-R + i * mesh)) < eta / 2 := hmod hdist
      rw [Real.dist_eq] at hgclose
      rw [hsig]
      calc
        |g x - (g (-R + i * mesh) + eta / 2)|
            ≤ |g x - g (-R + i * mesh)| + |eta / 2| := by
              calc
                |g x - (g (-R + i * mesh) + eta / 2)| =
                    |(g x - g (-R + i * mesh)) + -(eta / 2)| := by ring_nf
                _ ≤ |g x - g (-R + i * mesh)| + |-(eta / 2)| := abs_add_le _ _
                _ = |g x - g (-R + i * mesh)| + |eta / 2| := by rw [abs_neg]
        _ < eta / 2 + eta / 2 := by
          exact add_lt_add_of_lt_of_le hgclose
            (by simp [abs_of_pos (half_pos heta)])
        _ = eta := by ring
    · have hend : s.origin + s.cells * s.mesh = R := by
        dsimp [s, mesh]
        field_simp
        ring
      have hs0 : s.toSignal x = 0 := by
        apply toSignal_eq_zero_of_outside s
        simpa [s, hend] using hx
      have hg0 : g x = 0 := by
        by_contra hxne
        have hxball := hR (subset_tsupport _ hxne)
        simp only [mem_ball, Real.dist_eq, sub_zero] at hxball
        exact hx ⟨by linarith [abs_lt.1 hxball], by linarith [abs_lt.1 hxball]⟩
      simp [hs0, hg0, heta]
  refine ⟨s, hunif, ?_, ?_⟩
  · apply Function.support_subset_iff'.2
    intro x hx
    have hg0 : g x = 0 := by
      by_contra hxne
      have hxball := hR (subset_tsupport _ hxne)
      simp only [mem_ball, Real.dist_eq, sub_zero] at hxball
      exact hx ⟨by linarith [abs_lt.1 hxball], by linarith [abs_lt.1 hxball]⟩
    have hend : s.origin + s.cells * s.mesh = R := by
      dsimp [s, mesh]
      field_simp
      ring
    have hs0 : s.toSignal x = 0 := by
      apply toSignal_eq_zero_of_outside s
      simpa [s, hend] using hx
    simp [hg0, hs0]
  · have hscomp : HasCompactSupport s.toSignal := by
      apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc s.origin
        (s.origin + s.cells * s.mesh)))
      intro x hx
      apply toSignal_eq_zero_of_outside s
      exact fun hxIco => hx ⟨hxIco.1, hxIco.2.le⟩
    exact hgcomp.sub hscomp

private theorem exists_step_approx_continuous_compact
    {g : Signal} (hgcont : Continuous g) (hgcomp : HasCompactSupport g)
    (hgnonneg : ∀ x, 0 ≤ g x) {eps : ℝ} (heps : 0 < eps) :
    ∃ s : EqualGridStep,
      (∫ x, |g x - s.toSignal x|) < eps ∧
      (∫ x, (g x - s.toSignal x) ^ 2) < eps := by
  obtain ⟨R, hRpos, hR⟩ := hgcomp.isBounded.subset_ball_lt 0 0
  let eta : ℝ := min 1 (eps / (4 * R))
  have heta : 0 < eta := lt_min zero_lt_one (div_pos heps (mul_pos (by norm_num) hRpos))
  have heta_one : eta ≤ 1 := min_le_left _ _
  have heta_eps : eta ≤ eps / (4 * R) := min_le_right _ _
  obtain ⟨s, hunif, hsupp, _hscomp⟩ :=
    exists_step_uniform_of_support_ball hgcont hgcomp hgnonneg hRpos hR heta
  have hgint : Integrable g := hgcont.integrable_of_hasCompactSupport hgcomp
  have hdint : Integrable (g - s.toSignal) := hgint.sub s.toSignal_integrable
  have hd2mem : MemLp (g - s.toSignal) 2 volume :=
    (hgcont.memLp_of_hasCompactSupport hgcomp).sub s.toSignal_memLp_two
  have hconst_ne_top : volume (Ico (-R) R) ≠ ∞ := by
    simp [Real.volume_Ico]
  have hconst_int : Integrable
      ((Ico (-R) R).indicator (fun _ : ℝ => eta)) := by
    exact (integrableOn_const hconst_ne_top).integrable_indicator measurableSet_Ico
  have hconst2_int : Integrable
      ((Ico (-R) R).indicator (fun _ : ℝ => eta ^ 2)) := by
    exact (integrableOn_const hconst_ne_top).integrable_indicator measurableSet_Ico
  have hL1 : (∫ x, |g x - s.toSignal x|) ≤ eta * (2 * R) := by
    calc
      (∫ x, |g x - s.toSignal x|)
          ≤ ∫ x, (Ico (-R) R).indicator (fun _ : ℝ => eta) x := by
            apply integral_mono_ae hdint.abs hconst_int
            filter_upwards [] with x
            by_cases hx : x ∈ Ico (-R) R
            · simp only [indicator_of_mem hx]
              exact (hunif x).le
            · have hz : (g - s.toSignal) x = 0 :=
                Function.support_subset_iff'.1 hsupp x hx
              simp [hx, Pi.sub_apply] at hz ⊢
              exact hz
      _ = eta * (2 * R) := by
        rw [integral_indicator_const eta measurableSet_Ico]
        simp only [Measure.real, Real.volume_Ico, smul_eq_mul]
        rw [ENNReal.toReal_ofReal (by linarith [hRpos] : 0 ≤ R - -R)]
        ring
  have hL2 : (∫ x, (g x - s.toSignal x) ^ 2) ≤ eta ^ 2 * (2 * R) := by
    calc
      (∫ x, (g x - s.toSignal x) ^ 2)
          ≤ ∫ x, (Ico (-R) R).indicator (fun _ : ℝ => eta ^ 2) x := by
            apply integral_mono_ae hd2mem.integrable_sq hconst2_int
            filter_upwards [] with x
            by_cases hx : x ∈ Ico (-R) R
            · simp only [indicator_of_mem hx]
              have hp := (sq_le_sq₀ (abs_nonneg (g x - s.toSignal x)) heta.le).2
                (hunif x).le
              rwa [sq_abs] at hp
            · have hz : (g - s.toSignal) x = 0 :=
                Function.support_subset_iff'.1 hsupp x hx
              simp [hx, Pi.sub_apply] at hz ⊢
              exact hz
      _ = eta ^ 2 * (2 * R) := by
        rw [integral_indicator_const (eta ^ 2) measurableSet_Ico]
        simp only [Measure.real, Real.volume_Ico, smul_eq_mul]
        rw [ENNReal.toReal_ofReal (by linarith [hRpos] : 0 ≤ R - -R)]
        ring
  refine ⟨s, hL1.trans_lt ?_, hL2.trans_lt ?_⟩
  · have hR4 : 0 < 4 * R := mul_pos (by norm_num) hRpos
    calc
      eta * (2 * R) ≤ (eps / (4 * R)) * (2 * R) :=
        mul_le_mul_of_nonneg_right heta_eps (mul_nonneg (by norm_num) hRpos.le)
      _ = eps / 2 := by field_simp; ring
      _ < eps := half_lt_self heps
  · have heta_sq : eta ^ 2 ≤ eta := by nlinarith [heta.le]
    calc
      eta ^ 2 * (2 * R) ≤ eta * (2 * R) :=
        mul_le_mul_of_nonneg_right heta_sq (mul_nonneg (by norm_num) hRpos.le)
      _ < eps := by
        have hR4 : 0 < 4 * R := mul_pos (by norm_num) hRpos
        calc
          eta * (2 * R) ≤ (eps / (4 * R)) * (2 * R) :=
            mul_le_mul_of_nonneg_right heta_eps (mul_nonneg (by norm_num) hRpos.le)
          _ = eps / 2 := by field_simp; ring
          _ < eps := half_lt_self heps

private theorem exists_bounded_truncation
    {u : Signal} (husm : StronglyMeasurable u) (hunonneg : ∀ x, 0 ≤ u x)
    (huint : Integrable u) (hu2 : MemLp u 2 volume) {eps : ℝ} (heps : 0 < eps) :
    ∃ M : ℝ, 0 < M ∧
      let v : Signal := fun x => min (u x) M
      StronglyMeasurable v ∧ (∀ x, 0 ≤ v x ∧ v x ≤ M) ∧
      (∫ x, |u x - v x|) < eps ∧
      (∫ x, (u x - v x) ^ 2) < eps := by
  have hu1 : MemLp u 1 volume := memLp_one_iff_integrable.2 huint
  obtain ⟨M1, hM1, htail1⟩ :=
    hu1.integral_indicator_norm_ge_nonneg_le (half_pos heps)
  have huSqInt : Integrable (fun x => u x ^ 2) := hu2.integrable_sq
  have huSq1 : MemLp (fun x => u x ^ 2) 1 volume :=
    memLp_one_iff_integrable.2 huSqInt
  obtain ⟨A, hA, htail2⟩ :=
    huSq1.integral_indicator_norm_ge_nonneg_le (half_pos heps)
  let M : ℝ := max 1 (max M1 (Real.sqrt A))
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hM1M : M1 ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hsqrtM : Real.sqrt A ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  let v : Signal := fun x => min (u x) M
  have hvsm : StronglyMeasurable v := husm.inf stronglyMeasurable_const
  have hvbounds : ∀ x, 0 ≤ v x ∧ v x ≤ M := by
    intro x
    exact ⟨le_min (hunonneg x) hMpos.le, min_le_right _ _⟩
  let tail1 : Signal := {x | M1 ≤ ‖u x‖₊}.indicator u
  let tail2 : Signal := {x | A ≤ ‖u x ^ 2‖₊}.indicator (fun x => u x ^ 2)
  have hset1 : MeasurableSet {x | M1 ≤ ‖u x‖₊} :=
    StronglyMeasurable.measurableSet_le stronglyMeasurable_const
      husm.nnnorm.measurable.coe_nnreal_real.stronglyMeasurable
  have hset2 : MeasurableSet {x | A ≤ ‖u x ^ 2‖₊} :=
    StronglyMeasurable.measurableSet_le stronglyMeasurable_const
      (husm.pow 2).nnnorm.measurable.coe_nnreal_real.stronglyMeasurable
  have htail1int : Integrable tail1 := huint.indicator hset1
  have htail2int : Integrable tail2 := huSqInt.indicator hset2
  have htail1real : (∫ x, |tail1 x|) ≤ eps / 2 := by
    rw [show (∫ x, |tail1 x|) = (∫ x, ‖tail1 x‖) by simp [Real.norm_eq_abs]]
    rw [integral_norm_eq_lintegral_enorm htail1int.aestronglyMeasurable]
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top htail1
    simpa [tail1, ENNReal.toReal_ofReal (half_pos heps).le] using ht
  have htail2real : (∫ x, tail2 x) ≤ eps / 2 := by
    have hnonneg : ∀ x, 0 ≤ tail2 x := by
      intro x
      simp only [tail2]
      exact indicator_nonneg (fun _ _ => sq_nonneg _) x
    rw [show (∫ x, tail2 x) = (∫ x, ‖tail2 x‖) by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]]
    rw [integral_norm_eq_lintegral_enorm htail2int.aestronglyMeasurable]
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top htail2
    simpa [tail2, ENNReal.toReal_ofReal (half_pos heps).le] using ht
  have hvint : Integrable v := by
    apply Integrable.mono' huint hvsm.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hvbounds x).1]
    exact min_le_left _ _
  have hv2 : MemLp v 2 volume := by
    apply hu2.mono hvsm.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hvbounds x).1,
      abs_of_nonneg (hunonneg x)]
    exact min_le_left _ _
  have hdiffint : Integrable (u - v) := huint.sub hvint
  have hdiff2int : Integrable (fun x => (u x - v x) ^ 2) :=
    (hu2.sub hv2).integrable_sq
  have hL1 : (∫ x, |u x - v x|) ≤ ∫ x, |tail1 x| := by
    apply integral_mono_ae hdiffint.abs htail1int.abs
    filter_upwards [] with x
    by_cases hx : u x ≤ M
    · have hvx : v x = u x := by simp [v, min_eq_left hx]
      simp [hvx]
    · have hmem : x ∈ {x | M1 ≤ ‖u x‖₊} := by
        change M1 ≤ ‖u x‖₊
        rw [Real.nnnorm_of_nonneg (hunonneg x)]
        exact hM1M.trans (le_of_lt (lt_of_not_ge hx))
      have hMx : M < u x := lt_of_not_ge hx
      have hvx : v x = M := by simp [v, min_eq_right hMx.le]
      have htx : tail1 x = u x := by
        dsimp [tail1]
        rw [indicator_of_mem]
        change M1 ≤ |u x|
        rw [abs_of_nonneg (hunonneg x)]
        exact hM1M.trans hMx.le
      change |u x - v x| ≤ |tail1 x|
      rw [hvx, htx]
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (hunonneg x)]
      linarith [hMpos]
  have hL2 : (∫ x, (u x - v x) ^ 2) ≤ ∫ x, tail2 x := by
    apply integral_mono_ae hdiff2int htail2int
    filter_upwards [] with x
    by_cases hx : u x ≤ M
    · have ht2non : 0 ≤ tail2 x := by
        simp only [tail2]
        exact indicator_nonneg (fun _ _ => sq_nonneg _) x
      have hvx : v x = u x := by simp [v, min_eq_left hx]
      rw [hvx]
      simp [ht2non]
    · have hAMsq : A ≤ M ^ 2 := by
        calc
          A = (Real.sqrt A) ^ 2 := by rw [Real.sq_sqrt hA]
          _ ≤ M ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg A) hMpos.le).2 hsqrtM
      have hmem : x ∈ {x | A ≤ ‖u x ^ 2‖₊} := by
        have hMx : M < u x := lt_of_not_ge hx
        have hAu : A ≤ u x ^ 2 := by nlinarith
        simpa [Real.nnnorm_of_nonneg (sq_nonneg (u x))] using hAu
      have hMx : M < u x := lt_of_not_ge hx
      have hvx : v x = M := by simp [v, min_eq_right hMx.le]
      have htx : tail2 x = u x ^ 2 := by
        dsimp [tail2]
        rw [indicator_of_mem]
        change A ≤ |u x ^ 2|
        rw [abs_of_nonneg (sq_nonneg _)]
        exact hAMsq.trans (by nlinarith)
      rw [hvx, htx]
      nlinarith [hunonneg x, hMpos]
  refine ⟨M, hMpos, hvsm, hvbounds, hL1.trans_lt ?_, hL2.trans_lt ?_⟩
  · exact htail1real.trans_lt (half_lt_self heps)
  · exact htail2real.trans_lt (half_lt_self heps)

private def clip (M y : ℝ) : ℝ := max 0 (min y M)

private lemma clip_nonneg (M y : ℝ) : 0 ≤ clip M y := le_max_left _ _

private lemma clip_le {M y : ℝ} (hM : 0 ≤ M) : clip M y ≤ M := by
  exact max_le hM (min_le_right _ _)

private lemma abs_sub_clip_le {M x : ℝ} (hM : 0 ≤ M)
    (hx0 : 0 ≤ x) (hxM : x ≤ M) (y : ℝ) :
    |x - clip M y| ≤ |x - y| := by
  by_cases hy0 : y ≤ 0
  · have hyM : y ≤ M := hy0.trans hM
    rw [clip, min_eq_left hyM, max_eq_left hy0]
    simp only [sub_zero]
    rw [abs_of_nonneg hx0, abs_of_nonneg (by linarith)]
    linarith
  · have hypos : 0 ≤ y := le_of_not_ge hy0
    by_cases hMy : M ≤ y
    · rw [clip, min_eq_right hMy, max_eq_right hM]
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
    · have hyM : y ≤ M := le_of_not_ge hMy
      rw [clip, min_eq_left hyM, max_eq_right hypos]

private theorem exists_continuous_compact_approx_of_bounded
    {v : Signal} (hvint : Integrable v)
    {M : ℝ} (hM : 0 < M) (hvbounds : ∀ x, 0 ≤ v x ∧ v x ≤ M)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ g : Signal, Continuous g ∧ HasCompactSupport g ∧
      (∀ x, 0 ≤ g x ∧ g x ≤ M) ∧
      (∫ x, |v x - g x|) < eps ∧
      (∫ x, (v x - g x) ^ 2) < eps := by
  let delta : ℝ := min (eps / 2) (eps / (2 * M))
  have hdelta : 0 < delta :=
    lt_min (half_pos heps) (div_pos heps (mul_pos two_pos hM))
  obtain ⟨h, hhcomp, hvh, hhcont, hhint⟩ :=
    hvint.exists_hasCompactSupport_integral_sub_le hdelta
  let g : Signal := fun x => clip M (h x)
  have hgcont : Continuous g := by
    exact continuous_const.max (hhcont.min continuous_const)
  have hgbounds : ∀ x, 0 ≤ g x ∧ g x ≤ M := by
    intro x
    exact ⟨clip_nonneg _ _, clip_le hM.le⟩
  have hgcomp : HasCompactSupport g := by
    apply HasCompactSupport.intro hhcomp
    intro x hx
    have hh0 : h x = 0 := by
      apply Function.notMem_support.1
      exact fun hs => hx (subset_tsupport _ hs)
    simp [g, clip, hh0, hM.le]
  have hgint : Integrable g := hgcont.integrable_of_hasCompactSupport hgcomp
  have hcontract : ∀ x, |v x - g x| ≤ |v x - h x| := by
    intro x
    exact abs_sub_clip_le hM.le (hvbounds x).1 (hvbounds x).2 (h x)
  have hL1 : (∫ x, |v x - g x|) ≤ ∫ x, |v x - h x| := by
    apply integral_mono_ae (hvint.sub hgint).abs (hvint.sub hhint).abs
    exact Eventually.of_forall hcontract
  have hdiffsq : Integrable (fun x => (v x - g x) ^ 2) := by
    apply Integrable.mono' ((hvint.sub hgint).abs.const_mul M)
      ((hvint.sub hgint).aestronglyMeasurable.pow 2)
    filter_upwards [] with x
    simp only [Pi.pow_apply, Pi.sub_apply, Real.norm_eq_abs]
    rw [abs_of_nonneg (sq_nonneg _)]
    have hdnon : 0 ≤ |v x - g x| := abs_nonneg _
    have hdM : |v x - g x| ≤ M := by
      rw [abs_le]
      constructor <;> linarith [(hvbounds x).1, (hvbounds x).2,
        (hgbounds x).1, (hgbounds x).2]
    rw [← sq_abs]
    nlinarith
  have hL2 : (∫ x, (v x - g x) ^ 2) ≤ M * ∫ x, |v x - h x| := by
    calc
      (∫ x, (v x - g x) ^ 2) ≤ ∫ x, M * |v x - h x| := by
        apply integral_mono_ae hdiffsq ((hvint.sub hhint).abs.const_mul M)
        filter_upwards [] with x
        have hdnon : 0 ≤ |v x - g x| := abs_nonneg _
        have hdM : |v x - g x| ≤ M := by
          rw [abs_le]
          constructor <;> linarith [(hvbounds x).1, (hvbounds x).2,
            (hgbounds x).1, (hgbounds x).2]
        calc
          (v x - g x) ^ 2 = |v x - g x| ^ 2 := (sq_abs _).symm
          _ ≤ M * |v x - g x| := by nlinarith
          _ ≤ M * |v x - h x| :=
            mul_le_mul_of_nonneg_left (hcontract x) hM.le
      _ = M * ∫ x, |v x - h x| := integral_const_mul _ _
  refine ⟨g, hgcont, hgcomp, hgbounds, hL1.trans_lt ?_, hL2.trans_lt ?_⟩
  · exact hvh.trans_lt ((min_le_left _ _).trans_lt (half_lt_self heps))
  · calc
      M * (∫ x, |v x - h x|) ≤ M * delta := mul_le_mul_of_nonneg_left hvh hM.le
      _ ≤ M * (eps / (2 * M)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hM.le
      _ = eps / 2 := by field_simp
      _ < eps := half_lt_self heps

theorem exists_equalGridStep_approx_of_stronglyMeasurable
    {u : Signal} (husm : StronglyMeasurable u) (hunonneg : ∀ x, 0 ≤ u x)
    (huint : Integrable u) (hu2 : MemLp u 2 volume) {eps : ℝ} (heps : 0 < eps) :
    ∃ s : EqualGridStep,
      (∫ x, |u x - s.toSignal x|) < eps ∧
      (∫ x, (u x - s.toSignal x) ^ 2) < eps := by
  let delta : ℝ := eps / 10
  have hdelta : 0 < delta := div_pos heps (by norm_num)
  obtain ⟨M, hM, hvsm, hvbounds, huv1, huv2⟩ :=
    exists_bounded_truncation husm hunonneg huint hu2 hdelta
  let v : Signal := fun x => min (u x) M
  obtain ⟨g, hgcont, hgcomp, hgbounds, hvg1, hvg2⟩ :=
    exists_continuous_compact_approx_of_bounded (by
        apply Integrable.mono' huint hvsm.aestronglyMeasurable
        filter_upwards [] with x
        change ‖min (u x) M‖ ≤ u x
        rw [Real.norm_eq_abs, abs_of_nonneg (hvbounds x).1]
        exact min_le_left (u x) M)
      hM hvbounds hdelta
  obtain ⟨s, hgs1, hgs2⟩ :=
    exists_step_approx_continuous_compact hgcont hgcomp (fun x => (hgbounds x).1) hdelta
  have hvint : Integrable v := by
    apply Integrable.mono' huint hvsm.aestronglyMeasurable
    filter_upwards [] with x
    change ‖min (u x) M‖ ≤ u x
    rw [Real.norm_eq_abs, abs_of_nonneg (hvbounds x).1]
    exact min_le_left (u x) M
  have hgint : Integrable g := hgcont.integrable_of_hasCompactSupport hgcomp
  have htotalint : Integrable (u - s.toSignal) := huint.sub s.toSignal_integrable
  have hL1le : (∫ x, |u x - s.toSignal x|) ≤
      (∫ x, |u x - v x|) + (∫ x, |v x - g x|) +
        (∫ x, |g x - s.toSignal x|) := by
    calc
      (∫ x, |u x - s.toSignal x|) ≤
          ∫ x, |u x - v x| + |v x - g x| + |g x - s.toSignal x| := by
        apply integral_mono_ae htotalint.abs
          (((huint.sub hvint).abs.add (hvint.sub hgint).abs).add
            (hgint.sub s.toSignal_integrable).abs)
        filter_upwards [] with x
        calc
          |u x - s.toSignal x| =
              |(u x - v x) + (v x - g x) + (g x - s.toSignal x)| := by ring_nf
          _ ≤ |u x - v x| + |v x - g x| + |g x - s.toSignal x| :=
            (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = _ := by
        have hi1 := integral_add (huint.sub hvint).abs (hvint.sub hgint).abs
        have hi2 := integral_add
          ((huint.sub hvint).abs.add (hvint.sub hgint).abs)
          (hgint.sub s.toSignal_integrable).abs
        calc
          (∫ x, |u x - v x| + |v x - g x| + |g x - s.toSignal x|) =
              (∫ x, |u x - v x| + |v x - g x|) +
                ∫ x, |g x - s.toSignal x| := by
            simpa only [Pi.add_apply, Pi.sub_apply] using hi2
          _ = _ := by rw [show (∫ x, |u x - v x| + |v x - g x|) =
            (∫ x, |u x - v x|) + ∫ x, |v x - g x| by
              simpa only [Pi.add_apply, Pi.sub_apply] using hi1]
  have hv2 : MemLp v 2 volume := by
    apply hu2.mono hvsm.aestronglyMeasurable
    filter_upwards [] with x
    simpa [v, Real.norm_eq_abs, abs_of_nonneg (hvbounds x).1,
      abs_of_nonneg (hunonneg x)] using (min_le_left (u x) M)
  have hg2 : MemLp g 2 volume := hgcont.memLp_of_hasCompactSupport hgcomp
  have htotal2int : Integrable (fun x => (u x - s.toSignal x) ^ 2) :=
    (hu2.sub s.toSignal_memLp_two).integrable_sq
  have huv2int : Integrable (fun x => (u x - v x) ^ 2) := (hu2.sub hv2).integrable_sq
  have hvg2int : Integrable (fun x => (v x - g x) ^ 2) := (hv2.sub hg2).integrable_sq
  have hgs2int : Integrable (fun x => (g x - s.toSignal x) ^ 2) :=
    (hg2.sub s.toSignal_memLp_two).integrable_sq
  have hL2le : (∫ x, (u x - s.toSignal x) ^ 2) ≤
      3 * ((∫ x, (u x - v x) ^ 2) + (∫ x, (v x - g x) ^ 2) +
        (∫ x, (g x - s.toSignal x) ^ 2)) := by
    calc
      (∫ x, (u x - s.toSignal x) ^ 2) ≤
          ∫ x, 3 * ((u x - v x) ^ 2 + (v x - g x) ^ 2 +
            (g x - s.toSignal x) ^ 2) := by
        apply integral_mono_ae htotal2int
          (((huv2int.add hvg2int).add hgs2int).const_mul 3)
        filter_upwards [] with x
        let a := u x - v x
        let b := v x - g x
        let c := g x - s.toSignal x
        have hab : u x - s.toSignal x = a + b + c := by dsimp [a, b, c]; ring
        rw [hab]
        dsimp [a, b, c]
        nlinarith [sq_nonneg ((u x - v x) - (v x - g x)),
          sq_nonneg ((u x - v x) - (g x - s.toSignal x)),
          sq_nonneg ((v x - g x) - (g x - s.toSignal x))]
      _ = _ := by
        rw [integral_const_mul]
        congr 1
        have hi1 := integral_add huv2int hvg2int
        have hi2 := integral_add (huv2int.add hvg2int) hgs2int
        calc
          (∫ x, (u x - v x) ^ 2 + (v x - g x) ^ 2 +
              (g x - s.toSignal x) ^ 2) =
              (∫ x, (u x - v x) ^ 2 + (v x - g x) ^ 2) +
                ∫ x, (g x - s.toSignal x) ^ 2 := by
            simpa only [Pi.add_apply] using hi2
          _ = _ := by rw [show (∫ x, (u x - v x) ^ 2 + (v x - g x) ^ 2) =
            (∫ x, (u x - v x) ^ 2) + ∫ x, (v x - g x) ^ 2 by
              simpa only [Pi.add_apply] using hi1]
  refine ⟨s, hL1le.trans_lt ?_, hL2le.trans_lt ?_⟩
  · dsimp [delta] at huv1 hvg1 hgs1
    linarith
  · dsimp [delta] at huv2 hvg2 hgs2
    linarith

/-- Simultaneous `L¹` and squared-`L²` density of nonzero finite
equal-grid steps in the admissible class.  The approximating step is nonzero
by construction (the `EqualGridStep` type records this). -/
theorem Admissible.exists_equalGridStep_integral_sq_approx
    {f : Signal} (hf : Admissible f) {eps : ℝ} (heps : 0 < eps) :
    ∃ s : EqualGridStep,
      (∫ x, |f x - s.toSignal x|) < eps ∧
      (∫ x, (f x - s.toSignal x) ^ 2) < eps := by
  let hfm : AEStronglyMeasurable f volume := hf.2.1.aestronglyMeasurable
  let u : Signal := fun x => max (hfm.mk f x) 0
  have husm : StronglyMeasurable u := hfm.stronglyMeasurable_mk.sup stronglyMeasurable_const
  have hunonneg : ∀ x, 0 ≤ u x := fun x => le_max_right _ _
  have hfu : f =ᵐ[volume] u := by
    filter_upwards [hfm.ae_eq_mk, hf.1] with x hxeq hxnon
    dsimp [u]
    rw [← hxeq]
    exact (max_eq_left hxnon).symm
  have huint : Integrable u := hf.2.1.congr hfu
  have hu2 : MemLp u 2 volume := (memLp_congr_ae hfu).1 hf.2.2.1
  obtain ⟨s, hs1, hs2⟩ :=
    exists_equalGridStep_approx_of_stronglyMeasurable husm hunonneg huint hu2 heps
  refine ⟨s, ?_, ?_⟩
  · rw [show (∫ x, |f x - s.toSignal x|) =
        ∫ x, |u x - s.toSignal x| by
      apply integral_congr_ae
      filter_upwards [hfu] with x hx
      rw [hx]]
    exact hs1
  · rw [show (∫ x, (f x - s.toSignal x) ^ 2) =
        ∫ x, (u x - s.toSignal x) ^ 2 by
      apply integral_congr_ae
      filter_upwards [hfu] with x hx
      rw [hx]]
    exact hs2

end FlatAutoconvolutionS1
