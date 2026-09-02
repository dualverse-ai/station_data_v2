import FlatAutoconvolutionS1.ConvolutionL1
import FlatAutoconvolutionS1.ScoreLimit
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The `L²` continuity components of autoconvolution

Cauchy--Schwarz gives `L² * L² → L∞` directly.  Together with the
already formalized `L¹` mass convergence, the uniform output estimate also
controls the squared `L²` energy without requiring an `L¹ * L² → L²` Young
theorem.
-/

open scoped Convolution ENNReal
open MeasureTheory Filter Topology

namespace FlatAutoconvolutionS1

/-- The real-valued `L²` seminorm used in the estimates below. -/
noncomputable def l2Size (f : Signal) : ℝ := (eLpNorm f 2 volume).toReal

theorem l2Size_eq_integral_rpow (f : Signal) (hf : MemLp f 2 volume) :
    l2Size f = (∫ x, |f x| ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  unfold l2Size
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  norm_num [Real.norm_eq_abs]
  positivity

theorem l2Size_nonneg (f : Signal) : 0 ≤ l2Size f := ENNReal.toReal_nonneg

theorem convolutionExistsAt_of_memLp_two
    (f g : Signal) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (x : ℝ) :
    ConvolutionExistsAt f g x (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
  have hgx : MemLp (fun t ↦ g (x - t)) 2 volume := by
    simpa only [Function.comp_apply] using
      hg.comp_measurePreserving (volume.measurePreserving_sub_left x)
  change Integrable (fun t ↦ f t * g (x - t))
  simpa only [Pi.mul_apply] using hf.integrable_mul hgx

/-- Cauchy--Schwarz for the convolution integral at every output point. -/
theorem abs_convolution_le_l2Size_mul
    (f g : Signal) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (x : ℝ) :
    |(f ⋆ g) x| ≤ l2Size f * l2Size g := by
  have hpq : (2 : ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]
    norm_num
  have hgx : MemLp (fun t ↦ g (x - t)) 2 volume := by
    simpa only [Function.comp_apply] using
      hg.comp_measurePreserving (volume.measurePreserving_sub_left x)
  have hf' : MemLp f (ENNReal.ofReal (2 : ℝ)) volume := by norm_num; exact hf
  have hgx' : MemLp (fun t ↦ g (x - t)) (ENNReal.ofReal (2 : ℝ)) volume := by
    norm_num
    exact hgx
  change |∫ t, f t * g (x - t)| ≤ _
  rw [l2Size_eq_integral_rpow f hf, l2Size_eq_integral_rpow g hg]
  calc
    |∫ t, f t * g (x - t)| ≤ ∫ t, |f t| * |g (x - t)| := by
      simpa only [Real.norm_eq_abs, abs_mul] using
        (norm_integral_le_integral_norm (fun t ↦ f t * g (x - t)))
    _ ≤ (∫ t, |f t| ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) *
        (∫ t, |g (x - t)| ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
      simpa only [Real.norm_eq_abs, ENNReal.ofReal_ofNat] using
        (integral_mul_norm_le_Lp_mul_Lq hpq hf' hgx')
    _ = _ := by
      congr 2
      exact (volume.measurePreserving_sub_left x).integral_comp
        (Homeomorph.subLeft x).measurableEmbedding (fun t ↦ |g t| ^ (2 : ℝ))

/-- Reverse triangle inequality for the real `L²` seminorm. -/
theorem abs_l2Size_sub_le (u f : Signal) (hu : MemLp u 2 volume)
    (hf : MemLp f 2 volume) : |l2Size u - l2Size f| ≤ l2Size (u - f) := by
  have hd : MemLp (u - f) 2 volume := hu.sub hf
  have hu_le : eLpNorm u 2 volume ≤ eLpNorm (u - f) 2 volume + eLpNorm f 2 volume := by
    calc
      eLpNorm u 2 volume = eLpNorm ((u - f) + f) 2 volume := by
        congr 1
        abel
      _ ≤ _ := eLpNorm_add_le (p := (2 : ℝ≥0∞)) hd.1 hf.1 (by norm_num)
  have hf_le : eLpNorm f 2 volume ≤ eLpNorm (u - f) 2 volume + eLpNorm u 2 volume := by
    calc
      eLpNorm f 2 volume = eLpNorm (-(u - f) + u) 2 volume := by
        congr 1
        abel
      _ ≤ _ := by
        simpa only [eLpNorm_neg] using
          (eLpNorm_add_le (p := (2 : ℝ≥0∞)) hd.neg.1 hu.1 (by norm_num))
  have hu_le' := (ENNReal.toReal_le_toReal hu.eLpNorm_ne_top
    (ENNReal.add_ne_top.2 ⟨hd.eLpNorm_ne_top, hf.eLpNorm_ne_top⟩)).2 hu_le
  have hf_le' := (ENNReal.toReal_le_toReal hf.eLpNorm_ne_top
    (ENNReal.add_ne_top.2 ⟨hd.eLpNorm_ne_top, hu.eLpNorm_ne_top⟩)).2 hf_le
  rw [ENNReal.toReal_add hd.eLpNorm_ne_top hf.eLpNorm_ne_top] at hu_le'
  rw [ENNReal.toReal_add hd.eLpNorm_ne_top hu.eLpNorm_ne_top] at hf_le'
  change |l2Size u - l2Size f| ≤ l2Size (u - f)
  unfold l2Size
  rw [abs_le]
  constructor <;> linarith

theorem tendsto_l2Size_of_L2
    {u : ℕ → Signal} {f : Signal}
    (hu : ∀ n, MemLp (u n) 2 volume) (hf : MemLp f 2 volume)
    (hL2 : Tendsto (fun n ↦ l2Size (u n - f)) atTop (nhds 0)) :
    Tendsto (fun n ↦ l2Size (u n)) atTop (nhds (l2Size f)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun n ↦ dist_nonneg) _ hL2
  intro n
  simpa only [Real.dist_eq] using abs_l2Size_sub_le (u n) f (hu n) hf

/-- The algebraic polarization identity for autoconvolution.  `L²`
membership makes every convolution integrand in this identity integrable. -/
theorem autoconvolution_sub_eq_cross
    (u f : Signal) (hu : MemLp u 2 volume) (hf : MemLp f 2 volume) :
    autoconvolution u - autoconvolution f = (u - f) ⋆ u + f ⋆ (u - f) := by
  funext x
  have hd : MemLp (u - f) 2 volume := hu.sub hf
  have hdu := convolutionExistsAt_of_memLp_two (u - f) u hd hu x
  have hfu := convolutionExistsAt_of_memLp_two f u hf hu x
  have hfd := convolutionExistsAt_of_memLp_two f (u - f) hf hd x
  have hff := convolutionExistsAt_of_memLp_two f f hf hf x
  have hu_eq : (u - f) + f = u := by abel
  have hleft : (autoconvolution u) x = ((u - f) ⋆ u) x + (f ⋆ u) x := by
    change (u ⋆ u) x = _
    calc
      (u ⋆ u) x = (((u - f) + f) ⋆ u) x := by rw [hu_eq]
      _ = ((u - f) ⋆ u) x + (f ⋆ u) x := hdu.add_distrib hfu
  have hright : (f ⋆ u) x = (f ⋆ (u - f)) x + (autoconvolution f) x := by
    change (f ⋆ u) x = (f ⋆ (u - f)) x + (f ⋆ f) x
    calc
      (f ⋆ u) x = (f ⋆ ((u - f) + f)) x := by rw [hu_eq]
      _ = (f ⋆ (u - f)) x + (f ⋆ f) x := hfd.distrib_add hff
  simp only [Pi.sub_apply, Pi.add_apply]
  rw [hleft, hright]
  ring

/-- Uniform output error bound used for peak and energy convergence. -/
theorem abs_autoconvolution_sub_le_l2
    (u f : Signal) (hu : MemLp u 2 volume) (hf : MemLp f 2 volume) (x : ℝ) :
    |autoconvolution u x - autoconvolution f x| ≤
      l2Size (u - f) * l2Size u + l2Size f * l2Size (u - f) := by
  have hd : MemLp (u - f) 2 volume := hu.sub hf
  have hid := congrFun (autoconvolution_sub_eq_cross u f hu hf) x
  simp only [Pi.sub_apply, Pi.add_apply] at hid
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_convolution_le_l2Size_mul (u - f) u hd hu x)
    (abs_convolution_le_l2Size_mul f (u - f) hf hd x))

/-- An `L² * L²` convolution is a.e. strongly measurable. -/
theorem aestronglyMeasurable_convolution_of_memLp_two
    (f g : Signal) (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    AEStronglyMeasurable (f ⋆ g) volume := by
  exact (hf.1.convolution_integrand (ContinuousLinearMap.lsmul ℝ ℝ) hg.1).integral_prod_right'

theorem eLpNorm_top_autoconvolution_ne_top
    (f : Signal) (hf : MemLp f 2 volume) :
    eLpNorm (autoconvolution f) ⊤ volume ≠ ⊤ := by
  rw [eLpNorm_exponent_top]
  apply ne_of_lt
  apply eLpNormEssSup_lt_top_of_ae_bound
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs] using abs_convolution_le_l2Size_mul f f hf hf x

/-- Quantitative reverse-triangle estimate for the paper's convolution peak. -/
theorem abs_convolutionPeak_sub_le_l2
    (u f : Signal) (hu : MemLp u 2 volume) (hf : MemLp f 2 volume) :
    |convolutionPeak u - convolutionPeak f| ≤
      l2Size (u - f) * l2Size u + l2Size f * l2Size (u - f) := by
  let C := l2Size (u - f) * l2Size u + l2Size f * l2Size (u - f)
  have hC : 0 ≤ C := add_nonneg
    (mul_nonneg (l2Size_nonneg _) (l2Size_nonneg _))
    (mul_nonneg (l2Size_nonneg _) (l2Size_nonneg _))
  have hau_m := aestronglyMeasurable_convolution_of_memLp_two u u hu hu
  have haf_m := aestronglyMeasurable_convolution_of_memLp_two f f hf hf
  have herr_m : AEStronglyMeasurable
      (autoconvolution u - autoconvolution f) volume := hau_m.sub haf_m
  have herr : eLpNorm (autoconvolution u - autoconvolution f) ⊤ volume ≤
      ENNReal.ofReal C := by
    rw [eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs, C] using abs_autoconvolution_sub_le_l2 u f hu hf x
  have hau_top := eLpNorm_top_autoconvolution_ne_top u hu
  have haf_top := eLpNorm_top_autoconvolution_ne_top f hf
  have herr_top : eLpNorm (autoconvolution u - autoconvolution f) ⊤ volume ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top herr
  have hau_le : eLpNorm (autoconvolution u) ⊤ volume ≤
      eLpNorm (autoconvolution u - autoconvolution f) ⊤ volume +
        eLpNorm (autoconvolution f) ⊤ volume := by
    calc
      eLpNorm (autoconvolution u) ⊤ volume =
          eLpNorm ((autoconvolution u - autoconvolution f) + autoconvolution f) ⊤ volume := by
        congr 1
        abel
      _ ≤ _ := eLpNorm_add_le (p := ⊤) herr_m haf_m le_top
  have haf_le : eLpNorm (autoconvolution f) ⊤ volume ≤
      eLpNorm (autoconvolution u - autoconvolution f) ⊤ volume +
        eLpNorm (autoconvolution u) ⊤ volume := by
    calc
      eLpNorm (autoconvolution f) ⊤ volume =
          eLpNorm (-(autoconvolution u - autoconvolution f) + autoconvolution u) ⊤ volume := by
        congr 1
        abel
      _ ≤ _ := by
        simpa only [eLpNorm_neg] using
          (eLpNorm_add_le (p := ⊤) herr_m.neg hau_m le_top)
  have hau_le' := (ENNReal.toReal_le_toReal hau_top
    (ENNReal.add_ne_top.2 ⟨herr_top, haf_top⟩)).2 hau_le
  have haf_le' := (ENNReal.toReal_le_toReal haf_top
    (ENNReal.add_ne_top.2 ⟨herr_top, hau_top⟩)).2 haf_le
  rw [ENNReal.toReal_add herr_top haf_top] at hau_le'
  rw [ENNReal.toReal_add herr_top hau_top] at haf_le'
  have herr' : (eLpNorm (autoconvolution u - autoconvolution f) ⊤ volume).toReal ≤ C := by
    have := (ENNReal.toReal_le_toReal herr_top ENNReal.ofReal_ne_top).2 herr
    simpa only [ENNReal.toReal_ofReal hC] using this
  unfold convolutionPeak
  rw [abs_le]
  constructor <;> linarith

/-- The essential-supremum peak of autoconvolution is continuous under `L²`
input convergence. -/
theorem tendsto_convolutionPeak_of_L2
    {u : ℕ → Signal} {f : Signal}
    (hu : ∀ n, MemLp (u n) 2 volume) (hf : MemLp f 2 volume)
    (hL2 : Tendsto (fun n ↦ l2Size (u n - f)) atTop (nhds 0)) :
    Tendsto (fun n ↦ convolutionPeak (u n)) atTop (nhds (convolutionPeak f)) := by
  have hU := tendsto_l2Size_of_L2 hu hf hL2
  have hmajor : Tendsto (fun n ↦
      l2Size (u n - f) * l2Size (u n) + l2Size f * l2Size (u n - f))
      atTop (nhds 0) := by
    simpa only [zero_mul, mul_zero, add_zero] using
      (hL2.mul hU).add (tendsto_const_nhds.mul hL2)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun n ↦ dist_nonneg) _ hmajor
  intro n
  simpa only [Real.dist_eq] using abs_convolutionPeak_sub_le_l2 (u n) f (hu n) hf

/-- Integrability of the squared autoconvolution follows from its `L¹`
integrability and the pointwise `L² * L² → L∞` bound. -/
theorem integrable_autoconvolution_sq
    (f : Signal) (hf1 : Integrable f) (hf2 : MemLp f 2 volume) :
    Integrable (fun x ↦ autoconvolution f x ^ 2) := by
  have ha : Integrable (autoconvolution f) := hf1.integrable_convolution _ hf1
  have ham := aestronglyMeasurable_convolution_of_memLp_two f f hf2 hf2
  have hbound : ∀ᵐ x ∂volume,
      ‖autoconvolution f x‖ ≤ l2Size f * l2Size f := by
    filter_upwards [] with x
    simpa only [Real.norm_eq_abs] using abs_convolution_le_l2Size_mul f f hf2 hf2 x
  simpa only [pow_two] using ha.mul_bdd ham hbound

/-- Uniform output error and the two `L¹` masses control the energy error.
No nonnegativity is needed; in particular this applies to the paper's
nonnegative outputs. -/
theorem abs_convolutionEnergy_sub_le
    (u f : Signal) (hu1 : Integrable u) (hf1 : Integrable f)
    (hu2 : MemLp u 2 volume) (hf2 : MemLp f 2 volume) :
    |convolutionEnergy u - convolutionEnergy f| ≤
      (l2Size (u - f) * l2Size u + l2Size f * l2Size (u - f)) *
        (convolutionMass u + convolutionMass f) := by
  let C := l2Size (u - f) * l2Size u + l2Size f * l2Size (u - f)
  have hC : 0 ≤ C := add_nonneg
    (mul_nonneg (l2Size_nonneg _) (l2Size_nonneg _))
    (mul_nonneg (l2Size_nonneg _) (l2Size_nonneg _))
  have hau : Integrable (autoconvolution u) := hu1.integrable_convolution _ hu1
  have haf : Integrable (autoconvolution f) := hf1.integrable_convolution _ hf1
  have hau_sq := integrable_autoconvolution_sq u hu1 hu2
  have haf_sq := integrable_autoconvolution_sq f hf1 hf2
  have hpoint : ∀ x,
      |autoconvolution u x ^ 2 - autoconvolution f x ^ 2| ≤
        C * (|autoconvolution u x| + |autoconvolution f x|) := by
    intro x
    rw [show autoconvolution u x ^ 2 - autoconvolution f x ^ 2 =
      (autoconvolution u x - autoconvolution f x) *
        (autoconvolution u x + autoconvolution f x) by ring, abs_mul]
    calc
      |autoconvolution u x - autoconvolution f x| *
          |autoconvolution u x + autoconvolution f x| ≤
          C * |autoconvolution u x + autoconvolution f x| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        simpa only [C] using abs_autoconvolution_sub_le_l2 u f hu2 hf2 x
      _ ≤ C * (|autoconvolution u x| + |autoconvolution f x|) := by
        exact mul_le_mul_of_nonneg_left (abs_add_le _ _) hC
  unfold convolutionEnergy convolutionMass
  calc
    |(∫ x, autoconvolution u x ^ 2) -
        (∫ x, autoconvolution f x ^ 2)| =
        |∫ x, autoconvolution u x ^ 2 - autoconvolution f x ^ 2| := by
      rw [integral_sub hau_sq haf_sq]
    _ ≤ ∫ x, |autoconvolution u x ^ 2 - autoconvolution f x ^ 2| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun x ↦
          autoconvolution u x ^ 2 - autoconvolution f x ^ 2))
    _ ≤ ∫ x, C * (|autoconvolution u x| + |autoconvolution f x|) := by
      exact integral_mono (hau_sq.sub haf_sq).abs
        ((hau.abs.add haf.abs).const_mul C) hpoint
    _ = C * ((∫ x, |autoconvolution u x|) +
        (∫ x, |autoconvolution f x|)) := by
      rw [integral_const_mul, integral_add hau.abs haf.abs]
    _ = _ := by rfl

/-- The autoconvolution energy is continuous under simultaneous `L¹` and
`L²` convergence.  The proof uses uniform output convergence and mass
convergence, avoiding an additional `L¹ * L² → L²` theorem. -/
theorem tendsto_convolutionEnergy_of_L1_L2
    {u : ℕ → Signal} {f : Signal}
    (hu1 : ∀ n, Integrable (u n)) (hf1 : Integrable f)
    (hu2 : ∀ n, MemLp (u n) 2 volume) (hf2 : MemLp f 2 volume)
    (hL1 : Tendsto (fun n ↦ ∫ x, |u n x - f x|) atTop (nhds 0))
    (hL2 : Tendsto (fun n ↦ l2Size (u n - f)) atTop (nhds 0)) :
    Tendsto (fun n ↦ convolutionEnergy (u n)) atTop (nhds (convolutionEnergy f)) := by
  have hU := tendsto_l2Size_of_L2 hu2 hf2 hL2
  have hC : Tendsto (fun n ↦
      l2Size (u n - f) * l2Size (u n) + l2Size f * l2Size (u n - f))
      atTop (nhds 0) := by
    simpa only [zero_mul, mul_zero, add_zero] using
      (hL2.mul hU).add (tendsto_const_nhds.mul hL2)
  have hM := tendsto_convolutionMass_of_L1 hu1 hf1 hL1
  have hmajor : Tendsto (fun n ↦
      (l2Size (u n - f) * l2Size (u n) + l2Size f * l2Size (u n - f)) *
        (convolutionMass (u n) + convolutionMass f)) atTop (nhds 0) := by
    simpa only [zero_mul] using hC.mul (hM.add tendsto_const_nhds)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun n ↦ dist_nonneg) _ hmajor
  intro n
  simpa only [Real.dist_eq] using
    abs_convolutionEnergy_sub_le (u n) f (hu1 n) hf1 (hu2 n) hf2

/-- Lemma 2.2 in the concrete notation of the paper: simultaneous `L¹` and
`L²` convergence implies score convergence at a nonzero limiting
denominator. -/
theorem tendsto_score_of_L1_L2
    {u : ℕ → Signal} {f : Signal}
    (hu1 : ∀ n, Integrable (u n)) (hf1 : Integrable f)
    (hu2 : ∀ n, MemLp (u n) 2 volume) (hf2 : MemLp f 2 volume)
    (hL1 : Tendsto (fun n ↦ ∫ x, |u n x - f x|) atTop (nhds 0))
    (hL2 : Tendsto (fun n ↦ l2Size (u n - f)) atTop (nhds 0))
    (hden : convolutionMass f * convolutionPeak f ≠ 0) :
    Tendsto (fun n ↦ score (u n)) atTop (nhds (score f)) :=
  tendsto_score_of_components
    (tendsto_convolutionEnergy_of_L1_L2 hu1 hf1 hu2 hf2 hL1 hL2)
    (tendsto_convolutionMass_of_L1 hu1 hf1 hL1)
    (tendsto_convolutionPeak_of_L2 hu2 hf2 hL2) hden

end FlatAutoconvolutionS1
