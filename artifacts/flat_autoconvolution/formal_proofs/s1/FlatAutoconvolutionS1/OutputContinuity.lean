import FlatAutoconvolutionS1.AdmissibleBounds

/-!
# Score continuity from direct control of the autoconvolution

Bernoulli microcell refinements do not converge to their weighted profile in
input `L²`.  What converges is the autoconvolution itself.  This module records
the corresponding output-level continuity principle, keeping that distinction
explicit in the formal proof.
-/

open scoped ENNReal
open MeasureTheory Filter Topology

namespace FlatAutoconvolutionS1

/-- Reverse-triangle control of the essential-supremum peaks from an
everywhere uniform bound on the two autoconvolutions. -/
theorem abs_convolutionPeak_sub_le_of_uniform
    (u f : Signal) (hu : MemLp u 2 volume) (hf : MemLp f 2 volume)
    {K : ℝ} (hK : 0 ≤ K)
    (hpoint : ∀ x, |autoconvolution u x - autoconvolution f x| ≤ K) :
    |convolutionPeak u - convolutionPeak f| ≤ K := by
  have haum := aestronglyMeasurable_convolution_of_memLp_two u u hu hu
  have hafm := aestronglyMeasurable_convolution_of_memLp_two f f hf hf
  have herrm : AEStronglyMeasurable
      (autoconvolution u - autoconvolution f) volume := haum.sub hafm
  have herr : eLpNorm (autoconvolution u - autoconvolution f) ⊤ volume ≤
      ENNReal.ofReal K := by
    rw [eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_bound
    filter_upwards [] with x
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using hpoint x
  have hautop := eLpNorm_top_autoconvolution_ne_top u hu
  have haftop := eLpNorm_top_autoconvolution_ne_top f hf
  have herrtop : eLpNorm (autoconvolution u - autoconvolution f) ⊤ volume ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top herr
  have haule : eLpNorm (autoconvolution u) ⊤ volume ≤
      eLpNorm (autoconvolution u - autoconvolution f) ⊤ volume +
        eLpNorm (autoconvolution f) ⊤ volume := by
    calc
      eLpNorm (autoconvolution u) ⊤ volume =
          eLpNorm ((autoconvolution u - autoconvolution f) + autoconvolution f) ⊤ volume := by
        congr 1
        abel
      _ ≤ _ := eLpNorm_add_le (p := ⊤) herrm hafm le_top
  have hafle : eLpNorm (autoconvolution f) ⊤ volume ≤
      eLpNorm (autoconvolution u - autoconvolution f) ⊤ volume +
        eLpNorm (autoconvolution u) ⊤ volume := by
    calc
      eLpNorm (autoconvolution f) ⊤ volume =
          eLpNorm (-(autoconvolution u - autoconvolution f) + autoconvolution u) ⊤ volume := by
        congr 1
        abel
      _ ≤ _ := by
        simpa only [eLpNorm_neg] using
          (eLpNorm_add_le (p := ⊤) herrm.neg haum le_top)
  have haule' := (ENNReal.toReal_le_toReal hautop
    (ENNReal.add_ne_top.2 ⟨herrtop, haftop⟩)).2 haule
  have hafle' := (ENNReal.toReal_le_toReal haftop
    (ENNReal.add_ne_top.2 ⟨herrtop, hautop⟩)).2 hafle
  rw [ENNReal.toReal_add herrtop haftop] at haule'
  rw [ENNReal.toReal_add herrtop hautop] at hafle'
  have herr' : (eLpNorm (autoconvolution u - autoconvolution f) ⊤ volume).toReal ≤ K := by
    have := (ENNReal.toReal_le_toReal herrtop ENNReal.ofReal_ne_top).2 herr
    simpa only [ENNReal.toReal_ofReal hK] using this
  unfold convolutionPeak
  rw [abs_le]
  constructor <;> linarith

/-- Direct uniform output control bounds the difference of the two energy
integrals by the uniform error times the sum of their `L¹` masses. -/
theorem abs_convolutionEnergy_sub_le_of_uniform
    (u f : Signal) (hu1 : Integrable u) (hf1 : Integrable f)
    (hu2 : MemLp u 2 volume) (hf2 : MemLp f 2 volume)
    {K : ℝ} (hK : 0 ≤ K)
    (hpoint : ∀ x, |autoconvolution u x - autoconvolution f x| ≤ K) :
    |convolutionEnergy u - convolutionEnergy f| ≤
      K * (convolutionMass u + convolutionMass f) := by
  have hau : Integrable (autoconvolution u) := hu1.integrable_convolution _ hu1
  have haf : Integrable (autoconvolution f) := hf1.integrable_convolution _ hf1
  have hausq := integrable_autoconvolution_sq u hu1 hu2
  have hafsq := integrable_autoconvolution_sq f hf1 hf2
  have hp : ∀ x,
      |autoconvolution u x ^ 2 - autoconvolution f x ^ 2| ≤
        K * (|autoconvolution u x| + |autoconvolution f x|) := by
    intro x
    rw [show autoconvolution u x ^ 2 - autoconvolution f x ^ 2 =
      (autoconvolution u x - autoconvolution f x) *
        (autoconvolution u x + autoconvolution f x) by ring, abs_mul]
    calc
      |autoconvolution u x - autoconvolution f x| *
          |autoconvolution u x + autoconvolution f x| ≤
          K * |autoconvolution u x + autoconvolution f x| :=
        mul_le_mul_of_nonneg_right (hpoint x) (abs_nonneg _)
      _ ≤ K * (|autoconvolution u x| + |autoconvolution f x|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) hK
  unfold convolutionEnergy convolutionMass
  calc
    |(∫ x, autoconvolution u x ^ 2) - (∫ x, autoconvolution f x ^ 2)| =
        |∫ x, autoconvolution u x ^ 2 - autoconvolution f x ^ 2| := by
      rw [integral_sub hausq hafsq]
    _ ≤ ∫ x, |autoconvolution u x ^ 2 - autoconvolution f x ^ 2| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun x ↦
          autoconvolution u x ^ 2 - autoconvolution f x ^ 2))
    _ ≤ ∫ x, K * (|autoconvolution u x| + |autoconvolution f x|) :=
      integral_mono (hausq.sub hafsq).abs ((hau.abs.add haf.abs).const_mul K) hp
    _ = K * ((∫ x, |autoconvolution u x|) +
        (∫ x, |autoconvolution f x|)) := by
      rw [integral_const_mul, integral_add hau.abs haf.abs]

/-- Output-level convergence criterion used by the binary-refinement step. -/
theorem tendsto_score_of_autoconvolution_control
    {u : ℕ → Signal} {f : Signal} {K : ℕ → ℝ}
    (hu1 : ∀ n, Integrable (u n)) (hf1 : Integrable f)
    (hu2 : ∀ n, MemLp (u n) 2 volume) (hf2 : MemLp f 2 volume)
    (hKnonneg : ∀ n, 0 ≤ K n)
    (hK : Tendsto K atTop (nhds 0))
    (hpoint : ∀ n x, |autoconvolution (u n) x - autoconvolution f x| ≤ K n)
    (houtputL1 : Tendsto
      (fun n ↦ ∫ x, |autoconvolution (u n) x - autoconvolution f x|)
      atTop (nhds 0))
    (hden : convolutionMass f * convolutionPeak f ≠ 0) :
    Tendsto (fun n ↦ score (u n)) atTop (nhds (score f)) := by
  have hmass : Tendsto (fun n ↦ convolutionMass (u n)) atTop
      (nhds (convolutionMass f)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun n ↦ dist_nonneg) _ houtputL1
    intro n
    have hau : Integrable (autoconvolution (u n)) :=
      (hu1 n).integrable_convolution _ (hu1 n)
    have haf : Integrable (autoconvolution f) := hf1.integrable_convolution _ hf1
    simpa only [Real.dist_eq, convolutionMass] using
      abs_integral_abs_sub_integral_abs_le _ _ hau haf
  have hpeak : Tendsto (fun n ↦ convolutionPeak (u n)) atTop
      (nhds (convolutionPeak f)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun n ↦ dist_nonneg) _ hK
    intro n
    simpa only [Real.dist_eq] using
      abs_convolutionPeak_sub_le_of_uniform (u n) f (hu2 n) hf2
        (hKnonneg n) (hpoint n)
  have henergy : Tendsto (fun n ↦ convolutionEnergy (u n)) atTop
      (nhds (convolutionEnergy f)) := by
    have hmajor : Tendsto
        (fun n ↦ K n * (convolutionMass (u n) + convolutionMass f))
        atTop (nhds 0) := by
      simpa only [zero_mul] using hK.mul (hmass.add tendsto_const_nhds)
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun n ↦ dist_nonneg) _ hmajor
    intro n
    simpa only [Real.dist_eq] using
      abs_convolutionEnergy_sub_le_of_uniform (u n) f (hu1 n) hf1
        (hu2 n) hf2 (hKnonneg n) (hpoint n)
  exact tendsto_score_of_components henergy hmass hpeak hden

end FlatAutoconvolutionS1
