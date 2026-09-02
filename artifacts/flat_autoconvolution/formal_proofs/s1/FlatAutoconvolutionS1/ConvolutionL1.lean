import FlatAutoconvolutionS1.Definitions

/-!
# The `L¹` continuity component of autoconvolution

This file proves the concrete `L¹ * L¹ → L¹` Young estimate and the
mass-convergence part of Lemma 2.2.  The a.e. convolution algebra below is
important: arbitrary `L¹` representatives need not have a convolution
integrand at every output point.
-/

open scoped Convolution ENNReal
open MeasureTheory Filter Topology

namespace FlatAutoconvolutionS1

/-- Young's `L¹ * L¹ → L¹` estimate for the concrete real convolution
used in the paper. -/
theorem integral_abs_convolution_le_mul
    (f g : Signal) (hf : Integrable f) (hg : Integrable g) :
    (∫ x, |(f ⋆ g) x|) ≤ (∫ x, |f x|) * (∫ x, |g x|) := by
  let af : Signal := fun x ↦ |f x|
  let ag : Signal := fun x ↦ |g x|
  have haf : Integrable af := hf.abs
  have hag : Integrable ag := hg.abs
  have hfg : Integrable (f ⋆ g) := hf.integrable_convolution _ hg
  have hafg : Integrable (af ⋆ ag) := haf.integrable_convolution _ hag
  have hpoint : ∀ x, |(f ⋆ g) x| ≤ (af ⋆ ag) x := by
    intro x
    change |∫ t, f t * g (x - t)| ≤ ∫ t, |f t| * |g (x - t)|
    calc
      |∫ t, f t * g (x - t)| ≤ ∫ t, |f t * g (x - t)| := by
        simpa only [Real.norm_eq_abs] using
          (norm_integral_le_integral_norm (fun t ↦ f t * g (x - t)))
      _ = ∫ t, |f t| * |g (x - t)| := by simp only [abs_mul]
  calc
    (∫ x, |(f ⋆ g) x|) ≤ ∫ x, (af ⋆ ag) x :=
      integral_mono hfg.abs hafg hpoint
    _ = (∫ x, |f x|) * (∫ x, |g x|) := by
      simpa [af, ag, smul_eq_mul] using
        (integral_convolution (ContinuousLinearMap.lsmul ℝ ℝ) haf hag)

/-- Concrete `L¹` error estimate for autoconvolution.  This is the first of
the three estimates displayed in Lemma 2.2 of the verification notebook. -/
theorem integral_abs_autoconvolution_sub_le
    (u f : Signal) (hu : Integrable u) (hf : Integrable f) :
    (∫ x, |autoconvolution u x - autoconvolution f x|) ≤
      (∫ x, |u x - f x|) * (∫ x, |u x|) +
      (∫ x, |f x|) * (∫ x, |u x - f x|) := by
  let d : Signal := fun x ↦ u x - f x
  have hd : Integrable d := hu.sub hf
  have hdu : Integrable (d ⋆ u) := hd.integrable_convolution _ hu
  have hfd : Integrable (f ⋆ d) := hf.integrable_convolution _ hd
  have hident : ∀ᵐ x ∂volume,
      autoconvolution u x - autoconvolution f x = (d ⋆ u) x + (f ⋆ d) x := by
    filter_upwards [hd.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hu,
      hf.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hu,
      hf.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hd,
      hf.ae_convolution_exists (ContinuousLinearMap.lsmul ℝ ℝ) hf]
      with x hdu_x hfu_x hfd_x hff_x
    have hu_eq : d + f = u := by funext y; simp [d]
    have hleft : (autoconvolution u) x = (d ⋆ u) x + (f ⋆ u) x := by
      change (u ⋆ u) x = _
      calc
        (u ⋆ u) x = ((d + f) ⋆ u) x := by rw [hu_eq]
        _ = (d ⋆ u) x + (f ⋆ u) x := hdu_x.add_distrib hfu_x
    have hright : (f ⋆ u) x = (f ⋆ d) x + (autoconvolution f) x := by
      change (f ⋆ u) x = (f ⋆ d) x + (f ⋆ f) x
      calc
        (f ⋆ u) x = (f ⋆ (d + f)) x := by rw [hu_eq]
        _ = (f ⋆ d) x + (f ⋆ f) x := hfd_x.distrib_add hff_x
    rw [hleft, hright]
    ring
  have hdu_abs : Integrable (fun x ↦ |(d ⋆ u) x|) := hdu.abs
  have hfd_abs : Integrable (fun x ↦ |(f ⋆ d) x|) := hfd.abs
  calc
    (∫ x, |autoconvolution u x - autoconvolution f x|) =
        ∫ x, |(d ⋆ u) x + (f ⋆ d) x| := by
      apply integral_congr_ae
      filter_upwards [hident] with x hx
      exact congrArg (fun z : ℝ ↦ |z|) hx
    _ ≤ ∫ x, (|(d ⋆ u) x| + |(f ⋆ d) x|) := by
      exact integral_mono (hdu.add hfd).abs (hdu_abs.add hfd_abs)
        (fun x ↦ abs_add_le _ _)
    _ = (∫ x, |(d ⋆ u) x|) + (∫ x, |(f ⋆ d) x|) := by
      exact integral_add hdu_abs hfd_abs
    _ ≤ (∫ x, |d x|) * (∫ x, |u x|) +
        (∫ x, |f x|) * (∫ x, |d x|) :=
      add_le_add (integral_abs_convolution_le_mul d u hd hu)
        (integral_abs_convolution_le_mul f d hf hd)
    _ = (∫ x, |u x - f x|) * (∫ x, |u x|) +
        (∫ x, |f x|) * (∫ x, |u x - f x|) := by rfl

/-- Reverse-triangle inequality after integration: `L¹` convergence implies
convergence of `L¹` norms. -/
theorem abs_integral_abs_sub_integral_abs_le
    (u f : Signal) (hu : Integrable u) (hf : Integrable f) :
    |(∫ x, |u x|) - (∫ x, |f x|)| ≤ ∫ x, |u x - f x| := by
  rw [← integral_sub hu.abs hf.abs]
  calc
    abs (∫ x, |u x| - |f x|) ≤ ∫ x, abs (|u x| - |f x|) := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun x ↦ |u x| - |f x|))
    _ ≤ ∫ x, |u x - f x| := by
      exact integral_mono (hu.abs.sub hf.abs).abs (hu.sub hf).abs
        (fun x ↦ abs_abs_sub_abs_le_abs_sub (u x) (f x))

/-- The `L¹` mass of autoconvolution is continuous under `L¹` convergence.
No pointwise representatives or everywhere-existence assumption is used. -/
theorem tendsto_autoconvolution_mass_of_L1
    {u : ℕ → Signal} {f : Signal}
    (hu : ∀ n, Integrable (u n)) (hf : Integrable f)
    (hL1 : Tendsto (fun n ↦ ∫ x, |u n x - f x|) atTop (nhds 0)) :
    Tendsto (fun n ↦ ∫ x, |autoconvolution (u n) x|) atTop
      (nhds (∫ x, |autoconvolution f x|)) := by
  let D : ℕ → ℝ := fun n ↦ ∫ x, |u n x - f x|
  let U : ℕ → ℝ := fun n ↦ ∫ x, |u n x|
  let F : ℝ := ∫ x, |f x|
  have hU : Tendsto U atTop (nhds F) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun n ↦ dist_nonneg) _ hL1
    intro n
    simpa only [U, F, D, Real.dist_eq] using
      abs_integral_abs_sub_integral_abs_le (u n) f (hu n) hf
  have hmajor : Tendsto (fun n ↦ D n * U n + F * D n) atTop (nhds 0) := by
    simpa only [zero_mul, mul_zero, add_zero] using
      (hL1.mul hU).add (tendsto_const_nhds.mul hL1)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun n ↦ dist_nonneg) _ hmajor
  intro n
  have hau : Integrable (autoconvolution (u n)) :=
    (hu n).integrable_convolution _ (hu n)
  have haf : Integrable (autoconvolution f) := hf.integrable_convolution _ hf
  calc
    dist (∫ x, |autoconvolution (u n) x|)
        (∫ x, |autoconvolution f x|) =
        |(∫ x, |autoconvolution (u n) x|) -
          (∫ x, |autoconvolution f x|)| := Real.dist_eq _ _
    _ ≤ ∫ x, |autoconvolution (u n) x - autoconvolution f x| :=
      abs_integral_abs_sub_integral_abs_le _ _ hau haf
    _ ≤ D n * U n + F * D n := by
      simpa only [D, U, F] using
        integral_abs_autoconvolution_sub_le (u n) f (hu n) hf

/-- Named form matching the `convolutionMass` component of `score`. -/
theorem tendsto_convolutionMass_of_L1
    {u : ℕ → Signal} {f : Signal}
    (hu : ∀ n, Integrable (u n)) (hf : Integrable f)
    (hL1 : Tendsto (fun n ↦ ∫ x, |u n x - f x|) atTop (nhds 0)) :
    Tendsto (fun n ↦ convolutionMass (u n)) atTop (nhds (convolutionMass f)) := by
  simpa only [convolutionMass] using tendsto_autoconvolution_mass_of_L1 hu hf hL1

end FlatAutoconvolutionS1
