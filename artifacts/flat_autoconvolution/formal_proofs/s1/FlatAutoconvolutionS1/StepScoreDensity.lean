import FlatAutoconvolutionS1.StepDensity
import FlatAutoconvolutionS1.AdmissibleBounds

/-!
# Score density of equal-grid steps

The simultaneous `L¹`/`L²` approximation theorem is converted here into the
local score approximation form used by the supremum argument.
-/

open scoped ENNReal
open MeasureTheory Filter Topology

namespace FlatAutoconvolutionS1

/-- Every admissible signal has a nonzero nonnegative finite equal-grid step
whose score is arbitrarily close. -/
theorem Admissible.exists_equalGridStep_score_approx
    {f : Signal} (hf : Admissible f) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : EqualGridStep, |score s.toSignal - score f| < ε := by
  classical
  have hdelta (n : ℕ) : 0 < (1 : ℝ) / (n + 1) := by positivity
  choose s hs using fun n ↦
    hf.exists_equalGridStep_integral_sq_approx (hdelta n)
  let u : ℕ → Signal := fun n ↦ (s n).toSignal
  have hu1 : ∀ n, Integrable (u n) := fun n ↦ (s n).toSignal_integrable
  have hu2 : ∀ n, MemLp (u n) 2 volume := fun n ↦ (s n).toSignal_memLp_two
  have hL1 : Tendsto (fun n ↦ ∫ x, |u n x - f x|) atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact integral_nonneg fun _ ↦ abs_nonneg _
    · intro n
      have hn := (hs n).1
      calc
        (∫ x, |u n x - f x|) = ∫ x, |f x - u n x| := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [abs_sub_comm]
        _ ≤ (1 : ℝ) / (n + 1) := hn.le
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  let A : ℕ → ℝ := fun n ↦ ∫ x, (f x - u n x) ^ 2
  have hA : Tendsto A atTop (nhds 0) := by
    apply squeeze_zero
    · intro n
      exact integral_nonneg fun _ ↦ sq_nonneg _
    · intro n
      exact (hs n).2.le
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hl2eq (n : ℕ) : l2Size (u n - f) = Real.sqrt (A n) := by
    rw [l2Size_eq_integral_rpow _ ((hu2 n).sub hf.2.2.1), Real.sqrt_eq_rpow]
    congr 2
    funext x
    simp only [Pi.sub_apply, Real.rpow_two]
    rw [sq_abs]
    ring
  have hL2 : Tendsto (fun n ↦ l2Size (u n - f)) atTop (nhds 0) := by
    rw [show (fun n ↦ l2Size (u n - f)) = fun n ↦ Real.sqrt (A n) by
      funext n
      exact hl2eq n]
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hA
  have hscore : Tendsto (fun n ↦ score (u n)) atTop (nhds (score f)) :=
    tendsto_score_of_L1_L2 hu1 hf.2.1 hu2 hf.2.2.1 hL1 hL2
      hf.score_denominator_ne_zero
  have hevent : ∀ᶠ n in atTop, dist (score (u n)) (score f) < ε :=
    (Metric.tendsto_nhds.mp hscore) ε hε
  obtain ⟨n, hn⟩ := hevent.exists
  exact ⟨s n, by simpa only [u, Real.dist_eq] using hn⟩

end FlatAutoconvolutionS1
