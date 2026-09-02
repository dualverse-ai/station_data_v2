import FlatAutoconvolutionS1.Definitions

/-!
# Continuity of the score in its three output statistics

The analytic and probabilistic parts of the notebook both first establish
convergence of the three autoconvolution norms.  This file records the exact
nonvanishing-denominator passage to `Q` once, independently of how those
convergences are obtained.
-/

open Filter Topology

namespace FlatAutoconvolutionS1

theorem tendsto_score_of_components
    {ι : Type*} {l : Filter ι} {f : ι → Signal} {g : Signal}
    (henergy : Tendsto (fun n => convolutionEnergy (f n)) l
      (𝓝 (convolutionEnergy g)))
    (hmass : Tendsto (fun n => convolutionMass (f n)) l
      (𝓝 (convolutionMass g)))
    (hpeak : Tendsto (fun n => convolutionPeak (f n)) l
      (𝓝 (convolutionPeak g)))
    (hden : convolutionMass g * convolutionPeak g ≠ 0) :
    Tendsto (fun n => score (f n)) l (𝓝 (score g)) := by
  simpa only [score] using henergy.div (hmass.mul hpeak) hden

theorem abs_score_lt_of_components_eventually
    {ι : Type*} {l : Filter ι} {f : ι → Signal} {g : Signal}
    (henergy : Tendsto (fun n => convolutionEnergy (f n)) l
      (𝓝 (convolutionEnergy g)))
    (hmass : Tendsto (fun n => convolutionMass (f n)) l
      (𝓝 (convolutionMass g)))
    (hpeak : Tendsto (fun n => convolutionPeak (f n)) l
      (𝓝 (convolutionPeak g)))
    (hden : convolutionMass g * convolutionPeak g ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in l, |score (f n) - score g| < ε := by
  have h := tendsto_score_of_components henergy hmass hpeak hden
  simpa [Real.dist_eq] using Metric.tendsto_nhds.mp h ε hε

end FlatAutoconvolutionS1
