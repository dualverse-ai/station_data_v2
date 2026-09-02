import FlatAutoconvolutionS1.ConvolutionMass
import FlatAutoconvolutionS1.ConvolutionL2

/-!
# Positivity of the score denominator

The `ENNReal.toReal` in the definition of the essential-supremum peak is
harmless on the paper's admissible class: Cauchy--Schwarz makes the norm
finite, while positive convolution mass makes it nonzero.
-/

open scoped ENNReal
open MeasureTheory

namespace FlatAutoconvolutionS1

theorem Admissible.convolutionPeak_pos {f : Signal} (hf : Admissible f) :
    0 < convolutionPeak f := by
  have hfinite := eLpNorm_top_autoconvolution_ne_top f hf.2.2.1
  have hmeas := aestronglyMeasurable_convolution_of_memLp_two f f hf.2.2.1 hf.2.2.1
  have hnonzero : eLpNorm (autoconvolution f) ⊤ volume ≠ 0 := by
    intro hz
    have hae : autoconvolution f =ᵐ[volume] 0 :=
      (eLpNorm_eq_zero_iff hmeas (by simp)).mp hz
    have hmasszero : convolutionMass f = 0 := by
      unfold convolutionMass
      apply integral_eq_zero_of_ae
      filter_upwards [hae] with x hx
      simpa only [Pi.zero_apply, abs_zero] using congrArg abs hx
    exact (ne_of_gt hf.convolutionMass_pos) hmasszero
  unfold convolutionPeak
  exact ENNReal.toReal_pos hnonzero hfinite

theorem Admissible.score_denominator_ne_zero {f : Signal} (hf : Admissible f) :
    convolutionMass f * convolutionPeak f ≠ 0 :=
  mul_ne_zero (ne_of_gt hf.convolutionMass_pos) (ne_of_gt hf.convolutionPeak_pos)

end FlatAutoconvolutionS1
