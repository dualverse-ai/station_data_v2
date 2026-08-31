import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open scoped ENNReal NNReal
open Set MeasureTheory Filter

namespace HardyLittlewoodS1

/-- The mass of a nonnegative function on the open interval of centre `y` and radius `t`. -/
noncomputable def intervalMass (f : ℝ → ℝ≥0) (y t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Ioo (y - t) (y + t), (f z : ℝ≥0∞)

/-- The non-tangential Hardy--Littlewood maximal operator of aperture `alpha`.

The two proof-indexed suprema impose positivity of the radius and the aperture constraint.
-/
noncomputable def nonTangentialMaximal (alpha : ℝ) (f : ℝ → ℝ≥0) (x : ℝ) : ℝ≥0∞ :=
  ⨆ (y : ℝ) (t : ℝ) (_ht : 0 < t) (_hxy : |x - y| ≤ alpha * t),
    intervalMass f y t / ENNReal.ofReal (2 * t)

/-- The strict superlevel set `{x | M^alpha f x > lambda}`. -/
def strictSuperlevel (alpha : ℝ) (f : ℝ → ℝ≥0) (lambda : ℝ≥0) : Set ℝ :=
  {x | (lambda : ℝ≥0∞) < nonTangentialMaximal alpha f x}

/-- The `L¹` mass of a nonnegative function. -/
noncomputable def totalMass (f : ℝ → ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ x, (f x : ℝ≥0∞)

/-- `C` is a weak `(1,1)` constant at aperture `alpha`.

The inequality is written without division by the positive level.  The explicit finiteness
hypothesis is exactly the `L¹` assumption for a nonnegative function.
-/
def WeakTypeBound (alpha : ℝ) (C : ℝ≥0∞) : Prop :=
  ∀ (f : ℝ → ℝ≥0), AEMeasurable f volume → totalMass f < ∞ →
    ∀ (lambda : ℝ≥0), lambda ≠ 0 →
      (lambda : ℝ≥0∞) * volume (strictSuperlevel alpha f lambda) ≤ C * totalMass f

/-- The sharp weak `(1,1)` constant. -/
noncomputable def sharpConstant (alpha : ℝ) : ℝ≥0∞ :=
  sInf {C | WeakTypeBound alpha C}

end HardyLittlewoodS1
