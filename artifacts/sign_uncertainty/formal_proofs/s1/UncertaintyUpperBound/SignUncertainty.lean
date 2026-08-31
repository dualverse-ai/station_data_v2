import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

namespace UncertaintyUpperBound

open MeasureTheory Set
open scoped FourierTransform

def IsTailRadius (f : ℝ → ℝ) (r : ℝ) : Prop :=
  0 < r ∧ ∀ x : ℝ, r ≤ |x| → 0 ≤ f x

def IsEvenFunction (f : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, f (-x) = f x

noncomputable def signRadius (f : ℝ → ℝ) : ℝ :=
  sInf {r : ℝ | IsTailRadius f r}

lemma signRadius_nonneg {f : ℝ → ℝ} (h : ∃ r, IsTailRadius f r) :
    0 ≤ signRadius f := by
  apply le_csInf
  · simpa only [Set.nonempty_def, Set.mem_setOf_eq] using h
  · intro b hb
    exact hb.1.le

lemma signRadius_le {f : ℝ → ℝ} {r : ℝ} (hr : IsTailRadius f r) :
    signRadius f ≤ r := by
  apply csInf_le
  · exact ⟨0, fun _ hs => hs.1.le⟩
  · exact hr

/-- The paper's admissible class, represented as a pair of real functions so that the
complex-valued Mathlib Fourier integral can be related to an ordered real transform. -/
structure AdmissiblePair where
  f : ℝ → ℝ
  fourier : ℝ → ℝ
  f_integrable : Integrable f
  fourier_integrable : Integrable fourier
  f_even : IsEvenFunction f
  fourier_even : IsEvenFunction fourier
  f_nonzero : f ≠ 0
  transform_eq : 𝓕 (fun x : ℝ => (f x : ℂ)) = fun x : ℝ => (fourier x : ℂ)
  f_origin_negative : f 0 < 0
  fourier_origin_negative : fourier 0 < 0
  f_eventually_nonnegative : ∃ r, IsTailRadius f r
  fourier_eventually_nonnegative : ∃ r, IsTailRadius fourier r

noncomputable def AdmissiblePair.score (p : AdmissiblePair) : ℝ :=
  signRadius p.f * signRadius p.fourier

noncomputable def signUncertaintyConstant : ℝ :=
  sInf (Set.range (fun p : AdmissiblePair => p.score))

/-- Paper notation for the one-dimensional sign-uncertainty constant. -/
noncomputable abbrev C_SU : ℝ := signUncertaintyConstant

lemma admissible_score_nonneg (p : AdmissiblePair) : 0 ≤ p.score :=
  mul_nonneg (signRadius_nonneg p.f_eventually_nonnegative)
    (signRadius_nonneg p.fourier_eventually_nonnegative)

theorem signUncertaintyConstant_le_score (p : AdmissiblePair) :
    signUncertaintyConstant ≤ p.score := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact admissible_score_nonneg q
  · exact ⟨p, rfl⟩

lemma selfFourier_score_le_sq (p : AdmissiblePair) (hself : p.fourier = p.f)
    {r : ℝ} (hr : IsTailRadius p.f r) : p.score ≤ r ^ 2 := by
  rw [AdmissiblePair.score, hself, pow_two]
  exact mul_le_mul (signRadius_le hr) (signRadius_le hr)
    (signRadius_nonneg p.f_eventually_nonnegative) hr.1.le

end UncertaintyUpperBound
