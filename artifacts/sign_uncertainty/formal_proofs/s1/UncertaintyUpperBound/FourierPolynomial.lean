import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Tactic.Ring

namespace UncertaintyUpperBound

open MeasureTheory Polynomial
open scoped FourierTransform

noncomputable def gaussian (x : ℝ) : ℂ :=
  Complex.exp (-Real.pi * (x : ℂ) ^ 2)

noncomputable def polyGaussian (p : ℂ[X]) (x : ℝ) : ℂ :=
  p.eval (x : ℂ) * gaussian x

lemma fourier_gaussian : 𝓕 gaussian = gaussian := by
  have h := fourierIntegral_gaussian_pi (b := (1 : ℂ)) (by norm_num)
  unfold gaussian
  simpa using h

lemma integrable_monomial_gaussian (n : ℕ) :
    Integrable (fun x : ℝ => (x : ℂ) ^ n * gaussian x) := by
  have hr : Integrable (fun x : ℝ => x ^ n * Real.exp (-Real.pi * x ^ 2)) := by
    simpa [Real.rpow_natCast] using
      (integrable_rpow_mul_exp_neg_mul_sq Real.pi_pos (s := (n : ℝ)) (by
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith))
  have hc := hr.ofReal (𝕜 := ℂ)
  convert hc using 1 with x
  simp [gaussian, Complex.ofReal_exp]

lemma integrable_polyGaussian (p : ℂ[X]) : Integrable (polyGaussian p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      convert hp.add hq using 1
      funext x
      simp [polyGaussian, add_mul]
  | monomial n a =>
      convert (integrable_monomial_gaussian n).const_mul a using 1
      funext x
      simp [polyGaussian, mul_assoc]

noncomputable def raisingPolynomial (p : ℂ[X]) : ℂ[X] :=
  p.derivative - C (4 * (Real.pi : ℂ)) * X * p

noncomputable def raisingOperator (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  deriv f x - (2 * Real.pi * x) • f x

lemma hasDerivAt_polyGaussian (p : ℂ[X]) (x : ℝ) :
    HasDerivAt (polyGaussian p) (polyGaussian
      (p.derivative - C (2 * (Real.pi : ℂ)) * X * p) x) x := by
  have hp := (p.hasDerivAt (x : ℂ))
  have hg := ((hasDerivAt_pow 2 (x : ℂ)).const_mul (-(Real.pi : ℂ))).cexp
  convert (hp.mul hg).comp_ofReal using 1 <;>
    simp [polyGaussian, gaussian, pow_two]
  ring_nf

lemma deriv_polyGaussian (p : ℂ[X]) :
    deriv (polyGaussian p) =
      polyGaussian (p.derivative - C (2 * (Real.pi : ℂ)) * X * p) := by
  funext x
  exact (hasDerivAt_polyGaussian p x).deriv

lemma raising_polyGaussian (p : ℂ[X]) :
    raisingOperator (polyGaussian p) = polyGaussian (raisingPolynomial p) := by
  funext x
  rw [raisingOperator, deriv_polyGaussian]
  simp only [polyGaussian, raisingPolynomial, eval_sub, eval_mul, eval_C, eval_X,
    Complex.real_smul]
  push_cast
  ring

lemma fourier_const_mul (c : ℂ) (f : ℝ → ℂ) :
    𝓕 (fun x => c * f x) = fun x => c * 𝓕 f x := by
  simpa only [Pi.smul_apply, smul_eq_mul] using
    (VectorFourier.fourierIntegral_const_smul 𝐞 volume (innerₗ ℝ) f c)

lemma fourier_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    𝓕 (fun x => f x + g x) = fun x => 𝓕 f x + 𝓕 g x := by
  simpa only [Pi.add_apply] using
    (VectorFourier.fourierIntegral_add (L := innerₗ ℝ) Real.continuous_fourierChar
      (by fun_prop) hf hg)

lemma fourier_mul_x (p : ℂ[X]) :
    𝓕 (fun x : ℝ => (x : ℂ) * polyGaussian p x) =
      fun x => Complex.I / (2 * Real.pi) * deriv (𝓕 (polyGaussian p)) x := by
  have hd := Real.deriv_fourierIntegral (integrable_polyGaussian p) (by
    convert integrable_polyGaussian (X * p) using 1
    funext x
    simp [polyGaussian, Complex.real_smul, mul_assoc])
  have hs := fourier_const_mul (-2 * Real.pi * Complex.I)
    (fun x : ℝ => (x : ℂ) * polyGaussian p x)
  rw [hd]
  have hfun : (fun x : ℝ => (-2 * Real.pi * Complex.I * x) • polyGaussian p x) =
      fun x : ℝ => (-2 * Real.pi * Complex.I) * ((x : ℂ) * polyGaussian p x) := by
    funext x
    simp only [smul_eq_mul]
    push_cast
    ring
  rw [hfun, hs]
  funext x
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  rw [Complex.I_sq]
  ring

theorem fourier_raising_polyGaussian (p : ℂ[X]) :
    𝓕 (raisingOperator (polyGaussian p)) =
      fun x => -Complex.I * raisingOperator (𝓕 (polyGaussian p)) x := by
  have hdiff : Integrable (deriv (polyGaussian p)) := by
    rw [deriv_polyGaussian]
    exact integrable_polyGaussian _
  have hmul : Integrable (fun x : ℝ => (x : ℂ) * polyGaussian p x) := by
    convert integrable_polyGaussian (X * p) using 1
    funext x
    simp [polyGaussian, mul_assoc]
  have hscaled : Integrable
      (fun x : ℝ => (-2 * Real.pi : ℂ) * ((x : ℂ) * polyGaussian p x)) :=
    hmul.const_mul _
  have hshape : raisingOperator (polyGaussian p) = fun x =>
      deriv (polyGaussian p) x + (-2 * Real.pi : ℂ) * ((x : ℂ) * polyGaussian p x) := by
    funext x
    simp only [raisingOperator, Complex.real_smul]
    push_cast
    ring
  rw [hshape, fourier_add hdiff hscaled, fourier_const_mul,
    Real.fourierIntegral_deriv (integrable_polyGaussian p)
      (fun x => (hasDerivAt_polyGaussian p x).differentiableAt)
      hdiff,
    fourier_mul_x]
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, raisingOperator,
    Complex.real_smul]
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

noncomputable def raisedPolynomial : ℕ → ℂ[X]
  | 0 => 1
  | n + 1 => raisingPolynomial (raisedPolynomial n)

lemma raisingOperator_const_mul (c : ℂ) (p : ℂ[X]) :
    raisingOperator (fun x => c * polyGaussian p x) =
      fun x => c * raisingOperator (polyGaussian p) x := by
  funext x
  have hd := (hasDerivAt_polyGaussian p x).const_mul c
  simp only [raisingOperator, hd.deriv, Complex.real_smul]
  rw [← congrFun (deriv_polyGaussian p) x]
  push_cast
  ring

theorem fourier_raisedPolynomial (m : ℕ) :
    𝓕 (polyGaussian (raisedPolynomial m)) =
      fun x => (-Complex.I) ^ m * polyGaussian (raisedPolynomial m) x := by
  induction m with
  | zero =>
      have hpg : polyGaussian 1 = gaussian := by
        funext x
        simp [polyGaussian]
      simpa [raisedPolynomial, hpg] using fourier_gaussian
  | succ m ih =>
      rw [raisedPolynomial, ← raising_polyGaussian, fourier_raising_polyGaussian, ih,
        raisingOperator_const_mul]
      funext x
      simp only [pow_succ]
      ring

theorem fourier_raisedPolynomial_four_mul (j : ℕ) :
    𝓕 (polyGaussian (raisedPolynomial (4 * j))) =
      polyGaussian (raisedPolynomial (4 * j)) := by
  rw [fourier_raisedPolynomial]
  funext x
  rw [show (-Complex.I) ^ (4 * j) = 1 by
    rw [pow_mul, show (-Complex.I) ^ 4 = 1 by
      calc
        (-Complex.I) ^ 4 = (Complex.I ^ 2) ^ 2 := by ring
        _ = 1 := by rw [Complex.I_sq]; norm_num,
      one_pow],
    one_mul]

end UncertaintyUpperBound
