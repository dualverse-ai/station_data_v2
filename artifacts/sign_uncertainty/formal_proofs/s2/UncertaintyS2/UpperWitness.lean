import UncertaintyS2.Definitions
import UncertaintyS2.CertificateData

namespace UncertaintyS2

open Polynomial

def mulCoeffs (p q : Array ℚ) : Array ℚ :=
  if p.size = 0 ∨ q.size = 0 then #[] else
    (Array.range (p.size + q.size - 1)).map fun n =>
      ∑ i ∈ Finset.range (n + 1), coeffAt p i * coeffAt q (n - i)

def rootSquareCoeffs (r : ℚ) : Array ℚ := #[r ^ 2, -2 * r, 1]

def factorProductCoeffsN : ℕ → Array ℚ
  | 0 => #[0, 1]
  | n + 1 => mulCoeffs (factorProductCoeffsN n)
      (rootSquareCoeffs CertificateData.roots[n]!)

def factorProductCoeffs : Array ℚ := factorProductCoeffsN 20

def rawFactorCoeffs : Array ℚ :=
  mulCoeffs factorProductCoeffs CertificateData.residualCoefficients

def laguerreExpansionCoeffsN : ℕ → Array ℚ
  | 0 => #[0]
  | n + 1 => addCoeffs (laguerreExpansionCoeffsN n)
      (scaleCoeffs CertificateData.laguerreCoefficients[n]!
        (laguerreHalfCoeffs (2 * n)))

def laguerreExpansionCoeffs : Array ℚ :=
  laguerreExpansionCoeffsN CertificateData.laguerreCoefficients.size

def normalizeAtDerivative (p : Array ℚ) : Array ℚ :=
  scaleCoeffs (1 / coeffAt p 1) p

def witnessPowerCoeffs : Array ℚ := normalizeAtDerivative rawFactorCoeffs

def witnessLaguerrePowerCoeffs : Array ℚ := normalizeAtDerivative laguerreExpansionCoeffs

noncomputable def witnessQ : Polynomial ℚ := polynomialOfArray witnessPowerCoeffs

noncomputable def witnessR : Polynomial ℝ := witnessQ.map (Rat.castHom ℝ)

noncomputable def residualQ : Polynomial ℚ :=
  polynomialOfArray CertificateData.residualCoefficients

noncomputable def residualR : Polynomial ℝ := residualQ.map (Rat.castHom ℝ)

noncomputable def rootFactorQ : Polynomial ℚ := polynomialOfArray factorProductCoeffs

noncomputable def rawFactorPolynomialQ : Polynomial ℚ := rootFactorQ * residualQ

def rawFactorDerivative : ℚ := coeffAt rawFactorCoeffs 1

set_option maxHeartbeats 0 in
theorem exact_laguerre_factor_recomposition :
    witnessLaguerrePowerCoeffs = witnessPowerCoeffs := by
  native_decide

set_option maxHeartbeats 0 in
theorem rawFactorDerivative_pos : 0 < rawFactorDerivative := by
  native_decide

theorem polynomialOfArray_scale (c : ℚ) (p : Array ℚ) :
    polynomialOfArray (scaleCoeffs c p) = C c * polynomialOfArray p := by
  ext n
  simp only [coeff_polynomialOfArray, coeff_C_mul]
  by_cases hn : n < p.size
  · rw [if_pos]
    · simp [scaleCoeffs, hn]
    · simpa [scaleCoeffs] using hn
  · rw [if_neg]
    · simp [hn]
    · simpa [scaleCoeffs] using hn

theorem polynomialOfArray_add (p q : Array ℚ) :
    polynomialOfArray (addCoeffs p q) = polynomialOfArray p + polynomialOfArray q := by
  ext n
  rw [coeff_add, coeff_polynomialOfArray, coeff_polynomialOfArray,
    coeff_polynomialOfArray, ← coeffAt_eq, ← coeffAt_eq, ← coeffAt_eq]
  by_cases hn : n < max p.size q.size
  · have hs : n < (addCoeffs p q).size := by simpa [addCoeffs] using hn
    rw [coeffAt_eq, if_pos hs]
    simp [addCoeffs, hn, coeffAt_eq]
  · have hp : ¬ n < p.size := fun h => hn (lt_of_lt_of_le h (Nat.le_max_left _ _))
    have hq : ¬ n < q.size := fun h => hn (lt_of_lt_of_le h (Nat.le_max_right _ _))
    rw [coeffAt_eq]
    simp [addCoeffs, hn, coeffAt_eq, hp, hq]

theorem polynomialOfArray_mul (p q : Array ℚ) :
    polynomialOfArray (mulCoeffs p q) = polynomialOfArray p * polynomialOfArray q := by
  ext n
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    coeff_polynomialOfArray, ← coeffAt_eq]
  simp only [coeff_polynomialOfArray, ← coeffAt_eq]
  by_cases he : p.size = 0 ∨ q.size = 0
  · rcases he with hp | hq
    · simp [mulCoeffs, hp, polynomialOfArray, coeffAt]
    · simp [mulCoeffs, hq, polynomialOfArray, coeffAt]
  · have hp : 0 < p.size := Nat.pos_of_ne_zero (fun h => he (Or.inl h))
    have hq : 0 < q.size := Nat.pos_of_ne_zero (fun h => he (Or.inr h))
    have he' : ¬ (p = #[] ∨ q = #[]) := by simpa using he
    by_cases hn : n < p.size + q.size - 1
    · simp [mulCoeffs, he', hn, coeffAt]
    · have hleft : coeffAt (mulCoeffs p q) n = 0 := by
        simp [mulCoeffs, he', coeffAt, hn]
      rw [hleft]
      symm
      apply Finset.sum_eq_zero
      intro i hi
      by_cases hip : i < p.size
      · have hiN : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have hiq : ¬ n - i < q.size := by omega
        simp [coeffAt_eq, hip, hiq]
      · simp [coeffAt_eq, hip]

theorem polynomialOfArray_rootSquare (r : ℚ) :
    polynomialOfArray (rootSquareCoeffs r) = (X - C r) ^ 2 := by
  unfold rootSquareCoeffs polynomialOfArray
  simp [Finset.sum_range_succ]
  norm_num
  rw [show C (2 : ℚ) = (2 : ℚ[X]) by exact C_eq_natCast 2]
  ring

theorem polynomialOfArray_factorProductN (n : ℕ) (hn : n ≤ 20) :
    polynomialOfArray (factorProductCoeffsN n) =
      X * ∏ i ∈ Finset.range n, (X - C CertificateData.roots[i]!) ^ 2 := by
  induction n with
  | zero =>
      unfold factorProductCoeffsN polynomialOfArray
      simp [Finset.sum_range_succ]
  | succ n ih =>
      have hn' : n ≤ 20 := Nat.le_trans (Nat.le_succ n) hn
      rw [factorProductCoeffsN, polynomialOfArray_mul, ih hn',
        polynomialOfArray_rootSquare, Finset.prod_range_succ]
      ring

theorem exact_semantic_factorization :
    witnessQ = C (1 / rawFactorDerivative) * rawFactorPolynomialQ := by
  rw [witnessQ, witnessPowerCoeffs, normalizeAtDerivative, polynomialOfArray_scale,
    rawFactorDerivative, rawFactorPolynomialQ, rootFactorQ, residualQ,
    ← polynomialOfArray_mul]
  rfl

theorem polynomialOfArray_laguerreExpansionN (n : ℕ)
    (hn : n ≤ CertificateData.laguerreCoefficients.size) :
    polynomialOfArray (laguerreExpansionCoeffsN n) =
      ∑ j ∈ Finset.range n,
        C CertificateData.laguerreCoefficients[j]! * laguerreHalfQ (2 * j) := by
  induction n with
  | zero => norm_num [laguerreExpansionCoeffsN, polynomialOfArray]
  | succ n ih =>
      have hn' : n ≤ CertificateData.laguerreCoefficients.size := Nat.le_trans (Nat.le_succ n) hn
      rw [laguerreExpansionCoeffsN, polynomialOfArray_add, polynomialOfArray_scale,
        ih hn', Finset.sum_range_succ]
      rfl

theorem polynomialOfArray_laguerreExpansion :
    polynomialOfArray laguerreExpansionCoeffs =
      ∑ j ∈ Finset.range CertificateData.laguerreCoefficients.size,
        C CertificateData.laguerreCoefficients[j]! * laguerreHalfQ (2 * j) := by
  exact polynomialOfArray_laguerreExpansionN _ (le_refl _)

theorem certificate_laguerre_size : CertificateData.laguerreCoefficients.size = 42 := by
  native_decide

theorem witness_coeff_zero : coeffAt witnessPowerCoeffs 0 = 0 := by native_decide

theorem witness_coeff_one : coeffAt witnessPowerCoeffs 1 = 1 := by native_decide

def derivativeCoeffs (p : Array ℚ) : Array ℚ :=
  (Array.range (p.size - 1)).map fun i => (i + 1) * p[i + 1]!

def evalCoeffs (p : Array ℚ) (x : ℚ) : ℚ :=
  ∑ i ∈ Finset.range p.size, p[i]! * x ^ i

theorem derivative_polynomialOfArray (p : Array ℚ) :
    (polynomialOfArray p).derivative = polynomialOfArray (derivativeCoeffs p) := by
  ext n
  rw [coeff_derivative, coeff_polynomialOfArray, coeff_polynomialOfArray]
  simp only [derivativeCoeffs, Array.size_map, Array.size_range]
  by_cases hn : n < p.size - 1
  · have hn1 : n + 1 < p.size := by omega
    rw [if_pos hn1, if_pos hn]
    simp [derivativeCoeffs, hn]
    ring
  · have hn1 : ¬ n + 1 < p.size := by omega
    rw [if_neg hn1, if_neg hn]
    simp

set_option maxHeartbeats 0 in
theorem witness_double_roots_exact :
    ∀ i : Fin 20,
      evalCoeffs witnessPowerCoeffs CertificateData.roots[i] = 0 ∧
        evalCoeffs (derivativeCoeffs witnessPowerCoeffs) CertificateData.roots[i] = 0 := by
  native_decide

theorem witness_in_span_20 : InEvenLaguerreSpan 20 witnessR := by
  let d : ℚ := coeffAt laguerreExpansionCoeffs 1
  let c : ℕ → ℝ := fun j =>
    ((1 / d) * CertificateData.laguerreCoefficients[j]! : ℚ)
  refine ⟨c, ?_⟩
  have harray : witnessPowerCoeffs = witnessLaguerrePowerCoeffs :=
    exact_laguerre_factor_recomposition.symm
  rw [witnessR, witnessQ, harray, witnessLaguerrePowerCoeffs,
    normalizeAtDerivative, polynomialOfArray_scale,
    polynomialOfArray_laguerreExpansion]
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_sum, laguerreHalfR,
    Rat.coe_castHom]
  rw [certificate_laguerre_size]
  rw [Finset.mul_sum]
  norm_num
  apply Finset.sum_congr rfl
  intro j hj
  simp only [c, d]
  push_cast
  rw [← mul_assoc, ← C_mul]
  congr 1
  norm_num

theorem witness_at_zero_R : witnessR.eval 0 = 0 := by
  have hQ : witnessQ.eval 0 = 0 := by
    rw [← coeff_zero_eq_eval_zero, witnessQ, coeff_polynomialOfArray, ← coeffAt_eq,
      witness_coeff_zero]
  rw [witnessR, eval_map]
  rw [show (0 : ℝ) = (Rat.castHom ℝ) 0 by norm_num, eval₂_at_apply, hQ]

theorem witness_derivative_at_zero_R : witnessR.derivative.eval 0 = 1 := by
  have hQ : witnessQ.derivative.eval 0 = 1 := by
    rw [← coeff_zero_eq_eval_zero, coeff_derivative, witnessQ,
      coeff_polynomialOfArray, ← coeffAt_eq, witness_coeff_one]
    norm_num
  rw [witnessR, derivative_map, eval_map]
  rw [show (0 : ℝ) = (Rat.castHom ℝ) 0 by norm_num, eval₂_at_apply, hQ]
  norm_num

theorem roots_size : CertificateData.roots.size = 20 := by native_decide

theorem roots_positive_Q : ∀ i : Fin 20, (0 : ℚ) < CertificateData.roots[i] := by
  native_decide

theorem roots_positive : ∀ i : Fin 20, (0 : ℝ) < CertificateData.roots[i] := by
  intro i
  exact (Rat.cast_pos (K := ℝ)).mpr (roots_positive_Q i)

theorem roots_strict_Q :
    StrictMono (fun i : Fin 20 => CertificateData.roots[i]) := by
  native_decide

theorem roots_strictMono : StrictMono (fun i : Fin 20 => (CertificateData.roots[i] : ℝ)) := by
  intro i j hij
  exact (Rat.cast_lt (K := ℝ)).mpr (roots_strict_Q hij)

theorem witness_double_roots_R (i : Fin 20) :
    witnessR.eval (CertificateData.roots[i] : ℝ) = 0 ∧
      witnessR.derivative.eval (CertificateData.roots[i] : ℝ) = 0 := by
  have h := witness_double_roots_exact i
  have hvalueQ : witnessQ.eval CertificateData.roots[i] = 0 := by
    rw [witnessQ, eval_polynomialOfArray]
    exact h.1
  have hderivQ : witnessQ.derivative.eval CertificateData.roots[i] = 0 := by
    rw [witnessQ, derivative_polynomialOfArray, eval_polynomialOfArray]
    exact h.2
  constructor
  · rw [witnessR, eval_map]
    rw [show (CertificateData.roots[i] : ℝ) =
      (Rat.castHom ℝ) CertificateData.roots[i] by rfl, eval₂_at_apply, hvalueQ]
    norm_num
  · rw [witnessR, derivative_map, eval_map]
    rw [show (CertificateData.roots[i] : ℝ) =
      (Rat.castHom ℝ) CertificateData.roots[i] by rfl, eval₂_at_apply, hderivQ]
    norm_num

end UncertaintyS2
