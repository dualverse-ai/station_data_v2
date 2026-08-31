import UncertaintyS2.UpperComputation
import Mathlib.Tactic.Linarith

namespace UncertaintyS2

open Polynomial
open scoped Polynomial

def hasseCoefficientArray (ell : ℕ) : Array ℚ :=
  (Array.range (residualDegree + 1 - ell)).map fun k =>
    Nat.choose (k + ell) ell * CertificateData.residualCoefficients[k + ell]!

lemma residual_coefficients_size : CertificateData.residualCoefficients.size = 42 := by
  native_decide

lemma hasseCoefficientArray_get (ell k : ℕ) (hk : k < residualDegree + 1 - ell) :
    (hasseCoefficientArray ell)[k]! =
      Nat.choose (k + ell) ell * CertificateData.residualCoefficients[k + ell]! := by
  have hs : k < (hasseCoefficientArray ell).size := by
    simpa [hasseCoefficientArray] using hk
  rw [getElem!_pos _ k hs]
  simp [hasseCoefficientArray, hk]

lemma hasseDeriv_residual_eq (ell : ℕ) :
    hasseDeriv ell residualQ = polynomialOfArray (hasseCoefficientArray ell) := by
  ext k
  rw [hasseDeriv_coeff, coeff_polynomialOfArray]
  by_cases hk : k < residualDegree + 1 - ell
  · have hsum : k + ell < CertificateData.residualCoefficients.size := by
      rw [residual_coefficients_size]
      dsimp [residualDegree] at hk
      omega
    rw [if_pos]
    · rw [residualQ, coeff_polynomialOfArray, if_pos hsum,
        hasseCoefficientArray_get ell k hk]
    · simpa [hasseCoefficientArray] using hk
  · have hsum : ¬ k + ell < CertificateData.residualCoefficients.size := by
      rw [residual_coefficients_size]
      dsimp [residualDegree] at hk
      omega
    rw [if_neg]
    · rw [residualQ, coeff_polynomialOfArray, if_neg hsum]
      simp
    · simpa [hasseCoefficientArray] using hk

noncomputable def affineResidualQ (a b : ℚ) : Polynomial ℚ :=
  residualQ.comp (C a + C (b - a) * X)

noncomputable def bernsteinResidualQ (a b : ℚ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (residualDegree + 1),
    C ((bernsteinCoefficients a b)[j]!) *
      _root_.bernsteinPolynomial ℚ residualDegree j

lemma qPowerCoefficient_eq_affine_coeff (a b : ℚ) (ell : ℕ) :
    qPowerCoefficient a b ell = (affineResidualQ a b).coeff ell := by
  rw [affineResidualQ]
  have hcomp :
      residualQ.comp (C a + C (b - a) * X) =
        (taylor a residualQ).comp (C (b - a) * X) := by
    rw [taylor_apply, comp_assoc]
    congr 1
    simp [add_comp, X_comp, C_comp]
    ring
  rw [hcomp, comp_C_mul_X_coeff, taylor_coeff, hasseDeriv_residual_eq,
    eval_polynomialOfArray]
  rw [show (hasseCoefficientArray ell).size = residualDegree + 1 - ell by
    simp [hasseCoefficientArray]]
  change qPowerCoefficient a b ell =
    (∑ k ∈ Finset.range (residualDegree + 1 - ell),
      (hasseCoefficientArray ell)[k]! * a ^ k) * (b - a) ^ ell
  rw [qPowerCoefficient, mul_comm]
  apply congrArg (fun z : ℚ => z * (b - a) ^ ell)
  apply Finset.sum_congr rfl
  intro k hk
  rw [hasseCoefficientArray_get ell k (Finset.mem_range.mp hk)]
  ring

lemma affine_eq_qPowerPolynomial (a b : ℚ) :
    affineResidualQ a b = polynomialOfArray (qPowerCoefficients a b) := by
  ext r
  rw [← qPowerCoefficient_eq_affine_coeff, coeff_polynomialOfArray]
  by_cases hr : r < residualDegree + 1
  · rw [if_pos]
    · simp [qPowerCoefficients, hr]
    · simpa [qPowerCoefficients] using hr
  · rw [if_neg]
    · have hz : residualDegree + 1 - r = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hr)
      simp [qPowerCoefficient, hz]
    · simpa [qPowerCoefficients] using hr

lemma coeff_one_sub_X_pow (n k : ℕ) :
    (((1 - X) ^ n : ℚ[X]).coeff k) = Nat.choose n k * (-1 : ℚ) ^ k := by
  rw [show (1 - X : ℚ[X]) ^ n = ((1 + X) ^ n).comp (C (-1) * X) by
    rw [pow_comp, add_comp, one_comp, X_comp]
    congr 1
    simpa [sub_eq_add_neg]]
  rw [comp_C_mul_X_coeff, coeff_one_add_X_pow]

lemma coeff_bernsteinPolynomial (n j r : ℕ) (hj : j ≤ r) :
    (_root_.bernsteinPolynomial ℚ n j).coeff r =
      Nat.choose n j * Nat.choose (n - j) (r - j) * (-1 : ℚ) ^ (r - j) := by
  rw [_root_.bernsteinPolynomial]
  rw [show (Nat.choose n j : ℚ[X]) = C (Nat.choose n j : ℚ) by simp, mul_assoc]
  rw [coeff_C_mul, coeff_X_pow_mul', if_pos hj, coeff_one_sub_X_pow]
  ring

lemma bernsteinResidual_coeff (a b : ℚ) {r : ℕ} (hr : r < residualDegree + 1) :
    (bernsteinResidualQ a b).coeff r =
      (bernsteinPowerCoefficientsFrom (bernsteinCoefficients a b))[r]! := by
  rw [bernsteinResidualQ]
  change (lcoeff ℚ r) (∑ j ∈ Finset.range (residualDegree + 1),
    C ((bernsteinCoefficients a b)[j]!) *
      _root_.bernsteinPolynomial ℚ residualDegree j) = _
  rw [map_sum]
  simp only [lcoeff_apply, coeff_C_mul]
  have hsub : Finset.range (r + 1) ⊆ Finset.range (residualDegree + 1) := by
    intro j hj
    exact Finset.mem_range.mpr (lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hr)
  have hzero : ∀ j ∈ Finset.range (residualDegree + 1), j ∉ Finset.range (r + 1) →
      (bernsteinCoefficients a b)[j]! *
        (_root_.bernsteinPolynomial ℚ residualDegree j).coeff r = 0 := by
    intro j hjbig hjnot
    have hrj : r < j := by simpa [Finset.mem_range, Nat.not_lt] using hjnot
    rw [_root_.bernsteinPolynomial]
    rw [show (Nat.choose residualDegree j : ℚ[X]) = C (Nat.choose residualDegree j : ℚ) by simp,
      mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_neg (Nat.not_le.mpr hrj)]
    simp
  rw [← Finset.sum_subset hsub hzero]
  · have hs : r < (bernsteinPowerCoefficientsFrom (bernsteinCoefficients a b)).size := by
      simpa [bernsteinPowerCoefficientsFrom] using hr
    rw [getElem!_pos _ r hs]
    simp only [bernsteinPowerCoefficientsFrom, Array.getElem_map, Array.getElem_range,
      bernsteinPowerCoefficientFrom]
    apply Finset.sum_congr rfl
    intro j hj
    rw [coeff_bernsteinPolynomial _ _ _ (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))]
    ring

lemma affine_eq_bernstein (i : ℕ) (hi : i < CertificateData.tailIntervals.size) :
    affineResidualQ CertificateData.tailIntervals[i].1 CertificateData.tailIntervals[i].2 =
      bernsteinResidualQ CertificateData.tailIntervals[i].1 CertificateData.tailIntervals[i].2 := by
  ext r
  by_cases hr : r < residualDegree + 1
  · rw [← qPowerCoefficient_eq_affine_coeff, bernsteinResidual_coeff _ _ hr]
    have harr := exact_bernstein_power_identity i hi
    have hs : r < (qPowerCoefficients CertificateData.tailIntervals[i].1
        CertificateData.tailIntervals[i].2).size := by
      simpa [qPowerCoefficients] using hr
    have hq : (qPowerCoefficients CertificateData.tailIntervals[i].1
        CertificateData.tailIntervals[i].2)[r]! =
        qPowerCoefficient CertificateData.tailIntervals[i].1
          CertificateData.tailIntervals[i].2 r := by
      rw [getElem!_pos _ r hs]
      simp [qPowerCoefficients, hr]
    rw [← hq]
    exact congrArg (fun a : Array ℚ => a[r]!) harr
  · rw [← qPowerCoefficient_eq_affine_coeff]
    have hz : residualDegree + 1 - r = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hr)
    rw [show qPowerCoefficient CertificateData.tailIntervals[i].1
      CertificateData.tailIntervals[i].2 r = 0 by simp [qPowerCoefficient, hz]]
    rw [bernsteinResidualQ]
    change 0 = (lcoeff ℚ r) (∑ j ∈ Finset.range (residualDegree + 1),
      C ((bernsteinCoefficients CertificateData.tailIntervals[i].1
        CertificateData.tailIntervals[i].2)[j]!) *
          _root_.bernsteinPolynomial ℚ residualDegree j)
    rw [map_sum]
    simp only [lcoeff_apply, coeff_C_mul]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hrj : residualDegree < r := by omega
    rw [_root_.bernsteinPolynomial]
    rw [show (Nat.choose residualDegree j : ℚ[X]) = C (Nat.choose residualDegree j : ℚ) by simp,
      mul_assoc, coeff_C_mul, coeff_X_pow_mul']
    split_ifs with hjr
    · have hjle : j ≤ residualDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [coeff_one_sub_X_pow,
        Nat.choose_eq_zero_of_lt (by omega : residualDegree - j < r - j)]
      simp
    · simp

lemma bernstein_basis_nonneg (n j : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ (_root_.bernsteinPolynomial ℝ n j).eval s := by
  rw [_root_.bernsteinPolynomial]
  simp only [eval_mul, eval_natCast, eval_pow, eval_X, eval_sub, eval_one]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hs0 _))
    (pow_nonneg (sub_nonneg.mpr hs1) _)

lemma bernsteinResidual_nonpos (a b : ℚ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hnegative : ∀ j (hj : j < residualDegree + 1),
      (bernsteinCoefficients a b)[j]! < 0) :
    (bernsteinResidualQ a b).eval₂ (Rat.castHom ℝ) s ≤ 0 := by
  rw [bernsteinResidualQ, eval₂_finset_sum]
  apply Finset.sum_nonpos
  intro j hj
  rw [eval₂_mul, eval₂_C, eval₂_eq_eval_map, bernsteinPolynomial.map]
  exact mul_nonpos_of_nonpos_of_nonneg
    (by
      change ((bernsteinCoefficients a b)[j]! : ℝ) ≤ 0
      exact (Rat.cast_nonpos (K := ℝ)).mpr
        (hnegative j (Finset.mem_range.mp hj)).le)
    (bernstein_basis_nonneg _ _ hs0 hs1)

lemma residual_nonpos_on_interval (i : ℕ) (hi : i < CertificateData.tailIntervals.size)
    {x : ℝ} (hl : (CertificateData.tailIntervals[i].1 : ℝ) ≤ x)
    (hr : x ≤ (CertificateData.tailIntervals[i].2 : ℝ)) : residualR.eval x ≤ 0 := by
  let a := (CertificateData.tailIntervals[i].1 : ℝ)
  let b := (CertificateData.tailIntervals[i].2 : ℝ)
  let s := (x - a) / (b - a)
  have habQ : CertificateData.tailIntervals[i].1 < CertificateData.tailIntervals[i].2 := by
    exact interval_strict _ (by simpa [Array.mem_toList] using Array.getElem_mem hi)
  have hab : a < b := by
    dsimp [a, b]
    exact (Rat.cast_lt (K := ℝ)).mpr habQ
  have hs0 : 0 ≤ s := div_nonneg (sub_nonneg.mpr hl) (sub_nonneg.mpr hab.le)
  have hs1 : s ≤ 1 := (div_le_one (sub_pos.mpr hab)).mpr (by linarith)
  have hpoly := congrArg (fun p : ℚ[X] => p.eval₂ (Rat.castHom ℝ) s)
    (affine_eq_bernstein i hi)
  have hx : a + (b - a) * s = x := by
    dsimp [s]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  calc
    residualR.eval x = (affineResidualQ CertificateData.tailIntervals[i].1
        CertificateData.tailIntervals[i].2).eval₂ (Rat.castHom ℝ) s := by
      simp only [residualR, affineResidualQ, eval_map, eval₂_comp, eval₂_add, eval₂_C,
        eval₂_mul, eval₂_X, Rat.coe_castHom]
      congr 1
      simpa [a, b] using hx.symm
    _ = (bernsteinResidualQ CertificateData.tailIntervals[i].1
        CertificateData.tailIntervals[i].2).eval₂ (Rat.castHom ℝ) s := hpoly
    _ ≤ 0 := bernsteinResidual_nonpos _ _ hs0 hs1 (exact_bernstein_negative i hi)

lemma qPower_at_500_eq_shifted (r : ℕ) :
    qPowerCoefficient 500 501 r = shiftedCoefficient500 r := by
  norm_num [qPowerCoefficient, shiftedCoefficient500]

lemma residual_nonpos_on_ray {x : ℝ} (hx : 500 ≤ x) : residualR.eval x ≤ 0 := by
  let u := x - 500
  have hu : 0 ≤ u := sub_nonneg.mpr hx
  have hpoly := affine_eq_qPowerPolynomial 500 501
  have hEval : residualR.eval x =
      ∑ r ∈ Finset.range (residualDegree + 1), (shiftedCoefficient500 r : ℝ) * u ^ r := by
    calc
      residualR.eval x = (affineResidualQ 500 501).eval₂ (Rat.castHom ℝ) u := by
        simp only [residualR, affineResidualQ, eval_map, eval₂_comp, eval₂_add, eval₂_C,
          eval₂_mul, eval₂_X, Rat.coe_castHom]
        congr 1
        dsimp [u]
        norm_num
      _ = (polynomialOfArray (qPowerCoefficients 500 501)).eval₂
          (Rat.castHom ℝ) u := congrArg (fun p : ℚ[X] => p.eval₂ (Rat.castHom ℝ) u) hpoly
      _ = _ := by
        unfold polynomialOfArray
        rw [eval₂_finset_sum]
        rw [show (qPowerCoefficients 500 501).size = residualDegree + 1 by
          simp [qPowerCoefficients]]
        apply Finset.sum_congr rfl
        intro r hr
        have hrs : r < (qPowerCoefficients 500 501).size := by
          simpa [qPowerCoefficients] using Finset.mem_range.mp hr
        rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, getElem!_pos _ r hrs]
        simp [qPowerCoefficients, Finset.mem_range.mp hr]
        rw [qPower_at_500_eq_shifted]
        norm_num
  rw [hEval]
  apply Finset.sum_nonpos
  intro r hr
  have hnegQ := exact_shifted_coefficients_negative r hr
  exact mul_nonpos_of_nonpos_of_nonneg
    ((Rat.cast_nonpos (K := ℝ)).mpr hnegQ.le) (pow_nonneg hu _)

set_option maxHeartbeats 0 in
theorem residual_nonpos_on_bounded_tail {x : ℝ}
    (hq : (CertificateData.isolatingRight : ℝ) ≤ x) (hx : x ≤ 500) :
    residualR.eval x ≤ 0 := by
  by_cases h0 : x ≤ (CertificateData.tailIntervals[0]!.2 : ℝ)
  · refine residual_nonpos_on_interval 0 (by native_decide) ?_ h0
    simpa [interval_endpoints.1] using hq
  by_cases h1 : x ≤ (CertificateData.tailIntervals[1]!.2 : ℝ)
  · refine residual_nonpos_on_interval 1 (by native_decide) ?_ h1
    have hc := interval_chain 0 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[0]!.2 : ℝ) < x := lt_of_not_ge h0
    change (CertificateData.tailIntervals[1]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h2 : x ≤ (CertificateData.tailIntervals[2]!.2 : ℝ)
  · refine residual_nonpos_on_interval 2 (by native_decide) ?_ h2
    have hc := interval_chain 1 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[1]!.2 : ℝ) < x := lt_of_not_ge h1
    change (CertificateData.tailIntervals[2]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h3 : x ≤ (CertificateData.tailIntervals[3]!.2 : ℝ)
  · refine residual_nonpos_on_interval 3 (by native_decide) ?_ h3
    have hc := interval_chain 2 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[2]!.2 : ℝ) < x := lt_of_not_ge h2
    change (CertificateData.tailIntervals[3]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h4 : x ≤ (CertificateData.tailIntervals[4]!.2 : ℝ)
  · refine residual_nonpos_on_interval 4 (by native_decide) ?_ h4
    have hc := interval_chain 3 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[3]!.2 : ℝ) < x := lt_of_not_ge h3
    change (CertificateData.tailIntervals[4]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h5 : x ≤ (CertificateData.tailIntervals[5]!.2 : ℝ)
  · refine residual_nonpos_on_interval 5 (by native_decide) ?_ h5
    have hc := interval_chain 4 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[4]!.2 : ℝ) < x := lt_of_not_ge h4
    change (CertificateData.tailIntervals[5]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h6 : x ≤ (CertificateData.tailIntervals[6]!.2 : ℝ)
  · refine residual_nonpos_on_interval 6 (by native_decide) ?_ h6
    have hc := interval_chain 5 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[5]!.2 : ℝ) < x := lt_of_not_ge h5
    change (CertificateData.tailIntervals[6]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h7 : x ≤ (CertificateData.tailIntervals[7]!.2 : ℝ)
  · refine residual_nonpos_on_interval 7 (by native_decide) ?_ h7
    have hc := interval_chain 6 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[6]!.2 : ℝ) < x := lt_of_not_ge h6
    change (CertificateData.tailIntervals[7]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h8 : x ≤ (CertificateData.tailIntervals[8]!.2 : ℝ)
  · refine residual_nonpos_on_interval 8 (by native_decide) ?_ h8
    have hc := interval_chain 7 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[7]!.2 : ℝ) < x := lt_of_not_ge h7
    change (CertificateData.tailIntervals[8]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h9 : x ≤ (CertificateData.tailIntervals[9]!.2 : ℝ)
  · refine residual_nonpos_on_interval 9 (by native_decide) ?_ h9
    have hc := interval_chain 8 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[8]!.2 : ℝ) < x := lt_of_not_ge h8
    change (CertificateData.tailIntervals[9]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h10 : x ≤ (CertificateData.tailIntervals[10]!.2 : ℝ)
  · refine residual_nonpos_on_interval 10 (by native_decide) ?_ h10
    have hc := interval_chain 9 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[9]!.2 : ℝ) < x := lt_of_not_ge h9
    change (CertificateData.tailIntervals[10]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h11 : x ≤ (CertificateData.tailIntervals[11]!.2 : ℝ)
  · refine residual_nonpos_on_interval 11 (by native_decide) ?_ h11
    have hc := interval_chain 10 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[10]!.2 : ℝ) < x := lt_of_not_ge h10
    change (CertificateData.tailIntervals[11]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h12 : x ≤ (CertificateData.tailIntervals[12]!.2 : ℝ)
  · refine residual_nonpos_on_interval 12 (by native_decide) ?_ h12
    have hc := interval_chain 11 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[11]!.2 : ℝ) < x := lt_of_not_ge h11
    change (CertificateData.tailIntervals[12]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h13 : x ≤ (CertificateData.tailIntervals[13]!.2 : ℝ)
  · refine residual_nonpos_on_interval 13 (by native_decide) ?_ h13
    have hc := interval_chain 12 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[12]!.2 : ℝ) < x := lt_of_not_ge h12
    change (CertificateData.tailIntervals[13]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h14 : x ≤ (CertificateData.tailIntervals[14]!.2 : ℝ)
  · refine residual_nonpos_on_interval 14 (by native_decide) ?_ h14
    have hc := interval_chain 13 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[13]!.2 : ℝ) < x := lt_of_not_ge h13
    change (CertificateData.tailIntervals[14]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h15 : x ≤ (CertificateData.tailIntervals[15]!.2 : ℝ)
  · refine residual_nonpos_on_interval 15 (by native_decide) ?_ h15
    have hc := interval_chain 14 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[14]!.2 : ℝ) < x := lt_of_not_ge h14
    change (CertificateData.tailIntervals[15]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h16 : x ≤ (CertificateData.tailIntervals[16]!.2 : ℝ)
  · refine residual_nonpos_on_interval 16 (by native_decide) ?_ h16
    have hc := interval_chain 15 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[15]!.2 : ℝ) < x := lt_of_not_ge h15
    change (CertificateData.tailIntervals[16]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h17 : x ≤ (CertificateData.tailIntervals[17]!.2 : ℝ)
  · refine residual_nonpos_on_interval 17 (by native_decide) ?_ h17
    have hc := interval_chain 16 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[16]!.2 : ℝ) < x := lt_of_not_ge h16
    change (CertificateData.tailIntervals[17]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h18 : x ≤ (CertificateData.tailIntervals[18]!.2 : ℝ)
  · refine residual_nonpos_on_interval 18 (by native_decide) ?_ h18
    have hc := interval_chain 17 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[17]!.2 : ℝ) < x := lt_of_not_ge h17
    change (CertificateData.tailIntervals[18]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h19 : x ≤ (CertificateData.tailIntervals[19]!.2 : ℝ)
  · refine residual_nonpos_on_interval 19 (by native_decide) ?_ h19
    have hc := interval_chain 18 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[18]!.2 : ℝ) < x := lt_of_not_ge h18
    change (CertificateData.tailIntervals[19]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h20 : x ≤ (CertificateData.tailIntervals[20]!.2 : ℝ)
  · refine residual_nonpos_on_interval 20 (by native_decide) ?_ h20
    have hc := interval_chain 19 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[19]!.2 : ℝ) < x := lt_of_not_ge h19
    change (CertificateData.tailIntervals[20]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h21 : x ≤ (CertificateData.tailIntervals[21]!.2 : ℝ)
  · refine residual_nonpos_on_interval 21 (by native_decide) ?_ h21
    have hc := interval_chain 20 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[20]!.2 : ℝ) < x := lt_of_not_ge h20
    change (CertificateData.tailIntervals[21]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h22 : x ≤ (CertificateData.tailIntervals[22]!.2 : ℝ)
  · refine residual_nonpos_on_interval 22 (by native_decide) ?_ h22
    have hc := interval_chain 21 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[21]!.2 : ℝ) < x := lt_of_not_ge h21
    change (CertificateData.tailIntervals[22]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h23 : x ≤ (CertificateData.tailIntervals[23]!.2 : ℝ)
  · refine residual_nonpos_on_interval 23 (by native_decide) ?_ h23
    have hc := interval_chain 22 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[22]!.2 : ℝ) < x := lt_of_not_ge h22
    change (CertificateData.tailIntervals[23]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h24 : x ≤ (CertificateData.tailIntervals[24]!.2 : ℝ)
  · refine residual_nonpos_on_interval 24 (by native_decide) ?_ h24
    have hc := interval_chain 23 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[23]!.2 : ℝ) < x := lt_of_not_ge h23
    change (CertificateData.tailIntervals[24]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h25 : x ≤ (CertificateData.tailIntervals[25]!.2 : ℝ)
  · refine residual_nonpos_on_interval 25 (by native_decide) ?_ h25
    have hc := interval_chain 24 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[24]!.2 : ℝ) < x := lt_of_not_ge h24
    change (CertificateData.tailIntervals[25]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h26 : x ≤ (CertificateData.tailIntervals[26]!.2 : ℝ)
  · refine residual_nonpos_on_interval 26 (by native_decide) ?_ h26
    have hc := interval_chain 25 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[25]!.2 : ℝ) < x := lt_of_not_ge h25
    change (CertificateData.tailIntervals[26]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h27 : x ≤ (CertificateData.tailIntervals[27]!.2 : ℝ)
  · refine residual_nonpos_on_interval 27 (by native_decide) ?_ h27
    have hc := interval_chain 26 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[26]!.2 : ℝ) < x := lt_of_not_ge h26
    change (CertificateData.tailIntervals[27]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h28 : x ≤ (CertificateData.tailIntervals[28]!.2 : ℝ)
  · refine residual_nonpos_on_interval 28 (by native_decide) ?_ h28
    have hc := interval_chain 27 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[27]!.2 : ℝ) < x := lt_of_not_ge h27
    change (CertificateData.tailIntervals[28]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h29 : x ≤ (CertificateData.tailIntervals[29]!.2 : ℝ)
  · refine residual_nonpos_on_interval 29 (by native_decide) ?_ h29
    have hc := interval_chain 28 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[28]!.2 : ℝ) < x := lt_of_not_ge h28
    change (CertificateData.tailIntervals[29]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h30 : x ≤ (CertificateData.tailIntervals[30]!.2 : ℝ)
  · refine residual_nonpos_on_interval 30 (by native_decide) ?_ h30
    have hc := interval_chain 29 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[29]!.2 : ℝ) < x := lt_of_not_ge h29
    change (CertificateData.tailIntervals[30]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  by_cases h31 : x ≤ (CertificateData.tailIntervals[31]!.2 : ℝ)
  · refine residual_nonpos_on_interval 31 (by native_decide) ?_ h31
    have hc := interval_chain 30 (by native_decide)
    norm_num at hc
    have hp : (CertificateData.tailIntervals[30]!.2 : ℝ) < x := lt_of_not_ge h30
    change (CertificateData.tailIntervals[31]!.1 : ℝ) ≤ x
    rw [← hc]
    exact hp.le
  · refine residual_nonpos_on_interval 32 (by native_decide) ?_ ?_
    · have hc := interval_chain 31 (by native_decide)
      norm_num at hc
      have hp : (CertificateData.tailIntervals[31]!.2 : ℝ) < x := lt_of_not_ge h31
      change (CertificateData.tailIntervals[32]!.1 : ℝ) ≤ x
      rw [← hc]
      exact hp.le
    · simpa [interval_endpoints.2] using hx

/-- The exact upper certificate proves the residual is nonpositive on the whole ray. -/
theorem residual_tail_certificate {x : ℝ}
    (hx : (CertificateData.isolatingRight : ℝ) ≤ x) : residualR.eval x ≤ 0 := by
  by_cases h500 : x ≤ 500
  · exact residual_nonpos_on_bounded_tail hx h500
  · exact residual_nonpos_on_ray (le_of_not_ge h500)

theorem witness_tail_certificate {x : ℝ}
    (hx : (CertificateData.isolatingRight : ℝ) ≤ x) : witnessR.eval x ≤ 0 := by
  have hx0 : 0 ≤ x := by
    have hq : (0 : ℝ) < CertificateData.isolatingRight := by
      exact_mod_cast (by native_decide : (0 : ℚ) < CertificateData.isolatingRight)
    exact le_trans hq.le hx
  have hres : residualR.eval x ≤ 0 := residual_tail_certificate hx
  have hfactor : 0 ≤ (rootFactorQ.map (Rat.castHom ℝ)).eval x := by
    have hfactorQ : rootFactorQ =
        X * ∏ i ∈ Finset.range 20, (X - C CertificateData.roots[i]!) ^ 2 := by
      rw [rootFactorQ, factorProductCoeffs]
      exact polynomialOfArray_factorProductN 20 (by omega)
    rw [hfactorQ, Polynomial.map_mul, Polynomial.map_X, Polynomial.map_prod]
    simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_prod,
      Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_C, Rat.coe_castHom,
      eval_pow, eval_sub, eval_C]
    exact mul_nonneg hx0 (Finset.prod_nonneg fun _ _ => sq_nonneg _)
  have hscale : (0 : ℝ) ≤ (1 / rawFactorDerivative : ℚ) := by
    exact (Rat.cast_nonneg (K := ℝ)).mpr
      (le_of_lt (one_div_pos.mpr rawFactorDerivative_pos))
  rw [witnessR, exact_semantic_factorization, Polynomial.map_mul, Polynomial.map_C,
    rawFactorPolynomialQ, Polynomial.map_mul, Polynomial.eval_mul, Polynomial.eval_mul,
    Rat.coe_castHom]
  exact mul_nonpos_of_nonneg_of_nonpos (by simpa using hscale)
    (mul_nonpos_of_nonneg_of_nonpos hfactor hres)


end UncertaintyS2
