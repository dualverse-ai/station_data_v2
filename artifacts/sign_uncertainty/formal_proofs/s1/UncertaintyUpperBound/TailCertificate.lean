import UncertaintyUpperBound.ExactCertificate
import Mathlib.Data.Real.Basic

namespace UncertaintyUpperBound

open Polynomial
open scoped Polynomial

lemma eval_polynomialOfArray {R : Type*} [CommSemiring R] [Inhabited R]
    (coeffs : Array R) (x : R) :
    (polynomialOfArray coeffs).eval x =
      ∑ i ∈ Finset.range coeffs.size, coeffs[i]! * x ^ i := by
  unfold polynomialOfArray
  change (evalRingHom x) (∑ i ∈ Finset.range coeffs.size, C coeffs[i]! * X ^ i) = _
  rw [map_sum]
  simp

def hasseCoefficientArray (ell : ℕ) : Array ℚ :=
  (Array.range (certificateDegree + 1 - ell)).map fun k =>
    Nat.choose (k + ell) ell * CertificateData.powerCoefficients[k + ell]!

lemma hasseCoefficientArray_get (ell k : ℕ)
    (hk : k < certificateDegree + 1 - ell) :
    (hasseCoefficientArray ell)[k]! =
      Nat.choose (k + ell) ell * CertificateData.powerCoefficients[k + ell]! := by
  have hsize : k < (hasseCoefficientArray ell).size := by
    simpa [hasseCoefficientArray] using hk
  rw [getElem!_pos (hasseCoefficientArray ell) k hsize]
  simp [hasseCoefficientArray, hk]

lemma hasseDeriv_witness_eq (ell : ℕ) :
    hasseDeriv ell witnessPolynomialQ = polynomialOfArray (hasseCoefficientArray ell) := by
  ext k
  rw [hasseDeriv_coeff, coeff_polynomialOfArray]
  by_cases hk : k < certificateDegree + 1 - ell
  · have hsum : k + ell < CertificateData.powerCoefficients.size := by
      rw [power_coefficients_size]
      simp only [certificateDegree] at hk
      omega
    rw [if_pos]
    · rw [witnessPolynomialQ, coeff_polynomialOfArray, if_pos hsum]
      rw [hasseCoefficientArray_get ell k hk]
    · simpa [hasseCoefficientArray] using hk
  · have hsum : ¬ k + ell < CertificateData.powerCoefficients.size := by
      rw [power_coefficients_size]
      simp only [certificateDegree] at hk
      omega
    rw [if_neg]
    · rw [witnessPolynomialQ, coeff_polynomialOfArray, if_neg hsum]
      simp
    · simpa [hasseCoefficientArray] using hk

lemma qPowerCoefficient_eq_affine_coeff (a b : ℚ) (ell : ℕ) :
    qPowerCoefficient a b ell = (affineWitnessQ a b).coeff ell := by
  rw [affineWitnessQ]
  have hcomp :
      witnessPolynomialQ.comp (C a + C (b - a) * X) =
        (taylor a witnessPolynomialQ).comp (C (b - a) * X) := by
    rw [taylor_apply, comp_assoc]
    congr 1
    simp [add_comp, X_comp, C_comp]
    ring
  rw [hcomp, comp_C_mul_X_coeff, taylor_coeff, hasseDeriv_witness_eq,
    eval_polynomialOfArray]
  rw [show (hasseCoefficientArray ell).size = certificateDegree + 1 - ell by
    simp [hasseCoefficientArray]]
  change qPowerCoefficient a b ell =
    (∑ k ∈ Finset.range (certificateDegree + 1 - ell),
      (hasseCoefficientArray ell)[k]! * a ^ k) * (b - a) ^ ell
  rw [qPowerCoefficient]
  rw [mul_comm]
  apply congrArg (fun z : ℚ => z * (b - a) ^ ell)
  apply Finset.sum_congr rfl
  intro k hk
  rw [hasseCoefficientArray_get ell k (Finset.mem_range.mp hk)]
  ring

lemma affine_eq_qPowerPolynomial (a b : ℚ) :
    affineWitnessQ a b = polynomialOfArray (qPowerCoefficients a b) := by
  ext r
  rw [← qPowerCoefficient_eq_affine_coeff, coeff_polynomialOfArray]
  by_cases hr : r < certificateDegree + 1
  · rw [if_pos]
    · simp [qPowerCoefficients, hr]
    · simpa [qPowerCoefficients] using hr
  · rw [if_neg]
    · have hz : certificateDegree + 1 - r = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hr)
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

lemma bernsteinPolynomial_coeff (a b : ℚ) {r : ℕ} (hr : r < certificateDegree + 1) :
    (bernsteinPolynomialQ a b).coeff r =
      (bernsteinPowerCoefficientsFrom (bernsteinCoefficients a b))[r]! := by
  rw [bernsteinPolynomialQ]
  change (lcoeff ℚ r) (∑ j ∈ Finset.range (certificateDegree + 1),
    C (bernsteinCoefficient a b j) * _root_.bernsteinPolynomial ℚ certificateDegree j) = _
  rw [map_sum]
  simp only [lcoeff_apply, map_sum, coeff_C_mul]
  have hsub : Finset.range (r + 1) ⊆ Finset.range (certificateDegree + 1) := by
    intro j hj
    exact Finset.mem_range.mpr
      (lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp hj)) hr)
  have hzero : ∀ j ∈ Finset.range (certificateDegree + 1),
      j ∉ Finset.range (r + 1) →
      bernsteinCoefficient a b j *
        (_root_.bernsteinPolynomial ℚ certificateDegree j).coeff r = 0 := by
    intro j hjbig hjnot
    have hrj : r < j := by simpa [Finset.mem_range, Nat.not_lt] using hjnot
    rw [_root_.bernsteinPolynomial]
    rw [show (Nat.choose certificateDegree j : ℚ[X]) =
      C (Nat.choose certificateDegree j : ℚ) by simp, mul_assoc, coeff_C_mul,
      coeff_X_pow_mul', if_neg (Nat.not_le.mpr hrj)]
    simp
  rw [← Finset.sum_subset hsub hzero]
  · have hsize : r < (bernsteinPowerCoefficientsFrom
        (bernsteinCoefficients a b)).size := by
      simpa [bernsteinPowerCoefficientsFrom] using hr
    rw [getElem!_pos (bernsteinPowerCoefficientsFrom
      (bernsteinCoefficients a b)) r hsize]
    simp only [bernsteinPowerCoefficientsFrom, Array.getElem_map, Array.getElem_range,
      bernsteinPowerCoefficientFrom]
    apply Finset.sum_congr rfl
    intro j hj
    have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [coeff_bernsteinPolynomial _ _ _ hjr]
    simp [bernsteinCoefficient]
    ring

lemma affine_eq_bernstein (i : ℕ) (hi : i < CertificateData.intervals.size) :
    affineWitnessQ CertificateData.intervals[i].1 CertificateData.intervals[i].2 =
      bernsteinPolynomialQ CertificateData.intervals[i].1 CertificateData.intervals[i].2 := by
  ext r
  by_cases hr : r < certificateDegree + 1
  · rw [← qPowerCoefficient_eq_affine_coeff, bernsteinPolynomial_coeff _ _ hr]
    have harr := exact_bernstein_power_identity i hi
    have hsize : r < (qPowerCoefficients CertificateData.intervals[i].1
        CertificateData.intervals[i].2).size := by
      simpa [qPowerCoefficients] using hr
    have hq : (qPowerCoefficients CertificateData.intervals[i].1
        CertificateData.intervals[i].2)[r]! =
        qPowerCoefficient CertificateData.intervals[i].1
          CertificateData.intervals[i].2 r := by
      rw [getElem!_pos (qPowerCoefficients CertificateData.intervals[i].1
        CertificateData.intervals[i].2) r hsize]
      simp [qPowerCoefficients, hr]
    rw [← hq]
    exact congrArg (fun a : Array ℚ => a[r]!) harr
  · rw [← qPowerCoefficient_eq_affine_coeff]
    have hz : certificateDegree + 1 - r = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hr)
    have hqzero : qPowerCoefficient CertificateData.intervals[i].1
        CertificateData.intervals[i].2 r = 0 := by
      simp [qPowerCoefficient, hz]
    rw [hqzero, bernsteinPolynomialQ]
    change 0 = (lcoeff ℚ r) (∑ j ∈ Finset.range (certificateDegree + 1),
      C (bernsteinCoefficient CertificateData.intervals[i].1
        CertificateData.intervals[i].2 j) *
          _root_.bernsteinPolynomial ℚ certificateDegree j)
    rw [map_sum]
    simp only [lcoeff_apply, coeff_C_mul]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hrj : certificateDegree < r := by omega
    rw [_root_.bernsteinPolynomial]
    rw [show (Nat.choose certificateDegree j : ℚ[X]) =
      C (Nat.choose certificateDegree j : ℚ) by simp, mul_assoc, coeff_C_mul,
      coeff_X_pow_mul']
    split_ifs with hjr
    · have hjle : j ≤ certificateDegree :=
        Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [coeff_one_sub_X_pow]
      rw [Nat.choose_eq_zero_of_lt (by omega : certificateDegree - j < r - j)]
      simp
    · simp

noncomputable def evalWitness (x : ℝ) : ℝ :=
  witnessPolynomialQ.eval₂ (Rat.castHom ℝ) x

lemma bernstein_basis_nonneg (n j : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    0 ≤ (_root_.bernsteinPolynomial ℝ n j).eval s := by
  rw [_root_.bernsteinPolynomial]
  simp only [eval_mul, eval_natCast, eval_pow, eval_X, eval_sub, eval_one]
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hs0 _))
    (pow_nonneg (sub_nonneg.mpr hs1) _)

lemma bernstein_combination_le (a b : ℚ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hmargin : ∀ j (hj : j < certificateDegree + 1),
      (bernsteinCoefficients a b)[j]! < -(1 / 100000 : ℚ)) :
    (bernsteinPolynomialQ a b).eval₂ (Rat.castHom ℝ) s ≤ -(1 / 100000 : ℝ) := by
  rw [bernsteinPolynomialQ]
  rw [eval₂_finset_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range (certificateDegree + 1),
        (-(1 / 100000 : ℝ)) * (_root_.bernsteinPolynomial ℝ certificateDegree j).eval s := by
      apply Finset.sum_le_sum
      intro j hj
      rw [eval₂_mul, eval₂_C, eval₂_eq_eval_map,
        bernsteinPolynomial.map]
      apply mul_le_mul_of_nonneg_right
      · have hq : bernsteinCoefficient a b j ≤ -(1 / 100000 : ℚ) := by
          exact le_of_lt (hmargin j (Finset.mem_range.mp hj))
        change (bernsteinCoefficient a b j : ℝ) ≤ -(1 / 100000 : ℝ)
        convert (Rat.cast_le (K := ℝ)).mpr hq using 1 <;> norm_num
      · exact bernstein_basis_nonneg _ _ hs0 hs1
    _ = -(1 / 100000 : ℝ) := by
      rw [← Finset.mul_sum, ← eval_finset_sum, _root_.bernsteinPolynomial.sum]
      norm_num

lemma evalWitness_le_on_certificate_interval (i : ℕ)
    (hi : i < CertificateData.intervals.size) {x : ℝ}
    (hleft : (CertificateData.intervals[i].1 : ℝ) ≤ x)
    (hright : x ≤ (CertificateData.intervals[i].2 : ℝ)) :
    evalWitness x ≤ -(1 / 100000 : ℝ) := by
  let a := (CertificateData.intervals[i].1 : ℝ)
  let b := (CertificateData.intervals[i].2 : ℝ)
  let s := (x - a) / (b - a)
  have habQ : CertificateData.intervals[i].1 < CertificateData.intervals[i].2 := by
    have hmem : CertificateData.intervals[i] ∈ CertificateData.intervals.toList := by
      simpa [Array.mem_toList] using Array.getElem_mem hi
    exact interval_strict _ hmem
  have hab : a < b := by
    dsimp [a, b]
    exact_mod_cast habQ
  have hs0 : 0 ≤ s := div_nonneg (sub_nonneg.mpr hleft) (sub_nonneg.mpr hab.le)
  have hs1 : s ≤ 1 := (div_le_one (sub_pos.mpr hab)).mpr (by linarith)
  have hpoly := congrArg (fun p : ℚ[X] => p.eval₂ (Rat.castHom ℝ) s)
    (affine_eq_bernstein i hi)
  have hx : a + (b - a) * s = x := by
    dsimp [s]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  calc
    evalWitness x = (affineWitnessQ CertificateData.intervals[i].1
        CertificateData.intervals[i].2).eval₂ (Rat.castHom ℝ) s := by
      simp only [evalWitness, affineWitnessQ, eval₂_comp, eval₂_add, eval₂_C, eval₂_mul,
        eval₂_X]
      congr 1
      simpa [a, b] using hx.symm
    _ = (bernsteinPolynomialQ CertificateData.intervals[i].1
        CertificateData.intervals[i].2).eval₂ (Rat.castHom ℝ) s := hpoly
    _ ≤ -(1 / 100000 : ℝ) := bernstein_combination_le _ _ hs0 hs1
      (exact_bernstein_margin i hi)

lemma qPower_at_1000_eq_shifted (r : ℕ) :
    qPowerCoefficient 1000 1001 r = shiftedCoefficient r := by
  norm_num [qPowerCoefficient, shiftedCoefficient]

lemma evalWitness_le_on_ray {x : ℝ} (hx : 1000 ≤ x) :
    evalWitness x < -(1 / 1000000 : ℝ) := by
  let u := x - 1000
  have hu : 0 ≤ u := sub_nonneg.mpr hx
  have hpoly := affine_eq_qPowerPolynomial 1000 1001
  have hEval : evalWitness x =
      ∑ r ∈ Finset.range (certificateDegree + 1), (shiftedCoefficient r : ℝ) * u ^ r := by
    calc
      evalWitness x = (affineWitnessQ 1000 1001).eval₂ (Rat.castHom ℝ) u := by
        simp only [evalWitness, affineWitnessQ, eval₂_comp, eval₂_add, eval₂_C, eval₂_mul,
          eval₂_X]
        congr 1
        dsimp [u]
        norm_num
      _ = (polynomialOfArray (qPowerCoefficients 1000 1001)).eval₂
          (Rat.castHom ℝ) u := congrArg (fun p : ℚ[X] => p.eval₂ (Rat.castHom ℝ) u) hpoly
      _ = ∑ r ∈ Finset.range (certificateDegree + 1),
          (shiftedCoefficient r : ℝ) * u ^ r := by
        unfold polynomialOfArray
        rw [eval₂_finset_sum]
        rw [show (qPowerCoefficients 1000 1001).size = certificateDegree + 1 by
          simp [qPowerCoefficients]]
        apply Finset.sum_congr rfl
        intro r hr
        have hrs : r < (qPowerCoefficients 1000 1001).size := by
          simpa [qPowerCoefficients] using Finset.mem_range.mp hr
        rw [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X,
          getElem!_pos (qPowerCoefficients 1000 1001) r hrs]
        simp [qPowerCoefficients, Finset.mem_range.mp hr]
        rw [qPower_at_1000_eq_shifted]
        norm_num
  rw [hEval]
  have hconstant : (shiftedCoefficient 0 : ℝ) < -(1 / 1000000 : ℝ) := by
    have hq : shiftedCoefficient 0 < -(1 / 1000000 : ℚ) := by
      linarith [exact_shifted_constant_margin]
    convert (Rat.cast_lt (K := ℝ)).mpr hq using 1 <;> norm_num
  have hrest :
      ∑ r ∈ Finset.Ico 1 (certificateDegree + 1), (shiftedCoefficient r : ℝ) * u ^ r ≤ 0 := by
    apply Finset.sum_nonpos
    intro r hr
    have hnegQ : shiftedCoefficient r < 0 :=
      exact_shifted_coefficients_negative r
        (Finset.mem_range.mpr (Finset.mem_Ico.mp hr).2)
    have hnegR : (shiftedCoefficient r : ℝ) ≤ 0 := by
      exact_mod_cast (le_of_lt hnegQ)
    exact mul_nonpos_of_nonpos_of_nonneg hnegR (by positivity)
  rw [Finset.sum_range_eq_add_Ico _ (by norm_num [certificateDegree] : 0 < certificateDegree + 1)]
  simp only [pow_zero, mul_one]
  linarith

set_option maxHeartbeats 0 in
theorem evalWitness_le_on_bounded_tail {x : ℝ}
    (hT : (1213 / 625 : ℝ) ≤ x) (hx : x ≤ 1000) :
    evalWitness x ≤ -(1 / 100000 : ℝ) := by
  by_cases h0 : x ≤ (3108011 / 1280000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 0 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h1 : x ≤ (1865899 / 640000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 1 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h2 : x ≤ (1244843 / 320000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 2 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h3 : x ≤ (186863 / 32000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 3 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h4 : x ≤ (4361047 / 640000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 4 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h5 : x ≤ (2492417 / 320000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 5 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h6 : x ≤ (779051 / 80000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 6 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h7 : x ≤ (701419 / 40000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 7 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h8 : x ≤ (16213 / 640 : ℝ)
  · refine evalWitness_le_on_certificate_interval 8 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h9 : x ≤ (4677037 / 160000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 9 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h10 : x ≤ (662603 / 20000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 10 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h11 : x ≤ (1948993 / 40000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 11 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h12 : x ≤ (128639 / 2000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 12 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h13 : x ≤ (1910177 / 20000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 13 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h14 : x ≤ (633491 / 5000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 14 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h15 : x ≤ (3157751 / 20000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 15 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h16 : x ≤ (1890769 / 10000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 16 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h17 : x ≤ (176213 / 800 : ℝ)
  · refine evalWitness_le_on_certificate_interval 17 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h18 : x ≤ (628639 / 2500 : ℝ)
  · refine evalWitness_le_on_certificate_interval 18 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h19 : x ≤ (3138343 / 10000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 19 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h20 : x ≤ (376213 / 1000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 20 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h21 : x ≤ (4385917 / 10000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 21 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h22 : x ≤ (626213 / 1250 : ℝ)
  · refine evalWitness_le_on_certificate_interval 22 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h23 : x ≤ (5633491 / 10000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 23 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h24 : x ≤ (3128639 / 5000 : ℝ)
  · refine evalWitness_le_on_certificate_interval 24 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  by_cases h25 : x ≤ (1876213 / 2500 : ℝ)
  · refine evalWitness_le_on_certificate_interval 25 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith
  · refine evalWitness_le_on_certificate_interval 26 (by native_decide) ?_ ?_ <;>
      norm_num [CertificateData.intervals] <;> linarith

theorem witness_polynomial_whole_tail {x : ℝ} (hx : (1213 / 625 : ℝ) ≤ x) :
    evalWitness x < -(1 / 1000000 : ℝ) := by
  by_cases h : x ≤ 1000
  · exact lt_of_le_of_lt (evalWitness_le_on_bounded_tail hx h) (by norm_num)
  · exact evalWitness_le_on_ray (le_of_not_ge h)

end UncertaintyUpperBound
