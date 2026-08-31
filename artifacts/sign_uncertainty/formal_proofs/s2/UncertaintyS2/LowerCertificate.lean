import UncertaintyS2.Definitions
import UncertaintyS2.CertificateData
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Positivity

namespace UncertaintyS2

open Polynomial Set

abbrev basisCount : ℕ := 42

def weightedEvalQ (P : Polynomial ℚ) : ℚ :=
  ∑ i ∈ Finset.range CertificateData.nodes.size,
    CertificateData.weights[i]! * P.eval CertificateData.nodes[i]!

noncomputable def weightedEvalR (P : Polynomial ℝ) : ℝ :=
  ∑ i ∈ Finset.range CertificateData.nodes.size,
    (CertificateData.weights[i]! : ℝ) * P.eval (CertificateData.nodes[i]! : ℝ)

def evalCoeffsQ (p : Array ℚ) (x : ℚ) : ℚ :=
  ∑ i ∈ Finset.range p.size, p[i]! * x ^ i

def weightedCoeffsQ (p : Array ℚ) : ℚ :=
  ∑ i ∈ Finset.range CertificateData.nodes.size,
    CertificateData.weights[i]! * evalCoeffsQ p CertificateData.nodes[i]!

def certificateAlpha : ℚ := weightedCoeffsQ (laguerreHalfCoeffs 0)

theorem certificate_sizes :
    CertificateData.nodes.size = 41 ∧ CertificateData.weights.size = 41 := by
  native_decide

theorem certificate_nodes_ge_first :
    ∀ i (hi : i < CertificateData.nodes.size),
      (6191 / 3125 : ℚ) ≤ CertificateData.nodes[i]! := by
  native_decide

theorem certificate_weights_positive :
    ∀ i (hi : i < CertificateData.weights.size), 0 < CertificateData.weights[i]! := by
  native_decide

set_option maxHeartbeats 0 in
theorem exact_basis_moments :
    ∀ j (hj : j < basisCount),
      weightedCoeffsQ (laguerreHalfCoeffs (2 * j)) =
        CertificateData.certificateValue * coeffAt (laguerreHalfCoeffs (2 * j)) 1 +
          certificateAlpha * coeffAt (laguerreHalfCoeffs (2 * j)) 0 := by
  native_decide

lemma weightedEvalQ_laguerre (n : ℕ) :
    weightedEvalQ (laguerreHalfQ n) = weightedCoeffsQ (laguerreHalfCoeffs n) := by
  simp only [weightedEvalQ, weightedCoeffsQ, laguerreHalfQ, evalCoeffsQ,
    eval_polynomialOfArray]

lemma weightedEvalR_map (P : Polynomial ℚ) :
    weightedEvalR (P.map (Rat.castHom ℝ)) = (weightedEvalQ P : ℝ) := by
  simp only [weightedEvalR, weightedEvalQ, eval_map]
  rw [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [show (CertificateData.nodes[i]! : ℝ) =
      (Rat.castHom ℝ) CertificateData.nodes[i]! by rfl,
    eval₂_at_apply]
  simp only [Rat.coe_castHom]
  push_cast
  norm_num

lemma weightedEvalR_add (P Q : Polynomial ℝ) :
    weightedEvalR (P + Q) = weightedEvalR P + weightedEvalR Q := by
  simp [weightedEvalR, Finset.sum_add_distrib, mul_add]

lemma weightedEvalR_sum {ι : Type*} [Fintype ι] (P : ι → Polynomial ℝ) :
    weightedEvalR (∑ i, P i) = ∑ i, weightedEvalR (P i) := by
  classical
  unfold weightedEvalR
  simp_rw [eval_finset_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma weightedEvalR_finset_sum {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℝ) :
    weightedEvalR (∑ i ∈ s, P i) = ∑ i ∈ s, weightedEvalR (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [weightedEvalR]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, weightedEvalR_add, ih, Finset.sum_insert ha]

lemma weightedEvalR_C_mul (c : ℝ) (P : Polynomial ℝ) :
    weightedEvalR (C c * P) = c * weightedEvalR P := by
  simp only [weightedEvalR, eval_mul, eval_C, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma real_basis_moment (j : ℕ) (hj : j < basisCount) :
    weightedEvalR (laguerreHalfR (2 * j)) =
      (CertificateData.certificateValue : ℝ) *
          (laguerreHalfR (2 * j)).derivative.eval 0 +
        (certificateAlpha : ℝ) * (laguerreHalfR (2 * j)).eval 0 := by
  rw [laguerreHalfR, weightedEvalR_map]
  simp only [derivative_map, eval_map]
  rw [weightedEvalQ_laguerre]
  have hm := exact_basis_moments j hj
  rw [hm]
  rw [show (0 : ℝ) = (Rat.castHom ℝ) 0 by norm_num,
    eval₂_at_apply, eval₂_at_apply]
  simp only [Rat.coe_castHom]
  rw [show (laguerreHalfQ (2 * j)).derivative.eval 0 =
      coeffAt (laguerreHalfCoeffs (2 * j)) 1 by
        rw [← coeff_zero_eq_eval_zero, coeff_derivative, laguerreHalfQ,
          coeff_polynomialOfArray]
        rw [coeffAt_eq]
        norm_num,
    show (laguerreHalfQ (2 * j)).eval 0 =
      coeffAt (laguerreHalfCoeffs (2 * j)) 0 by
        rw [← coeff_zero_eq_eval_zero, laguerreHalfQ, coeff_polynomialOfArray]
        rw [coeffAt_eq]]
  push_cast
  rfl

/-- The exact 41-node obstruction, lifted from the rational certificate to every
normalized real polynomial in any `V_k`, `k ≤ 20`. -/
theorem weighted_identity {k : ℕ} (hk : k ≤ 20) {P : Polynomial ℝ}
    (hspan : InEvenLaguerreSpan k P) (h0 : P.eval 0 = 0)
    (h1 : P.derivative.eval 0 = 1) :
    weightedEvalR P = (CertificateData.certificateValue : ℝ) := by
  classical
  obtain ⟨c, rfl⟩ := hspan
  rw [weightedEvalR_finset_sum]
  simp only [weightedEvalR_C_mul]
  have hbasis (j : ℕ) (hj : j ∈ Finset.range (2 * k + 2)) : j < basisCount := by
    dsimp [basisCount]
    have := Finset.mem_range.mp hj
    omega
  calc
    ∑ j ∈ Finset.range (2 * k + 2), c j * weightedEvalR (laguerreHalfR (2 * j)) =
        ∑ j ∈ Finset.range (2 * k + 2), c j *
          ((CertificateData.certificateValue : ℝ) *
              (laguerreHalfR (2 * j)).derivative.eval 0 +
            (certificateAlpha : ℝ) * (laguerreHalfR (2 * j)).eval 0) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [real_basis_moment j (hbasis j hj)]
    _ = (CertificateData.certificateValue : ℝ) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have hd :
          (∑ x ∈ Finset.range (2 * k + 2),
            c x * ((CertificateData.certificateValue : ℝ) *
              (laguerreHalfR (2 * x)).derivative.eval 0)) =
            (CertificateData.certificateValue : ℝ) *
              ∑ x ∈ Finset.range (2 * k + 2),
                c x * (laguerreHalfR (2 * x)).derivative.eval 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      have hv :
          (∑ x ∈ Finset.range (2 * k + 2),
            c x * ((certificateAlpha : ℝ) *
              (laguerreHalfR (2 * x)).eval 0)) =
            (certificateAlpha : ℝ) *
              ∑ x ∈ Finset.range (2 * k + 2),
                c x * (laguerreHalfR (2 * x)).eval 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        ring
      rw [hd, hv]
      have hderiv :
        (∑ j ∈ Finset.range (2 * k + 2), C (c j) * laguerreHalfR (2 * j)).derivative.eval 0 =
          ∑ j ∈ Finset.range (2 * k + 2), c j * (laguerreHalfR (2 * j)).derivative.eval 0 := by
        rw [derivative_sum, eval_finset_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp
      have hvalue :
        (∑ j ∈ Finset.range (2 * k + 2), C (c j) * laguerreHalfR (2 * j)).eval 0 =
          ∑ j ∈ Finset.range (2 * k + 2), c j * (laguerreHalfR (2 * j)).eval 0 := by
        rw [eval_finset_sum]
        apply Finset.sum_congr rfl
        intro j hj
        simp
      rw [← hderiv, ← hvalue, h0, h1]
      ring

theorem certificateValue_pos : (0 : ℝ) < CertificateData.certificateValue := by
  exact_mod_cast (by native_decide : (0 : ℚ) < CertificateData.certificateValue)

/-- Every genuine tail threshold in the family is at least the first certificate node. -/
theorem first_node_le_tailThreshold {P : Polynomial ℝ} (hP : DR20Polynomial P) :
    (6191 / 3125 : ℝ) ≤ tailThreshold P := by
  apply le_csInf hP.tail_nonempty
  intro r hr
  by_contra hnot
  have hrlt : r < (6191 / 3125 : ℝ) := lt_of_not_ge hnot
  have hsum := weighted_identity hP.k_le hP.in_span hP.at_zero hP.derivative_at_zero
  have hnonpos : weightedEvalR P ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    have hiSize : i < CertificateData.nodes.size := Finset.mem_range.mp hi
    have hnodeQ := certificate_nodes_ge_first i hiSize
    have hnode : (6191 / 3125 : ℝ) ≤ (CertificateData.nodes[i]! : ℝ) := by
      convert (Rat.cast_le (K := ℝ)).mpr hnodeQ using 1 <;> norm_num
    have hPnode : P.eval (CertificateData.nodes[i]! : ℝ) ≤ 0 :=
      hr.2 _ (le_trans hrlt.le hnode)
    have hwQ := certificate_weights_positive i (by simpa [certificate_sizes.2] using hiSize)
    have hw : (0 : ℝ) ≤ CertificateData.weights[i]! :=
      (Rat.cast_nonneg (K := ℝ)).mpr hwQ.le
    exact mul_nonpos_of_nonneg_of_nonpos hw hPnode
  rw [hsum] at hnonpos
  exact (not_le_of_gt certificateValue_pos) hnonpos

theorem rational_lower_lt_node_score :
    (63061 / 200000 : ℝ) < (6191 / 3125 : ℝ) / (2 * Real.pi) := by
  have hpi : Real.pi < (355 / 113 : ℝ) := by
    have := Real.pi_lt_d20
    norm_num at this ⊢
    linarith
  have hpi0 := Real.pi_pos
  rw [lt_div_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
  calc
    (63061 / 200000 : ℝ) * (2 * Real.pi)
        < (63061 / 200000 : ℝ) * (2 * (355 / 113 : ℝ)) := by nlinarith
    _ < 6191 / 3125 := by norm_num

end UncertaintyS2
