import UncertaintyS2.UpperTail
import Mathlib.Analysis.Real.Pi.Bounds

namespace UncertaintyS2

open Polynomial Set

theorem witness_tail_mem :
    (CertificateData.isolatingRight : ℝ) ∈ TailSet witnessR := by
  constructor
  · exact_mod_cast (by native_decide : (0 : ℚ) ≤ CertificateData.isolatingRight)
  · intro t ht
    exact witness_tail_certificate ht

noncomputable def witness_is_DR20 : DR20Polynomial witnessR where
  k := 20
  k_le := by omega
  roots := fun i => CertificateData.roots[i]
  roots_pos := roots_positive
  roots_strictMono := roots_strictMono
  value_at_roots := fun i => (witness_double_roots_R i).1
  derivative_at_roots := fun i => (witness_double_roots_R i).2
  in_span := witness_in_span_20
  at_zero := witness_at_zero_R
  derivative_at_zero := witness_derivative_at_zero_R
  tail_nonempty := ⟨_, witness_tail_mem⟩

theorem witness_threshold_le :
    tailThreshold witnessR ≤ (CertificateData.isolatingRight : ℝ) :=
  tailThreshold_le witness_tail_mem

theorem rational_upper_score_bound :
    (CertificateData.isolatingRight : ℝ) / (2 * Real.pi) <
      (3153090099692479 / 10000000000000000 : ℝ) := by
  have hpi := Real.pi_gt_d20
  have hpi0 := Real.pi_pos
  rw [div_lt_iff₀ (by positivity)]
  norm_num [CertificateData.isolatingRight] at hpi ⊢
  nlinarith

theorem witness_score_lt_upper :
    tailThreshold witnessR / (2 * Real.pi) <
      (3153090099692479 / 10000000000000000 : ℝ) := by
  have hden : 0 < (2 * Real.pi) := by positivity
  exact (div_le_div_of_nonneg_right witness_threshold_le hden.le).trans_lt
    rational_upper_score_bound

end UncertaintyS2
