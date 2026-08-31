import PrimeS2.Reflection
import Mathlib.Tactic

namespace PrimeS2

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

/-- The cutoff weight is balanced exactly, not approximately. -/
theorem directCutoffWeight_balanced (D : ℕ) (hD : 1 ≤ D) :
    (∑ k ∈ Icc 1 D, directCutoffWeight D k / k) = 0 := by
  rw [← Finset.insert_Icc_succ_left_eq_Icc hD]
  rw [Finset.sum_insert (by simp)]
  rw [show directCutoffWeight D 1 =
      -(∑ d ∈ Icc 2 D, (μ d : ℚ) / d) by simp [directCutoffWeight]]
  rw [show Order.succ (1 : ℕ) = 2 by rfl]
  norm_num only [Nat.cast_one, div_one]
  change -(∑ d ∈ Icc 2 D, (μ d : ℚ) / d) +
      (∑ k ∈ Icc 2 D, directCutoffWeight D k / k) = 0
  have hrest : (∑ k ∈ Icc 2 D, directCutoffWeight D k / k) =
      ∑ k ∈ Icc 2 D, (μ k : ℚ) / k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk1 : k ≠ 1 := by omega
    simp [directCutoffWeight, hk, hk1]
  rw [hrest]
  norm_num

private theorem floor_sub_div_eq_neg_mod_div {n d : ℕ} (hd : 0 < d) :
    (((n / d : ℕ) : ℚ)) - (n : ℚ) / d = -(((n % d : ℕ) : ℚ) / d) := by
  have hdecomp : n % d + d * (n / d) = n := Nat.mod_add_div n d
  have hcast : ((n % d : ℕ) : ℚ) + (d : ℚ) * ((n / d : ℕ) : ℚ) = n := by
    exact_mod_cast hdecomp
  field_simp
  linarith

/-- The centered-path expression used in the reflection proof is exactly the
paper's weighted floor sum with the balanced direct Möbius cutoff. -/
theorem cutoffFloorSum_eq_weightedFloorSum (D n : ℕ) (hD : 1 ≤ D) :
    cutoffFloorSum D n = weightedFloorSum D n := by
  have hmertens : mertens D = 1 + ∑ d ∈ Icc 2 D, μ d := by
    rw [mertens, ← Finset.insert_Icc_succ_left_eq_Icc hD]
    simp
  have hcenter : cutoffFloorSum D n =
      -(∑ d ∈ Icc 2 D, (μ d : ℚ) * (((n % d : ℕ) : ℚ) / d)) := by
    have hexpand : (∑ d ∈ Icc 2 D, (μ d : ℚ) * centeredResidue n d) =
        (∑ d ∈ Icc 2 D, (μ d : ℚ) * (((n % d : ℕ) : ℚ) / d)) -
          (∑ d ∈ Icc 2 D, (μ d : ℚ)) / 2 := by
      calc
        (∑ d ∈ Icc 2 D, (μ d : ℚ) * centeredResidue n d) =
            ∑ d ∈ Icc 2 D,
              ((μ d : ℚ) * (((n % d : ℕ) : ℚ) / d) - (μ d : ℚ) / 2) := by
                apply Finset.sum_congr rfl
                intro d _hd
                simp only [centeredResidue]
                ring
        _ = (∑ d ∈ Icc 2 D, (μ d : ℚ) * (((n % d : ℕ) : ℚ) / d)) -
              (∑ d ∈ Icc 2 D, (μ d : ℚ)) / 2 := by
                rw [Finset.sum_sub_distrib]
                congr 1
                calc
                  (∑ d ∈ Icc 2 D, (μ d : ℚ) / 2) =
                      ∑ d ∈ Icc 2 D, (μ d : ℚ) * (1 / 2 : ℚ) := by
                        apply Finset.sum_congr rfl
                        intro d _hd
                        ring
                  _ = (∑ d ∈ Icc 2 D, (μ d : ℚ)) * (1 / 2 : ℚ) := by
                        rw [Finset.sum_mul]
                  _ = (∑ d ∈ Icc 2 D, (μ d : ℚ)) / 2 := by ring
    rw [cutoffFloorSum, mobiusPath, hmertens]
    push_cast
    rw [hexpand]
    ring
  have hweighted : weightedFloorSum D n =
      -(∑ d ∈ Icc 2 D, (μ d : ℚ) / d) * (n : ℚ) +
        ∑ d ∈ Icc 2 D, (μ d : ℚ) * (((n / d : ℕ) : ℚ)) := by
    rw [weightedFloorSum, ← Finset.insert_Icc_succ_left_eq_Icc hD]
    rw [Finset.sum_insert (by simp)]
    rw [show directCutoffWeight D 1 =
        -(∑ d ∈ Icc 2 D, (μ d : ℚ) / d) by simp [directCutoffWeight]]
    rw [show Order.succ (1 : ℕ) = 2 by rfl]
    norm_num only [Nat.div_one]
    change -(∑ d ∈ Icc 2 D, (μ d : ℚ) / d) * (n : ℚ) +
        (∑ k ∈ Icc 2 D, directCutoffWeight D k * (((n / k : ℕ) : ℚ))) =
          -(∑ d ∈ Icc 2 D, (μ d : ℚ) / d) * (n : ℚ) +
            ∑ d ∈ Icc 2 D, (μ d : ℚ) * (((n / d : ℕ) : ℚ))
    have hrest :
        (∑ k ∈ Icc 2 D, directCutoffWeight D k * (((n / k : ℕ) : ℚ))) =
          ∑ k ∈ Icc 2 D, (μ k : ℚ) * (((n / k : ℕ) : ℚ)) := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      have hk1 : k ≠ 1 := by omega
      simp [directCutoffWeight, hk, hk1]
    rw [hrest]
  have hterm : ∀ d ∈ Icc 2 D,
      (μ d : ℚ) * (((n / d : ℕ) : ℚ)) - (μ d : ℚ) * (n : ℚ) / d =
        -(μ d : ℚ) * (((n % d : ℕ) : ℚ) / d) := by
    intro d hdmem
    have hd2 : 2 ≤ d := (Finset.mem_Icc.mp hdmem).1
    have hd : 0 < d := by omega
    calc
      (μ d : ℚ) * (((n / d : ℕ) : ℚ)) - (μ d : ℚ) * (n : ℚ) / d =
          (μ d : ℚ) * ((((n / d : ℕ) : ℚ)) - (n : ℚ) / d) := by ring
      _ = -(μ d : ℚ) * (((n % d : ℕ) : ℚ) / d) := by
          rw [floor_sub_div_eq_neg_mod_div hd]
          ring
  rw [hcenter, hweighted]
  calc
    -(∑ d ∈ Icc 2 D, (μ d : ℚ) * (((n % d : ℕ) : ℚ) / d)) =
        ∑ d ∈ Icc 2 D,
          ((μ d : ℚ) * (((n / d : ℕ) : ℚ)) - (μ d : ℚ) * (n : ℚ) / d) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro d hdmem
      rw [hterm d hdmem]
      ring
    _ = -(∑ d ∈ Icc 2 D, (μ d : ℚ) / d) * (n : ℚ) +
        ∑ d ∈ Icc 2 D, (μ d : ℚ) * (((n / d : ℕ) : ℚ)) := by
      rw [Finset.sum_sub_distrib]
      have hfactor :
          (∑ d ∈ Icc 2 D, (μ d : ℚ) * (n : ℚ) / d) =
            (∑ d ∈ Icc 2 D, (μ d : ℚ) / d) * (n : ℚ) := by
        calc
          (∑ d ∈ Icc 2 D, (μ d : ℚ) * (n : ℚ) / d) =
              ∑ d ∈ Icc 2 D, ((μ d : ℚ) / d) * (n : ℚ) := by
                apply Finset.sum_congr rfl
                intro d _hd
                ring
          _ = (∑ d ∈ Icc 2 D, (μ d : ℚ) / d) * (n : ℚ) := by
                rw [Finset.sum_mul]
      rw [hfactor]
      ring

end PrimeS2
