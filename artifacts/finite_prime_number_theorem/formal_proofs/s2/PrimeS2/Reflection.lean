import PrimeS2.Definitions
import Mathlib.Tactic

namespace PrimeS2

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

/-- Exact residue reflection for a modulus dividing the reflection length. -/
theorem centeredResidue_reflect {d L n : ℕ} (hd : 0 < d) (hn : n ≤ L)
    (hdL : d ∣ L) :
    centeredResidue n d + centeredResidue (L - n) d =
      if d ∣ n then -1 else 0 := by
  have hmodL : L % d = 0 := Nat.mod_eq_zero_of_dvd hdL
  have hadd : n + (L - n) = L := Nat.add_sub_of_le hn
  have hmodsum : (n % d + (L - n) % d) % d = 0 := by
    rw [← Nat.add_mod, hadd, hmodL]
  by_cases hdn : d ∣ n
  · rw [if_pos hdn]
    have hnmod : n % d = 0 := Nat.mod_eq_zero_of_dvd hdn
    have hrefmod : (L - n) % d = 0 := by
      have hlt := Nat.mod_lt (L - n) hd
      rw [hnmod, zero_add, Nat.mod_eq_of_lt hlt] at hmodsum
      exact hmodsum
    simp [centeredResidue, hnmod, hrefmod]
    norm_num
  · rw [if_neg hdn]
    have hnmod_ne : n % d ≠ 0 := mt Nat.dvd_of_mod_eq_zero hdn
    have hsum_ne : n % d + (L - n) % d ≠ 0 := by omega
    have hsum_dvd : d ∣ n % d + (L - n) % d :=
      Nat.dvd_of_mod_eq_zero hmodsum
    have hsum_lt : n % d + (L - n) % d < 2 * d := by
      have h₁ := Nat.mod_lt n hd
      have h₂ := Nat.mod_lt (L - n) hd
      omega
    have hsum : n % d + (L - n) % d = d :=
      Nat.eq_of_dvd_of_lt_two_mul hsum_ne hsum_dvd hsum_lt
    rw [centeredResidue, centeredResidue]
    have hcast : ((n % d : ℕ) : ℚ) + (((L - n) % d : ℕ) : ℚ) = (d : ℚ) := by
      exact_mod_cast hsum
    calc
      ((n % d : ℕ) : ℚ) / d - 1 / 2 +
          ((((L - n) % d : ℕ) : ℚ) / d - 1 / 2) =
          (((n % d : ℕ) : ℚ) + (((L - n) % d : ℕ) : ℚ)) / d - 1 := by ring
      _ = 0 := by rw [hcast]; field_simp; norm_num

/-- The exact reflection identity
`g_D(n) + g_D(L-n) = 1 - E_D(n)` from Spotlight 2. -/
theorem mobiusPath_reflection {D L n : ℕ} (hD : 1 ≤ D) (hn : n ≤ L)
    (hL : ∀ d ∈ Icc 2 D, d ∣ L) :
    mobiusPath D n + mobiusPath D (L - n) = 1 - incompleteMobius D n := by
  have hinc : incompleteMobius D n =
      1 + ∑ d ∈ Icc 2 D, if d ∣ n then μ d else 0 := by
    rw [incompleteMobius, ← Finset.insert_Icc_succ_left_eq_Icc hD]
    simp
  rw [mobiusPath, mobiusPath, hinc]
  push_cast
  rw [← Finset.sum_add_distrib]
  ring_nf
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro d hdmem
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) (Finset.mem_Icc.mp hdmem).1
  rw [← mul_add, centeredResidue_reflect hdpos hn (hL d hdmem)]
  by_cases hdvd : d ∣ n <;> simp [hdvd]

/-- At least one point of a reflected pair realizes half of the incomplete-sum
obstruction. This is equation (1) of the notebook without introducing a
noncomputable maximum. -/
theorem exists_reflected_path_obstruction {D L n : ℕ} (hD : 1 ≤ D)
    (hn : n ≤ L) (hL : ∀ d ∈ Icc 2 D, d ∣ L) :
    ∃ m ≤ L, ((incompleteMobius D n : ℚ) - 1) / 2 ≤ -mobiusPath D m := by
  have href := mobiusPath_reflection hD hn hL
  by_cases hfirst : ((incompleteMobius D n : ℚ) - 1) / 2 ≤ -mobiusPath D n
  · exact ⟨n, hn, hfirst⟩
  · refine ⟨L - n, Nat.sub_le L n, ?_⟩
    linarith

/-- The corresponding exact lower bound for the balanced cutoff floor sum. -/
theorem exists_cutoffFloorSum_obstruction {D L n : ℕ} (hD : 1 ≤ D)
    (hn : n ≤ L) (hL : ∀ d ∈ Icc 2 D, d ∣ L) :
    ∃ m ≤ L,
      ((incompleteMobius D n : ℚ) - (mertens D : ℚ)) / 2 ≤
        cutoffFloorSum D m := by
  obtain ⟨m, hm, hpath⟩ := exists_reflected_path_obstruction hD hn hL
  refine ⟨m, hm, ?_⟩
  rw [cutoffFloorSum]
  linarith

end PrimeS2
