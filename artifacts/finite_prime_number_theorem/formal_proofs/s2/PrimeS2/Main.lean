import PrimeS2.PrimeBand
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Prime-number-theorem Spotlight 2: direct Möbius cutoffs fail

This module exports the exact finite obstruction at the heart of Spotlight 2.
It proves the reflection identity, evaluates the paper's concrete prime-band
witness, and obtains the corresponding lower bound on the maximum balanced
cutoff floor sum over a full period.

The paper turns this exact result into `Ω(D / log^2 D)` using three classical
analytic-number-theory inputs. Those inputs (a prime-band counting asymptotic,
a zero-free-region Mertens bound, and convergence of a logarithmic Möbius sum)
are not currently theorems in mathlib and are therefore not introduced here as
axioms.
-/

namespace PrimeS2

open ArithmeticFunction Finset
open scoped Function

/-- Maximum balanced cutoff floor sum on the complete period `0 ≤ n ≤ L_D`. -/
noncomputable def cutoffRoof (D : ℕ) : ℚ :=
  let values := (Finset.range (lcmUpTo D + 1)).image (cutoffFloorSum D)
  values.max' (by simp [values])

theorem cutoffFloorSum_le_roof {D m : ℕ} (hm : m ≤ lcmUpTo D) :
    cutoffFloorSum D m ≤ cutoffRoof D := by
  apply Finset.le_max' _ (cutoffFloorSum D m)
  exact Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr (by omega), rfl⟩

private theorem bandProduct_dvd_lcmUpTo (D : ℕ) :
    bandProduct (primeBand D) ∣ lcmUpTo D := by
  let P := primeBand D
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => (primeBand_spec.mp hp).1
  have hpair : (P : Set ℕ).Pairwise (IsRelPrime on fun p : ℕ => p) := by
    intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq)
  have heach : ∀ p ∈ P, p ∣ lcmUpTo D := by
    intro p hp
    apply dvd_lcmUpTo
    have hsquare := (primeBand_spec.mp hp).2.2
    have hp2 := (hprime p hp).two_le
    exact Finset.mem_Icc.mpr ⟨by omega, by nlinarith⟩
  exact Finset.prod_dvd_of_isRelPrime hpair heach

private theorem lcmUpTo_pos (D : ℕ) : 0 < lcmUpTo D := by
  apply Nat.pos_of_ne_zero
  rw [lcmUpTo, Finset.lcm_ne_zero_iff]
  intro d hd
  have hd1 := (Finset.mem_Icc.mp hd).1
  omega

/-- Reduction modulo `L_D` leaves the balanced cutoff floor sum unchanged. -/
theorem cutoffFloorSum_mod_lcmUpTo (D n : ℕ) :
    cutoffFloorSum D (n % lcmUpTo D) = cutoffFloorSum D n := by
  rw [cutoffFloorSum, cutoffFloorSum]
  congr 2
  rw [mobiusPath, mobiusPath]
  apply Finset.sum_congr rfl
  intro d hd
  have hd2 : 2 ≤ d := (Finset.mem_Icc.mp hd).1
  have hd1 : d ∈ Icc 1 D :=
    Finset.mem_Icc.mpr ⟨(by omega), (Finset.mem_Icc.mp hd).2⟩
  rw [centeredResidue, centeredResidue, Nat.mod_mod_of_dvd n (dvd_lcmUpTo hd1)]

/-- `cutoffRoof` is a genuine global roof, not merely a sampled maximum. -/
theorem cutoffFloorSum_le_roof_all (D n : ℕ) :
    cutoffFloorSum D n ≤ cutoffRoof D := by
  have hm : n % lcmUpTo D ≤ lcmUpTo D :=
    (Nat.mod_lt n (lcmUpTo_pos D)).le
  have h := cutoffFloorSum_le_roof hm
  rwa [cutoffFloorSum_mod_lcmUpTo] at h

/-- **Exact Möbius-cutoff obstruction (finite core of PNT Spotlight 2).**

Let `r_D` be the number of primes satisfying `D < p^3` and `p^2 ≤ D`, and
let `M(D)` be the Mertens sum. The maximum direct-cutoff floor sum over its
complete LCM period is at least

`(1 - r_D + choose r_D 2 - M(D)) / 2`.

This is the unconditional exact inequality from which the paper derives the
asymptotic `Ω(D / log^2 D)` obstruction. -/
theorem mobius_cutoff_primeBand_obstruction (D : ℕ) (hD : 1 ≤ D) :
    (((1 - ((primeBand D).card : ℤ) + ((primeBand D).card.choose 2 : ℤ) : ℤ) : ℚ) -
        (mertens D : ℚ)) / 2 ≤ cutoffRoof D := by
  let nStar := bandProduct (primeBand D)
  have hn_dvd : nStar ∣ lcmUpTo D := bandProduct_dvd_lcmUpTo D
  have hn_le : nStar ≤ lcmUpTo D := Nat.le_of_dvd (lcmUpTo_pos D) hn_dvd
  have hmods : ∀ d ∈ Icc 2 D, d ∣ lcmUpTo D := by
    intro d hd
    have hd2 : 2 ≤ d := (Finset.mem_Icc.mp hd).1
    exact dvd_lcmUpTo (Finset.mem_Icc.mpr ⟨(by omega), (Finset.mem_Icc.mp hd).2⟩)
  obtain ⟨m, hm, hfloor⟩ :=
    exists_cutoffFloorSum_obstruction hD hn_le hmods
  rw [show incompleteMobius D nStar =
      1 - ((primeBand D).card : ℤ) + ((primeBand D).card.choose 2 : ℤ) by
        exact incompleteMobius_primeBand D hD] at hfloor
  exact hfloor.trans (cutoffFloorSum_le_roof hm)

/-- The same result in the notebook's existential form: an explicit full
period contains a violating point at least as large as the prime-band bound. -/
theorem exists_primeBand_cutoff_obstruction (D : ℕ) (hD : 1 ≤ D) :
    ∃ m ≤ lcmUpTo D,
      (((1 - ((primeBand D).card : ℤ) + ((primeBand D).card.choose 2 : ℤ) : ℤ) : ℚ) -
          (mertens D : ℚ)) / 2 ≤ cutoffFloorSum D m := by
  let nStar := bandProduct (primeBand D)
  have hn_dvd : nStar ∣ lcmUpTo D := bandProduct_dvd_lcmUpTo D
  have hn_le : nStar ≤ lcmUpTo D := Nat.le_of_dvd (lcmUpTo_pos D) hn_dvd
  have hmods : ∀ d ∈ Icc 2 D, d ∣ lcmUpTo D := by
    intro d hd
    have hd2 : 2 ≤ d := (Finset.mem_Icc.mp hd).1
    exact dvd_lcmUpTo (Finset.mem_Icc.mpr ⟨(by omega), (Finset.mem_Icc.mp hd).2⟩)
  obtain ⟨m, hm, hfloor⟩ := exists_cutoffFloorSum_obstruction hD hn_le hmods
  refine ⟨m, hm, ?_⟩
  rw [show incompleteMobius D nStar =
      1 - ((primeBand D).card : ℤ) + ((primeBand D).card.choose 2 : ℤ) by
        exact incompleteMobius_primeBand D hD] at hfloor
  exact hfloor

end PrimeS2
