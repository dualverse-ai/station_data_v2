import PrimeS2.FloorSum
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

namespace PrimeS2

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

/-- Product of the distinct primes in a finite band. -/
def bandProduct (P : Finset ℕ) : ℕ := ∏ p ∈ P, p

/-- Least common multiple of all positive integers at most `D`. -/
def lcmUpTo (D : ℕ) : ℕ := (Icc 1 D).lcm (fun n : ℕ => n)

theorem dvd_lcmUpTo {D d : ℕ} (hd : d ∈ Icc 1 D) : d ∣ lcmUpTo D := by
  exact Finset.dvd_lcm (α := ℕ) hd

private theorem bandProduct_ne_zero {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) : bandProduct P ≠ 0 := by
  rw [bandProduct, Finset.prod_ne_zero_iff]
  exact fun p hp => (hprime p hp).ne_zero

private theorem bandProduct_squarefree {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) : Squarefree (bandProduct P) := by
  rw [bandProduct]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq)
  · exact fun p hp => (hprime p hp).squarefree

private theorem moebius_band_subproduct {P t : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime) (ht : t ⊆ P) :
    μ (∏ p ∈ t, p) = (-1 : ℤ) ^ t.card := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_prod_of_prime t
    (fun p hp => hprime p (ht hp))]
  calc
    (∏ p ∈ t, μ p) = ∏ _p ∈ t, (-1 : ℤ) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact ArithmeticFunction.moebius_apply_prime (hprime p (ht hp))
    _ = (-1 : ℤ) ^ t.card := by simp

private theorem sum_small_powerset (P : Finset ℕ) :
    (∑ t ∈ P.powerset, if t.card ≤ 2 then (-1 : ℤ) ^ t.card else 0) =
      1 - (P.card : ℤ) + (P.card.choose 2 : ℤ) := by
  let A := P.powersetCard 0
  let B := P.powersetCard 1
  let C := P.powersetCard 2
  have hfilter : P.powerset.filter (fun t => t.card ≤ 2) = (A ∪ B) ∪ C := by
    ext t
    simp only [mem_filter, mem_powerset, mem_union, mem_powersetCard, A, B, C]
    constructor
    · rintro ⟨htP, htcard⟩
      have hc : t.card = 0 ∨ t.card = 1 ∨ t.card = 2 := by omega
      rcases hc with hc | hc | hc
      · exact Or.inl (Or.inl ⟨htP, hc⟩)
      · exact Or.inl (Or.inr ⟨htP, hc⟩)
      · exact Or.inr ⟨htP, hc⟩
    · rintro ((⟨htP, hc⟩ | ⟨htP, hc⟩) | ⟨htP, hc⟩) <;>
        exact ⟨htP, by omega⟩
  rw [← Finset.sum_filter]
  rw [hfilter]
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro t htA htB
    have h0 := (Finset.mem_powersetCard.mp htA).2
    have h1 := (Finset.mem_powersetCard.mp htB).2
    omega
  have hABC : Disjoint (A ∪ B) C := by
    rw [Finset.disjoint_left]
    intro t htAB htC
    rcases Finset.mem_union.mp htAB with htA | htB
    · have h0 := (Finset.mem_powersetCard.mp htA).2
      have h2 := (Finset.mem_powersetCard.mp htC).2
      omega
    · have h1 := (Finset.mem_powersetCard.mp htB).2
      have h2 := (Finset.mem_powersetCard.mp htC).2
      omega
  rw [Finset.sum_union hABC, Finset.sum_union hAB]
  have hsum (k : ℕ) :
      (∑ t ∈ P.powersetCard k, (-1 : ℤ) ^ t.card) =
        (P.card.choose k : ℤ) * (-1 : ℤ) ^ k := by
    calc
      (∑ t ∈ P.powersetCard k, (-1 : ℤ) ^ t.card) =
          ∑ _t ∈ P.powersetCard k, (-1 : ℤ) ^ k := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [(Finset.mem_powersetCard.mp ht).2]
      _ = (P.card.choose k : ℤ) * (-1 : ℤ) ^ k := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard]
  rw [show (∑ t ∈ A, (-1 : ℤ) ^ t.card) =
      (P.card.choose 0 : ℤ) * (-1 : ℤ) ^ 0 from hsum 0]
  rw [show (∑ t ∈ B, (-1 : ℤ) ^ t.card) =
      (P.card.choose 1 : ℤ) * (-1 : ℤ) ^ 1 from hsum 1]
  rw [show (∑ t ∈ C, (-1 : ℤ) ^ t.card) =
      (P.card.choose 2 : ℤ) * (-1 : ℤ) ^ 2 from hsum 2]
  simp
  ring

/-- Exact prime-band evaluation of the incomplete Möbius sum.

The two cutoff hypotheses say precisely that subproducts with at most two band
primes are at most `D`, while subproducts with at least three band primes exceed
`D`. They are the finite arithmetic facts supplied by the interval
`D^(1/3) < p ≤ D^(1/2)` in the paper. -/
theorem incompleteMobius_bandProduct {D : ℕ} {P : Finset ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (hsmall : ∀ t ⊆ P, t.card ≤ 2 → (∏ p ∈ t, p) ≤ D)
    (hlarge : ∀ t ⊆ P, 3 ≤ t.card → D < ∏ p ∈ t, p) :
    incompleteMobius D (bandProduct P) =
      1 - (P.card : ℤ) + (P.card.choose 2 : ℤ) := by
  let N := bandProduct P
  have hN0 : N ≠ 0 := bandProduct_ne_zero hprime
  have hNsq : Squarefree N := bandProduct_squarefree hprime
  have hbase : incompleteMobius D N =
      ∑ d ∈ N.divisors, if d ≤ D then μ d else 0 := by
    rw [incompleteMobius]
    rw [← Finset.sum_filter]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext d
      simp only [mem_filter, mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hd1, hdD⟩, hdN⟩
        exact ⟨⟨hdN, hN0⟩, hdD⟩
      · rintro ⟨⟨hdN, _⟩, hdD⟩
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdN (Nat.pos_of_ne_zero hN0)
        exact ⟨⟨hdpos, hdD⟩, hdN⟩
    · intro d hd
      simp only [mem_filter] at hd
      simp
  rw [hbase]
  rw [← Nat.divisors_filter_squarefree_of_squarefree hNsq]
  rw [Nat.sum_divisors_filter_squarefree hN0]
  have hfac : (UniqueFactorizationMonoid.normalizedFactors N).toFinset = P := by
    rw [Nat.factors_eq]
    change N.primeFactors = P
    exact Nat.primeFactors_prod hprime
  rw [hfac]
  calc
    (∑ t ∈ P.powerset,
        if t.val.prod ≤ D then μ t.val.prod else 0) =
        ∑ t ∈ P.powerset, if t.card ≤ 2 then (-1 : ℤ) ^ t.card else 0 := by
      apply Finset.sum_congr rfl
      intro t ht
      have htP : t ⊆ P := Finset.mem_powerset.mp ht
      have hid : Multiset.map (fun p : ℕ => p) t.val = t.val := by simp
      have hμ : μ t.val.prod = (-1 : ℤ) ^ t.card := by
        simpa only [Finset.prod_eq_multiset_prod, hid] using
          moebius_band_subproduct hprime htP
      by_cases hcard : t.card ≤ 2
      · have htd : t.val.prod ≤ D := by
          simpa only [Finset.prod_eq_multiset_prod, hid] using hsmall t htP hcard
        rw [if_pos hcard, if_pos htd, hμ]
      · have hcard3 : 3 ≤ t.card := by omega
        have htd : D < t.val.prod := by
          simpa only [Finset.prod_eq_multiset_prod, hid] using hlarge t htP hcard3
        rw [if_neg hcard, if_neg (not_le.mpr htd)]
    _ = 1 - (P.card : ℤ) + (P.card.choose 2 : ℤ) := sum_small_powerset P

/-- The square/cube inequalities defining the paper's prime band imply the two
finite subproduct cutoff properties used above. -/
theorem band_cutoffs_of_square_cube {D : ℕ} {P : Finset ℕ} (hD : 1 ≤ D)
    (hprime : ∀ p ∈ P, p.Prime)
    (hcube : ∀ p ∈ P, D < p ^ 3)
    (hsquare : ∀ p ∈ P, p ^ 2 ≤ D) :
    (∀ t ⊆ P, t.card ≤ 2 → (∏ p ∈ t, p) ≤ D) ∧
      (∀ t ⊆ P, 3 ≤ t.card → D < ∏ p ∈ t, p) := by
  constructor
  · intro t htP htcard
    have hc : t.card = 0 ∨ t.card = 1 ∨ t.card = 2 := by omega
    rcases hc with hc | hc | hc
    · rw [(Finset.card_eq_zero.mp hc)]
      simp [hD]
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
      have haP : a ∈ P := htP (by simp)
      have ha2 := hsquare a haP
      have ha2pos := (hprime a haP).two_le
      simp only [Finset.prod_singleton]
      nlinarith
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc
      have haP : a ∈ P := htP (by simp)
      have hbP : b ∈ P := htP (by simp)
      have ha2 := hsquare a haP
      have hb2 := hsquare b hbP
      simp only [Finset.prod_insert, Finset.mem_singleton, hab, not_false_eq_true,
        Finset.prod_singleton]
      rcases le_total a b with hab' | hba'
      · nlinarith
      · nlinarith
  · intro t htP htcard
    obtain ⟨u, hut, hucard⟩ := Finset.exists_subset_card_eq htcard
    obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hucard
    have haP : a ∈ P := htP (hut (by simp))
    have hbP : b ∈ P := htP (hut (by simp))
    have hcP : c ∈ P := htP (hut (by simp))
    have ha := hcube a haP
    have hb := hcube b hbP
    have hc := hcube c hcP
    have htriple : D < a * b * c := by
      by_cases hab' : a ≤ b
      · by_cases hac' : a ≤ c
        · apply ha.trans_le
          calc
            a ^ 3 = a * a * a := by ring
            _ ≤ a * b * c := by gcongr
        · have hca : c ≤ a := le_of_not_ge hac'
          have hcb : c ≤ b := hca.trans hab'
          apply hc.trans_le
          calc
            c ^ 3 = c * c * c := by ring
            _ ≤ a * b * c := by gcongr
      · have hba : b ≤ a := le_of_not_ge hab'
        by_cases hbc' : b ≤ c
        · apply hb.trans_le
          calc
            b ^ 3 = b * b * b := by ring
            _ ≤ a * b * c := by gcongr
        · have hcb : c ≤ b := le_of_not_ge hbc'
          have hca : c ≤ a := hcb.trans hba
          apply hc.trans_le
          calc
            c ^ 3 = c * c * c := by ring
            _ ≤ a * b * c := by gcongr
    apply htriple.trans_le
    have hdvd := Finset.prod_dvd_prod_of_subset ({a, b, c} : Finset ℕ) t
      (fun p : ℕ => p) hut
    have hdvd' : a * b * c ∣ ∏ p ∈ t, p := by
      simpa [hab, hac, hbc, mul_assoc] using hdvd
    have hpos : 0 < ∏ p ∈ t, p :=
      Finset.prod_pos fun p hp => (hprime p (htP hp)).pos
    exact Nat.le_of_dvd hpos hdvd'

/-- The literal finite prime band used in the notebook: `D < p^3` and
`p^2 ≤ D`, i.e. `D^(1/3) < p ≤ D^(1/2)` without real roots. -/
def primeBand (D : ℕ) : Finset ℕ :=
  (Finset.range (D + 1)).filter fun p => p.Prime ∧ D < p ^ 3 ∧ p ^ 2 ≤ D

theorem primeBand_spec {D p : ℕ} :
    p ∈ primeBand D ↔ p.Prime ∧ D < p ^ 3 ∧ p ^ 2 ≤ D := by
  constructor
  · intro hp
    exact (Finset.mem_filter.mp hp).2
  · intro hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr ?_, hp⟩
    have hp2 : 2 ≤ p := hp.1.two_le
    nlinarith [hp.2.2]

/-- Unconditional exact evaluation for the paper's concrete prime band. -/
theorem incompleteMobius_primeBand (D : ℕ) (hD : 1 ≤ D) :
    incompleteMobius D (bandProduct (primeBand D)) =
      1 - ((primeBand D).card : ℤ) + ((primeBand D).card.choose 2 : ℤ) := by
  have hprime : ∀ p ∈ primeBand D, p.Prime := fun p hp => (primeBand_spec.mp hp).1
  have hcube : ∀ p ∈ primeBand D, D < p ^ 3 := fun p hp => (primeBand_spec.mp hp).2.1
  have hsquare : ∀ p ∈ primeBand D, p ^ 2 ≤ D := fun p hp => (primeBand_spec.mp hp).2.2
  obtain ⟨hsmall, hlarge⟩ := band_cutoffs_of_square_cube hD hprime hcube hsquare
  exact incompleteMobius_bandProduct hprime hsmall hlarge

/-- The paper's polynomial form of the prime-band evaluation, valid once the
band contains at least two primes. -/
theorem incompleteMobius_bandProduct_polynomial {D : ℕ} {P : Finset ℕ}
    (hcard : 2 ≤ P.card)
    (hprime : ∀ p ∈ P, p.Prime)
    (hsmall : ∀ t ⊆ P, t.card ≤ 2 → (∏ p ∈ t, p) ≤ D)
    (hlarge : ∀ t ⊆ P, 3 ≤ t.card → D < ∏ p ∈ t, p) :
    2 * incompleteMobius D (bandProduct P) =
      ((P.card - 1 : ℕ) * (P.card - 2 : ℕ) : ℤ) := by
  rw [incompleteMobius_bandProduct hprime hsmall hlarge]
  have hchooseNat : 2 * P.card.choose 2 = P.card * (P.card - 1) := by
    rw [mul_comm, Nat.choose_two_right,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self P.card)]
  have hchooseInt : (2 : ℤ) * (P.card.choose 2 : ℤ) =
      (P.card : ℤ) * (P.card - 1 : ℕ) := by
    exact_mod_cast hchooseNat
  have h1 : ((P.card - 1 : ℕ) : ℤ) = (P.card : ℤ) - 1 := by omega
  have h2 : ((P.card - 2 : ℕ) : ℤ) = (P.card : ℤ) - 2 := by omega
  rw [h1, h2]
  nlinarith

end PrimeS2
