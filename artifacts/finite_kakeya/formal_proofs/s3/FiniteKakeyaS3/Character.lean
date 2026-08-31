import Mathlib

/-!
# Quadratic-character identities

Elementary complete-sum identities used in the proof of the uniform one-pole
boundary estimate.  All character sums take values in `ℤ`.
-/

namespace FiniteKakeyaS3

open scoped BigOperators
open Finset

variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

theorem two_ne_zero_of_ringChar (hchar : ringChar F ≠ 2) : (2 : F) ≠ 0 := by
  intro h2
  apply hchar
  exact CharP.ringChar_of_prime_eq_zero Nat.prime_two h2

private def rootPairs (a : F) := {rx : F × F // rx.1 ^ 2 = rx.2 ^ 2 - a}

private def productPairs (a : F) := {uv : F × F // uv.1 * uv.2 = -a}

private def rootPairsEquivProductPairs (h2 : (2 : F) ≠ 0) (a : F) :
    rootPairs F a ≃ productPairs F a where
  toFun rx := ⟨(rx.1.1 - rx.1.2, rx.1.1 + rx.1.2), by
    change (rx.1.1 - rx.1.2) * (rx.1.1 + rx.1.2) = -a
    calc
      _ = rx.1.1 ^ 2 - rx.1.2 ^ 2 := by ring
      _ = -a := by rw [rx.2]; ring⟩
  invFun uv := ⟨((uv.1.1 + uv.1.2) / 2, (uv.1.2 - uv.1.1) / 2), by
    change ((uv.1.1 + uv.1.2) / 2) ^ 2 = ((uv.1.2 - uv.1.1) / 2) ^ 2 - a
    field_simp
    have hp := uv.2
    linear_combination 4 * hp⟩
  left_inv rx := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> field_simp <;> ring
  right_inv uv := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp <;> field_simp <;> ring

private def productPairsEquivNonzero (ha : a ≠ 0) :
    productPairs F a ≃ {u : F // u ≠ 0} where
  toFun uv := ⟨uv.1.1, by
    intro hu
    have hp := uv.2
    rw [hu, zero_mul] at hp
    exact ha (neg_eq_zero.mp hp.symm)⟩
  invFun u := ⟨(u.1, -a / u.1), by
    change u.1 * (-a / u.1) = -a
    rw [mul_comm]
    exact div_mul_cancel₀ (-a) u.2⟩
  left_inv uv := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp
      have huv : uv.1.1 ≠ 0 := by
        intro hu
        have hp := uv.2
        rw [hu, zero_mul] at hp
        exact ha (neg_eq_zero.mp hp.symm)
      apply (div_eq_iff huv).2
      simpa [mul_comm] using uv.2.symm
  right_inv _ := rfl

private def sigmaRootsEquivRootPairs (a : F) :
    (Σ x : F, {r : F // r ^ 2 = x ^ 2 - a}) ≃ rootPairs F a where
  toFun xr := ⟨(xr.2.1, xr.1), xr.2.2⟩
  invFun rx := ⟨rx.1.2, ⟨rx.1.1, rx.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def rootFiberEquivFinset (a x : F) :
    {r : F // r ^ 2 = x ^ 2 - a} ≃
      ↥((univ : Finset F).filter fun r => r ^ 2 = x ^ 2 - a) where
  toFun r := ⟨r.1, by simp [r.2]⟩
  invFun r := ⟨r.1, (mem_filter.1 r.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A translated monic quadratic with nonzero shift has character sum `-1`. -/
theorem sum_quadratic_square_sub (hchar : ringChar F ≠ 2) (a : F) (ha : a ≠ 0) :
    (∑ x : F, quadraticChar F (x ^ 2 - a)) = -1 := by
  classical
  have h2 := two_ne_zero_of_ringChar F hchar
  have hnonzero : Fintype.card {u : F // u ≠ 0} = Fintype.card F - 1 := by
    simpa using Fintype.card_subtype_compl (fun u : F => u = 0)
  letI : Fintype (productPairs F a) :=
    Fintype.ofEquiv {u : F // u ≠ 0} (productPairsEquivNonzero F ha).symm
  letI : Fintype (rootPairs F a) :=
    Fintype.ofEquiv (productPairs F a) (rootPairsEquivProductPairs F h2 a).symm
  letI (x : F) : Fintype {r : F // r ^ 2 = x ^ 2 - a} :=
    Fintype.ofEquiv ↥((univ : Finset F).filter fun r => r ^ 2 = x ^ 2 - a)
      (rootFiberEquivFinset F a x).symm
  have hpairs : Fintype.card (rootPairs F a) = Fintype.card F - 1 := by
    calc
      _ = Fintype.card (productPairs F a) :=
        Fintype.card_congr (rootPairsEquivProductPairs F h2 a)
      _ = Fintype.card {u : F // u ≠ 0} :=
        Fintype.card_congr (productPairsEquivNonzero F ha)
      _ = _ := hnonzero
  have hsigma :
      Fintype.card (rootPairs F a) =
        ∑ x : F, Fintype.card {r : F // r ^ 2 = x ^ 2 - a} := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (sigmaRootsEquivRootPairs F a).symm
  have hroot (x : F) :
      (Fintype.card {r : F // r ^ 2 = x ^ 2 - a} : ℤ) =
        quadraticChar F (x ^ 2 - a) + 1 := by
    rw [Fintype.card_congr (rootFiberEquivFinset F a x), Fintype.card_coe]
    simpa [Set.toFinset_setOf] using quadraticChar_card_sqrts hchar (x ^ 2 - a)
  have hcast := congrArg (fun n : ℕ => (n : ℤ)) hsigma
  change (Fintype.card (rootPairs F a) : ℤ) =
    ((∑ x : F, Fintype.card {r : F // r ^ 2 = x ^ 2 - a}) : ℕ) at hcast
  rw [Nat.cast_sum] at hcast
  simp_rw [hroot] at hcast
  rw [hpairs] at hcast
  have hpos := Fintype.card_pos (α := F)
  rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card F)] at hcast
  simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one] at hcast
  omega

/-- The sum of the quadratic character over a nonconstant affine function. -/
theorem sum_quadratic_affine (hchar : ringChar F ≠ 2) (a b : F) (ha : a ≠ 0) :
    (∑ x : F, quadraticChar F (a * x + b)) = 0 := by
  let e : F → F := fun x => a * x + b
  have he : Function.Bijective e := by
    constructor
    · intro x y h
      exact (mul_left_cancel₀ ha) (add_right_cancel h)
    · intro z
      refine ⟨(z - b) / a, ?_⟩
      dsimp [e]
      field_simp
      ring
  calc
    _ = ∑ z : F, quadraticChar F z :=
      Equiv.sum_comp (Equiv.ofBijective e he) (quadraticChar F)
    _ = 0 := quadraticChar_sum_zero (F := F) hchar

/-- Complete character sum of a genuine quadratic, separated according to
whether its discriminant vanishes. -/
theorem sum_quadratic_general (hchar : ringChar F ≠ 2) (a b c : F) (ha : a ≠ 0) :
    (∑ x : F, quadraticChar F (a * x ^ 2 + b * x + c)) =
      if b ^ 2 - 4 * a * c = 0 then
        ((Fintype.card F : ℤ) - 1) * quadraticChar F a
      else -quadraticChar F a := by
  classical
  have h2 := two_ne_zero_of_ringChar F hchar
  have h4 : (4 : F) ≠ 0 := by
    rw [show (4 : F) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  let d : F := b ^ 2 - 4 * a * c
  let shift : F := b / (2 * a)
  let e : F → F := fun t => t - shift
  have he : Function.Bijective e := by
    constructor
    · intro x y h
      dsimp [e] at h
      exact sub_left_inj.mp h
    · intro x
      exact ⟨x + shift, by simp [e]⟩
  have hpoly (t : F) :
      a * (e t) ^ 2 + b * e t + c = a * (t ^ 2 - d / (4 * a ^ 2)) := by
    dsimp [e, shift, d]
    field_simp
    ring
  rw [show b ^ 2 - 4 * a * c = d by rfl]
  by_cases hd : d = 0
  · simp only [hd, if_true]
    calc
      (∑ x : F, quadraticChar F (a * x ^ 2 + b * x + c)) =
          ∑ t : F, quadraticChar F (a * (e t) ^ 2 + b * e t + c) := by
            exact (Equiv.sum_comp (Equiv.ofBijective e he)
              (fun x => quadraticChar F (a * x ^ 2 + b * x + c))).symm
      _ = ∑ t : F, if t = 0 then 0 else quadraticChar F a := by
        apply sum_congr rfl
        intro t _
        rw [hpoly, hd]
        simp only [zero_div, sub_zero]
        by_cases ht : t = 0
        · simp [ht]
        · simp only [ht, if_false]
          change quadraticCharFun F (a * t ^ 2) = quadraticCharFun F a
          rw [quadraticCharFun_mul,
            show quadraticCharFun F (t ^ 2) = 1 from quadraticChar_sq_one' ht, mul_one]
      _ = ((Fintype.card F : ℤ) - 1) * quadraticChar F a := by
        rw [Finset.sum_ite]
        have hz : ((univ : Finset F).filter fun t => t = 0).card = 1 := by
          have : ((univ : Finset F).filter fun t => t = 0) = {0} := by ext; simp
          rw [this, card_singleton]
        have hn : ((univ : Finset F).filter fun t => ¬t = 0).card =
            Fintype.card F - 1 := by
          have hp := filter_card_add_filter_neg_card_eq_card
            (s := (univ : Finset F)) (fun t => t = 0)
          rw [hz, card_univ] at hp
          omega
        simp only [sum_const_zero, sum_const, nsmul_eq_mul, zero_add]
        rw [hn, Nat.cast_sub (by have := Fintype.card_pos (α := F); omega)]
        norm_num
  · simp only [hd, if_false]
    have hden : 4 * a ^ 2 ≠ 0 := mul_ne_zero h4 (pow_ne_zero 2 ha)
    have hd' : d / (4 * a ^ 2) ≠ 0 := div_ne_zero hd hden
    calc
      (∑ x : F, quadraticChar F (a * x ^ 2 + b * x + c)) =
          ∑ t : F, quadraticChar F (a * (e t) ^ 2 + b * e t + c) := by
            exact (Equiv.sum_comp (Equiv.ofBijective e he)
              (fun x => quadraticChar F (a * x ^ 2 + b * x + c))).symm
      _ = quadraticChar F a *
          (∑ t : F, quadraticChar F (t ^ 2 - d / (4 * a ^ 2))) := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro t _
        rw [hpoly]
        change quadraticCharFun F (a * (t ^ 2 - d / (4 * a ^ 2))) =
          quadraticCharFun F a * quadraticCharFun F (t ^ 2 - d / (4 * a ^ 2))
        rw [quadraticCharFun_mul]
      _ = quadraticChar F a * (-1) := by
        rw [sum_quadratic_square_sub F hchar _ hd']
      _ = -quadraticChar F a := by ring

end FiniteKakeyaS3
