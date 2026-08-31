import BookS3.WithinCorrelation
import BookS3.MixedCorrelation

/-!
# The concrete Yamada--Pott correlation profile

This module assembles the finite-field correlation identities into the
additive `CorrelationProfile` consumed by the two-fibre Ramsey lift.
-/

namespace BookS3

open scoped Classical

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

private theorem YamadaPott.skew_mul_char_eq_neg_one
    {a : Additive (YamadaPottSquareSubgroup F)} (ha : a ≠ 0)
    {b : F} (hb : b ≠ 0)
    (hne : YamadaPott.skew a * quadraticChar F b ≠ 1) :
    YamadaPott.skew a * quadraticChar F b = -1 := by
  have hsa : 1 - YamadaPott.squareValue a ≠ 0 := by
    intro hzero
    have hsquare : YamadaPott.squareValue a = 1 := (sub_eq_zero.mp hzero).symm
    exact ha (YamadaPott.squareValue_eq_one_iff a |>.mp hsquare)
  rcases quadraticChar_dichotomy hsa with hsaPos | hsaNeg
  · rcases quadraticChar_dichotomy hb with hbPos | hbNeg
    · simp [YamadaPott.skew, YamadaPottH, hsaPos, hbPos] at hne
    · simp [YamadaPott.skew, YamadaPottH, hsaPos, hbNeg]
  · rcases quadraticChar_dichotomy hb with hbPos | hbNeg
    · simp [YamadaPott.skew, YamadaPottH, hsaNeg, hbPos]
    · simp [YamadaPott.skew, YamadaPottH, hsaNeg, hbNeg] at hne

private theorem YamadaPott.I_le_square {t : Nat}
    (hF : ringChar F ≠ 2) (hcard : Fintype.card F = 4 * t + 3)
    (a : Additive (YamadaPottSquareSubgroup F)) :
    YamadaPottI F (YamadaPott.squareValue a) ≤ (2 * t + 2) ^ 2 := by
  have hle : YamadaPottI F (YamadaPott.squareValue a) ≤
      (YamadaPottD F).card := by
    exact Finset.card_le_card (Finset.filter_subset _ _)
  rw [card_YamadaPottD (F := F) hF hcard] at hle
  nlinarith

private theorem YamadaPott.nonzero_A_value
    (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    {a : Additive (YamadaPottSquareSubgroup F)} (ha : a ≠ 0)
    {b : F} (hb : b ≠ 0) {s : ℤ}
    (hs : YamadaPott.skew a * quadraticChar F b = s) :
    2 * (((correlation (YamadaPottA (F := F)) YamadaPottA (a, b)).card +
        (correlation (YamadaPottC (F := F)) YamadaPottC (a, b)).card : Nat) : ℤ) =
      2 * (YamadaPottN t : ℤ) - 3 - s := by
  have hA := YamadaPott_A_correlation_nonzero (F := F) hF hcard ha hb
  have hCNat := YamadaPott_C_correlation_nonzero_at_card
    (F := F) hF hcard a hb
  have hIle := YamadaPott.I_le_square (F := F) hF hcard a
  have hC := congrArg (fun z : Nat => (z : ℤ)) hCNat
  norm_num [Nat.cast_sub hIle] at hC
  have hsource := YamadaPott_H_add_two_I (F := F) hF hcard
    (YamadaPott.squareValue_mem_S a)
    (fun h => ha (YamadaPott.squareValue_eq_one_iff a |>.mp h))
  have hmOdd : Odd (2 * t + 1) := ⟨t, by omega⟩
  have hn := CodegreeArithmetic.bookParameter_int_relation hmOdd
  change 2 * (YamadaPottN t : ℤ) =
    2 * ((2 * t + 1 : Nat) : ℤ) ^ 2 + (2 * t + 1 : Nat) + 1 at hn
  have hA' :
      4 * ((correlation (YamadaPottA (F := F)) YamadaPottA (a, b)).card : ℤ) =
        ((2 * t + 1 : ℤ) - 2) * (2 * (2 * t + 1 : ℤ) + 3) -
          YamadaPottCorrH F (YamadaPott.squareValue a) - 2 * s := by
    nlinarith
  have hC' :
      2 * ((correlation (YamadaPottC (F := F)) YamadaPottC (a, b)).card : ℤ) =
        ((2 * t + 1 : ℤ) + 1) ^ 2 -
          YamadaPottI F (YamadaPott.squareValue a) := by
    nlinarith
  have hresult := CodegreeArithmetic.sameFiberA_nonzero_general
    hn hsource hA' hC'
  push_cast
  exact hresult

private theorem YamadaPott.nonzero_B_value
    (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    {a : Additive (YamadaPottSquareSubgroup F)} (ha : a ≠ 0)
    {b : F} (hb : b ≠ 0) {s : ℤ}
    (hs : YamadaPott.skew a * quadraticChar F b = s) :
    2 * (((correlation (YamadaPottB (F := F)) YamadaPottB (a, b)).card +
        (correlation (YamadaPottC (F := F)) YamadaPottC (a, b)).card : Nat) : ℤ) =
      2 * (YamadaPottN t : ℤ) - 3 + s := by
  have hB := YamadaPott_B_correlation_nonzero (F := F) hF hcard ha hb
  have hCNat := YamadaPott_C_correlation_nonzero_at_card
    (F := F) hF hcard a hb
  have hIle := YamadaPott.I_le_square (F := F) hF hcard a
  have hC := congrArg (fun z : Nat => (z : ℤ)) hCNat
  norm_num [Nat.cast_sub hIle] at hC
  have hsource := YamadaPott_H_add_two_I (F := F) hF hcard
    (YamadaPott.squareValue_mem_S a)
    (fun h => ha (YamadaPott.squareValue_eq_one_iff a |>.mp h))
  have hmOdd : Odd (2 * t + 1) := ⟨t, by omega⟩
  have hn := CodegreeArithmetic.bookParameter_int_relation hmOdd
  change 2 * (YamadaPottN t : ℤ) =
    2 * ((2 * t + 1 : Nat) : ℤ) ^ 2 + (2 * t + 1 : Nat) + 1 at hn
  have hB' :
      4 * ((correlation (YamadaPottB (F := F)) YamadaPottB (a, b)).card : ℤ) =
        ((2 * t + 1 : ℤ) - 2) * (2 * (2 * t + 1 : ℤ) + 3) -
          YamadaPottCorrH F (YamadaPott.squareValue a) + 2 * s := by
    nlinarith
  have hC' :
      2 * ((correlation (YamadaPottC (F := F)) YamadaPottC (a, b)).card : ℤ) =
        ((2 * t + 1 : ℤ) + 1) ^ 2 -
          YamadaPottI F (YamadaPott.squareValue a) := by
    nlinarith
  have hresult := CodegreeArithmetic.sameFiberB_nonzero_general
    hn hsource hB' hC'
  push_cast
  exact hresult

/-- Within-fibre-zero edge bound when both coordinates of the difference are
nonzero. -/
theorem YamadaPott.profile_edge_fibre0_nonzero
    (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    {a : Additive (YamadaPottSquareSubgroup F)} (ha : a ≠ 0)
    {b : F} (hb : b ≠ 0) (hd : (a, b) ∈ YamadaPottA) :
    (correlation (YamadaPottA (F := F)) YamadaPottA (a, b)).card +
        (correlation (YamadaPottC (F := F)) YamadaPottC (a, b)).card ≤
      YamadaPottN t - 2 := by
  have hs : YamadaPott.skew a * quadraticChar F b = 1 := by
    rcases (mem_YamadaPottA.mp hd).2 with hb0 | hs
    · exact (hb hb0).elim
    · exact hs
  have hvalue := YamadaPott.nonzero_A_value (F := F) hF hcard ha hb hs
  have hn : 2 ≤ YamadaPottN t := by rw [YamadaPottN_eq]; omega
  omega

/-- Within-fibre-zero nonedge bound when both coordinates of the difference
are nonzero. -/
theorem YamadaPott.profile_nonedge_fibre0_nonzero
    (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    {a : Additive (YamadaPottSquareSubgroup F)} (ha : a ≠ 0)
    {b : F} (hb : b ≠ 0) (hd : (a, b) ∉ YamadaPottA) :
    (correlation (YamadaPottA (F := F)) YamadaPottA (a, b)).card +
        (correlation (YamadaPottC (F := F)) YamadaPottC (a, b)).card ≤
      YamadaPottN t - 1 := by
  have hne : YamadaPott.skew a * quadraticChar F b ≠ 1 := by
    intro hs
    exact hd (mem_YamadaPottA.mpr ⟨ha, Or.inr hs⟩)
  have hs := YamadaPott.skew_mul_char_eq_neg_one (F := F) ha hb hne
  have hvalue := YamadaPott.nonzero_A_value (F := F) hF hcard ha hb hs
  have hn : 1 ≤ YamadaPottN t := by rw [YamadaPottN_eq]; omega
  omega

/-- Within-fibre-one edge bound when both coordinates of the difference are
nonzero. -/
theorem YamadaPott.profile_edge_fibre1_nonzero
    (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    {a : Additive (YamadaPottSquareSubgroup F)} (ha : a ≠ 0)
    {b : F} (hb : b ≠ 0) (hd : (a, b) ∈ YamadaPottB) :
    (correlation (YamadaPottB (F := F)) YamadaPottB (a, b)).card +
        (correlation (YamadaPottC (F := F)) YamadaPottC (a, b)).card ≤
      YamadaPottN t - 2 := by
  have hs : YamadaPott.skew a * quadraticChar F b = -1 := by
    rcases (mem_YamadaPottB.mp hd).2 with hb0 | hs
    · exact (hb hb0).elim
    · exact hs
  have hvalue := YamadaPott.nonzero_B_value (F := F) hF hcard ha hb hs
  have hn : 2 ≤ YamadaPottN t := by rw [YamadaPottN_eq]; omega
  omega

/-- Within-fibre-one nonedge bound when both coordinates of the difference
are nonzero. -/
theorem YamadaPott.profile_nonedge_fibre1_nonzero
    (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    {a : Additive (YamadaPottSquareSubgroup F)} (ha : a ≠ 0)
    {b : F} (hb : b ≠ 0) (hd : (a, b) ∉ YamadaPottB) :
    (correlation (YamadaPottB (F := F)) YamadaPottB (a, b)).card +
        (correlation (YamadaPottC (F := F)) YamadaPottC (a, b)).card ≤
      YamadaPottN t - 1 := by
  have hneNeg : YamadaPott.skew a * quadraticChar F b ≠ -1 := by
    intro hs
    exact hd (mem_YamadaPottB.mpr ⟨ha, Or.inr hs⟩)
  have hs : YamadaPott.skew a * quadraticChar F b = 1 := by
    by_contra hne
    exact hneNeg (YamadaPott.skew_mul_char_eq_neg_one (F := F) ha hb hne)
  have hvalue := YamadaPott.nonzero_B_value (F := F) hF hcard ha hb hs
  have hn : 1 ≤ YamadaPottN t := by rw [YamadaPottN_eq]; omega
  omega

/-- The `a=0`, `b≠0` exceptional line is a within-fibre-zero nonedge with
codegree exactly `n-1`. -/
theorem YamadaPott.profile_nonedge_fibre0_first_zero
    (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3) {b : F} (hb : b ≠ 0) :
    (correlation (YamadaPottA (F := F)) YamadaPottA (0, b)).card +
        (correlation (YamadaPottC (F := F)) YamadaPottC (0, b)).card ≤
      YamadaPottN t - 1 := by
  have hA := YamadaPott_A_correlation_first_zero (F := F) hF hcard hb
  have hCNat := YamadaPott_C_correlation_first_zero (F := F) hF hcard hb
  have hC := congrArg (fun z : Nat => (z : ℤ)) hCNat
  norm_num at hC
  have hmOdd : Odd (2 * t + 1) := ⟨t, by omega⟩
  have hn := CodegreeArithmetic.bookParameter_int_relation hmOdd
  change 2 * (YamadaPottN t : ℤ) =
    2 * ((2 * t + 1 : Nat) : ℤ) ^ 2 + (2 * t + 1 : Nat) + 1 at hn
  have hvalue := CodegreeArithmetic.sameFiber_zero_nonzero_value hn hA hC
  have hn1 : 1 ≤ YamadaPottN t := by rw [YamadaPottN_eq]; omega
  omega

/-- The `a=0`, `b≠0` exceptional line in fibre one. -/
theorem YamadaPott.profile_nonedge_fibre1_first_zero
    (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3) {b : F} (hb : b ≠ 0) :
    (correlation (YamadaPottB (F := F)) YamadaPottB (0, b)).card +
        (correlation (YamadaPottC (F := F)) YamadaPottC (0, b)).card ≤
      YamadaPottN t - 1 := by
  have hB := YamadaPott_B_correlation_first_zero (F := F) hF hcard hb
  have hCNat := YamadaPott_C_correlation_first_zero (F := F) hF hcard hb
  have hC := congrArg (fun z : Nat => (z : ℤ)) hCNat
  norm_num at hC
  have hmOdd : Odd (2 * t + 1) := ⟨t, by omega⟩
  have hn := CodegreeArithmetic.bookParameter_int_relation hmOdd
  change 2 * (YamadaPottN t : ℤ) =
    2 * ((2 * t + 1 : Nat) : ℤ) ^ 2 + (2 * t + 1 : Nat) + 1 at hn
  have hvalue := CodegreeArithmetic.sameFiber_zero_nonzero_value hn hB hC
  have hn1 : 1 ≤ YamadaPottN t := by rw [YamadaPottN_eq]; omega
  omega

/-- The `a≠0`, `b=0` exceptional line is a red edge in fibre zero. -/
theorem YamadaPott.profile_edge_fibre0_second_zero
    (hF : ringChar F ≠ 2) {t : Nat} (ht : 1 ≤ t)
    (hcard : Fintype.card F = 4 * t + 3)
    {a : Additive (YamadaPottSquareSubgroup F)} (ha : a ≠ 0) :
    (correlation (YamadaPottA (F := F)) YamadaPottA (a, 0)).card +
        (correlation (YamadaPottC (F := F)) YamadaPottC (a, 0)).card ≤
      YamadaPottN t - 2 := by
  have hA := YamadaPott_A_correlation_second_zero (F := F) hF hcard ha
  have hCNat := YamadaPott_C_correlation_zero_at_card (F := F) hF hcard a
  have hC := congrArg (fun z : Nat => (z : ℤ)) hCNat
  norm_num at hC
  have hsource := YamadaPott_H_add_two_I (F := F) hF hcard
    (YamadaPott.squareValue_mem_S a)
    (fun h => ha (YamadaPott.squareValue_eq_one_iff a |>.mp h))
  have hmOdd : Odd (2 * t + 1) := ⟨t, by omega⟩
  have hn := CodegreeArithmetic.bookParameter_int_relation hmOdd
  change 2 * (YamadaPottN t : ℤ) =
    2 * ((2 * t + 1 : Nat) : ℤ) ^ 2 + (2 * t + 1 : Nat) + 1 at hn
  have hvalue := CodegreeArithmetic.sameFiber_nonzero_zero_bound
    (m := (2 * t + 1 : Nat)) (n := YamadaPottN t)
    (H := YamadaPottCorrH F (YamadaPott.squareValue a))
    (I := YamadaPottI F (YamadaPott.squareValue a))
    (RA := (correlation (YamadaPottA (F := F)) YamadaPottA (a, 0)).card)
    (RC := (correlation (YamadaPottC (F := F)) YamadaPottC (a, 0)).card)
    (by omega) hn hsource hA hC
  have hn2 : 2 ≤ YamadaPottN t := by rw [YamadaPottN_eq]; omega
  omega

/-- The `a≠0`, `b=0` exceptional line in fibre one. -/
theorem YamadaPott.profile_edge_fibre1_second_zero
    (hF : ringChar F ≠ 2) {t : Nat} (ht : 1 ≤ t)
    (hcard : Fintype.card F = 4 * t + 3)
    {a : Additive (YamadaPottSquareSubgroup F)} (ha : a ≠ 0) :
    (correlation (YamadaPottB (F := F)) YamadaPottB (a, 0)).card +
        (correlation (YamadaPottC (F := F)) YamadaPottC (a, 0)).card ≤
      YamadaPottN t - 2 := by
  have hB := YamadaPott_B_correlation_second_zero (F := F) hF hcard ha
  have hCNat := YamadaPott_C_correlation_zero_at_card (F := F) hF hcard a
  have hC := congrArg (fun z : Nat => (z : ℤ)) hCNat
  norm_num at hC
  have hsource := YamadaPott_H_add_two_I (F := F) hF hcard
    (YamadaPott.squareValue_mem_S a)
    (fun h => ha (YamadaPott.squareValue_eq_one_iff a |>.mp h))
  have hmOdd : Odd (2 * t + 1) := ⟨t, by omega⟩
  have hn := CodegreeArithmetic.bookParameter_int_relation hmOdd
  change 2 * (YamadaPottN t : ℤ) =
    2 * ((2 * t + 1 : Nat) : ℤ) ^ 2 + (2 * t + 1 : Nat) + 1 at hn
  have hvalue := CodegreeArithmetic.sameFiber_nonzero_zero_bound
    (m := (2 * t + 1 : Nat)) (n := YamadaPottN t)
    (H := YamadaPottCorrH F (YamadaPott.squareValue a))
    (I := YamadaPottI F (YamadaPott.squareValue a))
    (RA := (correlation (YamadaPottB (F := F)) YamadaPottB (a, 0)).card)
    (RC := (correlation (YamadaPottC (F := F)) YamadaPottC (a, 0)).card)
    (by omega) hn hsource hB hC
  have hn2 : 2 ≤ YamadaPottN t := by rw [YamadaPottN_eq]; omega
  omega

/-- The concrete difference data, with odd characteristic and the congruence
hypothesis discharged from the field cardinality. -/
noncomputable def YamadaPott.dataOfCard {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3) :
    DifferenceData (YamadaPottW F) :=
  YamadaPottDifferenceData (YamadaPott.ringChar_ne_two hcard) (by omega)

/-- The cross-fibre edge bound, expressed through the concrete difference
data rather than through graph common neighbors. -/
theorem YamadaPott.profile_edge_cross (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    (hmod : Fintype.card F % 4 = 3)
    (d : YamadaPottW F)
    (hd : d ∈ (YamadaPottDifferenceData hF hmod).C) :
    (convolution (YamadaPottDifferenceData hF hmod).A
          (YamadaPottDifferenceData hF hmod).C d).card +
        (correlation (YamadaPottDifferenceData hF hmod).C
          (YamadaPottDifferenceData hF hmod).B d).card ≤
      YamadaPottN t - 2 := by
  change d ∈ YamadaPottC at hd
  change (convolution YamadaPottA YamadaPottC d).card +
      (correlation YamadaPottC YamadaPottB d).card ≤ YamadaPottN t - 2
  rw [YamadaPott_mixedCorrelation_edge hF hcard d hd, YamadaPottN_eq]
  omega

/-- The cross-fibre nonedge bound, again stated entirely in terms of explicit
finset convolution and correlation. -/
theorem YamadaPott.profile_nonedge_cross (hF : ringChar F ≠ 2) {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    (hmod : Fintype.card F % 4 = 3)
    (d : YamadaPottW F)
    (hd : d ∉ (YamadaPottDifferenceData hF hmod).C) :
    (convolution (YamadaPottDifferenceData hF hmod).A
          (YamadaPottDifferenceData hF hmod).C d).card +
        (correlation (YamadaPottDifferenceData hF hmod).C
          (YamadaPottDifferenceData hF hmod).B d).card ≤
      YamadaPottN t - 1 := by
  change d ∉ YamadaPottC at hd
  change (convolution YamadaPottA YamadaPottC d).card +
      (correlation YamadaPottC YamadaPottB d).card ≤ YamadaPottN t - 1
  have h := YamadaPott_mixedCorrelation_nonedge hF hcard d hd
  rw [YamadaPottN_eq]
  omega

/-- Card-only form of the cross-fibre edge field used by the final profile. -/
theorem YamadaPott.profile_edge_cross_of_card {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    (d : YamadaPottW F) (hd : d ∈ (YamadaPott.dataOfCard hcard).C) :
    (convolution (YamadaPott.dataOfCard hcard).A
          (YamadaPott.dataOfCard hcard).C d).card +
        (correlation (YamadaPott.dataOfCard hcard).C
          (YamadaPott.dataOfCard hcard).B d).card ≤
      YamadaPottN t - 2 := by
  exact YamadaPott.profile_edge_cross (YamadaPott.ringChar_ne_two hcard)
    hcard (by omega) d hd

/-- Card-only form of the cross-fibre nonedge field used by the final profile. -/
theorem YamadaPott.profile_nonedge_cross_of_card {t : Nat}
    (hcard : Fintype.card F = 4 * t + 3)
    (d : YamadaPottW F) (hd : d ∉ (YamadaPott.dataOfCard hcard).C) :
    (convolution (YamadaPott.dataOfCard hcard).A
          (YamadaPott.dataOfCard hcard).C d).card +
        (correlation (YamadaPott.dataOfCard hcard).C
          (YamadaPott.dataOfCard hcard).B d).card ≤
      YamadaPottN t - 1 := by
  exact YamadaPott.profile_nonedge_cross (YamadaPott.ringChar_ne_two hcard)
    hcard (by omega) d hd

/-- The complete concrete correlation profile for every finite field of order
`4t+3` with `t≥1` (equivalently, field order at least seven). -/
theorem YamadaPott.correlationProfile {t : Nat} (ht : 1 ≤ t)
    (hcard : Fintype.card F = 4 * t + 3) :
    CorrelationProfile (YamadaPott.dataOfCard hcard) (YamadaPottN t) := by
  let hF : ringChar F ≠ 2 := YamadaPott.ringChar_ne_two hcard
  refine
    { vertex_count := ?_
      degree_fibre0 := ?_
      degree_fibre1 := ?_
      edge_fibre0 := ?_
      edge_fibre1 := ?_
      edge_cross := YamadaPott.profile_edge_cross_of_card hcard
      nonedge_fibre0 := ?_
      nonedge_fibre1 := ?_
      nonedge_cross := YamadaPott.profile_nonedge_cross_of_card hcard }
  · simpa [YamadaPott.dataOfCard] using
      YamadaPott.profile_vertex_count hF hcard
  · simpa [YamadaPott.dataOfCard] using
      YamadaPott.profile_degree_A hF hcard
  · simpa [YamadaPott.dataOfCard] using
      YamadaPott.profile_degree_B hF hcard
  · rintro ⟨a, b⟩ hd
    change (a, b) ∈ YamadaPottA at hd
    change (correlation YamadaPottA YamadaPottA (a, b)).card +
        (correlation YamadaPottC YamadaPottC (a, b)).card ≤ YamadaPottN t - 2
    by_cases ha : a = 0
    · exact ((mem_YamadaPottA.mp hd).1 ha).elim
    · by_cases hb : b = 0
      · subst b
        exact YamadaPott.profile_edge_fibre0_second_zero hF ht hcard ha
      · exact YamadaPott.profile_edge_fibre0_nonzero hF hcard ha hb hd
  · rintro ⟨a, b⟩ hd
    change (a, b) ∈ YamadaPottB at hd
    change (correlation YamadaPottB YamadaPottB (a, b)).card +
        (correlation YamadaPottC YamadaPottC (a, b)).card ≤ YamadaPottN t - 2
    by_cases ha : a = 0
    · exact ((mem_YamadaPottB.mp hd).1 ha).elim
    · by_cases hb : b = 0
      · subst b
        exact YamadaPott.profile_edge_fibre1_second_zero hF ht hcard ha
      · exact YamadaPott.profile_edge_fibre1_nonzero hF hcard ha hb hd
  · rintro ⟨a, b⟩ hne hd
    change (a, b) ∉ YamadaPottA at hd
    change (correlation YamadaPottA YamadaPottA (a, b)).card +
        (correlation YamadaPottC YamadaPottC (a, b)).card ≤ YamadaPottN t - 1
    by_cases ha : a = 0
    · subst a
      by_cases hb : b = 0
      · subst b
        exact (hne rfl).elim
      · exact YamadaPott.profile_nonedge_fibre0_first_zero hF hcard hb
    · by_cases hb : b = 0
      · subst b
        exact (hd (mem_YamadaPottA.mpr ⟨ha, Or.inl rfl⟩)).elim
      · exact YamadaPott.profile_nonedge_fibre0_nonzero hF hcard ha hb hd
  · rintro ⟨a, b⟩ hne hd
    change (a, b) ∉ YamadaPottB at hd
    change (correlation YamadaPottB YamadaPottB (a, b)).card +
        (correlation YamadaPottC YamadaPottC (a, b)).card ≤ YamadaPottN t - 1
    by_cases ha : a = 0
    · subst a
      by_cases hb : b = 0
      · subst b
        exact (hne rfl).elim
      · exact YamadaPott.profile_nonedge_fibre1_first_zero hF hcard hb
    · by_cases hb : b = 0
      · subst b
        exact (hd (mem_YamadaPottB.mpr ⟨ha, Or.inl rfl⟩)).elim
      · exact YamadaPott.profile_nonedge_fibre1_nonzero hF hcard ha hb hd

/-- The concrete red graph avoids `B_(n-1)`, and its blue complement avoids
`B_n`, for `n=4t²+5t+2`. -/
theorem YamadaPott.bookFree {t : Nat} (ht : 1 ≤ t)
    (hcard : Fintype.card F = 4 * t + 3) :
    BookFree (differenceGraph (YamadaPott.dataOfCard hcard)) (YamadaPottN t - 1) ∧
      BookFree (differenceGraph (YamadaPott.dataOfCard hcard))ᶜ (YamadaPottN t) := by
  apply correlationProfile_bookFree
  · rw [YamadaPottN_eq]
    omega
  · exact YamadaPott.correlationProfile ht hcard

/-- Canonical finite certificate for the third book-Ramsey lower-bound
family.  It is a graph on `4n-2` vertices, with no red `B_(n-1)` and no blue
`B_n`. -/
theorem YamadaPott.lowerBoundCertificate {t : Nat} (ht : 1 ≤ t)
    (hcard : Fintype.card F = 4 * t + 3) :
    ∃ red : SimpleGraph (Fin (4 * YamadaPottN t - 2)),
      LowerBoundCertificate (4 * YamadaPottN t - 2)
        (YamadaPottN t - 1) (YamadaPottN t) red := by
  apply exists_lowerBoundCertificate_of_card
    (differenceGraph (YamadaPott.dataOfCard hcard))
  · simpa [Fintype.card_prod, Fintype.card_bool] using
      (YamadaPott.correlationProfile ht hcard).vertex_count
  · exact YamadaPott.bookFree ht hcard

end BookS3
