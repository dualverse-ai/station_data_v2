import FlatAutoconvolutionS1.GroupedIndependence
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Topology

namespace FlatAutoconvolutionS1.BinaryRefinement

def boolReal (b : Bool) : ℝ := cond b 1 0

def coeff (x : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ a ∈ Finset.range (t + 1), x a * x (t - a)

/-- The same ordered coefficient, written as unordered off-diagonal pairs plus the diagonal. -/
def pairedCoeff (x : ℕ → ℝ) (t : ℕ) : ℝ :=
  2 * ∑ a ∈ Finset.range ((t + 1) / 2), x a * x (t - a) +
    if Even t then x (t / 2) * x (t / 2) else 0

theorem pairedCoeff_eq_coeff (x : ℕ → ℝ) (t : ℕ) : pairedCoeff x t = coeff x t := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' t
  · simp only [pairedCoeff, coeff]
    rw [if_pos (by exact ⟨n, by omega⟩ : Even (2 * n))]
    have hdiv : (2 * n + 1) / 2 = n := by omega
    rw [hdiv]
    have hsplit :
        (∑ a ∈ Finset.range (2 * n + 1), x a * x (2 * n - a)) =
          (∑ a ∈ Finset.range n, x a * x (2 * n - a)) +
          ∑ j ∈ Finset.range (n + 1), x (n + j) * x (2 * n - (n + j)) := by
      simpa [show n + (n + 1) = 2 * n + 1 by omega] using
        (Finset.sum_range_add (fun a ↦ x a * x (2 * n - a)) n (n + 1))
    rw [hsplit]
    have hupper :
        (∑ j ∈ Finset.range (n + 1), x (n + j) * x (2 * n - (n + j))) =
          ∑ j ∈ Finset.range (n + 1),
            x (n + (n + 1 - 1 - j)) * x (2 * n - (n + (n + 1 - 1 - j))) := by
      exact (Finset.sum_range_reflect
        (fun j ↦ x (n + j) * x (2 * n - (n + j))) (n + 1)).symm
    rw [hupper, Finset.sum_range_succ]
    have hreflect :
        (∑ j ∈ Finset.range n,
          x (n + (n + 1 - 1 - j)) * x (2 * n - (n + (n + 1 - 1 - j)))) =
          ∑ j ∈ Finset.range n, x j * x (2 * n - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j < n := Finset.mem_range.mp hj
      have h1 : n + (n + 1 - 1 - j) = 2 * n - j := by omega
      have h2 : 2 * n - (2 * n - j) = j := by omega
      rw [h1, h2, mul_comm]
    rw [hreflect]
    have hhalf : 2 * n / 2 = n := by omega
    have hlast1 : n + (n + 1 - 1 - n) = n := by omega
    have hsub : 2 * n - n = n := by omega
    rw [hhalf, hlast1, hsub]
    ring
  · simp only [pairedCoeff, coeff]
    rw [if_neg (by
      rw [Nat.not_even_iff_odd]
      exact ⟨n, by omega⟩ : ¬ Even (2 * n + 1))]
    have hdiv : (2 * n + 1 + 1) / 2 = n + 1 := by omega
    rw [hdiv, add_zero]
    have hsplit :
        (∑ a ∈ Finset.range (2 * n + 1 + 1), x a * x (2 * n + 1 - a)) =
          (∑ a ∈ Finset.range (n + 1), x a * x (2 * n + 1 - a)) +
          ∑ j ∈ Finset.range (n + 1),
            x (n + 1 + j) * x (2 * n + 1 - (n + 1 + j)) := by
      simpa [show (n + 1) + (n + 1) = 2 * n + 1 + 1 by omega] using
        (Finset.sum_range_add (fun a ↦ x a * x (2 * n + 1 - a))
          (n + 1) (n + 1))
    rw [hsplit]
    have hupper :
        (∑ j ∈ Finset.range (n + 1),
          x (n + 1 + j) * x (2 * n + 1 - (n + 1 + j))) =
          ∑ j ∈ Finset.range (n + 1),
            x (n + 1 + (n + 1 - 1 - j)) *
              x (2 * n + 1 - (n + 1 + (n + 1 - 1 - j))) := by
      exact (Finset.sum_range_reflect
        (fun j ↦ x (n + 1 + j) * x (2 * n + 1 - (n + 1 + j))) (n + 1)).symm
    rw [hupper]
    have hreflect :
        (∑ j ∈ Finset.range (n + 1),
          x (n + 1 + (n + 1 - 1 - j)) *
            x (2 * n + 1 - (n + 1 + (n + 1 - 1 - j)))) =
          ∑ j ∈ Finset.range (n + 1), x j * x (2 * n + 1 - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j < n + 1 := Finset.mem_range.mp hj
      have h1 : n + 1 + (n + 1 - 1 - j) = 2 * n + 1 - j := by omega
      have h2 : 2 * n + 1 - (2 * n + 1 - j) = j := by omega
      rw [h1, h2, mul_comm]
    rw [hreflect]
    ring

def offCount (t : ℕ) : ℕ := (t + 1) / 2

def pairLeft (t j : ℕ) : ℕ :=
  if j < offCount t then j else t + 1 + 2 * (j - offCount t)

def pairRight (t j : ℕ) : ℕ :=
  if j < offCount t then t - j else t + 2 + 2 * (j - offCount t)

theorem pairBlocks_pairwise (t : ℕ) :
    Pairwise (fun j k ↦
      Disjoint
        (GroupedIndependence.block (pairLeft t) (pairRight t) j)
        (GroupedIndependence.block (pairLeft t) (pairRight t) k)) := by
  intro j k hjk
  simp only [GroupedIndependence.block, Finset.disjoint_left,
    Finset.mem_insert, Finset.mem_singleton]
  intro x hxj hxk
  rcases hxj with rfl | rfl <;> rcases hxk with h | h <;>
    simp only [pairLeft, pairRight, offCount] at h ⊢ <;>
    split_ifs at h ⊢ <;> simp only [offCount] at * <;> omega

noncomputable def coinMeasure (q : ℕ → NNReal) (hq : ∀ i, q i ≤ 1) (i : ℕ) : Measure Bool :=
  (PMF.bernoulli (q i) (hq i)).toMeasure

noncomputable def coinProduct (q : ℕ → NNReal) (hq : ∀ i, q i ≤ 1) :
    Measure (ℕ → Bool) :=
  Measure.infinitePi (coinMeasure q hq)

def coin (i : ℕ) (ω : ℕ → Bool) : ℝ := boolReal (ω i)

/-- A Bernoulli selector forced to zero whenever its prescribed weight is zero. -/
noncomputable def qCoin (q : ℕ → NNReal) (i : ℕ) (ω : ℕ → Bool) : ℝ :=
  if q i = 0 then 0 else coin i ω

theorem coin_measurable (i : ℕ) : Measurable (coin i) := by
  unfold coin
  fun_prop

theorem coins_independent (q : ℕ → NNReal) (hq : ∀ i, q i ≤ 1) :
    iIndepFun coin (coinProduct q hq) := by
  letI : ∀ i, IsProbabilityMeasure (coinMeasure q hq i) := fun i ↦ by
    dsimp [coinMeasure]
    infer_instance
  exact iIndepFun_infinitePi (P := coinMeasure q hq)
    (X := fun _ b ↦ boolReal b) (fun _ ↦ by fun_prop)

theorem qCoin_measurable (q : ℕ → NNReal) (i : ℕ) : Measurable (qCoin q i) := by
  unfold qCoin
  split_ifs
  · fun_prop
  · exact coin_measurable i

theorem qCoins_independent (q : ℕ → NNReal) (hq : ∀ i, q i ≤ 1) :
    iIndepFun (qCoin q) (coinProduct q hq) := by
  have h := (coins_independent q hq).comp
    (fun i x ↦ if q i = 0 then 0 else x)
    (fun i ↦ by
      by_cases hi : q i = 0
      · simp only [hi, if_pos]
        fun_prop
      · simp only [hi, if_neg]
        exact measurable_id)
  simpa [qCoin, Function.comp_def] using h

theorem integral_coin (q : ℕ → NNReal) (hq : ∀ i, q i ≤ 1) (i : ℕ) :
    ∫ ω, coin i ω ∂coinProduct q hq = (q i).toReal := by
  letI : ∀ i, IsProbabilityMeasure (coinMeasure q hq i) := fun i ↦ by
    dsimp [coinMeasure]
    infer_instance
  change (∫ ω, boolReal (ω i) ∂Measure.infinitePi (coinMeasure q hq)) = (q i).toReal
  calc
    _ = ∫ b, boolReal b ∂(Measure.infinitePi (coinMeasure q hq)).map (fun ω ↦ ω i) := by
      symm
      apply integral_map
      · exact (measurePreserving_eval_infinitePi (coinMeasure q hq) i).measurable.aemeasurable
      · rw [Measure.infinitePi_map_eval]
        exact (measurable_of_finite (f := fun b : Bool ↦ boolReal b)).aestronglyMeasurable
    _ = ∫ b, boolReal b ∂coinMeasure q hq i := by rw [Measure.infinitePi_map_eval]
    _ = (q i).toReal := by
      simpa [boolReal, coinMeasure] using PMF.bernoulli_expectation (hq i)

theorem integral_qCoin (q : ℕ → NNReal) (hq : ∀ i, q i ≤ 1) (i : ℕ) :
    ∫ ω, qCoin q i ω ∂coinProduct q hq = (q i).toReal := by
  by_cases hi : q i = 0
  · simp [qCoin, hi]
  · simp [qCoin, hi, integral_coin q hq i]

theorem pair_expectation (q : ℕ → NNReal) (hq : ∀ i, q i ≤ 1)
    {i j : ℕ} (hij : i ≠ j) :
    ∫ ω, 2 * (coin i ω * coin j ω) ∂coinProduct q hq =
      2 * (q i).toReal * (q j).toReal := by
  let μ := coinProduct q hq
  have hi := coin_measurable i
  have hj := coin_measurable j
  have hind := (coins_independent q hq).indepFun hij
  rw [integral_const_mul]
  change 2 * (∫ a, (coin i * coin j) a ∂coinProduct q hq) = _
  rw [hind.integral_mul_eq_mul_integral hi.aestronglyMeasurable hj.aestronglyMeasurable]
  simp only [integral_coin]
  ring

theorem qPair_expectation (q : ℕ → NNReal) (hq : ∀ i, q i ≤ 1)
    {i j : ℕ} (hij : i ≠ j) :
    ∫ ω, 2 * (qCoin q i ω * qCoin q j ω) ∂coinProduct q hq =
      2 * (q i).toReal * (q j).toReal := by
  have hi := qCoin_measurable q i
  have hj := qCoin_measurable q j
  have hind := (qCoins_independent q hq).indepFun hij
  rw [integral_const_mul]
  change 2 * (∫ a, (qCoin q i * qCoin q j) a ∂coinProduct q hq) = _
  rw [hind.integral_mul_eq_mul_integral hi.aestronglyMeasurable hj.aestronglyMeasurable]
  simp only [integral_qCoin]
  ring

def rawPair (_j : ℕ) (z : ℝ × ℝ) : ℝ := 2 * (z.1 * z.2)

def centeredPair (q : ℕ → NNReal) (t j : ℕ) (z : ℝ × ℝ) : ℝ :=
  rawPair j z - 2 * (q (pairLeft t j)).toReal * (q (pairRight t j)).toReal

noncomputable def offSum (q : ℕ → NNReal) (t : ℕ) (ω : ℕ → Bool) : ℝ :=
  ∑ j ∈ Finset.range (offCount t),
    GroupedIndependence.pairVar (qCoin q) (pairLeft t) (pairRight t)
      (centeredPair q t) j ω

theorem offSum_eq (q : ℕ → NNReal) (t : ℕ) (ω : ℕ → Bool) :
    offSum q t ω =
      2 * ∑ j ∈ Finset.range (offCount t), qCoin q j ω * qCoin q (t - j) ω -
      2 * ∑ j ∈ Finset.range (offCount t), (q j).toReal * (q (t - j)).toReal := by
  unfold offSum
  simp_rw [GroupedIndependence.pairVar, centeredPair, rawPair]
  have hp (j : ℕ) (hj : j ∈ Finset.range (offCount t)) :
      pairLeft t j = j ∧ pairRight t j = t - j := by
    have hlt := Finset.mem_range.mp hj
    simp [pairLeft, pairRight, hlt]
  simp_rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(hp j hj).1, (hp j hj).2]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [(hp j hj).1, (hp j hj).2]
    ring

theorem pairedCoeff_sub_eq (q : ℕ → NNReal) (t : ℕ) (ω : ℕ → Bool) :
    pairedCoeff (fun i ↦ qCoin q i ω) t - pairedCoeff (fun i ↦ (q i).toReal) t =
      offSum q t ω +
        if Even t then
          qCoin q (t / 2) ω * qCoin q (t / 2) ω -
            (q (t / 2)).toReal * (q (t / 2)).toReal
        else 0 := by
  rw [offSum_eq]
  simp only [pairedCoeff, offCount]
  split_ifs <;> ring

theorem diagonal_abs_le_one (q : ℕ → NNReal) (hq : ∀ i, q i ≤ 1)
    (i : ℕ) (ω : ℕ → Bool) :
    |qCoin q i ω * qCoin q i ω - (q i).toReal * (q i).toReal| ≤ 1 := by
  have hq0 : 0 ≤ (q i).toReal := NNReal.zero_le_coe
  have hq1 : (q i).toReal ≤ 1 := by exact_mod_cast hq i
  have hc : qCoin q i ω = 0 ∨ qCoin q i ω = 1 := by
    by_cases hqz : q i = 0
    · simp [qCoin, hqz]
    · cases h : ω i <;> simp [qCoin, hqz, coin, boolReal, h]
  have hsq0 : 0 ≤ (q i).toReal * (q i).toReal := mul_nonneg hq0 hq0
  have hsq1 : (q i).toReal * (q i).toReal ≤ 1 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)]
  rcases hc with hc | hc
  · rw [hc]
    norm_num only [zero_mul, zero_sub, abs_neg]
    rw [abs_of_nonneg hsq0]
    exact hsq1
  · rw [hc]
    norm_num only [one_mul]
    rw [abs_of_nonneg (sub_nonneg.mpr hsq1)]
    linarith

theorem centeredPair_subgaussian (q : ℕ → NNReal) (hq : ∀ i, q i ≤ 1)
    (t j : ℕ) :
    HasSubgaussianMGF
      (GroupedIndependence.pairVar (qCoin q) (pairLeft t) (pairRight t)
        (centeredPair q t) j)
      1 (coinProduct q hq) := by
  letI : IsProbabilityMeasure (coinProduct q hq) :=
    (qCoins_independent q hq).isProbabilityMeasure
  have hne : pairLeft t j ≠ pairRight t j := by
    simp only [pairLeft, pairRight]
    split_ifs <;> simp only [offCount] at * <;> omega
  have hm : AEMeasurable
      (GroupedIndependence.pairVar (qCoin q) (pairLeft t) (pairRight t) rawPair j)
      (coinProduct q hq) := by
    apply Measurable.aemeasurable
    unfold GroupedIndependence.pairVar rawPair
    exact measurable_const.mul ((qCoin_measurable q _).mul (qCoin_measurable q _))
  have hb : ∀ᵐ ω ∂coinProduct q hq,
      GroupedIndependence.pairVar (qCoin q) (pairLeft t) (pairRight t) rawPair j ω ∈
        Set.Icc (0 : ℝ) 2 := by
    filter_upwards [] with ω
    cases hl : ω (pairLeft t j) <;> cases hr : ω (pairRight t j) <;>
      simp only [GroupedIndependence.pairVar, rawPair, qCoin, coin, boolReal, hl, hr,
        cond_false, cond_true]
    all_goals split_ifs <;> norm_num
  have hraw := hasSubgaussianMGF_of_mem_Icc hm hb
  have hmean := qPair_expectation q hq hne
  have heq :
      (fun ω ↦
        GroupedIndependence.pairVar (qCoin q) (pairLeft t) (pairRight t) rawPair j ω -
          ∫ x, GroupedIndependence.pairVar (qCoin q) (pairLeft t) (pairRight t) rawPair j x
            ∂coinProduct q hq) =
      GroupedIndependence.pairVar (qCoin q) (pairLeft t) (pairRight t)
        (centeredPair q t) j := by
    funext ω
    rw [show (∫ x, GroupedIndependence.pairVar (qCoin q) (pairLeft t) (pairRight t)
      rawPair j x ∂coinProduct q hq) =
        2 * (q (pairLeft t j)).toReal * (q (pairRight t j)).toReal by
          simpa [GroupedIndependence.pairVar, rawPair] using hmean]
    rfl
  rw [← heq]
  simpa using hraw

theorem offdiag_subgaussian (q : ℕ → NNReal) (hq : ∀ i, q i ≤ 1) (t : ℕ) :
    HasSubgaussianMGF
      (fun ω ↦ ∑ j ∈ Finset.range (offCount t),
        GroupedIndependence.pairVar (qCoin q) (pairLeft t) (pairRight t)
          (centeredPair q t) j ω)
      (offCount t : NNReal) (coinProduct q hq) := by
  have h := GroupedIndependence.hasSubgaussianMGF_sum_pairVar_range
    (qCoins_independent q hq) (qCoin_measurable q) (pairLeft t) (pairRight t)
    (pairBlocks_pairwise t) (centeredPair q t) (fun _ ↦ by
      unfold centeredPair rawPair
      fun_prop)
    (fun _ ↦ (1 : NNReal)) (centeredPair_subgaussian q hq t) (offCount t)
  simpa using h

theorem offCount_le {N t : ℕ} (ht : t < 2 * N - 1) : offCount t ≤ N := by
  simp only [offCount]
  omega

theorem offdiag_subgaussian_bound (q : ℕ → NNReal) (hq : ∀ i, q i ≤ 1)
    {N t : ℕ} (ht : t < 2 * N - 1) :
    HasSubgaussianMGF
      (fun ω ↦ ∑ j ∈ Finset.range (offCount t),
        GroupedIndependence.pairVar (qCoin q) (pairLeft t) (pairRight t)
          (centeredPair q t) j ω)
      (N : NNReal) (coinProduct q hq) := by
  have h := offdiag_subgaussian q hq t
  refine ⟨h.integrable_exp_mul, fun u ↦ (h.mgf_le u).trans ?_⟩
  apply Real.exp_le_exp.mpr
  gcongr
  exact_mod_cast offCount_le ht

theorem offdiag_tail (q : ℕ → NNReal) (hq : ∀ i, q i ≤ 1)
    {N t : ℕ} (ht : t < 2 * N - 1) {s : ℝ} (hs : 0 ≤ s) :
    (coinProduct q hq).real
      {ω | s ≤ |∑ j ∈ Finset.range (offCount t),
        GroupedIndependence.pairVar (qCoin q) (pairLeft t) (pairRight t)
          (centeredPair q t) j ω|} ≤
      2 * Real.exp (-s ^ 2 / (2 * (N : ℝ))) := by
  let Z : (ℕ → Bool) → ℝ := fun ω ↦ ∑ j ∈ Finset.range (offCount t),
    GroupedIndependence.pairVar (qCoin q) (pairLeft t) (pairRight t)
      (centeredPair q t) j ω
  have hZ : HasSubgaussianMGF Z (N : NNReal) (coinProduct q hq) :=
    offdiag_subgaussian_bound q hq ht
  have hset : {ω | s ≤ |Z ω|} = {ω | s ≤ Z ω} ∪ {ω | s ≤ -Z ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union]
    rw [le_abs]
  rw [show {ω | s ≤ |∑ j ∈ Finset.range (offCount t),
      GroupedIndependence.pairVar (qCoin q) (pairLeft t) (pairRight t)
        (centeredPair q t) j ω|} = {ω | s ≤ |Z ω|} by rfl, hset]
  calc
    (coinProduct q hq).real ({ω | s ≤ Z ω} ∪ {ω | s ≤ -Z ω})
        ≤ (coinProduct q hq).real {ω | s ≤ Z ω} +
          (coinProduct q hq).real {ω | s ≤ -Z ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-s ^ 2 / (2 * (N : ℝ))) +
          Real.exp (-s ^ 2 / (2 * (N : ℝ))) :=
      add_le_add (hZ.measure_ge_le hs) (hZ.neg.measure_ge_le hs)
    _ = 2 * Real.exp (-s ^ 2 / (2 * (N : ℝ))) := by ring

theorem exists_sample_of_exponential_bound
    (q : ℕ → NNReal) (hq : ∀ i, q i ≤ 1)
    (N : ℕ) (hN : 0 < N) (s : ℝ) (hs : 0 < s)
    (hprob : ((2 * N - 1 : ℕ) : ℝ) *
        (2 * Real.exp (-s ^ 2 / (2 * (N : ℝ)))) < 1) :
    ∃ ω : ℕ → Bool, ∀ t : Fin (2 * N - 1),
      |pairedCoeff (fun i ↦ qCoin q i ω) t.val -
        pairedCoeff (fun i ↦ (q i).toReal) t.val| < s + 1 := by
  let μ := coinProduct q hq
  let bad : Fin (2 * N - 1) → Set (ℕ → Bool) := fun t ↦
    {ω | s ≤ |offSum q t.val ω|}
  letI : IsProbabilityMeasure μ := (qCoins_independent q hq).isProbabilityMeasure
  have heach (t : Fin (2 * N - 1)) :
      μ.real (bad t) ≤ 2 * Real.exp (-s ^ 2 / (2 * (N : ℝ))) := by
    exact offdiag_tail q hq t.isLt hs.le
  have hunion :
      μ.real (⋃ t, bad t) ≤ ∑ t, μ.real (bad t) :=
    measureReal_iUnion_fintype_le bad
  have hsum :
      (∑ t, μ.real (bad t)) ≤
        ∑ _t : Fin (2 * N - 1), 2 * Real.exp (-s ^ 2 / (2 * (N : ℝ))) := by
    exact Finset.sum_le_sum fun t _ ↦ heach t
  have hlt : μ.real (⋃ t, bad t) < 1 := by
    refine lt_of_le_of_lt (hunion.trans hsum) ?_
    simpa using hprob
  have hne : (⋃ t, bad t) ≠ Set.univ := by
    intro h
    rw [h] at hlt
    simpa using hlt
  obtain ⟨ω, hω⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  refine ⟨ω, fun t ↦ ?_⟩
  have hoff : |offSum q t.val ω| < s := by
    apply lt_of_not_ge
    intro hb
    apply hω
    exact Set.mem_iUnion.2 ⟨t, hb⟩
  rw [pairedCoeff_sub_eq]
  by_cases ht : Even t.val
  · rw [if_pos ht]
    calc
      |offSum q t.val ω +
          (qCoin q (t.val / 2) ω * qCoin q (t.val / 2) ω -
            (q (t.val / 2)).toReal * (q (t.val / 2)).toReal)|
          ≤ |offSum q t.val ω| +
            |qCoin q (t.val / 2) ω * qCoin q (t.val / 2) ω -
              (q (t.val / 2)).toReal * (q (t.val / 2)).toReal| := abs_add_le _ _
      _ < s + 1 := add_lt_add_of_lt_of_le hoff (diagonal_abs_le_one q hq _ _)
  · rw [if_neg ht, add_zero]
    exact hoff.trans (lt_add_of_pos_right _ zero_lt_one)

theorem exists_good_scale (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) (T₀ : ℕ) :
    ∃ T : ℕ, T₀ ≤ T ∧ 0 < T ∧
      ((2 * (m * T) - 1 : ℕ) : ℝ) *
          (2 * Real.exp (-(δ * (T : ℝ) / 2) ^ 2 / (2 * (m * T : ℕ)))) < 1 ∧
      (δ * (T : ℝ) / 2 + 1) / (T : ℝ) < δ := by
  let b : ℝ := δ ^ 2 / (8 * (m : ℝ))
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hlim : Tendsto
      (fun T : ℕ ↦ (4 * (m : ℝ)) *
        ((T : ℝ) * Real.exp (-b * (T : ℝ)))) atTop (𝓝 0) := by
    have hbase := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 b hb).comp
      tendsto_natCast_atTop_atTop
    have hbase' : Tendsto
        (fun T : ℕ ↦ (T : ℝ) * Real.exp (-b * (T : ℝ))) atTop (𝓝 0) := by
      simpa [Real.rpow_one] using hbase
    simpa using (tendsto_const_nhds.mul hbase')
  have hevProb : ∀ᶠ T : ℕ in atTop,
      (4 * (m : ℝ)) * ((T : ℝ) * Real.exp (-b * (T : ℝ))) < 1 :=
    (tendsto_order.1 hlim).2 1 zero_lt_one
  have hinv : Tendsto (fun T : ℕ ↦ (1 : ℝ) / (T : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hevInv : ∀ᶠ T : ℕ in atTop, (1 : ℝ) / (T : ℝ) < δ / 2 :=
    (tendsto_order.1 hinv).2 (δ / 2) (half_pos hδ)
  have hev : ∀ᶠ T : ℕ in atTop,
      (4 * (m : ℝ)) * ((T : ℝ) * Real.exp (-b * (T : ℝ))) < 1 ∧
      (1 : ℝ) / (T : ℝ) < δ / 2 ∧ T₀ ≤ T ∧ 0 < T := by
    filter_upwards [hevProb, hevInv, eventually_ge_atTop T₀, eventually_gt_atTop 0]
      with T hprob hinv hT₀ hT
    exact ⟨hprob, hinv, hT₀, hT⟩
  obtain ⟨T, hprob, hinv, hT₀, hT⟩ := hev.exists
  refine ⟨T, hT₀, hT, ?_, ?_⟩
  · have hTc : (0 : ℝ) < T := by exact_mod_cast hT
    have hmc : (0 : ℝ) < m := by exact_mod_cast hm
    have hexp :
        -(δ * (T : ℝ) / 2) ^ 2 / (2 * (m * T : ℕ)) = -b * (T : ℝ) := by
      push_cast
      dsimp [b]
      field_simp
      ring
    rw [hexp]
    calc
      ((2 * (m * T) - 1 : ℕ) : ℝ) * (2 * Real.exp (-b * (T : ℝ)))
          ≤ (4 * (m : ℝ)) * ((T : ℝ) * Real.exp (-b * (T : ℝ))) := by
            have hcard : ((2 * (m * T) - 1 : ℕ) : ℝ) ≤
                (2 : ℝ) * (m : ℝ) * (T : ℝ) := by
              calc
                ((2 * (m * T) - 1 : ℕ) : ℝ) ≤ ((2 * (m * T) : ℕ) : ℝ) := by
                  exact_mod_cast (Nat.sub_le (2 * (m * T)) 1)
                _ = (2 : ℝ) * (m : ℝ) * (T : ℝ) := by push_cast; ring
            calc
              ((2 * (m * T) - 1 : ℕ) : ℝ) * (2 * Real.exp (-b * (T : ℝ)))
                  ≤ ((2 : ℝ) * (m : ℝ) * (T : ℝ)) *
                      (2 * Real.exp (-b * (T : ℝ))) :=
                    mul_le_mul_of_nonneg_right hcard (by positivity)
              _ = (4 * (m : ℝ)) * ((T : ℝ) * Real.exp (-b * (T : ℝ))) := by
                    ring
      _ < 1 := hprob
  · have hTc : (0 : ℝ) < T := by exact_mod_cast hT
    calc
      (δ * (T : ℝ) / 2 + 1) / (T : ℝ) = δ / 2 + 1 / (T : ℝ) := by
        field_simp
      _ < δ / 2 + δ / 2 := by linarith
      _ = δ := by ring

/-- Repeat a finite nonnegative weight vector on blocks of `T` microcells and extend by zero. -/
noncomputable def blockProb (m T : ℕ) (v : Fin m → NNReal) (i : ℕ) : NNReal :=
  if h : i / T < m then v ⟨i / T, h⟩ else 0

theorem blockProb_le_one (m T : ℕ) (v : Fin m → NNReal) (hv : ∀ i, v i ≤ 1) :
    ∀ i, blockProb m T v i ≤ 1 := by
  intro i
  simp only [blockProb]
  split_ifs with h
  · exact hv ⟨i / T, h⟩
  · exact zero_le_one

noncomputable def selector (q : ℕ → NNReal) (ω : ℕ → Bool) (i : ℕ) : Bool :=
  if q i = 0 then false else ω i

@[simp] theorem boolReal_selector (q : ℕ → NNReal) (ω : ℕ → Bool) (i : ℕ) :
    boolReal (selector q ω i) = qCoin q i ω := by
  simp only [selector, qCoin]
  split_ifs <;> rfl

/--
Weighted blocks admit finitely supported Boolean refinements whose complete family of
anti-diagonal convolution coefficients converges uniformly, at arbitrarily fine resolution.
-/
theorem binaryRefinementProperty
    (m : ℕ) (hm : 0 < m) (v : Fin m → NNReal) (hv : ∀ i, v i ≤ 1)
    (δ : ℝ) (hδ : 0 < δ) (T₀ : ℕ) :
    ∃ T : ℕ, T₀ ≤ T ∧ 0 < T ∧ ∃ ξ : ℕ → Bool,
      (∀ i, m * T ≤ i → ξ i = false) ∧
      ∀ t : Fin (2 * (m * T) - 1),
        |coeff (fun i ↦ boolReal (ξ i)) t.val / (T : ℝ) -
          coeff (fun i ↦ (blockProb m T v i).toReal) t.val / (T : ℝ)| < δ := by
  obtain ⟨T, hT₀, hT, hprob, herr⟩ := exists_good_scale m hm δ hδ T₀
  let q := blockProb m T v
  have hq : ∀ i, q i ≤ 1 := blockProb_le_one m T v hv
  have hN : 0 < m * T := Nat.mul_pos hm hT
  obtain ⟨ω, hω⟩ := exists_sample_of_exponential_bound q hq (m * T) hN
    (δ * (T : ℝ) / 2) (by positivity) hprob
  let ξ := selector q ω
  refine ⟨T, hT₀, hT, ξ, ?_, fun t ↦ ?_⟩
  · intro i hi
    have hdiv : ¬ i / T < m := by
      intro hlt
      have : i < m * T := (Nat.div_lt_iff_lt_mul hT).mp hlt
      omega
    simp [ξ, selector, q, blockProb, hdiv]
  · have hsamp := hω t
    rw [← pairedCoeff_eq_coeff, ← pairedCoeff_eq_coeff]
    rw [show (fun i ↦ boolReal (ξ i)) = (fun i ↦ qCoin q i ω) by
      funext i
      exact boolReal_selector q ω i]
    rw [← sub_div, abs_div, abs_of_pos (by exact_mod_cast hT : (0 : ℝ) < T)]
    calc
      |pairedCoeff (fun i ↦ qCoin q i ω) t.val -
          pairedCoeff (fun i ↦ (q i).toReal) t.val| / (T : ℝ)
          < (δ * (T : ℝ) / 2 + 1) / (T : ℝ) :=
            div_lt_div_of_pos_right hsamp (by exact_mod_cast hT)
      _ < δ := herr

end FlatAutoconvolutionS1.BinaryRefinement
