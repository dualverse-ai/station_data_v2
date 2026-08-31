import HardyLittlewoodS1.Definitions
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Tactic

open scoped ENNReal NNReal BigOperators
open Set MeasureTheory Filter

namespace HardyLittlewoodS1

/-- Elementary projection geometry for one non-tangential averaging interval.

If an interval of mass `K` must contain `[a,b]`, its possible observation points fill the
displayed open reach interval.  The strict hypotheses let us choose a radius strictly below `K`.
-/
theorem exists_witness_of_mem_blockReach {alpha K a b x : ℝ}
    (halpha : 0 < alpha) (hK : 0 < K) (hab : a ≤ b) (hspan : b - a < 2 * K)
    (hx : x ∈ Ioo (b - (1 + alpha) * K) (a + (1 + alpha) * K)) :
    ∃ y t : ℝ, 0 < t ∧ t < K ∧ y - t < a ∧ b < y + t ∧ |x - y| ≤ alpha * t := by
  have hkappa : 0 < 1 + alpha := by linarith
  have hba : (b - a) / 2 < K := (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).2 (by linarith)
  have hbx : (b - x) / (1 + alpha) < K := by
    apply (div_lt_iff₀ hkappa).2
    linarith [hx.1]
  have hxa : (x - a) / (1 + alpha) < K := by
    apply (div_lt_iff₀ hkappa).2
    linarith [hx.2]
  let m := max ((b - a) / 2) (max ((b - x) / (1 + alpha)) ((x - a) / (1 + alpha)))
  have hmK : m < K := by
    simp only [m, max_lt_iff]
    exact ⟨hba, hbx, hxa⟩
  let t := (m + K) / 2
  have hmt : m < t := by dsimp [t]; linarith
  have htK : t < K := by dsimp [t]; linarith
  have htpos : 0 < t := by
    have hm_nonneg : 0 ≤ m := by
      dsimp [m]
      exact le_trans (by linarith : 0 ≤ (b - a) / 2) (le_max_left _ _)
    dsimp [t]
    linarith
  have hspan_t : b - a < 2 * t := by
    have : (b - a) / 2 < t := lt_of_le_of_lt (le_max_left _ _) hmt
    linarith
  have hbx_t : b - x < (1 + alpha) * t := by
    have : (b - x) / (1 + alpha) < t :=
      lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right _ _)) hmt
    simpa [mul_comm] using (div_lt_iff₀ hkappa).1 this
  have hxa_t : x - a < (1 + alpha) * t := by
    have : (x - a) / (1 + alpha) < t :=
      lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right _ _)) hmt
    simpa [mul_comm] using (div_lt_iff₀ hkappa).1 this
  let lo := max (b - t) (x - alpha * t)
  let hi := min (a + t) (x + alpha * t)
  have hlohi : lo < hi := by
    apply (max_lt_iff).2
    constructor
    · apply (lt_min_iff).2
      constructor <;> dsimp [lo, hi] <;> linarith
    · apply (lt_min_iff).2
      constructor <;> dsimp [lo, hi]
      · linarith
      · nlinarith
  let y := (lo + hi) / 2
  have hloy : lo < y := by dsimp [y]; linarith
  have hyhi : y < hi := by dsimp [y]; linarith
  refine ⟨y, t, htpos, htK, ?_, ?_, ?_⟩
  · have : y < a + t := hyhi.trans_le (min_le_left _ _)
    linarith
  · have : b - t < y := (le_max_left _ _).trans_lt hloy
    linarith
  · rw [abs_le]
    constructor
    · have : y < x + alpha * t := hyhi.trans_le (min_le_right _ _)
      nlinarith
    · have : x - alpha * t < y := (le_max_right _ _).trans_lt hloy
      nlinarith

/-- Half-width of the uniform bumps in the `n`-point lower-bound witness. -/
noncomputable def chainEpsilon (n : ℕ) : ℝ :=
  1 / (3 * (n : ℝ) * (2 * (n : ℝ) - 1))

/-- Gap between consecutive bump centres. -/
noncomputable def chainGap (n : ℕ) : ℝ :=
  4 / (n : ℝ) - 4 * chainEpsilon n

/-- Centre of bump `i` in the equal chain. -/
noncomputable def chainPoint (n : ℕ) (i : Fin n) : ℝ :=
  (i : ℕ) * chainGap n

/-- Height of each uniform bump.  Its area is `1/n`. -/
noncomputable def chainHeight (n : ℕ) : ℝ≥0 :=
  Real.toNNReal (1 / (2 * (n : ℝ) * chainEpsilon n))

/-- Support of the `i`th uniform bump. -/
noncomputable def chainSupport (n : ℕ) (i : Fin n) : Set ℝ :=
  Icc (chainPoint n i - chainEpsilon n) (chainPoint n i + chainEpsilon n)

/-- One summand of the equal-chain witness. -/
noncomputable def chainComponent (n : ℕ) (i : Fin n) (x : ℝ) : ℝ≥0 :=
  (chainSupport n i).indicator (fun _ ↦ chainHeight n) x

/-- The explicit absolutely continuous equal-chain witness. -/
noncomputable def equalChainBump (n : ℕ) (x : ℝ) : ℝ≥0 :=
  ∑ i : Fin n, chainComponent n i x

theorem chainEpsilon_pos {n : ℕ} (hn : 2 ≤ n) : 0 < chainEpsilon n := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
  rw [chainEpsilon]
  have hnreal' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have : (0 : ℝ) < 2 * n - 1 := by linarith
  positivity

theorem chainEpsilon_lt_inv {n : ℕ} (hn : 2 ≤ n) : chainEpsilon n < 1 / (n : ℝ) := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have htwo : (0 : ℝ) < 2 * n - 1 := by linarith
  rw [chainEpsilon]
  rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 3 * n * (2 * n - 1)) hnpos]
  nlinarith

theorem chainGap_pos {n : ℕ} (hn : 2 ≤ n) : 0 < chainGap n := by
  have he := chainEpsilon_lt_inv hn
  rw [chainGap]
  norm_num [div_eq_mul_inv] at he ⊢
  linarith

theorem four_thirds_inv_lt_chainGap {n : ℕ} (hn : 2 ≤ n) :
    4 / (3 * (n : ℝ)) < chainGap n := by
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have htwo : (0 : ℝ) < 2 * n - 1 := by linarith
  have hdenone : (1 : ℝ) < 2 * n - 1 := by linarith
  have hinv : 1 / (2 * (n : ℝ) - 1) < 1 := (div_lt_one htwo).2 hdenone
  have hinv' : 1 / ((n : ℝ) * 2 - 1) < 1 := by simpa [mul_comm] using hinv
  rw [chainGap, chainEpsilon]
  field_simp
  linarith

theorem chainGap_add_two_epsilon_lt {n : ℕ} (hn : 2 ≤ n) :
    chainGap n + 2 * chainEpsilon n < 4 / (n : ℝ) := by
  rw [chainGap]
  linarith [chainEpsilon_pos hn]

theorem equalChainBump_measurable (n : ℕ) : Measurable (equalChainBump n) := by
  unfold equalChainBump chainComponent chainSupport
  exact Finset.measurable_fun_sum _ fun i _ ↦ measurable_const.indicator measurableSet_Icc

theorem chainComponent_totalMass {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    (∫⁻ x, (chainComponent n i x : ℝ≥0∞)) = ENNReal.ofReal (1 / (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hn))
  have heps : 0 < chainEpsilon n := chainEpsilon_pos hn
  have hdensity : 0 ≤ 1 / (2 * (n : ℝ) * chainEpsilon n) := by positivity
  simp only [chainComponent, chainSupport]
  push_cast
  rw [lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc,
    chainHeight, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hdensity,
    ← ENNReal.ofReal_mul hdensity]
  congr 1
  field_simp
  ring

theorem equalChainBump_totalMass {n : ℕ} (hn : 2 ≤ n) : totalMass (equalChainBump n) = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hn))
  have heps : 0 < chainEpsilon n := chainEpsilon_pos hn
  have hdensity : 0 ≤ 1 / (2 * (n : ℝ) * chainEpsilon n) := by positivity
  simp only [totalMass, equalChainBump, chainComponent, chainSupport]
  push_cast
  rw [lintegral_finset_sum]
  · simp only [lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc]
    have hterm : ∀ i : Fin n,
        (chainHeight n : ℝ≥0∞) *
            ENNReal.ofReal
              ((chainPoint n i + chainEpsilon n) - (chainPoint n i - chainEpsilon n)) =
          ENNReal.ofReal (1 / (n : ℝ)) := by
      intro i
      rw [chainHeight, ← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal _ hdensity,
        ← ENNReal.ofReal_mul hdensity]
      congr 1
      field_simp
      ring
    simp_rw [hterm]
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
    congr 1
    field_simp
    norm_num
  · intro i hi
    exact measurable_const.indicator measurableSet_Icc

/-- Insert one concrete averaging interval into the defining supremum. -/
theorem mem_strictSuperlevel_of_interval {alpha : ℝ} {f : ℝ → ℝ≥0} {x y t : ℝ}
    {lambda : ℝ≥0} (ht : 0 < t) (hxy : |x - y| ≤ alpha * t)
    (havg : (lambda : ℝ≥0∞) * ENNReal.ofReal (2 * t) < intervalMass f y t) :
    x ∈ strictSuperlevel alpha f lambda := by
  have hden0 : ENNReal.ofReal (2 * t) ≠ 0 := by
    exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hdentop : ENNReal.ofReal (2 * t) ≠ ∞ := ENNReal.ofReal_ne_top
  have hratio : (lambda : ℝ≥0∞) < intervalMass f y t / ENNReal.ofReal (2 * t) :=
    (ENNReal.lt_div_iff_mul_lt (.inl hden0) (.inl hdentop)).2 havg
  exact hratio.trans_le <| le_iSup_of_le y <| le_iSup_of_le t <|
    le_iSup_of_le ht <| le_iSup_of_le hxy le_rfl

theorem chainComponent_mass_le_intervalMass {n : ℕ} (hn : 2 ≤ n) (i : Fin n)
    {y t : ℝ} (hsub : chainSupport n i ⊆ Ioo (y - t) (y + t)) :
    ENNReal.ofReal (1 / (n : ℝ)) ≤ intervalMass (equalChainBump n) y t := by
  rw [← chainComponent_totalMass hn i]
  unfold intervalMass
  rw [← lintegral_indicator measurableSet_Ioo]
  apply lintegral_mono
  intro z
  by_cases hz : z ∈ chainSupport n i
  · rw [indicator_of_mem (hsub hz)]
    have hc : chainComponent n i z ≤ equalChainBump n z := by
      unfold equalChainBump
      exact Finset.single_le_sum
        (fun j _ ↦ (zero_le (chainComponent n j z))) (Finset.mem_univ i)
    change (chainComponent n i z : ℝ≥0∞) ≤ (equalChainBump n z : ℝ≥0∞)
    exact_mod_cast hc
  · simp [chainComponent, hz]

theorem twoComponents_mass_le_intervalMass {n : ℕ} (hn : 2 ≤ n) {i j : Fin n}
    (hij : i ≠ j) {y t : ℝ}
    (hsubi : chainSupport n i ⊆ Ioo (y - t) (y + t))
    (hsubj : chainSupport n j ⊆ Ioo (y - t) (y + t)) :
    ENNReal.ofReal (2 / (n : ℝ)) ≤ intervalMass (equalChainBump n) y t := by
  have hnreal : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hone_nonneg : 0 ≤ 1 / (n : ℝ) := by positivity
  have hadd : ENNReal.ofReal (2 / (n : ℝ)) =
      ENNReal.ofReal (1 / (n : ℝ)) + ENNReal.ofReal (1 / (n : ℝ)) := by
    rw [← ENNReal.ofReal_add hone_nonneg hone_nonneg]
    congr 1
    ring
  rw [hadd]
  calc
    _ = (∫⁻ x, (chainComponent n i x : ℝ≥0∞)) +
          ∫⁻ x, (chainComponent n j x : ℝ≥0∞) := by
            rw [chainComponent_totalMass hn i, chainComponent_totalMass hn j]
    _ = ∫⁻ x, (chainComponent n i x : ℝ≥0∞) + (chainComponent n j x : ℝ≥0∞) := by
          rw [lintegral_add_left]
          unfold chainComponent chainSupport
          exact (measurable_const.indicator measurableSet_Icc).coe_nnreal_ennreal
    _ ≤ intervalMass (equalChainBump n) y t := by
      unfold intervalMass
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_mono
      intro z
      have hc : chainComponent n i z + chainComponent n j z ≤ equalChainBump n z := by
        unfold equalChainBump
        have hs : ({i, j} : Finset (Fin n)) ⊆ Finset.univ := by simp
        have := Finset.sum_le_sum_of_subset (f := fun k ↦ chainComponent n k z) hs
        simpa [hij] using this
      by_cases hzi : z ∈ chainSupport n i
      · rw [indicator_of_mem (hsubi hzi)]
        change ((chainComponent n i z + chainComponent n j z : ℝ≥0) : ℝ≥0∞) ≤
          (equalChainBump n z : ℝ≥0∞)
        exact_mod_cast hc
      · by_cases hzj : z ∈ chainSupport n j
        · rw [indicator_of_mem (hsubj hzj)]
          change ((chainComponent n i z + chainComponent n j z : ℝ≥0) : ℝ≥0∞) ≤
            (equalChainBump n z : ℝ≥0∞)
          exact_mod_cast hc
        · simp [chainComponent, hzi, hzj]

theorem half_mul_intervalLength {t : ℝ} (ht : 0 ≤ t) :
    ((1 / 2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (2 * t) = ENNReal.ofReal t := by
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul]
  · congr 1
    norm_num
    ring
  · norm_num

theorem singletonReach_subset_superlevel {n : ℕ} (hn : 2 ≤ n) (i : Fin n) :
    Ioo
        (chainPoint n i + chainEpsilon n - (1 + (1 / 3 : ℝ)) * (1 / (n : ℝ)))
        (chainPoint n i - chainEpsilon n + (1 + (1 / 3 : ℝ)) * (1 / (n : ℝ))) ⊆
      strictSuperlevel (1 / 3 : ℝ) (equalChainBump n) (1 / 2 : ℝ≥0) := by
  intro x hx
  have hnreal : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hK : 0 < (1 / (n : ℝ)) := by positivity
  have heps : 0 < chainEpsilon n := chainEpsilon_pos hn
  have heps_lt : chainEpsilon n < 1 / (n : ℝ) := chainEpsilon_lt_inv hn
  obtain ⟨y, t, ht, htK, hleft, hright, hxy⟩ :=
    exists_witness_of_mem_blockReach (alpha := (1 / 3 : ℝ)) (K := 1 / (n : ℝ))
      (a := chainPoint n i - chainEpsilon n) (b := chainPoint n i + chainEpsilon n)
      (x := x) (by norm_num) hK (by linarith) (by linarith) hx
  have hsub : chainSupport n i ⊆ Ioo (y - t) (y + t) := by
    intro z hz
    exact ⟨hleft.trans_le hz.1, hz.2.trans_lt hright⟩
  have hmass := chainComponent_mass_le_intervalMass hn i hsub
  apply mem_strictSuperlevel_of_interval ht hxy
  rw [half_mul_intervalLength ht.le]
  exact (ENNReal.ofReal_lt_ofReal_iff hK).2 htK |>.trans_le hmass

theorem pairReach_subset_superlevel {n : ℕ} (hn : 2 ≤ n) {i j : Fin n}
    (hij : i ≠ j) (hpoint : chainPoint n j = chainPoint n i + chainGap n) :
    Ioo
        (chainPoint n j + chainEpsilon n - (1 + (1 / 3 : ℝ)) * (2 / (n : ℝ)))
        (chainPoint n i - chainEpsilon n + (1 + (1 / 3 : ℝ)) * (2 / (n : ℝ))) ⊆
      strictSuperlevel (1 / 3 : ℝ) (equalChainBump n) (1 / 2 : ℝ≥0) := by
  intro x hx
  have hnreal : (0 : ℝ) < n := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hn)
  have hK : 0 < (2 / (n : ℝ)) := by positivity
  have heps : 0 < chainEpsilon n := chainEpsilon_pos hn
  have hgap : 0 < chainGap n := chainGap_pos hn
  have hgate := chainGap_add_two_epsilon_lt hn
  obtain ⟨y, t, ht, htK, hleft, hright, hxy⟩ :=
    exists_witness_of_mem_blockReach (alpha := (1 / 3 : ℝ)) (K := 2 / (n : ℝ))
      (a := chainPoint n i - chainEpsilon n) (b := chainPoint n j + chainEpsilon n)
      (x := x) (by norm_num) hK (by rw [hpoint]; linarith)
      (by rw [hpoint]; norm_num [div_eq_mul_inv] at *; nlinarith) hx
  have hsubi : chainSupport n i ⊆ Ioo (y - t) (y + t) := by
    intro z hz
    refine ⟨hleft.trans_le hz.1, ?_⟩
    have : chainPoint n i + chainEpsilon n ≤ chainPoint n j + chainEpsilon n := by
      rw [hpoint]
      linarith
    exact (hz.2.trans this).trans_lt hright
  have hsubj : chainSupport n j ⊆ Ioo (y - t) (y + t) := by
    intro z hz
    refine ⟨?_, hz.2.trans_lt hright⟩
    have : chainPoint n i - chainEpsilon n ≤ chainPoint n j - chainEpsilon n := by
      rw [hpoint]
      linarith
    exact hleft.trans_le (this.trans hz.1)
  have hmass := twoComponents_mass_le_intervalMass hn hij hsubi hsubj
  apply mem_strictSuperlevel_of_interval ht hxy
  rw [half_mul_intervalLength ht.le]
  exact (ENNReal.ofReal_lt_ofReal_iff hK).2 htK |>.trans_le hmass

theorem equalChain_interval_subset_superlevel {n : ℕ} (hn : 2 ≤ n) :
    Ioo
        (chainEpsilon n - (1 + (1 / 3 : ℝ)) * (1 / (n : ℝ)))
        (((n - 1 : ℕ) : ℝ) * chainGap n - chainEpsilon n +
          (1 + (1 / 3 : ℝ)) * (1 / (n : ℝ))) ⊆
      strictSuperlevel (1 / 3 : ℝ) (equalChainBump n) (1 / 2 : ℝ≥0) := by
  let E := strictSuperlevel (1 / 3 : ℝ) (equalChainBump n) (1 / 2 : ℝ≥0)
  let L := chainEpsilon n - (1 + (1 / 3 : ℝ)) * (1 / (n : ℝ))
  have hgap : 0 < chainGap n := chainGap_pos hn
  have hgap_large := four_thirds_inv_lt_chainGap hn
  have hgate := chainGap_add_two_epsilon_lt hn
  have hnpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hinvpos : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hnreal
  have Hind : ∀ k : ℕ, (hk : k < n) →
      Ioo L (chainPoint n ⟨k, hk⟩ - chainEpsilon n +
        (1 + (1 / 3 : ℝ)) * (1 / (n : ℝ))) ⊆ E := by
    intro k
    induction k with
    | zero =>
        intro hk
        simpa [E, L, chainPoint] using singletonReach_subset_superlevel hn ⟨0, hk⟩
    | succ k ih =>
        intro hk
        have hkprev : k < n := Nat.lt_trans (Nat.lt_succ_self k) hk
        let i : Fin n := ⟨k, hkprev⟩
        let j : Fin n := ⟨k + 1, hk⟩
        have hij : i ≠ j := by
          intro h
          have := congrArg Fin.val h
          simp [i, j] at this
        have hp : chainPoint n j = chainPoint n i + chainGap n := by
          simp only [chainPoint, i, j]
          push_cast
          ring
        have hprev := ih hkprev
        have hpair := pairReach_subset_superlevel hn hij hp
        have hsingle := singletonReach_subset_superlevel hn j
        intro x hx
        let Rprev := chainPoint n i - chainEpsilon n +
          (1 + (1 / 3 : ℝ)) * (1 / (n : ℝ))
        let Pleft := chainPoint n j + chainEpsilon n -
          (1 + (1 / 3 : ℝ)) * (2 / (n : ℝ))
        let Pright := chainPoint n i - chainEpsilon n +
          (1 + (1 / 3 : ℝ)) * (2 / (n : ℝ))
        let Sleft := chainPoint n j + chainEpsilon n -
          (1 + (1 / 3 : ℝ)) * (1 / (n : ℝ))
        let Sright := chainPoint n j - chainEpsilon n +
          (1 + (1 / 3 : ℝ)) * (1 / (n : ℝ))
        have hov1 : Pleft < Rprev := by
          dsimp [Pleft, Rprev]
          rw [hp]
          norm_num [div_eq_mul_inv] at *
          nlinarith
        have hLR : L < Pright := by
          dsimp [L, Pright]
          have hi_nonneg : 0 ≤ chainPoint n i := by
            unfold chainPoint
            exact mul_nonneg (Nat.cast_nonneg _) hgap.le
          have hepslt := chainEpsilon_lt_inv hn
          norm_num [div_eq_mul_inv] at *
          nlinarith
        have hov2 : Sleft < Pright := by
          dsimp [Sleft, Pright]
          rw [hp]
          norm_num [div_eq_mul_inv] at *
          nlinarith
        have hLS : L < Sright := by
          dsimp [L, Sright]
          rw [hp]
          have hi_nonneg : 0 ≤ chainPoint n i := by
            unfold chainPoint
            exact mul_nonneg (Nat.cast_nonneg _) hgap.le
          norm_num [div_eq_mul_inv] at *
          nlinarith
        have hRle : Rprev ≤ Pright := by
          dsimp [Rprev, Pright]
          norm_num [div_eq_mul_inv] at *
          have hnreal' : (0 : ℝ) < n := by exact_mod_cast hnpos
          have hinvpos' : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hnreal'
          linarith
        have hPle : L ≤ Pleft := by
          dsimp [L, Pleft]
          rw [hp]
          have hi_nonneg : 0 ≤ chainPoint n i := by
            unfold chainPoint
            exact mul_nonneg (Nat.cast_nonneg _) hgap.le
          norm_num [div_eq_mul_inv] at *
          nlinarith
        have hSright : Pright ≤ Sright := by
          dsimp [Pright, Sright]
          rw [hp]
          norm_num [div_eq_mul_inv] at *
          nlinarith
        have hu1 : Ioo L Rprev ∪ Ioo Pleft Pright = Ioo L Pright := by
          rw [Ioo_union_Ioo' hov1 hLR, min_eq_left hPle, max_eq_right hRle]
        have hu2 : Ioo L Pright ∪ Ioo Sleft Sright = Ioo L Sright := by
          rw [Ioo_union_Ioo' hov2 hLS, min_eq_left (le_trans hPle (by linarith)),
            max_eq_right hSright]
        have hx' : x ∈ (Ioo L Rprev ∪ Ioo Pleft Pright) ∪ Ioo Sleft Sright := by
          rw [hu1, hu2]
          simpa [Sright, j] using hx
        rcases hx' with (hxold | hxs)
        · rcases hxold with (hxp | hxp)
          · exact hprev (by simpa [Rprev, i] using hxp)
          · exact hpair (by simpa [Pleft, Pright] using hxp)
        · exact hsingle (by simpa [Sleft, Sright] using hxs)
  have hlast : n - 1 < n := Nat.sub_lt (Nat.zero_lt_of_lt hnpos) (by decide)
  simpa [E, L, chainPoint] using Hind (n - 1) hlast

theorem strictSuperlevel_mono_aperture {alpha beta : ℝ} (halpha : 0 ≤ alpha)
    (hab : alpha ≤ beta) (f : ℝ → ℝ≥0) (lambda : ℝ≥0) :
    strictSuperlevel alpha f lambda ⊆ strictSuperlevel beta f lambda := by
  intro x hx
  simp only [strictSuperlevel, mem_setOf_eq, nonTangentialMaximal, lt_iSup_iff] at hx ⊢
  rcases hx with ⟨y, t, ht, hxy, havg⟩
  refine ⟨y, t, ht, ?_, havg⟩
  exact hxy.trans (mul_le_mul_of_nonneg_right hab ht.le)

theorem equalChain_interval_length {n : ℕ} (hn : 2 ≤ n) :
    (((n - 1 : ℕ) : ℝ) * chainGap n - chainEpsilon n +
          (1 + (1 / 3 : ℝ)) * (1 / (n : ℝ))) -
        (chainEpsilon n - (1 + (1 / 3 : ℝ)) * (1 / (n : ℝ))) =
      4 - 2 / (n : ℝ) := by
  have hn1 : 1 ≤ n := le_trans (by decide) hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hn))
  have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hden0 : (2 * (n : ℝ) - 1) ≠ 0 := by nlinarith
  have hden0' : ((n : ℝ) * 2 - 1) ≠ 0 := by nlinarith
  rw [chainGap, chainEpsilon]
  rw [Nat.cast_sub hn1]
  norm_num
  field_simp [hn0, hden0, hden0']
  ring

theorem weakTypeBound_equalChain_score {alpha : ℝ} {C : ℝ≥0∞}
    (halpha : (1 / 3 : ℝ) ≤ alpha) (hC : WeakTypeBound alpha C)
    {n : ℕ} (hn : 2 ≤ n) : ENNReal.ofReal (2 - 1 / (n : ℝ)) ≤ C := by
  have hmass : totalMass (equalChainBump n) = 1 := equalChainBump_totalMass hn
  have hfinite : totalMass (equalChainBump n) < ∞ := by simp [hmass]
  have hw := hC (equalChainBump n) (equalChainBump_measurable n).aemeasurable hfinite
    (1 / 2 : ℝ≥0) (by norm_num)
  have hsub13 := equalChain_interval_subset_superlevel hn
  have hsub : Ioo
        (chainEpsilon n - (1 + (1 / 3 : ℝ)) * (1 / (n : ℝ)))
        (((n - 1 : ℕ) : ℝ) * chainGap n - chainEpsilon n +
          (1 + (1 / 3 : ℝ)) * (1 / (n : ℝ))) ⊆
      strictSuperlevel alpha (equalChainBump n) (1 / 2 : ℝ≥0) :=
    hsub13.trans (strictSuperlevel_mono_aperture (by norm_num) halpha _ _)
  have hmeasure := measure_mono (μ := volume) hsub
  rw [Real.volume_Ioo, equalChain_interval_length hn] at hmeasure
  have hlen_nonneg : 0 ≤ 4 - 2 / (n : ℝ) := by
    have hnreal : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    have : 2 / (n : ℝ) ≤ 1 := (div_le_one hnpos).2 hnreal
    linarith
  have hhalf : ((1 / 2 : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal (4 - 2 / (n : ℝ)) =
      ENNReal.ofReal (2 - 1 / (n : ℝ)) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul]
    · congr 1
      norm_num
      ring
    · norm_num
  rw [← hhalf]
  calc
    _ ≤ ((1 / 2 : ℝ≥0) : ℝ≥0∞) *
        volume (strictSuperlevel alpha (equalChainBump n) (1 / 2 : ℝ≥0)) :=
      mul_le_mul_left' hmeasure _
    _ ≤ C := by simpa [hmass] using hw

/-- Every analytic weak-type constant is at least two on the plateau. -/
theorem weakTypeBound_ge_two {alpha : ℝ} {C : ℝ≥0∞}
    (halpha : (1 / 3 : ℝ) ≤ alpha) (hC : WeakTypeBound alpha C) : (2 : ℝ≥0∞) ≤ C := by
  have hreal : Tendsto (fun n : ℕ ↦ 2 - 1 / ((n : ℝ) + 1)) atTop (nhds 2) := by
    simpa using (tendsto_const_nhds.sub
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0)))
  have henn : Tendsto
      (fun n : ℕ ↦ ENNReal.ofReal (2 - 1 / ((n : ℝ) + 1)))
      atTop (nhds (2 : ℝ≥0∞)) := by
    simpa using ENNReal.tendsto_ofReal hreal
  apply le_of_tendsto' henn
  intro n
  cases n with
  | zero =>
      have hs := weakTypeBound_equalChain_score halpha hC (n := 2) (by omega)
      norm_num at hs ⊢
      exact le_trans (by norm_num) hs
  | succ n =>
      convert weakTypeBound_equalChain_score halpha hC (n := n + 2) (by omega) using 1 <;>
        norm_num <;> ring

end HardyLittlewoodS1
