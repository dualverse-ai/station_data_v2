import FlatAutoconvolutionS1.AffineScore
import FlatAutoconvolutionS1.StepProfileBridge
import FlatAutoconvolutionS1.CoefficientBridge
import FlatAutoconvolutionS1.OutputContinuity
import FlatAutoconvolutionS1.StepAdmissible

open scoped Convolution ENNReal BigOperators
open MeasureTheory Set Filter Topology

namespace FlatAutoconvolutionS1

open Finite Bridge

/-- The deterministic interface delivered by the probabilistic rounding layer.
The normalization by `T` is the one used in the paper. -/
def HasFineCoefficientRefinements {m : ℕ} (v : Profile m) : Prop :=
  ∀ (δ : ℝ), 0 < δ → ∀ T₀ : ℕ,
    ∃ T : ℕ, T₀ ≤ T ∧ 0 < T ∧ ∃ s : Fin (m * T) → Bool,
      ∀ k ∈ outputRange (m * T),
        |convCoeff (boolProfile s) k / (T : ℝ) -
          convCoeff (Bridge.blockProfile T v) k / (T : ℝ)| < δ

theorem mass_bridge_blockProfile {m T : ℕ} (v : Profile m) :
    mass (Bridge.blockProfile T v) = (T : ℝ) * mass v := by
  unfold mass Bridge.blockProfile
  rw [← (finProdFinEquiv : Fin m × Fin T ≃ Fin (m * T)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp [Finset.mul_sum]

theorem bridge_blockProfile_nonnegative {m T : ℕ} {v : Profile m}
    (hv : Nonnegative v) : Nonnegative (Bridge.blockProfile T v) := by
  intro i
  exact hv _

/-- A selector furnished by coefficient rounding cannot be identically false
once the target has mass one and the normalized error is below `1/(2m)`.
This closes the small but essential nonzero-condition gap in the construction
of a `BinaryStep`. -/
theorem selector_nonempty_of_coeff_close
    {m T : ℕ} (hm : 0 < m) (hT : 0 < T)
    (v : Profile m) (hv : Nonnegative v) (hmass : mass v = 1)
    (s : Fin (m * T) → Bool) {δ : ℝ}
    (hδsmall : 2 * (m : ℝ) * δ ≤ 1)
    (hclose : ∀ k ∈ outputRange (m * T),
      |convCoeff (boolProfile s) k / (T : ℝ) -
        convCoeff (Bridge.blockProfile T v) k / (T : ℝ)| < δ) :
    ∃ i, s i = true := by
  by_contra hs
  push_neg at hs
  have hsfalse : ∀ i, s i = false := by
    intro i
    cases h : s i
    · rfl
    · exact (hs i h).elim
  have hbzero : boolProfile s = fun _ ↦ (0 : ℝ) := by
    funext i
    simp [boolProfile, hsfalse i]
  let w : Profile (m * T) := Bridge.blockProfile T v
  have hw : Nonnegative w := bridge_blockProfile_nonnegative hv
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hN : 0 < m * T := Nat.mul_pos hm hT
  have hterm : ∀ k ∈ outputRange (m * T), convCoeff w k / (T : ℝ) < δ := by
    intro k hk
    have h := hclose k hk
    rw [hbzero] at h
    have hz : convCoeff (fun _ : Fin (m * T) ↦ (0 : ℝ)) k = 0 := by
      simp [convCoeff]
    rw [hz, zero_div, zero_sub, abs_neg] at h
    have habs : |convCoeff w k / (T : ℝ)| = convCoeff w k / (T : ℝ) :=
      abs_of_nonneg (div_nonneg (convCoeff_nonneg hw k) hTreal.le)
    simpa only [w, habs] using h
  have hrange : (outputRange (m * T)).Nonempty := by
    refine ⟨0, ?_⟩
    simp [outputRange, hN]
  have hsum := Finset.sum_lt_sum_of_nonempty hrange hterm
  have hmassw : mass w = (T : ℝ) := by
    dsimp [w]
    rw [mass_bridge_blockProfile, hmass, mul_one]
  have hsum' : (T : ℝ) < ((2 * (m * T) : ℕ) : ℝ) * δ := by
    calc
      (T : ℝ) = (mass w) ^ 2 / (T : ℝ) := by
        rw [hmassw]
        field_simp
      _ = ∑ k ∈ outputRange (m * T), convCoeff w k / (T : ℝ) := by
        rw [← Finset.sum_div, sum_convCoeff_eq_mass_sq]
      _ < ∑ _k ∈ outputRange (m * T), δ := hsum
      _ = ((2 * (m * T) : ℕ) : ℝ) * δ := by
        simp [outputRange]
  push_cast at hsum'
  nlinarith

/-- The `L¹` companion to the pointwise scaled bridge.  The extra inverse
scale is the Jacobian from spatial compression. -/
theorem integral_abs_scaledProfileSignal_autoconvolution_sub_le
    {n : ℕ} (T : ℝ) (hT : 0 < T) (u v : Profile n) (E : ℝ) (hE : 0 ≤ E)
    (hcoeff : ∀ k ∈ outputRange n, |convCoeff u k - convCoeff v k| ≤ E) :
    (∫ x, |(scaledProfileSignal T u ⋆ scaledProfileSignal T u) x -
      (scaledProfileSignal T v ⋆ scaledProfileSignal T v) x|) ≤
        T⁻¹ ^ 2 * (((2 * n : ℕ) : ℝ) + 1) * E := by
  let D : ℝ → ℝ := fun y ↦
    (profileSignal u ⋆ profileSignal u) y -
      (profileSignal v ⋆ profileSignal v) y
  have hformula (x : ℝ) :
      |(scaledProfileSignal T u ⋆ scaledProfileSignal T u) x -
        (scaledProfileSignal T v ⋆ scaledProfileSignal T v) x| =
        T⁻¹ * |D (T * x)| := by
    rw [scaledProfileSignal_convolution T u hT,
      scaledProfileSignal_convolution T v hT, ← mul_sub, abs_mul,
      abs_of_pos (inv_pos.mpr hT)]
  calc
    (∫ x, |(scaledProfileSignal T u ⋆ scaledProfileSignal T u) x -
        (scaledProfileSignal T v ⋆ scaledProfileSignal T v) x|) =
        ∫ x, T⁻¹ * |D (T * x)| := by
          apply integral_congr_ae
          filter_upwards [] with x
          exact hformula x
    _ = T⁻¹ * ∫ x, |D (T * x)| := by rw [integral_const_mul]
    _ = T⁻¹ * (|T⁻¹| * ∫ y, |D y|) := by
      congr 1
      exact Measure.integral_comp_mul_left (fun y ↦ |D y|) T
    _ = T⁻¹ ^ 2 * ∫ y, |D y| := by
      rw [abs_of_pos (inv_pos.mpr hT)]
      ring
    _ ≤ T⁻¹ ^ 2 * (((2 * n : ℕ) : ℝ) + 1) * E := by
      have hraw :=
        integral_abs_profileSignal_autoconvolution_sub_le u v E hE hcoeff
      have := mul_le_mul_of_nonneg_left hraw (sq_nonneg T⁻¹)
      simpa only [D, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using this

structure FineRefinementData {m : ℕ} (v : Profile m) (δ : ℝ) (T₀ : ℕ) where
  T : ℕ
  T_ge : T₀ ≤ T
  T_pos : 0 < T
  selector : Fin (m * T) → Bool
  coeff_close : ∀ k ∈ outputRange (m * T),
    |convCoeff (boolProfile selector) k / (T : ℝ) -
      convCoeff (Bridge.blockProfile T v) k / (T : ℝ)| < δ

noncomputable def chooseFineRefinement {m : ℕ} {v : Profile m}
    (href : HasFineCoefficientRefinements v) (δ : ℝ) (hδ : 0 < δ) (T₀ : ℕ) :
    FineRefinementData v δ T₀ := by
  classical
  let hex := href δ hδ T₀
  let T := Classical.choose hex
  have hspec := Classical.choose_spec hex
  let s := Classical.choose hspec.2.2
  have hs := Classical.choose_spec hspec.2.2
  have hT₀ := hspec.1
  have hT := hspec.2.1
  exact ⟨T, hT₀, hT, s, hs⟩

/-- A canonical unit-mesh step carrying the normalized weights of `g`. -/
noncomputable def normalizedUnitStep (g : EqualGridStep) : EqualGridStep where
  cells := g.cells
  cells_pos := g.cells_pos
  origin := 0
  mesh := 1
  mesh_pos := zero_lt_one
  weight := g.normalizedProfile
  weight_nonneg := g.normalizedProfile_nonnegative
  weight_nonzero := by
    obtain ⟨i, hi⟩ := g.weight_nonzero
    exact ⟨i, div_pos hi g.profileMass_pos⟩

theorem normalizedUnitStep_toSignal (g : EqualGridStep) :
    (normalizedUnitStep g).toSignal = profileSignal g.normalizedProfile := by
  funext x
  simpa [normalizedUnitStep, EqualGridStep.profile] using
    (normalizedUnitStep g).toSignal_eq_profileSignal_affine x

theorem score_eq_normalized_profileSignal (g : EqualGridStep) :
    score g.toSignal = score (profileSignal g.normalizedProfile) := by
  exact g.score_toSignal_eq_normalizedProfile

noncomputable def refinementError (m n : ℕ) : ℝ :=
  (1 / (4 * (m : ℝ))) * (1 / ((n : ℝ) + 1))

theorem refinementError_pos {m : ℕ} (hm : 0 < m) (n : ℕ) :
    0 < refinementError m n := by
  unfold refinementError
  positivity

theorem refinementError_small {m : ℕ} (hm : 0 < m) (n : ℕ) :
    2 * (m : ℝ) * refinementError m n ≤ 1 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  unfold refinementError
  field_simp
  nlinarith

theorem tendsto_refinementError (m : ℕ) :
    Tendsto (refinementError m) atTop (𝓝 0) := by
  unfold refinementError
  simpa only [mul_zero] using
    (tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))

noncomputable def stepRefinementData (g : EqualGridStep)
    (href : HasFineCoefficientRefinements g.normalizedProfile) (n : ℕ) :
    FineRefinementData g.normalizedProfile (refinementError g.cells n) (n + 1) :=
  chooseFineRefinement href _ (refinementError_pos g.cells_pos n) _

theorem FineRefinementData.raw_coeff_close_le {m : ℕ} {v : Profile m}
    {δ : ℝ} {T₀ : ℕ} (d : FineRefinementData v δ T₀)
    (k : ℕ) (hk : k ∈ outputRange (m * d.T)) :
    |convCoeff (boolProfile d.selector) k -
      convCoeff (Bridge.blockProfile d.T v) k| ≤ (d.T : ℝ) * δ := by
  have h := d.coeff_close k hk
  have hTreal : (0 : ℝ) < d.T := by exact_mod_cast d.T_pos
  rw [← sub_div, abs_div, abs_of_pos hTreal] at h
  have h' := (div_lt_iff₀ hTreal).1 h
  simpa only [mul_comm] using h'.le

theorem stepRefinementData_selector_nonempty (g : EqualGridStep)
    (href : HasFineCoefficientRefinements g.normalizedProfile) (n : ℕ) :
    ∃ i, (stepRefinementData g href n).selector i = true := by
  let d := stepRefinementData g href n
  exact selector_nonempty_of_coeff_close g.cells_pos d.T_pos
    g.normalizedProfile g.normalizedProfile_nonnegative
    g.mass_normalizedProfile d.selector (refinementError_small g.cells_pos n)
    d.coeff_close

noncomputable def binaryApproximation (g : EqualGridStep)
    (href : HasFineCoefficientRefinements g.normalizedProfile) (n : ℕ) : BinaryStep :=
  let d := stepRefinementData g href n
  binaryStepOfBoolProfile d.T_pos d.selector
    (stepRefinementData_selector_nonempty g href n)

theorem binaryApproximation_toSignal (g : EqualGridStep)
    (href : HasFineCoefficientRefinements g.normalizedProfile) (n : ℕ) :
    (binaryApproximation g href n).toSignal =
      scaledProfileSignal ((stepRefinementData g href n).T : ℝ)
        (boolProfile (stepRefinementData g href n).selector) := by
  simpa [binaryApproximation] using
    binaryStepOfBoolProfile_toSignal
      (stepRefinementData g href n).T_pos
      (stepRefinementData g href n).selector
      (stepRefinementData_selector_nonempty g href n)

theorem binaryApproximation_pointwise (g : EqualGridStep)
    (href : HasFineCoefficientRefinements g.normalizedProfile) (n : ℕ) (x : ℝ) :
    |autoconvolution (binaryApproximation g href n).toSignal x -
      autoconvolution (profileSignal g.normalizedProfile) x| ≤
        refinementError g.cells n := by
  let d := stepRefinementData g href n
  have hTreal : (0 : ℝ) < (d.T : ℝ) := by exact_mod_cast d.T_pos
  have hδ : 0 ≤ refinementError g.cells n :=
    (refinementError_pos g.cells_pos n).le
  have hraw : ∀ k ∈ outputRange (g.cells * d.T),
      |convCoeff (boolProfile d.selector) k -
        convCoeff (Bridge.blockProfile d.T g.normalizedProfile) k| ≤
          (d.T : ℝ) * refinementError g.cells n :=
    d.raw_coeff_close_le
  rw [binaryApproximation_toSignal]
  rw [← Bridge.scaledProfileSignal_blockProfile d.T_pos g.normalizedProfile]
  have h := Bridge.scaledProfileSignal_autoconvolution_sub_le
    (d.T : ℝ) hTreal (boolProfile d.selector)
    (Bridge.blockProfile d.T g.normalizedProfile)
    ((d.T : ℝ) * refinementError g.cells n) (mul_nonneg hTreal.le hδ)
    hraw x
  convert h using 1
  field_simp

theorem binaryApproximation_outputL1_bound (g : EqualGridStep)
    (href : HasFineCoefficientRefinements g.normalizedProfile) (n : ℕ) :
    (∫ x, |autoconvolution (binaryApproximation g href n).toSignal x -
      autoconvolution (profileSignal g.normalizedProfile) x|) ≤
        (2 * (g.cells : ℝ) + 1) * refinementError g.cells n := by
  let d := stepRefinementData g href n
  have hTreal : (0 : ℝ) < (d.T : ℝ) := by exact_mod_cast d.T_pos
  have hTone : (1 : ℝ) ≤ d.T := by exact_mod_cast d.T_pos
  have hδ : 0 ≤ refinementError g.cells n :=
    (refinementError_pos g.cells_pos n).le
  have hraw : ∀ k ∈ outputRange (g.cells * d.T),
      |convCoeff (boolProfile d.selector) k -
        convCoeff (Bridge.blockProfile d.T g.normalizedProfile) k| ≤
          (d.T : ℝ) * refinementError g.cells n :=
    d.raw_coeff_close_le
  rw [binaryApproximation_toSignal]
  rw [← Bridge.scaledProfileSignal_blockProfile d.T_pos g.normalizedProfile]
  have h := integral_abs_scaledProfileSignal_autoconvolution_sub_le
    (d.T : ℝ) hTreal (boolProfile d.selector)
    (Bridge.blockProfile d.T g.normalizedProfile)
    ((d.T : ℝ) * refinementError g.cells n) (mul_nonneg hTreal.le hδ) hraw
  refine h.trans ?_
  have halg :
      (d.T : ℝ)⁻¹ ^ 2 * (((2 * (g.cells * d.T) : ℕ) : ℝ) + 1) *
          ((d.T : ℝ) * refinementError g.cells n) =
        (2 * (g.cells : ℝ) + (d.T : ℝ)⁻¹) * refinementError g.cells n := by
    push_cast
    field_simp
  rw [halg]
  apply mul_le_mul_of_nonneg_right _ hδ
  gcongr
  exact (inv_le_one₀ hTreal).2 hTone

theorem tendsto_binaryApproximation_score (g : EqualGridStep)
    (href : HasFineCoefficientRefinements g.normalizedProfile) :
    Tendsto (fun n ↦ score (binaryApproximation g href n).toSignal) atTop
      (𝓝 (score (profileSignal g.normalizedProfile))) := by
  let u : ℕ → Signal := fun n ↦ (binaryApproximation g href n).toSignal
  let f : Signal := profileSignal g.normalizedProfile
  let K : ℕ → ℝ := refinementError g.cells
  have hu1 : ∀ n, Integrable (u n) := by
    intro n
    dsimp only [u]
    simpa only [BinaryStep.toEqualGridStep_toSignal] using
      (binaryApproximation g href n).toEqualGridStep.toSignal_integrable
  have hf1 : Integrable f := by
    rw [show f = (normalizedUnitStep g).toSignal by
      exact (normalizedUnitStep_toSignal g).symm]
    exact (normalizedUnitStep g).toSignal_integrable
  have hu2 : ∀ n, MemLp (u n) 2 volume := by
    intro n
    dsimp only [u]
    simpa only [BinaryStep.toEqualGridStep_toSignal] using
      (binaryApproximation g href n).toEqualGridStep.toSignal_memLp_two
  have hf2 : MemLp f 2 volume := by
    rw [show f = (normalizedUnitStep g).toSignal by
      exact (normalizedUnitStep_toSignal g).symm]
    exact (normalizedUnitStep g).toSignal_memLp_two
  have hKnonneg : ∀ n, 0 ≤ K n := fun n ↦
    (refinementError_pos g.cells_pos n).le
  have hK : Tendsto K atTop (𝓝 0) := tendsto_refinementError g.cells
  have hpoint : ∀ n x,
      |autoconvolution (u n) x - autoconvolution f x| ≤ K n := by
    intro n x
    exact binaryApproximation_pointwise g href n x
  have hmajor : Tendsto
      (fun n ↦ (2 * (g.cells : ℝ) + 1) * refinementError g.cells n)
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (tendsto_refinementError g.cells))
  have houtputL1 : Tendsto
      (fun n ↦ ∫ x, |autoconvolution (u n) x - autoconvolution f x|)
      atTop (𝓝 0) := by
    apply squeeze_zero
    · intro n
      exact integral_nonneg fun _ ↦ abs_nonneg _
    · intro n
      exact binaryApproximation_outputL1_bound g href n
    · exact hmajor
  have hfadm : Admissible f := by
    rw [show f = (normalizedUnitStep g).toSignal by
      exact (normalizedUnitStep_toSignal g).symm]
    exact (normalizedUnitStep g).admissible
  exact tendsto_score_of_autoconvolution_control hu1 hf1 hu2 hf2
    hKnonneg hK hpoint houtputL1 hfadm.score_denominator_ne_zero

/-- Conditional only on the independently proved finite rounding interface,
every equal-grid step has binary-step scores arbitrarily close to its score. -/
theorem exists_binaryStep_score_approx_of_fine_refinements
    (g : EqualGridStep)
    (href : HasFineCoefficientRefinements g.normalizedProfile)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ b : BinaryStep, |score b.toSignal - score g.toSignal| < ε := by
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1
    (tendsto_binaryApproximation_score g href) ε hε
  refine ⟨binaryApproximation g href N, ?_⟩
  have h := hN N le_rfl
  rw [Real.dist_eq] at h
  rwa [g.score_toSignal_eq_normalizedProfile]

def natBoolReal (b : Bool) : ℝ := if b then 1 else 0

def natBlockProfile {m : ℕ} (T : ℕ) (v : Profile m) (i : ℕ) : ℝ :=
  if h : i / T < m then v ⟨i / T, h⟩ else 0

theorem profileGetZero_bridge_blockProfile {m T : ℕ} (hT : 0 < T)
    (v : Profile m) (i : ℕ) :
    profileGetZero (Bridge.blockProfile T v) i = natBlockProfile T v i := by
  by_cases hi : i < m * T
  · have hdiv : i / T < m := (Nat.div_lt_iff_lt_mul hT).2 hi
    simp only [profileGetZero, hi, dif_pos, natBlockProfile, hdiv]
    congr 1
  · have hdiv : ¬i / T < m := by
      intro h
      exact hi ((Nat.div_lt_iff_lt_mul hT).1 h)
    simp [profileGetZero, hi, natBlockProfile, hdiv]

theorem profileGetZero_boolProfile_eq_natBoolReal
    {N : ℕ} (ξ : ℕ → Bool) (hsupport : ∀ i, N ≤ i → ξ i = false) (i : ℕ) :
    profileGetZero (boolProfile (fun j : Fin N ↦ ξ j)) i = natBoolReal (ξ i) := by
  by_cases hi : i < N
  · simp [profileGetZero, hi, boolProfile, natBoolReal]
  · have hfalse := hsupport i (le_of_not_gt hi)
    simp [profileGetZero, hi, natBoolReal, hfalse]

/-- The precise Nat-indexed interface emitted by the probability layer before
conversion to finite profiles. -/
def HasNatCoefficientRefinements {m : ℕ} (v : Profile m) : Prop :=
  ∀ (δ : ℝ), 0 < δ → ∀ T₀ : ℕ,
    ∃ T : ℕ, T₀ ≤ T ∧ 0 < T ∧ ∃ ξ : ℕ → Bool,
      (∀ i, m * T ≤ i → ξ i = false) ∧
      ∀ t : Fin (2 * (m * T) - 1),
        |rangeCoeff (fun i ↦ natBoolReal (ξ i)) t.val / (T : ℝ) -
          rangeCoeff (natBlockProfile T v) t.val / (T : ℝ)| < δ

/-- Adapter from the Nat-indexed rounding output to the finite-profile
interface consumed by the analytic assembly.  The sole padded final
coefficient is zero on both sides. -/
theorem fineCoefficientRefinements_of_nat
    {m : ℕ} {v : Profile m} (hm : 0 < m)
    (hround : HasNatCoefficientRefinements v) :
    HasFineCoefficientRefinements v := by
  intro δ hδ T₀
  obtain ⟨T, hT₀, hT, ξ, hsupp, hclose⟩ := hround δ hδ T₀
  let s : Fin (m * T) → Bool := fun i ↦ ξ i
  refine ⟨T, hT₀, hT, s, ?_⟩
  intro k hk
  have hN : 0 < m * T := Nat.mul_pos hm hT
  have hklt : k < 2 * (m * T) := by simpa [outputRange] using hk
  by_cases hkmain : k < 2 * (m * T) - 1
  · have h := hclose ⟨k, hkmain⟩
    rw [show (fun i ↦ natBoolReal (ξ i)) =
        profileGetZero (boolProfile s) by
      funext i
      exact (profileGetZero_boolProfile_eq_natBoolReal ξ hsupp i).symm] at h
    rw [show natBlockProfile T v =
        profileGetZero (Bridge.blockProfile T v) by
      funext i
      exact (profileGetZero_bridge_blockProfile hT v i).symm] at h
    simpa only [rangeCoeff_profileGetZero_eq_convCoeff] using h
  · have hklast : k = 2 * (m * T) - 1 := by omega
    subst k
    simp only [convCoeff_last_eq_zero, zero_div, sub_self, abs_zero]
    exact hδ

def nnBlockProfile {m : ℕ} (T : ℕ) (v : Fin m → NNReal) (i : ℕ) : NNReal :=
  if h : i / T < m then v ⟨i / T, h⟩ else 0

/-- Signature of the probability theorem, with probabilities represented by
`NNReal` exactly as in mathlib's Bernoulli PMF. -/
def HasNNRealCoefficientRefinements {m : ℕ} (v : Fin m → NNReal) : Prop :=
  ∀ (δ : ℝ), 0 < δ → ∀ T₀ : ℕ,
    ∃ T : ℕ, T₀ ≤ T ∧ 0 < T ∧ ∃ ξ : ℕ → Bool,
      (∀ i, m * T ≤ i → ξ i = false) ∧
      ∀ t : Fin (2 * (m * T) - 1),
        |rangeCoeff (fun i ↦ natBoolReal (ξ i)) t.val / (T : ℝ) -
          rangeCoeff (fun i ↦ (nnBlockProfile T v i : ℝ)) t.val / (T : ℝ)| < δ

theorem natCoefficientRefinements_of_nnreal
    {m : ℕ} (v : Profile m) (hv : Nonnegative v)
    (hround : HasNNRealCoefficientRefinements
      (fun i ↦ ⟨v i, hv i⟩)) :
    HasNatCoefficientRefinements v := by
  intro δ hδ T₀
  obtain ⟨T, hT₀, hT, ξ, hsupp, hclose⟩ := hround δ hδ T₀
  refine ⟨T, hT₀, hT, ξ, hsupp, ?_⟩
  have heq : (fun i ↦ (nnBlockProfile T (fun j ↦ ⟨v j, hv j⟩) i : ℝ)) =
      natBlockProfile T v := by
    funext i
    unfold nnBlockProfile natBlockProfile
    split_ifs <;> rfl
  intro t
  rw [← heq]
  exact hclose t

/-- Fully assembled local binary approximation theorem, parametrized only by
the exact NNReal-valued Bernoulli rounding statement. -/
theorem exists_binaryStep_score_approx_of_nnreal_rounding
    (g : EqualGridStep)
    (hround : HasNNRealCoefficientRefinements
      (fun i ↦ ⟨g.normalizedProfile i,
        g.normalizedProfile_nonnegative i⟩))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ b : BinaryStep, |score b.toSignal - score g.toSignal| < ε := by
  apply exists_binaryStep_score_approx_of_fine_refinements g
    (fineCoefficientRefinements_of_nat g.cells_pos
      (natCoefficientRefinements_of_nnreal g.normalizedProfile
        g.normalizedProfile_nonnegative hround)) hε

end FlatAutoconvolutionS1
