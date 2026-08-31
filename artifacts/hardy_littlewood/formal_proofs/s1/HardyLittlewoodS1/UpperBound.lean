import HardyLittlewoodS1.Definitions
import HardyLittlewoodS1.IntervalCover

open scoped ENNReal NNReal
open Set MeasureTheory

namespace HardyLittlewoodS1

/-- A point in the strict superlevel set has a literal averaging-interval witness. -/
theorem exists_maximal_witness {alpha : ℝ} {f : ℝ → ℝ≥0} {lambda : ℝ≥0} {x : ℝ}
    (hx : x ∈ strictSuperlevel alpha f lambda) :
    ∃ y t : ℝ, ∃ ht : 0 < t, ∃ hxy : |x - y| ≤ alpha * t,
      (lambda : ℝ≥0∞) < intervalMass f y t / ENNReal.ofReal (2 * t) := by
  change (lambda : ℝ≥0∞) < nonTangentialMaximal alpha f x at hx
  rw [nonTangentialMaximal] at hx
  rcases lt_iSup_iff.mp hx with ⟨y, hy⟩
  rcases lt_iSup_iff.mp hy with ⟨t, ht'⟩
  rcases lt_iSup_iff.mp ht' with ⟨ht, hxy'⟩
  rcases lt_iSup_iff.mp hxy' with ⟨hxy, havg⟩
  exact ⟨y, t, ht, hxy, havg⟩

/-- Every non-tangential witness at aperture at most one is contained in an uncentered interval. -/
theorem witness_point_mem_Icc {alpha y t x : ℝ} (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1)
    (ht : 0 < t) (hxy : |x - y| ≤ alpha * t) :
    x ∈ Icc (y - t) (y + t) := by
  have hdist : |x - y| ≤ t := by
    calc |x - y| ≤ alpha * t := hxy
      _ ≤ 1 * t := mul_le_mul_of_nonneg_right ha1 ht.le
      _ = t := one_mul t
  constructor <;> rw [abs_le] at hdist <;> linarith

/-- An interval whose mass is strictly larger than `lambda` times its length. -/
structure GoodInterval (f : ℝ → ℝ≥0) (lambda : ℝ≥0) extends OpenInterval where
  good : (lambda : ℝ≥0∞) * volume toOpenInterval.carrier <
    ∫⁻ z in toOpenInterval.carrier, (f z : ℝ≥0∞)

namespace GoodInterval

def carrier {f : ℝ → ℝ≥0} {lambda : ℝ≥0} (I : GoodInterval f lambda) : Set ℝ :=
  I.toOpenInterval.carrier

theorem isOpen_carrier {f : ℝ → ℝ≥0} {lambda : ℝ≥0} (I : GoodInterval f lambda) :
    IsOpen I.carrier := OpenInterval.isOpen_carrier _

end GoodInterval

/-- A strict maximal-function witness can be enlarged slightly to a genuinely open good interval
containing the point.  Finiteness of the total mass makes the strict ENNReal inequality an
ordinary real margin. -/
theorem exists_goodInterval_of_witness {alpha : ℝ} {f : ℝ → ℝ≥0} {lambda : ℝ≥0}
    {x y t : ℝ} (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hlambda : lambda ≠ 0)
    (hfinite : totalMass f < ∞) (ht : 0 < t) (hxy : |x - y| ≤ alpha * t)
    (havg : (lambda : ℝ≥0∞) < intervalMass f y t / ENNReal.ofReal (2 * t)) :
    ∃ I : GoodInterval f lambda, x ∈ I.carrier := by
  have hm_le : intervalMass f y t ≤ totalMass f := by
    simpa [intervalMass, totalMass] using
      (lintegral_mono_set (μ := volume) (f := fun z : ℝ => (f z : ℝ≥0∞)) (subset_univ _))
  have hmtop : intervalMass f y t ≠ ⊤ :=
    ne_top_of_le_ne_top (ne_of_lt hfinite) hm_le
  have hden0 : ENNReal.ofReal (2 * t) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, ht]
  have hmul : (lambda : ℝ≥0∞) * ENNReal.ofReal (2 * t) < intervalMass f y t :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl hden0) (Or.inl ENNReal.ofReal_ne_top)).mp havg
  have hlefttop : (lambda : ℝ≥0∞) * ENNReal.ofReal (2 * t) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
  have hreal := (ENNReal.toReal_lt_toReal hlefttop hmtop).2 hmul
  have hlpos : 0 < (lambda : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hlambda : 0 < lambda)
  have htwo : 0 ≤ 2 * t := by linarith
  have hreal' : (lambda : ℝ) * (2 * t) < (intervalMass f y t).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal htwo] at hreal
    exact hreal
  let q : ℝ := (intervalMass f y t).toReal / (lambda : ℝ)
  have hdq : 2 * t < q := (lt_div_iff₀ hlpos).2 (by simpa [mul_comm] using hreal')
  let r : ℝ := (2 * t + q) / 4
  have htr : t < r := by dsimp [r]; linarith
  have hrpos : 0 < r := ht.trans htr
  let J : OpenInterval := ⟨y - r, y + r⟩
  have hxJ : x ∈ J.carrier := by
    have hxclosed := witness_point_mem_Icc ha0 ha1 ht hxy
    exact ⟨by dsimp [J, OpenInterval.carrier] at hxclosed ⊢; linarith [hxclosed.1],
      by dsimp [J, OpenInterval.carrier] at hxclosed ⊢; linarith [hxclosed.2]⟩
  have hsubset : Ioo (y - t) (y + t) ⊆ J.carrier := by
    intro z hz
    dsimp [J, OpenInterval.carrier]
    constructor <;> linarith [hz.1, hz.2]
  have hmassmono : intervalMass f y t ≤ ∫⁻ z in J.carrier, (f z : ℝ≥0∞) :=
    lintegral_mono_set hsubset
  have hlenq : 2 * r < q := by dsimp [r]; linarith
  have hgoodreal : (lambda : ℝ) * (2 * r) < (intervalMass f y t).toReal := by
    rw [show (intervalMass f y t).toReal = (lambda : ℝ) * q by
      dsimp [q]; field_simp]
    exact mul_lt_mul_of_pos_left hlenq hlpos
  have hgoodinner : (lambda : ℝ≥0∞) * volume J.carrier < intervalMass f y t := by
    rw [show volume J.carrier = ENNReal.ofReal (2 * r) by
      change volume (Ioo (y - r) (y + r)) = ENNReal.ofReal (2 * r)
      rw [Real.volume_Ioo]
      congr 1 <;> ring]
    have hLtop : (lambda : ℝ≥0∞) * ENNReal.ofReal (2 * r) ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top
    apply (ENNReal.toReal_lt_toReal hLtop hmtop).mp
    rw [ENNReal.toReal_mul, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * r)]
    exact hgoodreal
  refine ⟨{ toOpenInterval := J, good := hgoodinner.trans_le hmassmono }, hxJ⟩

/-- The open union of every interval with average strictly above `lambda`. -/
def goodEnvelope (f : ℝ → ℝ≥0) (lambda : ℝ≥0) : Set ℝ :=
  ⋃ I : GoodInterval f lambda, I.carrier

theorem isOpen_goodEnvelope (f : ℝ → ℝ≥0) (lambda : ℝ≥0) :
    IsOpen (goodEnvelope f lambda) := isOpen_iUnion fun I => I.isOpen_carrier

theorem strictSuperlevel_subset_goodEnvelope {alpha : ℝ} {f : ℝ → ℝ≥0}
    {lambda : ℝ≥0} (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) (hlambda : lambda ≠ 0)
    (hfinite : totalMass f < ∞) :
    strictSuperlevel alpha f lambda ⊆ goodEnvelope f lambda := by
  intro x hx
  obtain ⟨y, t, ht, hxy, havg⟩ := exists_maximal_witness hx
  obtain ⟨I, hxI⟩ :=
    exists_goodInterval_of_witness ha0 ha1 hlambda hfinite ht hxy havg
  exact mem_iUnion.mpr ⟨I, hxI⟩

namespace GoodInterval

/-- Forgetting the average proof is injective (proof irrelevance supplies the proof field). -/
def toOpenEmbedding {f : ℝ → ℝ≥0} {lambda : ℝ≥0} :
    GoodInterval f lambda ↪ OpenInterval where
  toFun := toOpenInterval
  inj' := by
    intro I J h
    cases I
    cases J
    simp_all

end GoodInterval

/-- Multiplicity at most two bounds the total restricted mass of an irredundant interval family. -/
theorem sum_lintegral_le_two {f : ℝ → ℝ≥0} (hf : AEMeasurable f volume)
    {K : Set ℝ} {s : Finset OpenInterval} (hs : IrredundantOn K s) :
    ∑ I ∈ s, ∫⁻ z in I.carrier, (f z : ℝ≥0∞) ≤ 2 * totalMass f := by
  classical
  calc
    (∑ I ∈ s, ∫⁻ z in I.carrier, (f z : ℝ≥0∞)) =
        ∑ I ∈ s, ∫⁻ z, I.carrier.indicator (fun z => (f z : ℝ≥0∞)) z := by
          apply Finset.sum_congr rfl
          intro I hI
          rw [lintegral_indicator I.isOpen_carrier.measurableSet]
    _ = ∫⁻ z, ∑ I ∈ s, I.carrier.indicator (fun z => (f z : ℝ≥0∞)) z := by
      rw [lintegral_finset_sum']
      intro I hIs
      exact hf.coe_nnreal_ennreal.indicator I.isOpen_carrier.measurableSet
    _ ≤ 2 * totalMass f := by
      calc
        (∫⁻ z, ∑ I ∈ s, I.carrier.indicator (fun z => (f z : ℝ≥0∞)) z) ≤
          ∫⁻ z, 2 * (f z : ℝ≥0∞) := by
            apply lintegral_mono
            intro z
            have hcard := card_filter_mem_le_two hs z
            simp only [Set.indicator_apply]
            calc
              (∑ I ∈ s, if z ∈ I.carrier then (f z : ℝ≥0∞) else 0) =
                  ∑ I ∈ s with z ∈ I.carrier, (f z : ℝ≥0∞) := by
                    symm
                    exact Finset.sum_filter _ _
              _ = (s.filter fun I => z ∈ I.carrier).card * (f z : ℝ≥0∞) := by
                    rw [Finset.sum_const, nsmul_eq_mul]
              _ ≤ 2 * (f z : ℝ≥0∞) := by
                    apply mul_le_mul_right'
                    exact Nat.cast_le.2 (by simpa [OpenInterval.carrier] using hcard)
      _ = 2 * totalMass f := by
        rw [lintegral_const_mul'' 2 (hf.coe_nnreal_ennreal)]
        rfl

/-- Every compact subset of the good-interval envelope satisfies the sharp factor-two bound. -/
theorem compact_goodEnvelope_bound {f : ℝ → ℝ≥0} {lambda : ℝ≥0}
    (hf : AEMeasurable f volume) {K : Set ℝ} (hK : IsCompact K)
    (hsub : K ⊆ goodEnvelope f lambda) :
    (lambda : ℝ≥0∞) * volume K ≤ 2 * totalMass f := by
  classical
  have hopen : ∀ I : GoodInterval f lambda, IsOpen I.carrier :=
    fun I => I.isOpen_carrier
  have hcover : K ⊆ ⋃ I : GoodInterval f lambda, I.carrier := hsub
  obtain ⟨q, hq⟩ := hK.elim_finite_subcover (fun I : GoodInterval f lambda => I.carrier)
    hopen hcover
  let e := GoodInterval.toOpenEmbedding (f := f) (lambda := lambda)
  let s : Finset OpenInterval := q.map e
  have hscover : Covers K s := by
    intro x hx
    have hx' := hq hx
    simp only [mem_iUnion, exists_prop] at hx' ⊢
    obtain ⟨I, hIq, hxI⟩ := hx'
    exact ⟨I.toOpenInterval, Finset.mem_map.mpr ⟨I, hIq, rfl⟩, hxI⟩
  obtain ⟨u, hus, hu⟩ := exists_irredundant_subcover K s hscover
  have hmeasure : volume K ≤ ∑ J ∈ u, volume J.carrier := by
    calc
      volume K ≤ volume (⋃ J ∈ u, J.carrier) := measure_mono hu.1
      _ ≤ ∑ J ∈ u, volume J.carrier := measure_biUnion_finset_le u _
  calc
    (lambda : ℝ≥0∞) * volume K ≤
        (lambda : ℝ≥0∞) * ∑ J ∈ u, volume J.carrier :=
      mul_le_mul_left' hmeasure _
    _ = ∑ J ∈ u, (lambda : ℝ≥0∞) * volume J.carrier := by
      simp [Finset.mul_sum]
    _ ≤ ∑ J ∈ u, ∫⁻ z in J.carrier, (f z : ℝ≥0∞) := by
      apply Finset.sum_le_sum
      intro J hJu
      have hJs : J ∈ s := hus hJu
      obtain ⟨I, hIq, hIJ⟩ := Finset.mem_map.mp hJs
      subst J
      exact I.good.le
    _ ≤ 2 * totalMass f := sum_lintegral_le_two hf hu

/-- The open good-interval envelope has weak mass at most two. -/
theorem goodEnvelope_bound {f : ℝ → ℝ≥0} {lambda : ℝ≥0}
    (hf : AEMeasurable f volume) :
    (lambda : ℝ≥0∞) * volume (goodEnvelope f lambda) ≤ 2 * totalMass f := by
  rw [(isOpen_goodEnvelope f lambda).measure_eq_iSup_isCompact volume]
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro K
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro hsub
  rw [ENNReal.mul_iSup]
  apply iSup_le
  intro hK
  exact compact_goodEnvelope_bound hf hK hsub

/-- The classical uncentered weak `(1,1)` bound, inherited by every aperture `alpha ≤ 1`. -/
theorem weakTypeBound_two {alpha : ℝ} (ha0 : 0 ≤ alpha) (ha1 : alpha ≤ 1) :
    WeakTypeBound alpha 2 := by
  intro f hf hfinite lambda hlambda
  calc
    (lambda : ℝ≥0∞) * volume (strictSuperlevel alpha f lambda) ≤
        (lambda : ℝ≥0∞) * volume (goodEnvelope f lambda) :=
      mul_le_mul_left' (measure_mono
        (strictSuperlevel_subset_goodEnvelope ha0 ha1 hlambda hfinite)) _
    _ ≤ 2 * totalMass f := goodEnvelope_bound hf

end HardyLittlewoodS1
