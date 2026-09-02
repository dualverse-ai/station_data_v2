import KakeyaNeedleC3C4.SweepCertificate

/-!
# Native-checkable five-interval sweep schedules

This is the n=5 specialization of the exact rational/Farkas sweep checker.
Ties are accepted by weak inequalities, so arrangement walls are covered.
-/

namespace KakeyaNeedleC3C4
open Set MeasureTheory
namespace SweepCertificate

set_option maxHeartbeats 2000000

def coordinateAffine5 (j : Fin 5) : RationalAffine 5 where
  constant := 0
  linear := fun i ↦ if i = j then 1 else 0

def leftLine5 (j : Fin 5) : ParametricLine 5 where
  intercept := coordinateAffine5 j
  slope := (j.1 + 1 : ℚ) / 5

def widthLine5 : ParametricLine 5 where
  intercept := affineConst 5 (1 / 5)
  slope := -1 / 5

/-- Positive exactly when the adjacent intervals overlap. -/
def overlapLine5 (a b : Fin 5) : ParametricLine 5 :=
  widthLine5.sub ((leftLine5 b).sub (leftLine5 a))

theorem eval_coordinateAffine5 (j : Fin 5) (p : Fin 5 → ℝ) :
    (coordinateAffine5 j).eval p = p j := by
  simp only [coordinateAffine5, RationalAffine.eval, Rat.cast_zero, zero_add]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    simp [hbj]
  · simp

theorem eval_leftLine5 (j : Fin 5) (p : Fin 5 → ℝ) (y : ℝ) :
    (leftLine5 j).eval p y = leftEndpoint 5 p j y := by
  rw [ParametricLine.eval]
  simp [leftLine5, eval_coordinateAffine5, leftEndpoint]

theorem eval_widthLine5 (p : Fin 5 → ℝ) (y : ℝ) :
    widthLine5.eval p y = (1 - y) / 5 := by
  simp [widthLine5, ParametricLine.eval, eval_affineConst]
  ring

structure Slab5 (m : ℕ) where
  order : Fin 5 → Fin 5
  overlap : Fin 4 → Bool
  orderCertificate : Fin 4 → SparseFarkasCertificate m
  overlapCertificate : Fin 4 → SparseFarkasCertificate m
  deriving DecidableEq

structure Certificate5 (m : ℕ) where
  slabCount : ℕ
  breakpoint : Fin (slabCount + 1) → RationalAffine 5
  breakpointOrderCertificate : Fin slabCount → SparseFarkasCertificate m
  slab : Fin slabCount → Slab5 m
  deriving DecidableEq

def adjacentOrderLine5 {m : ℕ} (s : Slab5 m) (r : Fin 4) : ParametricLine 5 :=
  (leftLine5 (s.order r.succ)).sub (leftLine5 (s.order r.castSucc))

def signedOverlapLine5 {m : ℕ} (s : Slab5 m) (r : Fin 4) : ParametricLine 5 :=
  let gap := overlapLine5 (s.order r.castSucc) (s.order r.succ)
  if s.overlap r then gap else gap.neg

def Valid5 {m : ℕ} (c : Certificate5 m) (P : RationalPolyhedron 5 m) : Prop :=
  0 < c.slabCount ∧
  c.breakpoint 0 = affineConst 5 0 ∧
  c.breakpoint (Fin.last c.slabCount) = affineConst 5 1 ∧
  (∀ i, (c.breakpointOrderCertificate i).checkImplication P
    (affineSub (c.breakpoint i.succ) (c.breakpoint i.castSucc)) = true) ∧
  (∀ i a b, (c.slab i).order a = (c.slab i).order b → a = b) ∧
  (∀ i r, ((c.slab i).orderCertificate r).checkImplication P
    (selectedEndpoint (adjacentOrderLine5 (c.slab i) r)
      (c.breakpoint i.castSucc) (c.breakpoint i.succ)) = true) ∧
  (∀ i r, ((c.slab i).overlapCertificate r).checkImplication P
    (selectedEndpoint (signedOverlapLine5 (c.slab i) r)
      (c.breakpoint i.castSucc) (c.breakpoint i.succ)) = true)

def check5 {m : ℕ} (c : Certificate5 m) (P : RationalPolyhedron 5 m) : Bool :=
  decide (0 < c.slabCount) &&
  decide (c.breakpoint 0 = affineConst 5 0) &&
  decide (c.breakpoint (Fin.last c.slabCount) = affineConst 5 1) &&
  finAll (fun i ↦
    (c.breakpointOrderCertificate i).checkImplication P
      (affineSub (c.breakpoint i.succ) (c.breakpoint i.castSucc))) &&
  finAll (fun i ↦ finAll (fun a ↦
    finAll (fun b ↦
      decide ((c.slab i).order a = (c.slab i).order b → a = b)))) &&
  finAll (fun i ↦ finAll (fun r ↦
    ((c.slab i).orderCertificate r).checkImplication P
      (selectedEndpoint (adjacentOrderLine5 (c.slab i) r)
        (c.breakpoint i.castSucc) (c.breakpoint i.succ)))) &&
  finAll (fun i ↦ finAll (fun r ↦
    ((c.slab i).overlapCertificate r).checkImplication P
      (selectedEndpoint (signedOverlapLine5 (c.slab i) r)
        (c.breakpoint i.castSucc) (c.breakpoint i.succ))))

theorem valid5_of_check {m : ℕ} {c : Certificate5 m}
    {P : RationalPolyhedron 5 m} (h : check5 c P = true) : Valid5 c P :=
  by
    simp only [check5, Bool.and_eq_true, decide_eq_true_eq,
      finAll_eq_true] at h
    rcases h with ⟨⟨⟨⟨⟨hab, hc⟩, hd⟩, he⟩, hf⟩, hg⟩
    rcases hab with ⟨ha, hb⟩
    exact ⟨ha, hb, hc, hd, he, hf, hg⟩

def zeroLine5 : ParametricLine 5 where
  intercept := affineZero 5
  slope := 0

def baseSliceLine5 : ParametricLine 5 where
  intercept := affineConst 5 1
  slope := -1

def overlapContribution5 {m : ℕ} (s : Slab5 m) (r : Fin 4) :
    ParametricLine 5 :=
  if s.overlap r then overlapLine5 (s.order r.castSucc) (s.order r.succ)
  else zeroLine5

/-- The affine slice formula represented by one accepted slab. -/
def slabLine5 {m : ℕ} (s : Slab5 m) : ParametricLine 5 :=
  (((baseSliceLine5.sub (overlapContribution5 s 0)).sub
    (overlapContribution5 s 1)).sub (overlapContribution5 s 2)).sub
      (overlapContribution5 s 3)

theorem eval_overlapLine5 (a b : Fin 5) (p : Fin 5 → ℝ) (y : ℝ) :
    (overlapLine5 a b).eval p y =
      (1 - y) / 5 - (leftEndpoint 5 p b y - leftEndpoint 5 p a y) := by
  rw [overlapLine5, ParametricLine.eval_sub, eval_widthLine5,
    ParametricLine.eval_sub, eval_leftLine5, eval_leftLine5]

theorem eval_baseSliceLine5 (p : Fin 5 → ℝ) (y : ℝ) :
    baseSliceLine5.eval p y = 1 - y := by
  simp [baseSliceLine5, ParametricLine.eval, eval_affineConst]
  ring

theorem eval_zeroLine5 (p : Fin 5 → ℝ) (y : ℝ) :
    zeroLine5.eval p y = 0 := by
  simp [zeroLine5, ParametricLine.eval, eval_affineZero]

/-- Soundness of the consecutive breakpoint certificate at a parameter point. -/
theorem breakpoint_order_sound5 {m : ℕ} {c : Certificate5 m}
    {P : RationalPolyhedron 5 m} (hv : Valid5 c P)
    {p : Fin 5 → ℝ} (hp : p ∈ P.carrier) (i : Fin c.slabCount) :
    (c.breakpoint i.castSucc).eval p ≤ (c.breakpoint i.succ).eval p := by
  have h := SparseFarkasCertificate.checkImplication_sound (hv.2.2.2.1 i) p hp
  simpa [eval_affineSub] using h

/-- Exact schedule classification on a single closed slab. -/
theorem slab_slice_eq5 {m : ℕ} {c : Certificate5 m}
    {P : RationalPolyhedron 5 m} (hv : Valid5 c P)
    {p : Fin 5 → ℝ} (hp : p ∈ P.carrier) (i : Fin c.slabCount)
    (hwithin : Icc ((c.breakpoint i.castSucc).eval p)
      ((c.breakpoint i.succ).eval p) ⊆ Icc (0 : ℝ) 1) :
    EqOn (sliceLength 5 p) (fun y ↦ (slabLine5 (c.slab i)).eval p y)
      (Icc ((c.breakpoint i.castSucc).eval p)
        ((c.breakpoint i.succ).eval p)) := by
  intro y hy
  let s := c.slab i
  have horderSelected (r : Fin 4) :
      0 ≤ (selectedEndpoint (adjacentOrderLine5 s r)
        (c.breakpoint i.castSucc) (c.breakpoint i.succ)).eval p :=
    SparseFarkasCertificate.checkImplication_sound (hv.2.2.2.2.2.1 i r) p hp
  have hordered (r : Fin 4) :
      leftEndpoint 5 p (s.order r.castSucc) y ≤
        leftEndpoint 5 p (s.order r.succ) y := by
    have hline := ParametricLine.nonneg_on_Icc_of_selected_endpoint
      (adjacentOrderLine5 s r) (c.breakpoint i.castSucc)
      (c.breakpoint i.succ) p (by
        simpa only [selectedEndpoint] using horderSelected r) y hy
    simpa [adjacentOrderLine5, ParametricLine.eval_sub, eval_leftLine5] using hline
  have hoverlapSelected (r : Fin 4) :
      0 ≤ (selectedEndpoint (signedOverlapLine5 s r)
        (c.breakpoint i.castSucc) (c.breakpoint i.succ)).eval p :=
    SparseFarkasCertificate.checkImplication_sound (hv.2.2.2.2.2.2 i r) p hp
  have hsigned (r : Fin 4) : 0 ≤ (signedOverlapLine5 s r).eval p y :=
    ParametricLine.nonneg_on_Icc_of_selected_endpoint
      (signedOverlapLine5 s r) (c.breakpoint i.castSucc)
      (c.breakpoint i.succ) p (by
        simpa only [selectedEndpoint] using hoverlapSelected r) y hy
  have hgap (r : Fin 4) :
      if s.overlap r then
        0 ≤ (overlapLine5 (s.order r.castSucc) (s.order r.succ)).eval p y
      else (overlapLine5 (s.order r.castSucc) (s.order r.succ)).eval p y ≤ 0 := by
    by_cases hr : s.overlap r
    · simpa [hr, signedOverlapLine5] using hsigned r
    · have := hsigned r
      simp [hr, signedOverlapLine5, ParametricLine.eval_neg] at this ⊢
      linarith
  have hinjective : Function.Injective s.order := hv.2.2.2.2.1 i
  let σ : Equiv.Perm (Fin 5) := Equiv.ofBijective s.order
    ⟨hinjective, Finite.injective_iff_surjective.mp hinjective⟩
  have hsigma (r : Fin 5) : σ r = s.order r := rfl
  have hy01 : y ∈ Icc (0 : ℝ) 1 := hwithin hy
  rw [sliceLength_five_of_order p y hy01 σ]
  · simp_rw [hsigma]
    have hg0 := hgap 0
    have hg1 := hgap 1
    have hg2 := hgap 2
    have hg3 := hgap 3
    simp only [s] at hg0 hg1 hg2 hg3 ⊢
    cases h0 : (c.slab i).overlap 0 <;>
      cases h1 : (c.slab i).overlap 1 <;>
      cases h2 : (c.slab i).overlap 2 <;>
      cases h3 : (c.slab i).overlap 3 <;>
      simp_all [slabLine5, overlapContribution5,
        ParametricLine.eval_sub, eval_baseSliceLine5, eval_overlapLine5,
        eval_zeroLine5] <;> ring
  · simpa [hsigma] using hordered 0
  · simpa [hsigma] using hordered 1
  · simpa [hsigma] using hordered 2
  · simpa [hsigma] using hordered 3

def breakpointNat5 {m : ℕ} (c : Certificate5 m) (p : Fin 5 → ℝ)
    (r : ℕ) : ℝ :=
  if hr : r ≤ c.slabCount then
    (c.breakpoint ⟨r, Nat.lt_succ_iff.mpr hr⟩).eval p
  else 1

def slabAAtNat5 {m : ℕ} (c : Certificate5 m) (p : Fin 5 → ℝ)
    (r : ℕ) : ℝ :=
  if hr : r < c.slabCount then
    (slabLine5 (c.slab ⟨r, hr⟩)).intercept.eval p
  else 0

def slabBAtNat5 {m : ℕ} (c : Certificate5 m) (r : ℕ) : ℝ :=
  if hr : r < c.slabCount then
    ((slabLine5 (c.slab ⟨r, hr⟩)).slope : ℝ)
  else 0

theorem breakpointNat5_zero {m : ℕ} {c : Certificate5 m}
    {P : RationalPolyhedron 5 m} (hv : Valid5 c P) (p : Fin 5 → ℝ) :
    breakpointNat5 c p 0 = 0 := by
  simp [breakpointNat5, hv.2.1, eval_affineConst]

theorem breakpointNat5_last {m : ℕ} {c : Certificate5 m}
    {P : RationalPolyhedron 5 m} (hv : Valid5 c P) (p : Fin 5 → ℝ) :
    breakpointNat5 c p c.slabCount = 1 := by
  rw [show breakpointNat5 c p c.slabCount =
      (c.breakpoint (Fin.last c.slabCount)).eval p by
    simp [breakpointNat5]
    congr]
  rw [hv.2.2.1, eval_affineConst]
  norm_num

theorem breakpointNat5_step {m : ℕ} {c : Certificate5 m}
    {P : RationalPolyhedron 5 m} (hv : Valid5 c P)
    {p : Fin 5 → ℝ} (hp : p ∈ P.carrier) (r : ℕ) :
    breakpointNat5 c p r ≤ breakpointNat5 c p (r + 1) := by
  by_cases hr : r < c.slabCount
  · have hrle : r ≤ c.slabCount := hr.le
    have hrsle : r + 1 ≤ c.slabCount := hr
    simpa [breakpointNat5, hrle, hrsle] using
      breakpoint_order_sound5 hv hp (⟨r, hr⟩ : Fin c.slabCount)
  · have hkr : c.slabCount ≤ r := Nat.le_of_not_gt hr
    by_cases heq : r = c.slabCount
    · subst r
      rw [breakpointNat5_last hv p]
      simp [breakpointNat5]
    · have hgt : c.slabCount < r := lt_of_le_of_ne hkr (Ne.symm heq)
      have hnle : ¬r ≤ c.slabCount := Nat.not_le.mpr hgt
      have hsnle : ¬r + 1 ≤ c.slabCount :=
        Nat.not_le.mpr (hgt.trans (Nat.lt_succ_self r))
      simp [breakpointNat5, hnle, hsnle]

/-! ## Exact affine-on-slab integration -/

/-- The exact affine-on-slab integral emitted by the checker; all breakpoints and
coefficients are evaluations of rational affine data. -/
theorem sliceArea_eq_checkedSweep_five {m : ℕ} {c : Certificate5 m}
    {P : RationalPolyhedron 5 m} (hcheck : check5 c P = true)
    {p : Fin 5 → ℝ} (hp : p ∈ P.carrier) :
    sliceArea 5 p = ∑ r ∈ Finset.range c.slabCount,
      (slabAAtNat5 c p r * (breakpointNat5 c p (r + 1) - breakpointNat5 c p r) +
        slabBAtNat5 c r *
          (breakpointNat5 c p (r + 1) ^ 2 - breakpointNat5 c p r ^ 2) / 2) := by
  have hv : Valid5 c P := valid5_of_check hcheck
  have hmono : Monotone (breakpointNat5 c p) :=
    monotone_nat_of_le_succ (breakpointNat5_step hv hp)
  apply sliceArea_eq_sum_piecewise_affine 5 c.slabCount p
    (breakpointNat5 c p) (slabAAtNat5 c p) (slabBAtNat5 c)
  · exact breakpointNat5_zero hv p
  · exact breakpointNat5_last hv p
  · intro r hr
    exact breakpointNat5_step hv hp r
  · intro r hr
    have hrle : r ≤ c.slabCount := hr.le
    have hrsle : r + 1 ≤ c.slabCount := hr
    have hzero_le : 0 ≤ breakpointNat5 c p r := by
      rw [← breakpointNat5_zero hv p]
      exact hmono (Nat.zero_le r)
    have hle_one : breakpointNat5 c p (r + 1) ≤ 1 := by
      rw [← breakpointNat5_last hv p]
      exact hmono hrsle
    have hwithin : Icc (breakpointNat5 c p r) (breakpointNat5 c p (r + 1)) ⊆
        Icc (0 : ℝ) 1 := by
      intro y hy
      exact ⟨hzero_le.trans hy.1, hy.2.trans hle_one⟩
    have hs := slab_slice_eq5 hv hp (⟨r, hr⟩ : Fin c.slabCount) (by
      simpa [breakpointNat5, hrle, hrsle] using hwithin)
    simpa [slabAAtNat5, slabBAtNat5, breakpointNat5, hr, hrle, hrsle,
      ParametricLine.eval] using hs

/-! ## Exact quadratic assembled from the checked schedule -/

def integratedQuadratic5 {m : ℕ} (c : Certificate5 m) : RationalQuadratic 5 :=
  RationalQuadratic.sum (List.ofFn fun i : Fin c.slabCount ↦
    lineIntegralQuadratic (slabLine5 (c.slab i))
      (c.breakpoint i.castSucc) (c.breakpoint i.succ))

theorem eval_integratedQuadratic5 {m : ℕ} (c : Certificate5 m)
    (p : Fin 5 → ℝ) :
    (integratedQuadratic5 c).eval p = ∑ r ∈ Finset.range c.slabCount,
      (slabAAtNat5 c p r * (breakpointNat5 c p (r + 1) - breakpointNat5 c p r) +
        slabBAtNat5 c r *
          (breakpointNat5 c p (r + 1) ^ 2 - breakpointNat5 c p r ^ 2) / 2) := by
  rw [integratedQuadratic5, RationalQuadratic.eval_sum]
  simp only [List.map_ofFn, List.sum_ofFn]
  rw [← Fin.sum_univ_eq_sum_range (fun r ↦
    slabAAtNat5 c p r * (breakpointNat5 c p (r + 1) - breakpointNat5 c p r) +
      slabBAtNat5 c r *
        (breakpointNat5 c p (r + 1) ^ 2 - breakpointNat5 c p r ^ 2) / 2)
    c.slabCount]
  apply Finset.sum_congr rfl
  intro i _
  have hr : i.1 < c.slabCount := i.2
  have hrsle : i.1 + 1 ≤ c.slabCount := i.2
  have hsucc : (⟨i.1 + 1, Nat.lt_succ_iff.mpr hrsle⟩ :
      Fin (c.slabCount + 1)) = i.succ := by ext; rfl
  have hcast : (⟨i.1, Nat.lt_succ_iff.mpr hr.le⟩ :
      Fin (c.slabCount + 1)) = i.castSucc := by ext; rfl
  change (lineIntegralQuadratic (slabLine5 (c.slab i))
    (c.breakpoint i.castSucc) (c.breakpoint i.succ)).eval p = _
  rw [eval_lineIntegralQuadratic]
  simp [slabAAtNat5, slabBAtNat5, breakpointNat5, hr, hr.le, hrsle,
    hsucc, hcast]

/-- Final exact semantic bridge: an accepted native sweep certificate proves
that the genuine slice integral is the evaluation of its computed rational
quadratic. -/
theorem sliceArea_eq_integratedQuadratic_five {m : ℕ} {c : Certificate5 m}
    {P : RationalPolyhedron 5 m} (hcheck : check5 c P = true)
    {p : Fin 5 → ℝ} (hp : p ∈ P.carrier) :
    sliceArea 5 p = (integratedQuadratic5 c).eval p := by
  rw [sliceArea_eq_checkedSweep_five hcheck hp, eval_integratedQuadratic5]

end SweepCertificate
end KakeyaNeedleC3C4
