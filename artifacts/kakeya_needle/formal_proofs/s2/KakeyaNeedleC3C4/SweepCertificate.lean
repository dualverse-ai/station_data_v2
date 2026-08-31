import KakeyaNeedleC3C4.SweepIntegration
import KakeyaNeedleC3C4.FarkasChecker
import KakeyaNeedleC3C4.RationalCertificateChecker

/-!
# Native-checkable four-interval sweep schedules

This module checks the combinatorial sweep data using only rational
arithmetic and sparse Farkas certificates.  Its soundness theorem turns an
accepted schedule into the exact piecewise-affine integral for `sliceArea 4`.
Ties are deliberately accepted throughout: every comparison is non-strict.
-/

namespace KakeyaNeedleC3C4

open Set MeasureTheory

namespace SweepCertificate

/-! ## Exact affine arithmetic -/

def affineZero (n : ℕ) : RationalAffine n where
  constant := 0
  linear := fun _ ↦ 0

def affineConst (n : ℕ) (c : ℚ) : RationalAffine n where
  constant := c
  linear := fun _ ↦ 0

def affineAdd {n : ℕ} (a b : RationalAffine n) : RationalAffine n where
  constant := a.constant + b.constant
  linear := fun i ↦ a.linear i + b.linear i

def affineNeg {n : ℕ} (a : RationalAffine n) : RationalAffine n where
  constant := -a.constant
  linear := fun i ↦ -a.linear i

def affineSub {n : ℕ} (a b : RationalAffine n) : RationalAffine n :=
  affineAdd a (affineNeg b)

def affineScale {n : ℕ} (c : ℚ) (a : RationalAffine n) : RationalAffine n where
  constant := c * a.constant
  linear := fun i ↦ c * a.linear i

theorem eval_affineZero {n : ℕ} (p : Fin n → ℝ) :
    (affineZero n).eval p = 0 := by simp [affineZero, RationalAffine.eval]

theorem eval_affineConst {n : ℕ} (c : ℚ) (p : Fin n → ℝ) :
    (affineConst n c).eval p = (c : ℝ) := by
  simp [affineConst, RationalAffine.eval]

theorem eval_affineAdd {n : ℕ} (a b : RationalAffine n) (p : Fin n → ℝ) :
    (affineAdd a b).eval p = a.eval p + b.eval p := by
  simp only [affineAdd, RationalAffine.eval, Rat.cast_add, add_mul,
    Finset.sum_add_distrib]
  ring

theorem eval_affineNeg {n : ℕ} (a : RationalAffine n) (p : Fin n → ℝ) :
    (affineNeg a).eval p = -a.eval p := by
  simp only [affineNeg, RationalAffine.eval, Rat.cast_neg, neg_mul,
    Finset.sum_neg_distrib]
  ring

theorem eval_affineSub {n : ℕ} (a b : RationalAffine n) (p : Fin n → ℝ) :
    (affineSub a b).eval p = a.eval p - b.eval p := by
  rw [affineSub, eval_affineAdd, eval_affineNeg]
  ring

theorem eval_affineScale {n : ℕ} (c : ℚ) (a : RationalAffine n)
    (p : Fin n → ℝ) :
    (affineScale c a).eval p = (c : ℝ) * a.eval p := by
  simp only [affineScale, RationalAffine.eval, Rat.cast_mul]
  have hsum : (∑ i, (c : ℝ) * (a.linear i : ℝ) * p i) =
      (c : ℝ) * ∑ i, (a.linear i : ℝ) * p i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  ring

/-- A function affine in the sweep variable `y`, whose intercept is affine in
the position parameters. -/
structure ParametricLine (n : ℕ) where
  intercept : RationalAffine n
  slope : ℚ
  deriving DecidableEq

namespace ParametricLine

def eval {n : ℕ} (f : ParametricLine n) (p : Fin n → ℝ) (y : ℝ) : ℝ :=
  f.intercept.eval p + (f.slope : ℝ) * y

def add {n : ℕ} (f g : ParametricLine n) : ParametricLine n where
  intercept := affineAdd f.intercept g.intercept
  slope := f.slope + g.slope

def neg {n : ℕ} (f : ParametricLine n) : ParametricLine n where
  intercept := affineNeg f.intercept
  slope := -f.slope

def sub {n : ℕ} (f g : ParametricLine n) : ParametricLine n := add f (neg g)

/-- Substitute a parameter-affine breakpoint into a parametric line. -/
def substBreakpoint {n : ℕ} (f : ParametricLine n)
    (b : RationalAffine n) : RationalAffine n :=
  affineAdd f.intercept (affineScale f.slope b)

theorem eval_add {n : ℕ} (f g : ParametricLine n) (p : Fin n → ℝ) (y : ℝ) :
    (f.add g).eval p y = f.eval p y + g.eval p y := by
  simp [add, eval, eval_affineAdd]
  ring

theorem eval_neg {n : ℕ} (f : ParametricLine n) (p : Fin n → ℝ) (y : ℝ) :
    f.neg.eval p y = -f.eval p y := by
  simp [neg, eval, eval_affineNeg]
  ring

theorem eval_sub {n : ℕ} (f g : ParametricLine n) (p : Fin n → ℝ) (y : ℝ) :
    (f.sub g).eval p y = f.eval p y - g.eval p y := by
  rw [sub, eval_add, eval_neg]
  ring

theorem eval_substBreakpoint {n : ℕ} (f : ParametricLine n)
    (b : RationalAffine n) (p : Fin n → ℝ) :
    (f.substBreakpoint b).eval p = f.eval p (b.eval p) := by
  simp [substBreakpoint, eval, eval_affineAdd, eval_affineScale]

/-- For an affine line, the endpoint selected by the sign of its slope is a
certified minimum on the whole closed slab. -/
theorem nonneg_on_Icc_of_selected_endpoint {n : ℕ} (f : ParametricLine n)
    (lo hi : RationalAffine n) (p : Fin n → ℝ)
    (hselected : 0 ≤ (if 0 ≤ f.slope then f.substBreakpoint lo
      else f.substBreakpoint hi).eval p) :
    ∀ y ∈ Icc (lo.eval p) (hi.eval p), 0 ≤ f.eval p y := by
  intro y hy
  by_cases hs : 0 ≤ f.slope
  · simp only [hs, if_true, eval_substBreakpoint] at hselected
    have hsreal : (0 : ℝ) ≤ (f.slope : ℝ) := by exact_mod_cast hs
    have hmono := mul_le_mul_of_nonneg_left hy.1 hsreal
    dsimp [eval] at hselected ⊢
    linarith
  · simp only [hs, if_false, eval_substBreakpoint] at hselected
    have hsreal : (f.slope : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hs)
    have hmono := mul_le_mul_of_nonpos_left hy.2 hsreal
    dsimp [eval] at hselected ⊢
    linarith

end ParametricLine

/-! ## Four-interval schedule data and executable checker -/

def coordinateAffine (j : Fin 4) : RationalAffine 4 where
  constant := 0
  linear := fun i ↦ if i = j then 1 else 0

def leftLine (j : Fin 4) : ParametricLine 4 where
  intercept := coordinateAffine j
  slope := (j.1 + 1 : ℚ) / 4

def widthLine : ParametricLine 4 where
  intercept := affineConst 4 (1 / 4)
  slope := -1 / 4

/-- Positive exactly when the adjacent intervals overlap. -/
def overlapLine (a b : Fin 4) : ParametricLine 4 :=
  widthLine.sub ((leftLine b).sub (leftLine a))

theorem eval_coordinateAffine (j : Fin 4) (p : Fin 4 → ℝ) :
    (coordinateAffine j).eval p = p j := by
  simp only [coordinateAffine, RationalAffine.eval, Rat.cast_zero, zero_add]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    simp [hbj]
  · simp

theorem eval_leftLine (j : Fin 4) (p : Fin 4 → ℝ) (y : ℝ) :
    (leftLine j).eval p y = leftEndpoint 4 p j y := by
  rw [ParametricLine.eval]
  simp [leftLine, eval_coordinateAffine, leftEndpoint]

theorem eval_widthLine (p : Fin 4 → ℝ) (y : ℝ) :
    widthLine.eval p y = (1 - y) / 4 := by
  simp [widthLine, ParametricLine.eval, eval_affineConst]
  ring

structure Slab4 (m : ℕ) where
  order : Fin 4 → Fin 4
  overlap : Fin 3 → Bool
  orderCertificate : Fin 3 → SparseFarkasCertificate m
  overlapCertificate : Fin 3 → SparseFarkasCertificate m
  deriving DecidableEq

structure Certificate4 (m : ℕ) where
  slabCount : ℕ
  breakpoint : Fin (slabCount + 1) → RationalAffine 4
  breakpointOrderCertificate : Fin slabCount → SparseFarkasCertificate m
  slab : Fin slabCount → Slab4 m
  deriving DecidableEq

def selectedEndpoint {n : ℕ} (f : ParametricLine n)
    (lo hi : RationalAffine n) : RationalAffine n :=
  if 0 ≤ f.slope then f.substBreakpoint lo else f.substBreakpoint hi

def adjacentOrderLine {m : ℕ} (s : Slab4 m) (r : Fin 3) : ParametricLine 4 :=
  (leftLine (s.order r.succ)).sub (leftLine (s.order r.castSucc))

def signedOverlapLine {m : ℕ} (s : Slab4 m) (r : Fin 3) : ParametricLine 4 :=
  let gap := overlapLine (s.order r.castSucc) (s.order r.succ)
  if s.overlap r then gap else gap.neg

def Valid {m : ℕ} (c : Certificate4 m) (P : RationalPolyhedron 4 m) : Prop :=
  0 < c.slabCount ∧
  c.breakpoint 0 = affineConst 4 0 ∧
  c.breakpoint (Fin.last c.slabCount) = affineConst 4 1 ∧
  (∀ i, (c.breakpointOrderCertificate i).checkImplication P
    (affineSub (c.breakpoint i.succ) (c.breakpoint i.castSucc)) = true) ∧
  (∀ i a b, (c.slab i).order a = (c.slab i).order b → a = b) ∧
  (∀ i r, ((c.slab i).orderCertificate r).checkImplication P
    (selectedEndpoint (adjacentOrderLine (c.slab i) r)
      (c.breakpoint i.castSucc) (c.breakpoint i.succ)) = true) ∧
  (∀ i r, ((c.slab i).overlapCertificate r).checkImplication P
    (selectedEndpoint (signedOverlapLine (c.slab i) r)
      (c.breakpoint i.castSucc) (c.breakpoint i.succ)) = true)

def finAll {n : ℕ} (f : Fin n → Bool) : Bool := (List.ofFn f).all id

theorem finAll_eq_true {n : ℕ} {f : Fin n → Bool} :
    finAll f = true ↔ ∀ i, f i = true := by
  rw [finAll, List.all_eq_true]
  constructor
  · intro h i
    exact h (f i) (by simp)
  · intro h z hz
    simp only [List.mem_ofFn] at hz
    obtain ⟨i, rfl⟩ := hz
    exact h i

/-- Entirely executable rational/Farkas schedule checker. -/
def check {m : ℕ} (c : Certificate4 m) (P : RationalPolyhedron 4 m) : Bool :=
  decide (0 < c.slabCount) &&
  decide (c.breakpoint 0 = affineConst 4 0) &&
  decide (c.breakpoint (Fin.last c.slabCount) = affineConst 4 1) &&
  finAll (fun i ↦
    (c.breakpointOrderCertificate i).checkImplication P
      (affineSub (c.breakpoint i.succ) (c.breakpoint i.castSucc))) &&
  finAll (fun i ↦ finAll (fun a ↦
    finAll (fun b ↦
      decide ((c.slab i).order a = (c.slab i).order b → a = b)))) &&
  finAll (fun i ↦ finAll (fun r ↦
    ((c.slab i).orderCertificate r).checkImplication P
      (selectedEndpoint (adjacentOrderLine (c.slab i) r)
        (c.breakpoint i.castSucc) (c.breakpoint i.succ)))) &&
  finAll (fun i ↦ finAll (fun r ↦
    ((c.slab i).overlapCertificate r).checkImplication P
      (selectedEndpoint (signedOverlapLine (c.slab i) r)
        (c.breakpoint i.castSucc) (c.breakpoint i.succ))))

theorem valid_of_check {m : ℕ} {c : Certificate4 m}
    {P : RationalPolyhedron 4 m} (h : check c P = true) : Valid c P :=
  by
    simp only [check, Bool.and_eq_true, decide_eq_true_eq,
      finAll_eq_true] at h
    rcases h with ⟨⟨⟨⟨⟨hab, hc⟩, hd⟩, he⟩, hf⟩, hg⟩
    rcases hab with ⟨ha, hb⟩
    exact ⟨ha, hb, hc, hd, he, hf, hg⟩

def zeroLine : ParametricLine 4 where
  intercept := affineZero 4
  slope := 0

def baseSliceLine : ParametricLine 4 where
  intercept := affineConst 4 1
  slope := -1

def overlapContribution {m : ℕ} (s : Slab4 m) (r : Fin 3) :
    ParametricLine 4 :=
  if s.overlap r then overlapLine (s.order r.castSucc) (s.order r.succ)
  else zeroLine

/-- The affine slice formula represented by one accepted slab. -/
def slabLine {m : ℕ} (s : Slab4 m) : ParametricLine 4 :=
  ((baseSliceLine.sub (overlapContribution s 0)).sub
    (overlapContribution s 1)).sub (overlapContribution s 2)

theorem eval_overlapLine (a b : Fin 4) (p : Fin 4 → ℝ) (y : ℝ) :
    (overlapLine a b).eval p y =
      (1 - y) / 4 - (leftEndpoint 4 p b y - leftEndpoint 4 p a y) := by
  rw [overlapLine, ParametricLine.eval_sub, eval_widthLine,
    ParametricLine.eval_sub, eval_leftLine, eval_leftLine]

theorem eval_baseSliceLine (p : Fin 4 → ℝ) (y : ℝ) :
    baseSliceLine.eval p y = 1 - y := by
  simp [baseSliceLine, ParametricLine.eval, eval_affineConst]
  ring

theorem eval_zeroLine (p : Fin 4 → ℝ) (y : ℝ) :
    zeroLine.eval p y = 0 := by
  simp [zeroLine, ParametricLine.eval, eval_affineZero]

/-- Soundness of the consecutive breakpoint certificate at a parameter point. -/
theorem breakpoint_order_sound {m : ℕ} {c : Certificate4 m}
    {P : RationalPolyhedron 4 m} (hv : Valid c P)
    {p : Fin 4 → ℝ} (hp : p ∈ P.carrier) (i : Fin c.slabCount) :
    (c.breakpoint i.castSucc).eval p ≤ (c.breakpoint i.succ).eval p := by
  have h := SparseFarkasCertificate.checkImplication_sound (hv.2.2.2.1 i) p hp
  simpa [eval_affineSub] using h

/-- Exact schedule classification on a single closed slab. -/
theorem slab_slice_eq {m : ℕ} {c : Certificate4 m}
    {P : RationalPolyhedron 4 m} (hv : Valid c P)
    {p : Fin 4 → ℝ} (hp : p ∈ P.carrier) (i : Fin c.slabCount)
    (hwithin : Icc ((c.breakpoint i.castSucc).eval p)
      ((c.breakpoint i.succ).eval p) ⊆ Icc (0 : ℝ) 1) :
    EqOn (sliceLength 4 p) (fun y ↦ (slabLine (c.slab i)).eval p y)
      (Icc ((c.breakpoint i.castSucc).eval p)
        ((c.breakpoint i.succ).eval p)) := by
  intro y hy
  let s := c.slab i
  have horderSelected (r : Fin 3) :
      0 ≤ (selectedEndpoint (adjacentOrderLine s r)
        (c.breakpoint i.castSucc) (c.breakpoint i.succ)).eval p :=
    SparseFarkasCertificate.checkImplication_sound (hv.2.2.2.2.2.1 i r) p hp
  have hordered (r : Fin 3) :
      leftEndpoint 4 p (s.order r.castSucc) y ≤
        leftEndpoint 4 p (s.order r.succ) y := by
    have hline := ParametricLine.nonneg_on_Icc_of_selected_endpoint
      (adjacentOrderLine s r) (c.breakpoint i.castSucc)
      (c.breakpoint i.succ) p (by
        simpa only [selectedEndpoint] using horderSelected r) y hy
    simpa [adjacentOrderLine, ParametricLine.eval_sub, eval_leftLine] using hline
  have hoverlapSelected (r : Fin 3) :
      0 ≤ (selectedEndpoint (signedOverlapLine s r)
        (c.breakpoint i.castSucc) (c.breakpoint i.succ)).eval p :=
    SparseFarkasCertificate.checkImplication_sound (hv.2.2.2.2.2.2 i r) p hp
  have hsigned (r : Fin 3) : 0 ≤ (signedOverlapLine s r).eval p y :=
    ParametricLine.nonneg_on_Icc_of_selected_endpoint
      (signedOverlapLine s r) (c.breakpoint i.castSucc)
      (c.breakpoint i.succ) p (by
        simpa only [selectedEndpoint] using hoverlapSelected r) y hy
  have hgap (r : Fin 3) :
      if s.overlap r then
        0 ≤ (overlapLine (s.order r.castSucc) (s.order r.succ)).eval p y
      else (overlapLine (s.order r.castSucc) (s.order r.succ)).eval p y ≤ 0 := by
    by_cases hr : s.overlap r
    · simpa [hr, signedOverlapLine] using hsigned r
    · have := hsigned r
      simp [hr, signedOverlapLine, ParametricLine.eval_neg] at this ⊢
      linarith
  have hinjective : Function.Injective s.order := hv.2.2.2.2.1 i
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective s.order
    ⟨hinjective, Finite.injective_iff_surjective.mp hinjective⟩
  have hsigma (r : Fin 4) : σ r = s.order r := rfl
  have hy01 : y ∈ Icc (0 : ℝ) 1 := hwithin hy
  rw [sliceLength_four_of_order p y hy01 σ]
  · simp_rw [hsigma]
    have hg0 := hgap 0
    have hg1 := hgap 1
    have hg2 := hgap 2
    simp only [s] at hg0 hg1 hg2 ⊢
    cases h0 : (c.slab i).overlap 0 <;>
      cases h1 : (c.slab i).overlap 1 <;>
      cases h2 : (c.slab i).overlap 2 <;>
      simp_all [slabLine, overlapContribution,
        ParametricLine.eval_sub, eval_baseSliceLine, eval_overlapLine,
        eval_zeroLine] <;> ring
  · simpa [hsigma] using hordered 0
  · simpa [hsigma] using hordered 1
  · simpa [hsigma] using hordered 2

def breakpointNat {m : ℕ} (c : Certificate4 m) (p : Fin 4 → ℝ)
    (r : ℕ) : ℝ :=
  if hr : r ≤ c.slabCount then
    (c.breakpoint ⟨r, Nat.lt_succ_iff.mpr hr⟩).eval p
  else 1

def slabAAtNat {m : ℕ} (c : Certificate4 m) (p : Fin 4 → ℝ)
    (r : ℕ) : ℝ :=
  if hr : r < c.slabCount then
    (slabLine (c.slab ⟨r, hr⟩)).intercept.eval p
  else 0

def slabBAtNat {m : ℕ} (c : Certificate4 m) (r : ℕ) : ℝ :=
  if hr : r < c.slabCount then
    ((slabLine (c.slab ⟨r, hr⟩)).slope : ℝ)
  else 0

theorem breakpointNat_zero {m : ℕ} {c : Certificate4 m}
    {P : RationalPolyhedron 4 m} (hv : Valid c P) (p : Fin 4 → ℝ) :
    breakpointNat c p 0 = 0 := by
  simp [breakpointNat, hv.2.1, eval_affineConst]

theorem breakpointNat_last {m : ℕ} {c : Certificate4 m}
    {P : RationalPolyhedron 4 m} (hv : Valid c P) (p : Fin 4 → ℝ) :
    breakpointNat c p c.slabCount = 1 := by
  rw [show breakpointNat c p c.slabCount =
      (c.breakpoint (Fin.last c.slabCount)).eval p by
    simp [breakpointNat]
    congr]
  rw [hv.2.2.1, eval_affineConst]
  norm_num

theorem breakpointNat_step {m : ℕ} {c : Certificate4 m}
    {P : RationalPolyhedron 4 m} (hv : Valid c P)
    {p : Fin 4 → ℝ} (hp : p ∈ P.carrier) (r : ℕ) :
    breakpointNat c p r ≤ breakpointNat c p (r + 1) := by
  by_cases hr : r < c.slabCount
  · have hrle : r ≤ c.slabCount := hr.le
    have hrsle : r + 1 ≤ c.slabCount := hr
    simpa [breakpointNat, hrle, hrsle] using
      breakpoint_order_sound hv hp (⟨r, hr⟩ : Fin c.slabCount)
  · have hkr : c.slabCount ≤ r := Nat.le_of_not_gt hr
    by_cases heq : r = c.slabCount
    · subst r
      rw [breakpointNat_last hv p]
      simp [breakpointNat]
    · have hgt : c.slabCount < r := lt_of_le_of_ne hkr (Ne.symm heq)
      have hnle : ¬r ≤ c.slabCount := Nat.not_le.mpr hgt
      have hsnle : ¬r + 1 ≤ c.slabCount :=
        Nat.not_le.mpr (hgt.trans (Nat.lt_succ_self r))
      simp [breakpointNat, hnle, hsnle]

/-- Global soundness of an accepted sweep schedule.  The right side is the
exact affine-on-slab integral emitted by the checker; all breakpoints and
coefficients are evaluations of rational affine data. -/
theorem sliceArea_eq_checkedSweep_four {m : ℕ} {c : Certificate4 m}
    {P : RationalPolyhedron 4 m} (hcheck : check c P = true)
    {p : Fin 4 → ℝ} (hp : p ∈ P.carrier) :
    sliceArea 4 p = ∑ r ∈ Finset.range c.slabCount,
      (slabAAtNat c p r * (breakpointNat c p (r + 1) - breakpointNat c p r) +
        slabBAtNat c r *
          (breakpointNat c p (r + 1) ^ 2 - breakpointNat c p r ^ 2) / 2) := by
  have hv : Valid c P := valid_of_check hcheck
  have hmono : Monotone (breakpointNat c p) :=
    monotone_nat_of_le_succ (breakpointNat_step hv hp)
  apply sliceArea_eq_sum_piecewise_affine 4 c.slabCount p
    (breakpointNat c p) (slabAAtNat c p) (slabBAtNat c)
  · exact breakpointNat_zero hv p
  · exact breakpointNat_last hv p
  · intro r hr
    exact breakpointNat_step hv hp r
  · intro r hr
    have hrle : r ≤ c.slabCount := hr.le
    have hrsle : r + 1 ≤ c.slabCount := hr
    have hzero_le : 0 ≤ breakpointNat c p r := by
      rw [← breakpointNat_zero hv p]
      exact hmono (Nat.zero_le r)
    have hle_one : breakpointNat c p (r + 1) ≤ 1 := by
      rw [← breakpointNat_last hv p]
      exact hmono hrsle
    have hwithin : Icc (breakpointNat c p r) (breakpointNat c p (r + 1)) ⊆
        Icc (0 : ℝ) 1 := by
      intro y hy
      exact ⟨hzero_le.trans hy.1, hy.2.trans hle_one⟩
    have hs := slab_slice_eq hv hp (⟨r, hr⟩ : Fin c.slabCount) (by
      simpa [breakpointNat, hrle, hrsle] using hwithin)
    simpa [slabAAtNat, slabBAtNat, breakpointNat, hr, hrle, hrsle,
      ParametricLine.eval] using hs

/-! ## Exact quadratic assembled from the checked schedule -/

def quadraticScale {n : ℕ} (a : ℚ) (q : RationalQuadratic n) :
    RationalQuadratic n where
  constant := a * q.constant
  linear := fun i ↦ a * q.linear i
  quadratic := fun i j ↦ a * q.quadratic i j

theorem eval_quadraticScale {n : ℕ} (a : ℚ) (q : RationalQuadratic n)
    (p : Fin n → ℝ) :
    (quadraticScale a q).eval p = (a : ℝ) * q.eval p := by
  simp only [quadraticScale, RationalQuadratic.eval, Rat.cast_mul]
  have hlinear : (∑ i, (a : ℝ) * (q.linear i : ℝ) * p i) =
      (a : ℝ) * ∑ i, (q.linear i : ℝ) * p i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hquadratic :
      (∑ i, ∑ j, (a : ℝ) * (q.quadratic i j : ℝ) * p i * p j) =
        (a : ℝ) * ∑ i, ∑ j, (q.quadratic i j : ℝ) * p i * p j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hlinear, hquadratic]
  ring

/-- Integral of `line` between the two parameter-affine breakpoints. -/
def lineIntegralQuadratic {n : ℕ} (line : ParametricLine n)
    (lo hi : RationalAffine n) : RationalQuadratic n :=
  RationalQuadratic.add
    (RationalQuadratic.mulAffine line.intercept (affineSub hi lo))
    (quadraticScale (line.slope / 2)
      (RationalQuadratic.add (RationalQuadratic.mulAffine hi hi)
        (RationalQuadratic.neg (RationalQuadratic.mulAffine lo lo))))

theorem eval_lineIntegralQuadratic {n : ℕ} (line : ParametricLine n)
    (lo hi : RationalAffine n) (p : Fin n → ℝ) :
    (lineIntegralQuadratic line lo hi).eval p =
      line.intercept.eval p * (hi.eval p - lo.eval p) +
        (line.slope : ℝ) * (hi.eval p ^ 2 - lo.eval p ^ 2) / 2 := by
  simp [lineIntegralQuadratic, RationalQuadratic.eval_add,
    RationalQuadratic.eval_mulAffine, RationalQuadratic.eval_neg,
    eval_affineSub, eval_quadraticScale]
  ring

/-- The exact rational quadratic produced by all slabs of a schedule. -/
def integratedQuadratic {m : ℕ} (c : Certificate4 m) : RationalQuadratic 4 :=
  RationalQuadratic.sum (List.ofFn fun i : Fin c.slabCount ↦
    lineIntegralQuadratic (slabLine (c.slab i))
      (c.breakpoint i.castSucc) (c.breakpoint i.succ))

theorem eval_integratedQuadratic {m : ℕ} (c : Certificate4 m)
    (p : Fin 4 → ℝ) :
    (integratedQuadratic c).eval p = ∑ r ∈ Finset.range c.slabCount,
      (slabAAtNat c p r * (breakpointNat c p (r + 1) - breakpointNat c p r) +
        slabBAtNat c r *
          (breakpointNat c p (r + 1) ^ 2 - breakpointNat c p r ^ 2) / 2) := by
  rw [integratedQuadratic, RationalQuadratic.eval_sum]
  simp only [List.map_ofFn, List.sum_ofFn]
  rw [← Fin.sum_univ_eq_sum_range (fun r ↦
    slabAAtNat c p r * (breakpointNat c p (r + 1) - breakpointNat c p r) +
      slabBAtNat c r *
        (breakpointNat c p (r + 1) ^ 2 - breakpointNat c p r ^ 2) / 2)
    c.slabCount]
  apply Finset.sum_congr rfl
  intro i _
  have hr : i.1 < c.slabCount := i.2
  have hrsle : i.1 + 1 ≤ c.slabCount := i.2
  have hsucc : (⟨i.1 + 1, Nat.lt_succ_iff.mpr hrsle⟩ :
      Fin (c.slabCount + 1)) = i.succ := by ext; rfl
  have hcast : (⟨i.1, Nat.lt_succ_iff.mpr hr.le⟩ :
      Fin (c.slabCount + 1)) = i.castSucc := by ext; rfl
  change (lineIntegralQuadratic (slabLine (c.slab i))
    (c.breakpoint i.castSucc) (c.breakpoint i.succ)).eval p = _
  rw [eval_lineIntegralQuadratic]
  simp [slabAAtNat, slabBAtNat, breakpointNat, hr, hr.le, hrsle,
    hsucc, hcast]

/-- Final exact semantic bridge: an accepted native sweep certificate proves
that the genuine slice integral is the evaluation of its computed rational
quadratic. -/
theorem sliceArea_eq_integratedQuadratic_four {m : ℕ} {c : Certificate4 m}
    {P : RationalPolyhedron 4 m} (hcheck : check c P = true)
    {p : Fin 4 → ℝ} (hp : p ∈ P.carrier) :
    sliceArea 4 p = (integratedQuadratic c).eval p := by
  rw [sliceArea_eq_checkedSweep_four hcheck hp, eval_integratedQuadratic]

/-! ## Three-interval schedules -/

def coordinateAffine3 (j : Fin 3) : RationalAffine 3 where
  constant := 0
  linear := fun i ↦ if i = j then 1 else 0

def leftLine3 (j : Fin 3) : ParametricLine 3 where
  intercept := coordinateAffine3 j
  slope := (j.1 + 1 : ℚ) / 3

def widthLine3 : ParametricLine 3 where
  intercept := affineConst 3 (1 / 3)
  slope := -1 / 3

def overlapLine3 (a b : Fin 3) : ParametricLine 3 :=
  widthLine3.sub ((leftLine3 b).sub (leftLine3 a))

theorem eval_coordinateAffine3 (j : Fin 3) (p : Fin 3 → ℝ) :
    (coordinateAffine3 j).eval p = p j := by
  simp only [coordinateAffine3, RationalAffine.eval, Rat.cast_zero, zero_add]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hbj
    simp [hbj]
  · simp

theorem eval_leftLine3 (j : Fin 3) (p : Fin 3 → ℝ) (y : ℝ) :
    (leftLine3 j).eval p y = leftEndpoint 3 p j y := by
  rw [ParametricLine.eval]
  simp [leftLine3, eval_coordinateAffine3, leftEndpoint]

theorem eval_widthLine3 (p : Fin 3 → ℝ) (y : ℝ) :
    widthLine3.eval p y = (1 - y) / 3 := by
  simp [widthLine3, ParametricLine.eval, eval_affineConst]
  ring

theorem eval_overlapLine3 (a b : Fin 3) (p : Fin 3 → ℝ) (y : ℝ) :
    (overlapLine3 a b).eval p y =
      (1 - y) / 3 - (leftEndpoint 3 p b y - leftEndpoint 3 p a y) := by
  rw [overlapLine3, ParametricLine.eval_sub, eval_widthLine3,
    ParametricLine.eval_sub, eval_leftLine3, eval_leftLine3]

structure Slab3 (m : ℕ) where
  order : Fin 3 → Fin 3
  overlap : Fin 2 → Bool
  orderCertificate : Fin 2 → SparseFarkasCertificate m
  overlapCertificate : Fin 2 → SparseFarkasCertificate m
  deriving DecidableEq

structure Certificate3 (m : ℕ) where
  slabCount : ℕ
  breakpoint : Fin (slabCount + 1) → RationalAffine 3
  breakpointOrderCertificate : Fin slabCount → SparseFarkasCertificate m
  slab : Fin slabCount → Slab3 m
  deriving DecidableEq

def adjacentOrderLine3 {m : ℕ} (s : Slab3 m) (r : Fin 2) : ParametricLine 3 :=
  (leftLine3 (s.order r.succ)).sub (leftLine3 (s.order r.castSucc))

def signedOverlapLine3 {m : ℕ} (s : Slab3 m) (r : Fin 2) : ParametricLine 3 :=
  let gap := overlapLine3 (s.order r.castSucc) (s.order r.succ)
  if s.overlap r then gap else gap.neg

def Valid3 {m : ℕ} (c : Certificate3 m) (P : RationalPolyhedron 3 m) : Prop :=
  0 < c.slabCount ∧
  c.breakpoint 0 = affineConst 3 0 ∧
  c.breakpoint (Fin.last c.slabCount) = affineConst 3 1 ∧
  (∀ i, (c.breakpointOrderCertificate i).checkImplication P
    (affineSub (c.breakpoint i.succ) (c.breakpoint i.castSucc)) = true) ∧
  (∀ i a b, (c.slab i).order a = (c.slab i).order b → a = b) ∧
  (∀ i r, ((c.slab i).orderCertificate r).checkImplication P
    (selectedEndpoint (adjacentOrderLine3 (c.slab i) r)
      (c.breakpoint i.castSucc) (c.breakpoint i.succ)) = true) ∧
  (∀ i r, ((c.slab i).overlapCertificate r).checkImplication P
    (selectedEndpoint (signedOverlapLine3 (c.slab i) r)
      (c.breakpoint i.castSucc) (c.breakpoint i.succ)) = true)

def check3 {m : ℕ} (c : Certificate3 m) (P : RationalPolyhedron 3 m) : Bool :=
  decide (0 < c.slabCount) &&
  decide (c.breakpoint 0 = affineConst 3 0) &&
  decide (c.breakpoint (Fin.last c.slabCount) = affineConst 3 1) &&
  finAll (fun i ↦ (c.breakpointOrderCertificate i).checkImplication P
    (affineSub (c.breakpoint i.succ) (c.breakpoint i.castSucc))) &&
  finAll (fun i ↦ finAll (fun a ↦ finAll (fun b ↦
    decide ((c.slab i).order a = (c.slab i).order b → a = b)))) &&
  finAll (fun i ↦ finAll (fun r ↦
    ((c.slab i).orderCertificate r).checkImplication P
      (selectedEndpoint (adjacentOrderLine3 (c.slab i) r)
        (c.breakpoint i.castSucc) (c.breakpoint i.succ)))) &&
  finAll (fun i ↦ finAll (fun r ↦
    ((c.slab i).overlapCertificate r).checkImplication P
      (selectedEndpoint (signedOverlapLine3 (c.slab i) r)
        (c.breakpoint i.castSucc) (c.breakpoint i.succ))))

theorem valid3_of_check {m : ℕ} {c : Certificate3 m}
    {P : RationalPolyhedron 3 m} (h : check3 c P = true) : Valid3 c P := by
  simp only [check3, Bool.and_eq_true, decide_eq_true_eq, finAll_eq_true] at h
  rcases h with ⟨⟨⟨⟨⟨hab, hc⟩, hd⟩, he⟩, hf⟩, hg⟩
  rcases hab with ⟨ha, hb⟩
  exact ⟨ha, hb, hc, hd, he, hf, hg⟩

def zeroLine3 : ParametricLine 3 where
  intercept := affineZero 3
  slope := 0

def baseSliceLine3 : ParametricLine 3 where
  intercept := affineConst 3 1
  slope := -1

def overlapContribution3 {m : ℕ} (s : Slab3 m) (r : Fin 2) :
    ParametricLine 3 :=
  if s.overlap r then overlapLine3 (s.order r.castSucc) (s.order r.succ)
  else zeroLine3

def slabLine3 {m : ℕ} (s : Slab3 m) : ParametricLine 3 :=
  (baseSliceLine3.sub (overlapContribution3 s 0)).sub
    (overlapContribution3 s 1)

theorem eval_baseSliceLine3 (p : Fin 3 → ℝ) (y : ℝ) :
    baseSliceLine3.eval p y = 1 - y := by
  simp [baseSliceLine3, ParametricLine.eval, eval_affineConst]
  ring

theorem eval_zeroLine3 (p : Fin 3 → ℝ) (y : ℝ) : zeroLine3.eval p y = 0 := by
  simp [zeroLine3, ParametricLine.eval, eval_affineZero]

theorem breakpoint_order_sound3 {m : ℕ} {c : Certificate3 m}
    {P : RationalPolyhedron 3 m} (hv : Valid3 c P)
    {p : Fin 3 → ℝ} (hp : p ∈ P.carrier) (i : Fin c.slabCount) :
    (c.breakpoint i.castSucc).eval p ≤ (c.breakpoint i.succ).eval p := by
  have h := SparseFarkasCertificate.checkImplication_sound (hv.2.2.2.1 i) p hp
  simpa [eval_affineSub] using h

theorem slab_slice_eq3 {m : ℕ} {c : Certificate3 m}
    {P : RationalPolyhedron 3 m} (hv : Valid3 c P)
    {p : Fin 3 → ℝ} (hp : p ∈ P.carrier) (i : Fin c.slabCount)
    (hwithin : Icc ((c.breakpoint i.castSucc).eval p)
      ((c.breakpoint i.succ).eval p) ⊆ Icc (0 : ℝ) 1) :
    EqOn (sliceLength 3 p) (fun y ↦ (slabLine3 (c.slab i)).eval p y)
      (Icc ((c.breakpoint i.castSucc).eval p)
        ((c.breakpoint i.succ).eval p)) := by
  intro y hy
  let s := c.slab i
  have horderSelected (r : Fin 2) :
      0 ≤ (selectedEndpoint (adjacentOrderLine3 s r)
        (c.breakpoint i.castSucc) (c.breakpoint i.succ)).eval p :=
    SparseFarkasCertificate.checkImplication_sound (hv.2.2.2.2.2.1 i r) p hp
  have hordered (r : Fin 2) :
      leftEndpoint 3 p (s.order r.castSucc) y ≤
        leftEndpoint 3 p (s.order r.succ) y := by
    have hline := ParametricLine.nonneg_on_Icc_of_selected_endpoint
      (adjacentOrderLine3 s r) (c.breakpoint i.castSucc)
      (c.breakpoint i.succ) p (by
        simpa only [selectedEndpoint] using horderSelected r) y hy
    simpa [adjacentOrderLine3, ParametricLine.eval_sub, eval_leftLine3] using hline
  have hoverlapSelected (r : Fin 2) :
      0 ≤ (selectedEndpoint (signedOverlapLine3 s r)
        (c.breakpoint i.castSucc) (c.breakpoint i.succ)).eval p :=
    SparseFarkasCertificate.checkImplication_sound (hv.2.2.2.2.2.2 i r) p hp
  have hsigned (r : Fin 2) : 0 ≤ (signedOverlapLine3 s r).eval p y :=
    ParametricLine.nonneg_on_Icc_of_selected_endpoint
      (signedOverlapLine3 s r) (c.breakpoint i.castSucc)
      (c.breakpoint i.succ) p (by
        simpa only [selectedEndpoint] using hoverlapSelected r) y hy
  have hgap (r : Fin 2) :
      if s.overlap r then
        0 ≤ (overlapLine3 (s.order r.castSucc) (s.order r.succ)).eval p y
      else (overlapLine3 (s.order r.castSucc) (s.order r.succ)).eval p y ≤ 0 := by
    by_cases hr : s.overlap r
    · simpa [hr, signedOverlapLine3] using hsigned r
    · have := hsigned r
      simp [hr, signedOverlapLine3, ParametricLine.eval_neg] at this ⊢
      linarith
  have hinjective : Function.Injective s.order := hv.2.2.2.2.1 i
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective s.order
    ⟨hinjective, Finite.injective_iff_surjective.mp hinjective⟩
  have hsigma (r : Fin 3) : σ r = s.order r := rfl
  have hy01 : y ∈ Icc (0 : ℝ) 1 := hwithin hy
  rw [sliceLength_three_of_order p y hy01 σ]
  · simp_rw [hsigma]
    have hg0 := hgap 0
    have hg1 := hgap 1
    simp only [s] at hg0 hg1 ⊢
    cases h0 : (c.slab i).overlap 0 <;>
      cases h1 : (c.slab i).overlap 1 <;>
      simp_all [slabLine3, overlapContribution3, ParametricLine.eval_sub,
        eval_baseSliceLine3, eval_overlapLine3, eval_zeroLine3] <;> ring
  · simpa [hsigma] using hordered 0
  · simpa [hsigma] using hordered 1

def breakpointNat3 {m : ℕ} (c : Certificate3 m) (p : Fin 3 → ℝ)
    (r : ℕ) : ℝ :=
  if hr : r ≤ c.slabCount then
    (c.breakpoint ⟨r, Nat.lt_succ_iff.mpr hr⟩).eval p
  else 1

def slabAAtNat3 {m : ℕ} (c : Certificate3 m) (p : Fin 3 → ℝ)
    (r : ℕ) : ℝ :=
  if hr : r < c.slabCount then
    (slabLine3 (c.slab ⟨r, hr⟩)).intercept.eval p
  else 0

def slabBAtNat3 {m : ℕ} (c : Certificate3 m) (r : ℕ) : ℝ :=
  if hr : r < c.slabCount then ((slabLine3 (c.slab ⟨r, hr⟩)).slope : ℝ)
  else 0

theorem breakpointNat3_zero {m : ℕ} {c : Certificate3 m}
    {P : RationalPolyhedron 3 m} (hv : Valid3 c P) (p : Fin 3 → ℝ) :
    breakpointNat3 c p 0 = 0 := by
  simp [breakpointNat3, hv.2.1, eval_affineConst]

theorem breakpointNat3_last {m : ℕ} {c : Certificate3 m}
    {P : RationalPolyhedron 3 m} (hv : Valid3 c P) (p : Fin 3 → ℝ) :
    breakpointNat3 c p c.slabCount = 1 := by
  rw [show breakpointNat3 c p c.slabCount =
      (c.breakpoint (Fin.last c.slabCount)).eval p by
    simp [breakpointNat3]
    congr]
  rw [hv.2.2.1, eval_affineConst]
  norm_num

theorem breakpointNat3_step {m : ℕ} {c : Certificate3 m}
    {P : RationalPolyhedron 3 m} (hv : Valid3 c P)
    {p : Fin 3 → ℝ} (hp : p ∈ P.carrier) (r : ℕ) :
    breakpointNat3 c p r ≤ breakpointNat3 c p (r + 1) := by
  by_cases hr : r < c.slabCount
  · have hrle : r ≤ c.slabCount := hr.le
    have hrsle : r + 1 ≤ c.slabCount := hr
    simpa [breakpointNat3, hrle, hrsle] using
      breakpoint_order_sound3 hv hp (⟨r, hr⟩ : Fin c.slabCount)
  · have hkr : c.slabCount ≤ r := Nat.le_of_not_gt hr
    by_cases heq : r = c.slabCount
    · subst r
      rw [breakpointNat3_last hv p]
      simp [breakpointNat3]
    · have hgt : c.slabCount < r := lt_of_le_of_ne hkr (Ne.symm heq)
      have hnle : ¬r ≤ c.slabCount := Nat.not_le.mpr hgt
      have hsnle : ¬r + 1 ≤ c.slabCount :=
        Nat.not_le.mpr (hgt.trans (Nat.lt_succ_self r))
      simp [breakpointNat3, hnle, hsnle]

theorem sliceArea_eq_checkedSweep_three {m : ℕ} {c : Certificate3 m}
    {P : RationalPolyhedron 3 m} (hcheck : check3 c P = true)
    {p : Fin 3 → ℝ} (hp : p ∈ P.carrier) :
    sliceArea 3 p = ∑ r ∈ Finset.range c.slabCount,
      (slabAAtNat3 c p r *
          (breakpointNat3 c p (r + 1) - breakpointNat3 c p r) +
        slabBAtNat3 c r *
          (breakpointNat3 c p (r + 1) ^ 2 - breakpointNat3 c p r ^ 2) / 2) := by
  have hv : Valid3 c P := valid3_of_check hcheck
  have hmono : Monotone (breakpointNat3 c p) :=
    monotone_nat_of_le_succ (breakpointNat3_step hv hp)
  apply sliceArea_eq_sum_piecewise_affine 3 c.slabCount p
    (breakpointNat3 c p) (slabAAtNat3 c p) (slabBAtNat3 c)
  · exact breakpointNat3_zero hv p
  · exact breakpointNat3_last hv p
  · intro r hr
    exact breakpointNat3_step hv hp r
  · intro r hr
    have hrle : r ≤ c.slabCount := hr.le
    have hrsle : r + 1 ≤ c.slabCount := hr
    have hzero_le : 0 ≤ breakpointNat3 c p r := by
      rw [← breakpointNat3_zero hv p]
      exact hmono (Nat.zero_le r)
    have hle_one : breakpointNat3 c p (r + 1) ≤ 1 := by
      rw [← breakpointNat3_last hv p]
      exact hmono hrsle
    have hwithin : Icc (breakpointNat3 c p r) (breakpointNat3 c p (r + 1)) ⊆
        Icc (0 : ℝ) 1 := by
      intro y hy
      exact ⟨hzero_le.trans hy.1, hy.2.trans hle_one⟩
    have hs := slab_slice_eq3 hv hp (⟨r, hr⟩ : Fin c.slabCount) (by
      simpa [breakpointNat3, hrle, hrsle] using hwithin)
    simpa [slabAAtNat3, slabBAtNat3, breakpointNat3, hr, hrle, hrsle,
      ParametricLine.eval] using hs

/-- Exact rational quadratic generated by a three-interval schedule. -/
def integratedQuadratic3 {m : ℕ} (c : Certificate3 m) : RationalQuadratic 3 :=
  RationalQuadratic.sum (List.ofFn fun i : Fin c.slabCount ↦
    lineIntegralQuadratic (slabLine3 (c.slab i))
      (c.breakpoint i.castSucc) (c.breakpoint i.succ))

namespace Certificate3

/-- Namespace-friendly name used by generated three-interval certificates. -/
def integratedQuadratic {m : ℕ} (c : SweepCertificate.Certificate3 m) :
    RationalQuadratic 3 := integratedQuadratic3 c

end Certificate3

theorem eval_integratedQuadratic3 {m : ℕ} (c : Certificate3 m)
    (p : Fin 3 → ℝ) :
    (integratedQuadratic3 c).eval p = ∑ r ∈ Finset.range c.slabCount,
      (slabAAtNat3 c p r *
          (breakpointNat3 c p (r + 1) - breakpointNat3 c p r) +
        slabBAtNat3 c r *
          (breakpointNat3 c p (r + 1) ^ 2 - breakpointNat3 c p r ^ 2) / 2) := by
  rw [integratedQuadratic3, RationalQuadratic.eval_sum]
  simp only [List.map_ofFn, List.sum_ofFn]
  rw [← Fin.sum_univ_eq_sum_range (fun r ↦
    slabAAtNat3 c p r *
        (breakpointNat3 c p (r + 1) - breakpointNat3 c p r) +
      slabBAtNat3 c r *
        (breakpointNat3 c p (r + 1) ^ 2 - breakpointNat3 c p r ^ 2) / 2)
    c.slabCount]
  apply Finset.sum_congr rfl
  intro i _
  have hr : i.1 < c.slabCount := i.2
  have hrsle : i.1 + 1 ≤ c.slabCount := i.2
  have hsucc : (⟨i.1 + 1, Nat.lt_succ_iff.mpr hrsle⟩ :
      Fin (c.slabCount + 1)) = i.succ := by ext; rfl
  have hcast : (⟨i.1, Nat.lt_succ_iff.mpr hr.le⟩ :
      Fin (c.slabCount + 1)) = i.castSucc := by ext; rfl
  change (lineIntegralQuadratic (slabLine3 (c.slab i))
    (c.breakpoint i.castSucc) (c.breakpoint i.succ)).eval p = _
  rw [eval_lineIntegralQuadratic]
  simp [slabAAtNat3, slabBAtNat3, breakpointNat3, hr, hr.le, hrsle,
    hsucc, hcast]

theorem sliceArea_eq_integratedQuadratic_three {m : ℕ} {c : Certificate3 m}
    {P : RationalPolyhedron 3 m} (hcheck : check3 c P = true)
    {p : Fin 3 → ℝ} (hp : p ∈ P.carrier) :
    sliceArea 3 p = (Certificate3.integratedQuadratic c).eval p := by
  simpa [Certificate3.integratedQuadratic] using
    (show sliceArea 3 p = (integratedQuadratic3 c).eval p by
      rw [sliceArea_eq_checkedSweep_three hcheck hp, eval_integratedQuadratic3])

end SweepCertificate

end KakeyaNeedleC3C4
