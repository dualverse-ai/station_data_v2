import ErdosMinimum.NumericRow

/-!
# A fixed-dyadic hot loop for sequential row evaluation

Rational certificate data are rounded outward once.  Point evaluation then
uses only integer endpoint arithmetic at a common scale; multiplication is
followed immediately by outward Euclidean division by that scale.
-/

namespace ErdosMinimum

open RatInterval

/-- Precision of the exact fixed-point hot loop.  All rounding is directed
outward.  The four packaged rows have a strictly positive checked margin at
this 80-bit scale. -/
def fixedDyadicBits : ℕ := 80
def fixedDyadicScale : ℤ := (2 : ℤ) ^ fixedDyadicBits

theorem fixedDyadicScale_pos : 0 < fixedDyadicScale := by
  norm_num [fixedDyadicScale, fixedDyadicBits]

structure FixedInterval where
  lo : ℤ
  hi : ℤ
deriving DecidableEq, Repr

namespace FixedInterval

def Contains (I : FixedInterval) (x : ℝ) : Prop :=
  (I.lo : ℝ) / fixedDyadicScale ≤ x ∧
    x ≤ (I.hi : ℝ) / fixedDyadicScale

def pointInt (z : ℤ) : FixedInterval := ⟨z * fixedDyadicScale, z * fixedDyadicScale⟩

def ofRat (q : ℚ) : FixedInterval :=
  ⟨⌊q * fixedDyadicScale⌋, ⌈q * fixedDyadicScale⌉⟩

def ofRatInterval (I : RatInterval) : FixedInterval :=
  ⟨⌊I.lo * fixedDyadicScale⌋, ⌈I.hi * fixedDyadicScale⌉⟩

/-- View a fixed-dyadic interval as an exact rational interval. -/
def toRatInterval (I : FixedInterval) : RatInterval :=
  ⟨(I.lo : ℚ) / (fixedDyadicScale : ℚ),
    (I.hi : ℚ) / (fixedDyadicScale : ℚ)⟩

theorem contains_toRatInterval {I : FixedInterval} {x : ℝ}
    (hx : I.Contains x) : I.toRatInterval.Contains x := by
  simpa [toRatInterval, FixedInterval.Contains, RatInterval.Contains] using hx

def add (I J : FixedInterval) : FixedInterval := ⟨I.lo + J.lo, I.hi + J.hi⟩
def neg (I : FixedInterval) : FixedInterval := ⟨-I.hi, -I.lo⟩
def sub (I J : FixedInterval) : FixedInterval := add I (neg J)

def shiftDown (z : ℤ) : ℤ := z / fixedDyadicScale
def shiftUp (z : ℤ) : ℤ := -((-z) / fixedDyadicScale)

def mul (I J : FixedInterval) : FixedInterval :=
  let p1 := I.lo * J.lo
  let p2 := I.lo * J.hi
  let p3 := I.hi * J.lo
  let p4 := I.hi * J.hi
  ⟨shiftDown (min (min p1 p2) (min p3 p4)),
    shiftUp (max (max p1 p2) (max p3 p4))⟩

theorem contains_ofRat (q : ℚ) : (ofRat q).Contains (q : ℝ) := by
  have hs : (0 : ℝ) < fixedDyadicScale := by exact_mod_cast fixedDyadicScale_pos
  constructor
  · dsimp [ofRat, Contains]
    rw [div_le_iff₀ hs]
    exact_mod_cast Int.floor_le (q * fixedDyadicScale)
  · dsimp [ofRat, Contains]
    rw [le_div_iff₀ hs]
    exact_mod_cast Int.le_ceil (q * fixedDyadicScale)

theorem contains_ofRatInterval {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    (ofRatInterval I).Contains x := by
  have hlo := contains_ofRat I.lo
  have hhi := contains_ofRat I.hi
  exact ⟨hlo.1.trans hx.1, hx.2.trans hhi.2⟩

theorem contains_add {I J : FixedInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (add I J).Contains (x + y) := by
  rcases hx with ⟨hxlo, hxhi⟩
  rcases hy with ⟨hylo, hyhi⟩
  constructor
  · calc
      ((I.lo + J.lo : ℤ) : ℝ) / fixedDyadicScale =
          (I.lo : ℝ) / fixedDyadicScale + (J.lo : ℝ) / fixedDyadicScale := by
            push_cast; ring
      _ ≤ x + y := add_le_add hxlo hylo
  · calc
      x + y ≤ (I.hi : ℝ) / fixedDyadicScale +
          (J.hi : ℝ) / fixedDyadicScale := add_le_add hxhi hyhi
      _ = ((I.hi + J.hi : ℤ) : ℝ) / fixedDyadicScale := by
        push_cast; ring

theorem contains_neg {I : FixedInterval} {x : ℝ} (hx : I.Contains x) :
    I.neg.Contains (-x) := by
  rcases hx with ⟨hxlo, hxhi⟩
  constructor
  · dsimp [Contains, neg]
    push_cast
    rw [neg_div]
    exact neg_le_neg hxhi
  · dsimp [Contains, neg]
    push_cast
    rw [neg_div]
    exact neg_le_neg hxlo

theorem contains_sub {I J : FixedInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (sub I J).Contains (x - y) := by
  simpa [sub_eq_add_neg, sub] using contains_add hx (contains_neg hy)

private theorem shiftDown_bound (z : ℤ) :
    ((shiftDown z : ℤ) : ℝ) / fixedDyadicScale ≤
      (z : ℝ) / ((fixedDyadicScale : ℝ) * fixedDyadicScale) := by
  have h := Int.ediv_mul_le z fixedDyadicScale_pos.ne'
  have hr : ((shiftDown z * fixedDyadicScale : ℤ) : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast h
  have hs : (0 : ℝ) < fixedDyadicScale := by exact_mod_cast fixedDyadicScale_pos
  calc
    ((shiftDown z : ℤ) : ℝ) / fixedDyadicScale =
        (((shiftDown z * fixedDyadicScale : ℤ) : ℝ) /
          ((fixedDyadicScale : ℝ) * fixedDyadicScale)) := by
            push_cast
            field_simp [ne_of_gt hs]
    _ ≤ (z : ℝ) / ((fixedDyadicScale : ℝ) * fixedDyadicScale) := by
      exact div_le_div_of_nonneg_right hr (mul_pos hs hs).le

private theorem shiftUp_bound (z : ℤ) :
    (z : ℝ) / ((fixedDyadicScale : ℝ) * fixedDyadicScale) ≤
      ((shiftUp z : ℤ) : ℝ) / fixedDyadicScale := by
  have h := Int.ediv_mul_le (-z) fixedDyadicScale_pos.ne'
  have hr : (z : ℝ) ≤ ((shiftUp z * fixedDyadicScale : ℤ) : ℝ) := by
    exact_mod_cast (show z ≤ shiftUp z * fixedDyadicScale by
      dsimp [shiftUp]
      linarith)
  have hs : (0 : ℝ) < fixedDyadicScale := by exact_mod_cast fixedDyadicScale_pos
  calc
    (z : ℝ) / ((fixedDyadicScale : ℝ) * fixedDyadicScale) ≤
        (((shiftUp z * fixedDyadicScale : ℤ) : ℝ) /
          ((fixedDyadicScale : ℝ) * fixedDyadicScale)) := by
      exact div_le_div_of_nonneg_right hr (mul_pos hs hs).le
    _ = ((shiftUp z : ℤ) : ℝ) / fixedDyadicScale := by
      push_cast
      field_simp [ne_of_gt hs]

private theorem four_mul_lower {a b c d x y : ℝ}
    (hax : a ≤ x) (hxb : x ≤ b) (hcy : c ≤ y) (hyd : y ≤ d) :
    min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ x*y := by
  by_cases hx : 0 ≤ x
  · have hxy := mul_le_mul_of_nonneg_left hcy hx
    by_cases hc : 0 ≤ c
    · exact (min_le_of_left_le (min_le_of_left_le
        (mul_le_mul_of_nonneg_right hax hc))).trans hxy
    · exact (min_le_of_right_le (min_le_of_left_le
        (mul_le_mul_of_nonpos_right hxb (le_of_not_ge hc)))).trans hxy
  · have hxy := mul_le_mul_of_nonpos_left hyd (le_of_not_ge hx)
    by_cases hd : 0 ≤ d
    · exact (min_le_of_left_le (min_le_of_right_le
        (mul_le_mul_of_nonneg_right hax hd))).trans hxy
    · exact (min_le_of_right_le (min_le_of_right_le
        (mul_le_mul_of_nonpos_right hxb (le_of_not_ge hd)))).trans hxy

private theorem four_mul_upper {a b c d x y : ℝ}
    (hax : a ≤ x) (hxb : x ≤ b) (hcy : c ≤ y) (hyd : y ≤ d) :
    x*y ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) := by
  by_cases hx : 0 ≤ x
  · have hxy := mul_le_mul_of_nonneg_left hyd hx
    by_cases hd : 0 ≤ d
    · exact hxy.trans (le_max_of_le_right (le_max_of_le_right
        (mul_le_mul_of_nonneg_right hxb hd)))
    · exact hxy.trans (le_max_of_le_left (le_max_of_le_right
        (mul_le_mul_of_nonpos_right hax (le_of_not_ge hd))))
  · have hxy := mul_le_mul_of_nonpos_left hcy (le_of_not_ge hx)
    by_cases hc : 0 ≤ c
    · exact hxy.trans (le_max_of_le_right (le_max_of_le_left
        (mul_le_mul_of_nonneg_right hxb hc)))
    · exact hxy.trans (le_max_of_le_left (le_max_of_le_left
        (mul_le_mul_of_nonpos_right hax (le_of_not_ge hc))))

theorem contains_mul {I J : FixedInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) : (mul I J).Contains (x*y) := by
  rcases hx with ⟨hxlo, hxhi⟩
  rcases hy with ⟨hylo, hyhi⟩
  let s : ℝ := fixedDyadicScale
  have hs : 0 < s := by dsimp [s]; exact_mod_cast fixedDyadicScale_pos
  have hl := four_mul_lower hxlo hxhi hylo hyhi
  have hu := four_mul_upper hxlo hxhi hylo hyhi
  let rawLo : ℤ :=
    min (min (I.lo*J.lo) (I.lo*J.hi)) (min (I.hi*J.lo) (I.hi*J.hi))
  let rawHi : ℤ :=
    max (max (I.lo*J.lo) (I.lo*J.hi)) (max (I.hi*J.lo) (I.hi*J.hi))
  have hden : (0 : ℝ) ≤ (fixedDyadicScale : ℝ) * fixedDyadicScale :=
    (mul_pos hs hs).le
  have hl' : (rawLo : ℝ) /
      ((fixedDyadicScale : ℝ) * fixedDyadicScale) ≤ x*y := by
    dsimp [rawLo]
    push_cast
    rw [← min_div_div_right hden, ← min_div_div_right hden,
      ← min_div_div_right hden]
    convert hl using 1 <;> field_simp [ne_of_gt hs]
  have hu' : x*y ≤ (rawHi : ℝ) /
      ((fixedDyadicScale : ℝ) * fixedDyadicScale) := by
    dsimp [rawHi]
    push_cast
    rw [← max_div_div_right hden, ← max_div_div_right hden,
      ← max_div_div_right hden]
    convert hu using 1 <;> field_simp [ne_of_gt hs]
  constructor
  · simpa [mul, rawLo] using (shiftDown_bound rawLo).trans hl'
  · simpa [mul, rawHi] using hu'.trans (shiftUp_bound rawHi)

end FixedInterval

open FixedInterval

abbrev FixedTrig := FixedInterval × FixedInterval

def fixedTrigAt (q : ℚ) : FixedTrig :=
  let T := fastTrigAt q
  (ofRatInterval T.1, ofRatInterval T.2)

theorem fixedTrigAt_contains (q : ℚ) :
    (fixedTrigAt q).1.Contains (Real.sin (q : ℝ)) ∧
      (fixedTrigAt q).2.Contains (Real.cos (q : ℝ)) := by
  have h := fastTrigAt_contains q
  exact ⟨contains_ofRatInterval h.1, contains_ofRatInterval h.2⟩

def addFixedTrig (A D : FixedTrig) : FixedTrig :=
  (add (mul A.1 D.2) (mul A.2 D.1),
    sub (mul A.2 D.2) (mul A.1 D.1))

theorem addFixedTrig_contains {A D : FixedTrig} {x y : ℝ}
    (hA : A.1.Contains (Real.sin x) ∧ A.2.Contains (Real.cos x))
    (hD : D.1.Contains (Real.sin y) ∧ D.2.Contains (Real.cos y)) :
    (addFixedTrig A D).1.Contains (Real.sin (x+y)) ∧
      (addFixedTrig A D).2.Contains (Real.cos (x+y)) := by
  constructor
  · rw [Real.sin_add]
    exact contains_add (contains_mul hA.1 hD.2) (contains_mul hA.2 hD.1)
  · rw [Real.cos_add]
    exact contains_sub (contains_mul hA.2 hD.2) (contains_mul hA.1 hD.1)

/-- Coefficients rounded once before evaluating a batch of points. -/
structure FixedAtom where
  frequency : ℚ
  alpha : FixedInterval
  beta : FixedInterval
  alphaFrequency : FixedInterval
  betaFrequency : FixedInterval
  negAlphaDivFrequency : FixedInterval
  betaDivFrequency : FixedInterval
deriving DecidableEq, Repr

def FixedAtom.ofRatAtom (a : RatAtom) : FixedAtom :=
  ⟨a.frequency, ofRat a.alpha, ofRat a.beta,
    ofRat (a.alpha*a.frequency), ofRat (a.beta*a.frequency),
    ofRat (-(a.alpha/a.frequency)), ofRat (a.beta/a.frequency)⟩

structure FixedRow where
  a0 : FixedInterval
  a1 : FixedInterval
  a2 : FixedInterval
  a1Half : FixedInterval
  a2Third : FixedInterval
  atoms : List FixedAtom
deriving DecidableEq, Repr

def FixedRow.ofRatRow (row : RatRow) : FixedRow :=
  ⟨ofRat row.a0, ofRat row.a1, ofRat row.a2,
    ofRat (row.a1/2), ofRat (row.a2/3),
    row.atoms.map FixedAtom.ofRatAtom⟩

def cachedFixedTrig (x gap : ℚ) : List (ℚ × FixedTrig) →
    FixedTrig × List (ℚ × FixedTrig)
  | [] => let T := fixedTrigAt (gap*x); (T, [(gap,T)])
  | entry :: rest =>
      if entry.1 = gap then (entry.2, entry :: rest)
      else
        let result := cachedFixedTrig x gap rest
        (result.1, entry :: result.2)

def FixedCacheSound (x : ℝ) (cache : List (ℚ × FixedTrig)) : Prop :=
  ∀ entry ∈ cache,
    entry.2.1.Contains (Real.sin ((entry.1 : ℝ) * x)) ∧
      entry.2.2.Contains (Real.cos ((entry.1 : ℝ) * x))

theorem cachedFixedTrig_sound (x gap : ℚ) (cache : List (ℚ × FixedTrig))
    (hcache : FixedCacheSound (x : ℝ) cache) :
    let result := cachedFixedTrig x gap cache
    (result.1.1.Contains (Real.sin ((gap : ℝ) * x)) ∧
      result.1.2.Contains (Real.cos ((gap : ℝ) * x))) ∧
      FixedCacheSound (x : ℝ) result.2 := by
  induction cache with
  | nil =>
      simpa [cachedFixedTrig, FixedCacheSound] using
        fixedTrigAt_contains (gap*x)
  | cons head rest ih =>
      by_cases heq : head.1 = gap
      · have hentry := hcache head (by simp)
        subst gap
        simpa [cachedFixedTrig, FixedCacheSound] using
          And.intro hentry hcache
      · have htail : FixedCacheSound (x : ℝ) rest := by
          intro e he
          exact hcache e (by simp [he])
        have hrest := ih htail
        simp only [cachedFixedTrig, heq, if_false]
        constructor
        · exact hrest.1
        · intro item he
          simp only [List.mem_cons] at he
          rcases he with rfl | he
          · exact hcache _ (by simp)
          · exact hrest.2 item he

structure FixedState where
  previousFrequency : ℚ
  currentTrig : FixedTrig
  cache : List (ℚ × FixedTrig)
  value : FixedInterval
  derivative : FixedInterval
  antiderivative : FixedInterval
  stepsSinceReset : ℕ
deriving DecidableEq, Repr

def initialFixedState : FixedState :=
  ⟨0, (pointInt 0, pointInt 1), [], pointInt 0, pointInt 0, pointInt 0, 0⟩

def fixedNextTrig (x : ℚ) (state : FixedState) (a : FixedAtom) :
    FixedTrig × List (ℚ × FixedTrig) :=
  if state.stepsSinceReset = 32 then
    (fixedTrigAt (a.frequency*x), state.cache)
  else
    let gap := a.frequency - state.previousFrequency
    let lookup := cachedFixedTrig x gap state.cache
    (addFixedTrig state.currentTrig lookup.1, lookup.2)

theorem fixedNextTrig_sound (x : ℚ) (state : FixedState) (a : FixedAtom)
    (htrig : state.currentTrig.1.Contains
        (Real.sin ((state.previousFrequency : ℝ) * x)) ∧
      state.currentTrig.2.Contains
        (Real.cos ((state.previousFrequency : ℝ) * x)))
    (hcache : FixedCacheSound (x : ℝ) state.cache) :
    let result := fixedNextTrig x state a
    (result.1.1.Contains (Real.sin ((a.frequency : ℝ) * x)) ∧
      result.1.2.Contains (Real.cos ((a.frequency : ℝ) * x))) ∧
      FixedCacheSound (x : ℝ) result.2 := by
  by_cases hreset : state.stepsSinceReset = 32
  · simpa [fixedNextTrig, hreset] using
      And.intro (fixedTrigAt_contains (a.frequency*x)) hcache
  · let gap := a.frequency - state.previousFrequency
    let lookup := cachedFixedTrig x gap state.cache
    have hlookup := cachedFixedTrig_sound x gap state.cache hcache
    have hraw := addFixedTrig_contains htrig hlookup.1
    have hangle : (state.previousFrequency : ℝ) * x + (gap : ℝ) * x =
        (a.frequency : ℝ) * x := by
      dsimp [gap]
      push_cast
      ring
    have hT : (addFixedTrig state.currentTrig lookup.1).1.Contains
          (Real.sin ((a.frequency : ℝ) * x)) ∧
        (addFixedTrig state.currentTrig lookup.1).2.Contains
          (Real.cos ((a.frequency : ℝ) * x)) := by
      simpa [hangle] using hraw
    simpa [fixedNextTrig, hreset, gap, lookup] using And.intro hT hlookup.2

def fixedStep (withAntiderivative : Bool) (x : ℚ)
    (state : FixedState) (a : FixedAtom) : FixedState :=
  let reset := state.stepsSinceReset = 32
  let trigAndCache := fixedNextTrig x state a
  let T := trigAndCache.1
  let av := add (mul a.alpha T.2) (mul a.beta T.1)
  let ad := sub (mul a.alphaFrequency T.1) (mul a.betaFrequency T.2)
  let aa := add (mul a.negAlphaDivFrequency T.1) (mul a.betaDivFrequency T.2)
  ⟨a.frequency, T, trigAndCache.2,
    if withAntiderivative then state.value else add state.value av,
    if withAntiderivative then state.derivative else add state.derivative ad,
    if withAntiderivative then add state.antiderivative aa else state.antiderivative,
    if reset then 1 else state.stepsSinceReset + 1⟩

def fixedLoop (withAntiderivative : Bool) (x : ℚ) :
    List FixedAtom → FixedState → FixedState
  | [], state => state
  | a :: atoms, state =>
      fixedLoop withAntiderivative x atoms
        (fixedStep withAntiderivative x state a)

def fixedRowValueDerivative (row : FixedRow) (x : ℚ) :
    FixedInterval × FixedInterval :=
  let X := ofRat x
  let X2 := mul X X
  let poly := add row.a0 (add (mul row.a1 X) (mul row.a2 X2))
  let derivPoly := add row.a1 (mul (add row.a2 row.a2) X)
  let result := fixedLoop false x row.atoms initialFixedState
  (sub poly result.value, add derivPoly result.derivative)

/-- Fixed-dyadic antiderivative evaluation using the same sequential trig
state and globally cached frequency gaps as value/derivative evaluation. -/
def fixedRowAntiderivative (row : FixedRow) (x : ℚ) : FixedInterval :=
  let X := ofRat x
  let X2 := mul X X
  let X3 := mul X2 X
  let poly := add (mul row.a0 X)
    (add (mul row.a1Half X2) (mul row.a2Third X3))
  let result := fixedLoop true x row.atoms initialFixedState
  add poly result.antiderivative

private theorem fixedLoop_contains (x : ℚ) (atoms : List RatAtom)
    (state : FixedState) (value derivative : ℝ)
    (htrig : state.currentTrig.1.Contains
        (Real.sin ((state.previousFrequency : ℝ) * x)) ∧
      state.currentTrig.2.Contains
        (Real.cos ((state.previousFrequency : ℝ) * x)))
    (hcache : FixedCacheSound (x : ℝ) state.cache)
    (hvalue : state.value.Contains value)
    (hderivative : state.derivative.Contains derivative) :
    let result := fixedLoop false x (atoms.map FixedAtom.ofRatAtom) state
    result.value.Contains
      (value + (atoms.map fun a ↦
        (a.alpha : ℝ) * Real.cos ((a.frequency : ℝ) * x) +
        (a.beta : ℝ) * Real.sin ((a.frequency : ℝ) * x)).sum) ∧
    result.derivative.Contains
      (derivative + (atoms.map fun a ↦
        ((a.alpha*a.frequency : ℚ) : ℝ) *
            Real.sin ((a.frequency : ℝ) * x) -
        ((a.beta*a.frequency : ℚ) : ℝ) *
            Real.cos ((a.frequency : ℝ) * x)).sum) := by
  induction atoms generalizing state value derivative with
  | nil => simpa [fixedLoop] using And.intro hvalue hderivative
  | cons a atoms ih =>
      let da := FixedAtom.ofRatAtom a
      let next := fixedNextTrig x state da
      have hnext := fixedNextTrig_sound x state da htrig hcache
      let T := next.1
      have hT := hnext.1
      let av := add (mul da.alpha T.2) (mul da.beta T.1)
      let ad := sub (mul da.alphaFrequency T.1) (mul da.betaFrequency T.2)
      have hav : av.Contains
          ((a.alpha : ℝ) * Real.cos ((a.frequency : ℝ) * x) +
            (a.beta : ℝ) * Real.sin ((a.frequency : ℝ) * x)) := by
        apply FixedInterval.contains_add
        · exact contains_mul (contains_ofRat a.alpha) hT.2
        · exact contains_mul (contains_ofRat a.beta) hT.1
      have had : ad.Contains
          (((a.alpha*a.frequency : ℚ) : ℝ) *
              Real.sin ((a.frequency : ℝ) * x) -
            ((a.beta*a.frequency : ℚ) : ℝ) *
              Real.cos ((a.frequency : ℝ) * x)) := by
        apply FixedInterval.contains_sub
        · exact contains_mul (contains_ofRat (a.alpha*a.frequency)) hT.1
        · exact contains_mul (contains_ofRat (a.beta*a.frequency)) hT.2
      have hv' : (add state.value av).Contains
          (value + ((a.alpha : ℝ) * Real.cos ((a.frequency : ℝ) * x) +
            (a.beta : ℝ) * Real.sin ((a.frequency : ℝ) * x))) :=
        contains_add hvalue hav
      have hd' : (add state.derivative ad).Contains
          (derivative + (((a.alpha*a.frequency : ℚ) : ℝ) *
              Real.sin ((a.frequency : ℝ) * x) -
            ((a.beta*a.frequency : ℚ) : ℝ) *
              Real.cos ((a.frequency : ℝ) * x))) :=
        contains_add hderivative had
      have hrest := ih
        (fixedStep false x state da)
        (value + ((a.alpha : ℝ) * Real.cos ((a.frequency : ℝ) * x) +
          (a.beta : ℝ) * Real.sin ((a.frequency : ℝ) * x)))
        (derivative + (((a.alpha*a.frequency : ℚ) : ℝ) *
          Real.sin ((a.frequency : ℝ) * x) -
          ((a.beta*a.frequency : ℚ) : ℝ) *
          Real.cos ((a.frequency : ℝ) * x)))
        hT hnext.2 hv' hd'
      simpa [fixedLoop, fixedStep, da, next, T, av, ad, add_assoc] using hrest

private theorem fixedLoop_antiderivative_contains (x : ℚ)
    (atoms : List RatAtom) (state : FixedState) (antiderivative : ℝ)
    (htrig : state.currentTrig.1.Contains
        (Real.sin ((state.previousFrequency : ℝ) * x)) ∧
      state.currentTrig.2.Contains
        (Real.cos ((state.previousFrequency : ℝ) * x)))
    (hcache : FixedCacheSound (x : ℝ) state.cache)
    (hantiderivative : state.antiderivative.Contains antiderivative) :
    let result := fixedLoop true x (atoms.map FixedAtom.ofRatAtom) state
    result.antiderivative.Contains
      (antiderivative + (atoms.map fun a ↦
        ((-(a.alpha/a.frequency) : ℚ) : ℝ) *
            Real.sin ((a.frequency : ℝ) * x) +
        ((a.beta/a.frequency : ℚ) : ℝ) *
            Real.cos ((a.frequency : ℝ) * x)).sum) := by
  induction atoms generalizing state antiderivative with
  | nil => simpa [fixedLoop] using hantiderivative
  | cons a atoms ih =>
      let da := FixedAtom.ofRatAtom a
      let next := fixedNextTrig x state da
      have hnext := fixedNextTrig_sound x state da htrig hcache
      let T := next.1
      have hT := hnext.1
      let aa := add (mul da.negAlphaDivFrequency T.1)
        (mul da.betaDivFrequency T.2)
      have haa : aa.Contains
          (((-(a.alpha/a.frequency) : ℚ) : ℝ) *
              Real.sin ((a.frequency : ℝ) * x) +
            ((a.beta/a.frequency : ℚ) : ℝ) *
              Real.cos ((a.frequency : ℝ) * x)) := by
        apply FixedInterval.contains_add
        · exact contains_mul (contains_ofRat (-(a.alpha/a.frequency))) hT.1
        · exact contains_mul (contains_ofRat (a.beta/a.frequency)) hT.2
      have ha' : (add state.antiderivative aa).Contains
          (antiderivative +
            (((-(a.alpha/a.frequency) : ℚ) : ℝ) *
                Real.sin ((a.frequency : ℝ) * x) +
              ((a.beta/a.frequency : ℚ) : ℝ) *
                Real.cos ((a.frequency : ℝ) * x))) :=
        contains_add hantiderivative haa
      have hrest := ih (fixedStep true x state da)
        (antiderivative +
          (((-(a.alpha/a.frequency) : ℚ) : ℝ) *
              Real.sin ((a.frequency : ℝ) * x) +
            ((a.beta/a.frequency : ℚ) : ℝ) *
              Real.cos ((a.frequency : ℝ) * x)))
        hT hnext.2 ha'
      simpa [fixedLoop, fixedStep, da, next, T, aa, add_assoc] using hrest

theorem fixedRowValueDerivative_contains (row : RatRow) (x : ℚ) :
    let result := fixedRowValueDerivative (FixedRow.ofRatRow row) x
    result.1.Contains (ratRowFunction row x) ∧
      result.2.Contains (ratRowDerivative row x) := by
  have hloop := fixedLoop_contains x row.atoms initialFixedState 0 0
    (by
      norm_num [initialFixedState, FixedInterval.Contains, pointInt]
      field_simp [fixedDyadicScale_pos.ne']
      constructor <;> norm_num)
    (by simp [initialFixedState, FixedCacheSound])
    (by norm_num [initialFixedState, FixedInterval.Contains, pointInt])
    (by norm_num [initialFixedState, FixedInterval.Contains, pointInt])
  have hX := contains_ofRat x
  have hX2 := contains_mul hX hX
  have hp :
      (add (ofRat row.a0)
        (add (mul (ofRat row.a1) (ofRat x))
          (mul (ofRat row.a2) (mul (ofRat x) (ofRat x))))).Contains
        ((row.a0 : ℝ) + row.a1*x + row.a2*(x:ℝ)^2) := by
    convert contains_add (contains_ofRat row.a0)
      (contains_add (contains_mul (contains_ofRat row.a1) hX)
        (contains_mul (contains_ofRat row.a2) hX2)) using 1 <;> norm_num <;> ring
  have hdp :
      (add (ofRat row.a1)
        (mul (add (ofRat row.a2) (ofRat row.a2)) (ofRat x))).Contains
        ((row.a1 : ℝ) + 2*(row.a2 : ℝ)*(x : ℝ)) := by
    have h := contains_add (contains_ofRat row.a1)
      (contains_mul (contains_add (contains_ofRat row.a2) (contains_ofRat row.a2)) hX)
    convert h using 1
    ring
  constructor
  · unfold fixedRowValueDerivative FixedRow.ofRatRow ratRowFunction
    apply contains_sub hp
    simpa using hloop.1
  · unfold fixedRowValueDerivative FixedRow.ofRatRow ratRowDerivative
    apply contains_add hdp
    simpa using hloop.2

/-- The pre-rounded fixed row's antiderivative interval encloses the exact
rational-row antiderivative. -/
theorem fixedRowAntiderivative_contains (row : RatRow) (x : ℚ) :
    (fixedRowAntiderivative (FixedRow.ofRatRow row) x).Contains
      (ratRowAntiderivative row x) := by
  have hloop := fixedLoop_antiderivative_contains x row.atoms
    initialFixedState 0
    (by
      norm_num [initialFixedState, FixedInterval.Contains, pointInt]
      field_simp [fixedDyadicScale_pos.ne']
      constructor <;> norm_num)
    (by simp [initialFixedState, FixedCacheSound])
    (by norm_num [initialFixedState, FixedInterval.Contains, pointInt])
  have hX := contains_ofRat x
  have hX2 := contains_mul hX hX
  have hX3 := contains_mul hX2 hX
  have hp :
      (add (mul (ofRat row.a0) (ofRat x))
        (add (mul (ofRat (row.a1/2)) (mul (ofRat x) (ofRat x)))
          (mul (ofRat (row.a2/3))
            (mul (mul (ofRat x) (ofRat x)) (ofRat x))))).Contains
        ((row.a0 : ℝ)*(x:ℝ) + (row.a1:ℝ)*(x:ℝ)^2/2 +
          (row.a2:ℝ)*(x:ℝ)^3/3) := by
    have h := contains_add (contains_mul (contains_ofRat row.a0) hX)
      (contains_add (contains_mul (contains_ofRat (row.a1/2)) hX2)
        (contains_mul (contains_ofRat (row.a2/3)) hX3))
    convert h using 1 <;> norm_num <;> ring
  unfold fixedRowAntiderivative FixedRow.ofRatRow ratRowAntiderivative
  apply contains_add hp
  simpa only [Rat.cast_neg, zero_add] using hloop

end ErdosMinimum
