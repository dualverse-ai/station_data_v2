import ErdosMinimum.NumericRow

/-!
# Sequential trigonometric evaluation of certificate rows

Certificate frequencies are sorted and commonly occur in long arithmetic
progressions.  This evaluator traverses the atoms once.  It obtains the first
angle (and every changed frequency gap) from `fastTrigAt`, reuses the cached
gap enclosure while the gap stays constant, and advances sine/cosine by the
angle-addition formulas.  Value and derivative sums are accumulated in the
same pass; antiderivatives can be enabled by a Boolean flag.
-/

namespace ErdosMinimum

open RatInterval

/-- Compressed angle addition on simultaneous sine/cosine enclosures. -/
def addTrigCompressed (A D : RatInterval × RatInterval) :
    RatInterval × RatInterval :=
  (addCompressed trigPrecision
      (mulCompressed trigPrecision A.1 D.2)
      (mulCompressed trigPrecision A.2 D.1),
    subCompressed trigPrecision
      (mulCompressed trigPrecision A.2 D.2)
      (mulCompressed trigPrecision A.1 D.1))

theorem addTrigCompressed_contains {A D : RatInterval × RatInterval} {x y : ℝ}
    (hA : A.1.Contains (Real.sin x) ∧ A.2.Contains (Real.cos x))
    (hD : D.1.Contains (Real.sin y) ∧ D.2.Contains (Real.cos y)) :
    (addTrigCompressed A D).1.Contains (Real.sin (x + y)) ∧
      (addTrigCompressed A D).2.Contains (Real.cos (x + y)) := by
  constructor
  · rw [Real.sin_add]
    exact contains_addCompressed
      (contains_mulCompressed hA.1 hD.2 trigPrecision)
      (contains_mulCompressed hA.2 hD.1 trigPrecision) trigPrecision
  · rw [Real.cos_add]
    exact contains_subCompressed
      (contains_mulCompressed hA.2 hD.2 trigPrecision)
      (contains_mulCompressed hA.1 hD.1 trigPrecision) trigPrecision

structure SequentialSums where
  value : RatInterval
  derivative : RatInterval
  antiderivative : RatInterval
deriving DecidableEq, Repr

def SequentialSums.zero : SequentialSums :=
  ⟨point 0, point 0, point 0⟩

/-- The three contributions of an atom, all using the same trigonometric
pair.  When `withAntiderivative` is false its third component is unused. -/
def atomSequentialContributions (withAntiderivative : Bool) (a : RatAtom)
    (T : RatInterval × RatInterval) : SequentialSums :=
  ⟨addCompressed trigPrecision
      (scaleCompressed trigPrecision a.alpha T.2)
      (scaleCompressed trigPrecision a.beta T.1),
    subCompressed trigPrecision
      (scaleCompressed trigPrecision (a.alpha * a.frequency) T.1)
      (scaleCompressed trigPrecision (a.beta * a.frequency) T.2),
    if withAntiderivative then
      addCompressed trigPrecision
        (scaleCompressed trigPrecision (-(a.alpha / a.frequency)) T.1)
        (scaleCompressed trigPrecision (a.beta / a.frequency) T.2)
    else point 0⟩

def addSequentialSums (withAntiderivative : Bool)
    (A B : SequentialSums) : SequentialSums :=
  ⟨addCompressed trigPrecision A.value B.value,
    addCompressed trigPrecision A.derivative B.derivative,
    if withAntiderivative then
      addCompressed trigPrecision A.antiderivative B.antiderivative
    else A.antiderivative⟩

noncomputable def atomValueReal (a : RatAtom) (x : ℝ) : ℝ :=
  (a.alpha : ℝ) * Real.cos ((a.frequency : ℝ) * x) +
    (a.beta : ℝ) * Real.sin ((a.frequency : ℝ) * x)

noncomputable def atomDerivativeReal (a : RatAtom) (x : ℝ) : ℝ :=
  ((a.alpha * a.frequency : ℚ) : ℝ) *
      Real.sin ((a.frequency : ℝ) * x) -
    ((a.beta * a.frequency : ℚ) : ℝ) *
      Real.cos ((a.frequency : ℝ) * x)

noncomputable def atomAntiderivativeReal (a : RatAtom) (x : ℝ) : ℝ :=
  ((-(a.alpha / a.frequency) : ℚ) : ℝ) *
      Real.sin ((a.frequency : ℝ) * x) +
    ((a.beta / a.frequency : ℚ) : ℝ) *
      Real.cos ((a.frequency : ℝ) * x)

theorem atomSequentialContributions_contains (withAntiderivative : Bool)
    (a : RatAtom) {T : RatInterval × RatInterval} {x : ℝ}
    (hT : T.1.Contains (Real.sin ((a.frequency : ℝ) * x)) ∧
      T.2.Contains (Real.cos ((a.frequency : ℝ) * x))) :
    (atomSequentialContributions withAntiderivative a T).value.Contains
        (atomValueReal a x) ∧
      (atomSequentialContributions withAntiderivative a T).derivative.Contains
        (atomDerivativeReal a x) := by
  constructor
  · simpa [atomSequentialContributions, atomValueReal] using
      contains_addCompressed
        (contains_scaleCompressed a.alpha hT.2 trigPrecision)
        (contains_scaleCompressed a.beta hT.1 trigPrecision) trigPrecision
  · simpa [atomSequentialContributions, atomDerivativeReal] using
      contains_subCompressed
        (contains_scaleCompressed (a.alpha * a.frequency) hT.1 trigPrecision)
        (contains_scaleCompressed (a.beta * a.frequency) hT.2 trigPrecision)
        trigPrecision

theorem atomSequentialAntiderivative_contains (a : RatAtom)
    {T : RatInterval × RatInterval} {x : ℝ}
    (hT : T.1.Contains (Real.sin ((a.frequency : ℝ) * x)) ∧
      T.2.Contains (Real.cos ((a.frequency : ℝ) * x))) :
    (atomSequentialContributions true a T).antiderivative.Contains
      (atomAntiderivativeReal a x) := by
  simpa [atomSequentialContributions, atomAntiderivativeReal] using
    contains_addCompressed
      (contains_scaleCompressed (-(a.alpha / a.frequency)) hT.1 trigPrecision)
      (contains_scaleCompressed (a.beta / a.frequency) hT.2 trigPrecision)
      trigPrecision

/-- State after processing a prefix of atoms.  `cachedDelta` records the last
frequency gap and its sine/cosine enclosure. -/
structure SequentialState where
  previousFrequency : ℚ
  currentTrig : RatInterval × RatInterval
  cachedDelta : Option (ℚ × (RatInterval × RatInterval))
  sums : SequentialSums
deriving DecidableEq, Repr

def initialSequentialState : SequentialState where
  previousFrequency := 0
  currentTrig := (point 0, point 1)
  cachedDelta := none
  sums := SequentialSums.zero

/-- Reuse the cached delta precisely when the next rational gap is equal;
otherwise run the global evaluator once for the new gap. -/
def deltaTrig (x gap : ℚ)
    (cache : Option (ℚ × (RatInterval × RatInterval))) :
    RatInterval × RatInterval :=
  match cache with
  | some (oldGap, T) => if oldGap = gap then T else fastTrigAt (gap * x)
  | none => fastTrigAt (gap * x)

def DeltaCacheSound (x : ℝ) :
    Option (ℚ × (RatInterval × RatInterval)) → Prop
  | none => True
  | some (gap, T) =>
      T.1.Contains (Real.sin ((gap : ℝ) * x)) ∧
        T.2.Contains (Real.cos ((gap : ℝ) * x))

theorem deltaTrig_contains (x gap : ℚ)
    (cache : Option (ℚ × (RatInterval × RatInterval)))
    (hcache : DeltaCacheSound (x : ℝ) cache) :
    (deltaTrig x gap cache).1.Contains (Real.sin ((gap : ℝ) * x)) ∧
      (deltaTrig x gap cache).2.Contains (Real.cos ((gap : ℝ) * x)) := by
  rcases cache with _ | ⟨oldGap, T⟩
  · simpa [deltaTrig] using fastTrigAt_contains (gap * x)
  · by_cases hgap : oldGap = gap
    · subst gap
      simpa [deltaTrig] using hcache
    · simpa [deltaTrig, hgap] using fastTrigAt_contains (gap * x)

def sequentialStep (withAntiderivative : Bool) (x : ℚ)
    (state : SequentialState) (a : RatAtom) : SequentialState :=
  let gap := a.frequency - state.previousFrequency
  let D := deltaTrig x gap state.cachedDelta
  let T := addTrigCompressed state.currentTrig D
  let contribution := atomSequentialContributions withAntiderivative a T
  ⟨a.frequency, T, some (gap, D),
    addSequentialSums withAntiderivative state.sums contribution⟩

def sequentialLoop (withAntiderivative : Bool) (x : ℚ) :
    List RatAtom → SequentialState → SequentialState
  | [], state => state
  | a :: atoms, state =>
      sequentialLoop withAntiderivative x atoms
        (sequentialStep withAntiderivative x state a)

/-- One-pass atom sums.  Set the flag only when the antiderivative sum is
needed; value and derivative are always accumulated. -/
def sequentialAtomSums (withAntiderivative : Bool) (x : ℚ)
    (atoms : List RatAtom) : SequentialSums :=
  (sequentialLoop withAntiderivative x atoms initialSequentialState).sums

private theorem sequentialLoop_value_derivative_contains
    (withAntiderivative : Bool) (x : ℚ) (atoms : List RatAtom)
    (state : SequentialState) (value derivative : ℝ)
    (htrig : state.currentTrig.1.Contains
        (Real.sin ((state.previousFrequency : ℝ) * x)) ∧
      state.currentTrig.2.Contains
        (Real.cos ((state.previousFrequency : ℝ) * x)))
    (hcache : DeltaCacheSound (x : ℝ) state.cachedDelta)
    (hvalue : state.sums.value.Contains value)
    (hderivative : state.sums.derivative.Contains derivative) :
    let result := sequentialLoop withAntiderivative x atoms state
    result.sums.value.Contains
        (value + (atoms.map fun a ↦ atomValueReal a x).sum) ∧
      result.sums.derivative.Contains
        (derivative + (atoms.map fun a ↦ atomDerivativeReal a x).sum) := by
  induction atoms generalizing state value derivative with
  | nil => simpa [sequentialLoop] using And.intro hvalue hderivative
  | cons a atoms ih =>
      let gap := a.frequency - state.previousFrequency
      let D := deltaTrig x gap state.cachedDelta
      let T := addTrigCompressed state.currentTrig D
      have hD : D.1.Contains (Real.sin ((gap : ℝ) * x)) ∧
          D.2.Contains (Real.cos ((gap : ℝ) * x)) :=
        deltaTrig_contains x gap state.cachedDelta hcache
      have hTraw := addTrigCompressed_contains htrig hD
      have hangle : (state.previousFrequency : ℝ) * x + (gap : ℝ) * x =
          (a.frequency : ℝ) * x := by
        dsimp [gap]
        push_cast
        ring
      have hT : T.1.Contains (Real.sin ((a.frequency : ℝ) * x)) ∧
          T.2.Contains (Real.cos ((a.frequency : ℝ) * x)) := by
        simpa [T, hangle] using hTraw
      let contribution := atomSequentialContributions withAntiderivative a T
      have hcontribution := atomSequentialContributions_contains
        withAntiderivative a hT
      have hvalue' :
          (addSequentialSums withAntiderivative state.sums contribution).value.Contains
            (value + atomValueReal a x) := by
        exact contains_addCompressed hvalue hcontribution.1 trigPrecision
      have hderivative' :
          (addSequentialSums withAntiderivative state.sums contribution).derivative.Contains
            (derivative + atomDerivativeReal a x) := by
        exact contains_addCompressed hderivative hcontribution.2 trigPrecision
      have hcache' : DeltaCacheSound (x : ℝ) (some (gap, D)) := hD
      have hrest := ih (sequentialStep withAntiderivative x state a)
        (value + atomValueReal a x) (derivative + atomDerivativeReal a x)
        hT hcache' hvalue' hderivative'
      simpa [sequentialLoop, sequentialStep, gap, D, T, contribution, add_assoc] using hrest

theorem sequentialAtomSums_value_derivative_contains
    (withAntiderivative : Bool) (x : ℚ) (atoms : List RatAtom) :
    (sequentialAtomSums withAntiderivative x atoms).value.Contains
        (atoms.map fun a ↦ atomValueReal a x).sum ∧
      (sequentialAtomSums withAntiderivative x atoms).derivative.Contains
        (atoms.map fun a ↦ atomDerivativeReal a x).sum := by
  have h := sequentialLoop_value_derivative_contains withAntiderivative x atoms
    initialSequentialState 0 0
    (by norm_num [initialSequentialState, RatInterval.Contains, point])
    (by simp [initialSequentialState, DeltaCacheSound])
    (by simpa [initialSequentialState, SequentialSums.zero] using contains_point 0)
    (by simpa [initialSequentialState, SequentialSums.zero] using contains_point 0)
  simpa [sequentialAtomSums] using h

private theorem sequentialLoop_antiderivative_contains
    (x : ℚ) (atoms : List RatAtom) (state : SequentialState)
    (antiderivative : ℝ)
    (htrig : state.currentTrig.1.Contains
        (Real.sin ((state.previousFrequency : ℝ) * x)) ∧
      state.currentTrig.2.Contains
        (Real.cos ((state.previousFrequency : ℝ) * x)))
    (hcache : DeltaCacheSound (x : ℝ) state.cachedDelta)
    (hantiderivative : state.sums.antiderivative.Contains antiderivative) :
    let result := sequentialLoop true x atoms state
    result.sums.antiderivative.Contains
      (antiderivative + (atoms.map fun a ↦ atomAntiderivativeReal a x).sum) := by
  induction atoms generalizing state antiderivative with
  | nil => simpa [sequentialLoop] using hantiderivative
  | cons a atoms ih =>
      let gap := a.frequency - state.previousFrequency
      let D := deltaTrig x gap state.cachedDelta
      let T := addTrigCompressed state.currentTrig D
      have hD : D.1.Contains (Real.sin ((gap : ℝ) * x)) ∧
          D.2.Contains (Real.cos ((gap : ℝ) * x)) :=
        deltaTrig_contains x gap state.cachedDelta hcache
      have hTraw := addTrigCompressed_contains htrig hD
      have hangle : (state.previousFrequency : ℝ) * x + (gap : ℝ) * x =
          (a.frequency : ℝ) * x := by
        dsimp [gap]
        push_cast
        ring
      have hT : T.1.Contains (Real.sin ((a.frequency : ℝ) * x)) ∧
          T.2.Contains (Real.cos ((a.frequency : ℝ) * x)) := by
        simpa [T, hangle] using hTraw
      let contribution := atomSequentialContributions true a T
      have hcontribution : contribution.antiderivative.Contains
          (atomAntiderivativeReal a x) :=
        atomSequentialAntiderivative_contains a hT
      have hantiderivative' :
          (addSequentialSums true state.sums contribution).antiderivative.Contains
            (antiderivative + atomAntiderivativeReal a x) := by
        exact contains_addCompressed hantiderivative hcontribution trigPrecision
      have hcache' : DeltaCacheSound (x : ℝ) (some (gap, D)) := hD
      have hrest := ih (sequentialStep true x state a)
        (antiderivative + atomAntiderivativeReal a x)
        hT hcache' hantiderivative'
      simpa [sequentialLoop, sequentialStep, gap, D, T, contribution,
        add_assoc] using hrest

theorem sequentialAtomSums_antiderivative_contains (x : ℚ)
    (atoms : List RatAtom) :
    (sequentialAtomSums true x atoms).antiderivative.Contains
      (atoms.map fun a ↦ atomAntiderivativeReal a x).sum := by
  have h := sequentialLoop_antiderivative_contains x atoms
    initialSequentialState 0
    (by norm_num [initialSequentialState, RatInterval.Contains, point])
    (by simp [initialSequentialState, DeltaCacheSound])
    (by simpa [initialSequentialState, SequentialSums.zero] using contains_point 0)
  simpa [sequentialAtomSums] using h

/-- Fast row value and derivative intervals produced together. -/
def rowValueDerivativeSequential (row : RatRow) (x : ℚ) :
    RatInterval × RatInterval :=
  let sums := sequentialAtomSums false x row.atoms
  (subCompressed trigPrecision
      (point (row.a0 + row.a1 * x + row.a2 * x ^ 2)) sums.value,
    addCompressed trigPrecision
      (point (row.a1 + 2 * row.a2 * x)) sums.derivative)

theorem rowValueDerivativeSequential_contains (row : RatRow) (x : ℚ) :
    (rowValueDerivativeSequential row x).1.Contains (ratRowFunction row x) ∧
      (rowValueDerivativeSequential row x).2.Contains (ratRowDerivative row x) := by
  have hs := sequentialAtomSums_value_derivative_contains false x row.atoms
  constructor
  · unfold rowValueDerivativeSequential ratRowFunction
    apply contains_subCompressed
    · convert contains_point (row.a0 + row.a1 * x + row.a2 * x ^ 2) using 1
      norm_num
    · simpa [atomValueReal] using hs.1
  · unfold rowValueDerivativeSequential ratRowDerivative
    apply contains_addCompressed
    · convert contains_point (row.a1 + 2 * row.a2 * x) using 1
      norm_num
    · simpa [atomDerivativeReal] using hs.2

/-- Fast antiderivative interval, using the same sequential recurrence. -/
def rowAntiderivativeSequential (row : RatRow) (x : ℚ) : RatInterval :=
  let sums := sequentialAtomSums true x row.atoms
  addCompressed trigPrecision
    (point (row.a0 * x + row.a1 * x ^ 2 / 2 + row.a2 * x ^ 3 / 3))
    sums.antiderivative

theorem rowAntiderivativeSequential_contains (row : RatRow) (x : ℚ) :
    (rowAntiderivativeSequential row x).Contains
      (ratRowAntiderivative row x) := by
  have hs := sequentialAtomSums_antiderivative_contains x row.atoms
  unfold rowAntiderivativeSequential ratRowAntiderivative
  apply contains_addCompressed
  · convert contains_point
      (row.a0 * x + row.a1 * x ^ 2 / 2 + row.a2 * x ^ 3 / 3) using 1
    norm_num
  · simpa [atomAntiderivativeReal] using hs

end ErdosMinimum
