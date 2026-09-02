import ErdosMinimum.FixedDyadic

/-!
# Fixed-dyadic replay of the Fourier support charge

The rational coefficient multiplying `sin frequency ^ 2` is rounded outward
once.  Trigonometric values are then generated in frequency order by the same
cached, periodically-reset fixed-dyadic recurrence used for row evaluation.
-/

namespace ErdosMinimum

open FixedInterval

/-- An atom prepared for fixed-dyadic support replay.  The other coefficient
fields in `trigAtom` are deliberately retained so that the proved common
sequential trigonometric evaluator can be reused verbatim. -/
structure FixedSupportAtom where
  trigAtom : FixedAtom
  coefficient : FixedInterval
deriving DecidableEq, Repr

def FixedSupportAtom.ofRatAtom (a : RatAtom) : FixedSupportAtom :=
  ⟨FixedAtom.ofRatAtom a,
    ofRat ((a.alpha + a.beta ^ 2 / a.alpha) / a.frequency ^ 2)⟩

structure FixedSupportState where
  trigState : FixedState
  charge : FixedInterval
deriving DecidableEq, Repr

def initialFixedSupportState : FixedSupportState :=
  ⟨initialFixedState, pointInt 0⟩

def fixedSupportStep (state : FixedSupportState)
    (a : FixedSupportAtom) : FixedSupportState :=
  let reset := state.trigState.stepsSinceReset = 32
  let next := fixedNextTrig 1 state.trigState a.trigAtom
  let sinSquare := mul next.1.1 next.1.1
  let term := mul sinSquare a.coefficient
  ⟨⟨a.trigAtom.frequency, next.1, next.2,
      state.trigState.value, state.trigState.derivative,
      state.trigState.antiderivative,
      if reset then 1 else state.trigState.stepsSinceReset + 1⟩,
    add state.charge term⟩

def fixedSupportLoop :
    List FixedSupportAtom → FixedSupportState → FixedSupportState
  | [], state => state
  | a :: atoms, state =>
      fixedSupportLoop atoms (fixedSupportStep state a)

def fixedSupportChargeInterval (row : RatRow) : FixedInterval :=
  (fixedSupportLoop (row.atoms.map FixedSupportAtom.ofRatAtom)
    initialFixedSupportState).charge

/-- A rational upper bound with the common fixed-dyadic denominator. -/
def fixedSupportChargeUpper (row : RatRow) : ℚ :=
  ((fixedSupportChargeInterval row).hi : ℚ) /
    (fixedDyadicScale : ℚ)

private theorem fixedSupportLoop_contains (atoms : List RatAtom)
    (state : FixedSupportState) (charge : ℝ)
    (htrig : state.trigState.currentTrig.1.Contains
        (Real.sin (state.trigState.previousFrequency : ℝ)) ∧
      state.trigState.currentTrig.2.Contains
        (Real.cos (state.trigState.previousFrequency : ℝ)))
    (hcache : FixedCacheSound ((1 : ℚ) : ℝ) state.trigState.cache)
    (hcharge : state.charge.Contains charge)
    (halpha : ∀ a ∈ atoms, 0 < a.alpha)
    (hfrequency : ∀ a ∈ atoms, a.frequency ≠ 0) :
    let result := fixedSupportLoop
      (atoms.map FixedSupportAtom.ofRatAtom) state
    result.charge.Contains
      (charge + (atoms.map fun a ↦ atomCharge a.toDual).sum) := by
  induction atoms generalizing state charge with
  | nil => simpa [fixedSupportLoop] using hcharge
  | cons a atoms ih =>
      let fa := FixedSupportAtom.ofRatAtom a
      let next := fixedNextTrig 1 state.trigState fa.trigAtom
      have hnext := fixedNextTrig_sound 1 state.trigState fa.trigAtom
        (by simpa using htrig) hcache
      have haPos : 0 < a.alpha := halpha a (by simp)
      have haNe : a.alpha ≠ 0 := ne_of_gt haPos
      have hfreq : a.frequency ≠ 0 := hfrequency a (by simp)
      have hsinSquare : (mul next.1.1 next.1.1).Contains
          (Real.sin (a.frequency : ℝ) ^ 2) := by
        simpa [fa, FixedSupportAtom.ofRatAtom, FixedAtom.ofRatAtom, pow_two]
          using contains_mul hnext.1.1 hnext.1.1
      have hcoefficient : fa.coefficient.Contains
          (((a.alpha + a.beta ^ 2 / a.alpha) / a.frequency ^ 2 : ℚ) : ℝ) := by
        simpa only [fa, FixedSupportAtom.ofRatAtom] using
          contains_ofRat ((a.alpha + a.beta ^ 2 / a.alpha) / a.frequency ^ 2)
      have hterm : (mul (mul next.1.1 next.1.1) fa.coefficient).Contains
          (atomCharge a.toDual) := by
        have hmul := contains_mul hsinSquare hcoefficient
        have hfreqReal : (a.frequency : ℝ) ≠ 0 := by exact_mod_cast hfreq
        simp only [atomCharge, RatAtom.toDual]
        rw [Real.sinc_of_ne_zero hfreqReal]
        convert hmul using 1
        push_cast
        field_simp [hfreq, haNe]
        <;> ring
      have hcharge' :
          (add state.charge
            (mul (mul next.1.1 next.1.1) fa.coefficient)).Contains
            (charge + atomCharge a.toDual) :=
        contains_add hcharge hterm
      have hrest := ih (fixedSupportStep state fa)
        (charge + atomCharge a.toDual)
        (by simpa [fixedSupportStep, fa, next] using hnext.1)
        (by simpa [fixedSupportStep, fa, next] using hnext.2) hcharge'
        (fun b hb ↦ halpha b (by simp [hb]))
        (fun b hb ↦ hfrequency b (by simp [hb]))
      simpa [fixedSupportLoop, fixedSupportStep, fa, next, add_assoc] using hrest

theorem fixedSupportChargeInterval_contains (row : RatRow)
    (halpha : ∀ a ∈ row.atoms, 0 < a.alpha)
    (hfrequency : ∀ a ∈ row.atoms, a.frequency ≠ 0) :
    (fixedSupportChargeInterval row).Contains
      ((row.atoms.map fun a ↦ atomCharge a.toDual).sum) := by
  have hloop := fixedSupportLoop_contains row.atoms
    initialFixedSupportState 0
    (by
      norm_num [initialFixedSupportState, initialFixedState,
        FixedInterval.Contains, pointInt]
      field_simp [fixedDyadicScale_pos.ne']
      constructor <;> norm_num)
    (by simp [initialFixedSupportState, initialFixedState, FixedCacheSound])
    (by norm_num [initialFixedSupportState, FixedInterval.Contains, pointInt])
    halpha hfrequency
  simpa [fixedSupportChargeInterval] using hloop

theorem sum_atomCharge_le_fixedSupportChargeUpper (row : RatRow)
    (halpha : ∀ a ∈ row.atoms, 0 < a.alpha)
    (hfrequency : ∀ a ∈ row.atoms, a.frequency ≠ 0) :
    (∑ i, atomCharge (row.dualAtoms i)) ≤
      (fixedSupportChargeUpper row : ℝ) := by
  have hcontains := fixedSupportChargeInterval_contains row halpha hfrequency
  change (∑ i, atomCharge ((row.atoms.get i).toDual)) ≤ _
  rw [← list_sum_map_eq_fin_sum (l := row.atoms)
    (fun a ↦ atomCharge a.toDual)]
  simpa [fixedSupportChargeUpper, FixedInterval.Contains] using hcontains.2

end ErdosMinimum
