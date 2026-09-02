import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/-!
# The continuum Erdős minimum-overlap problem

These definitions follow Theorem 2.1 of the verification notebook.  The
correlation orientation is `g (t + x)`.  `overlapMaximum` uses the pointwise
supremum of the correlation; for admissible `L¹` profiles the correlation is
continuous, so this agrees mathematically with the paper's `L∞` norm.  The
formal continuity and exact `L∞` equivalence are proved in
`OverlapContinuity.lean`.
-/

open MeasureTheory

namespace ErdosMinimum

noncomputable section

/-- The indicator of the active interval `[-1,1]`. -/
def activeInterval (x : ℝ) : ℝ := Set.Icc (-1 : ℝ) 1 |>.indicator (fun _ => 1) x

/-- A pointwise representative of an admissible balanced profile. -/
def Admissible (f : ℝ → ℝ) : Prop :=
  Measurable f ∧
  (∀ x, 0 ≤ f x ∧ f x ≤ activeInterval x) ∧
  ∫ x, f x = 1

/-- The constant half-density on `[-1,1]`; used to show that the admissible
class, and hence the set in the infimum, is nonempty. -/
def balancedProfile (x : ℝ) : ℝ := activeInterval x / 2

theorem balancedProfile_admissible : Admissible balancedProfile := by
  refine ⟨?_, ?_, ?_⟩
  · exact ((measurable_const.indicator measurableSet_Icc).div_const 2)
  · intro x
    by_cases hx : x ∈ Set.Icc (-1 : ℝ) 1
    · simp [balancedProfile, activeInterval, hx]
      norm_num
    · simp [balancedProfile, activeInterval, hx]
  · rw [show (fun x : ℝ => balancedProfile x) =
        fun x => (2 : ℝ)⁻¹ * activeInterval x by
          funext x
          simp [balancedProfile, div_eq_mul_inv, mul_comm]]
    rw [integral_const_mul]
    rw [show (fun x : ℝ => activeInterval x) =
        (fun x : ℝ => (Set.Icc (-1 : ℝ) 1).indicator (fun _ => (1 : ℝ)) x) by rfl]
    rw [integral_indicator_const (1 : ℝ) measurableSet_Icc]
    norm_num [Measure.real, Real.volume_Icc]

def complementProfile (f : ℝ → ℝ) (x : ℝ) : ℝ := activeInterval x - f x

/-- The complementary overlap at shift `x`. -/
noncomputable def overlap (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t, f t * complementProfile f (t + x)

/-- Pointwise supremum of all translated overlaps. -/
noncomputable def overlapMaximum (f : ℝ → ℝ) : ℝ :=
  sSup (Set.range (overlap f))

/-- The continuum minimum-overlap constant. -/
noncomputable def erdosMinimum : ℝ :=
  sInf {r : ℝ | ∃ f : ℝ → ℝ, Admissible f ∧ r = overlapMaximum f}

/-- A conservative exact common floor implied by the four outward-rounded
certificate rows. -/
def certifiedFloor : ℝ :=
  951380643474567731203083941203 /
    2500000000000000000000000000000

theorem claimedLower_lt_certifiedFloor :
    (380552 : ℝ) / 1000000 < certifiedFloor := by
  norm_num [certifiedFloor]

/-- Exact `sInf` bridge: a common floor for every admissible profile is a
floor for the minimum-overlap constant. -/
theorem certifiedFloor_le_erdosMinimum
    (hexists : ∃ f : ℝ → ℝ, Admissible f)
    (huniform : ∀ f : ℝ → ℝ, Admissible f → certifiedFloor ≤ overlapMaximum f) :
    certifiedFloor ≤ erdosMinimum := by
  rw [erdosMinimum]
  apply le_csInf
  · obtain ⟨f, hf⟩ := hexists
    exact ⟨overlapMaximum f, f, hf, rfl⟩
  · rintro r ⟨f, hf, rfl⟩
    exact huniform f hf

/-- Faithful statement of the paper's main discovery, reducing the main bound
to the uniform analytic/certificate estimate `huniform`. -/
theorem erdos_minimum_overlap_lower_bound_of_certificate
    (huniform : ∀ f : ℝ → ℝ, Admissible f → certifiedFloor ≤ overlapMaximum f) :
    (380552 : ℝ) / 1000000 < erdosMinimum := by
  exact lt_of_lt_of_le claimedLower_lt_certifiedFloor
    (certifiedFloor_le_erdosMinimum ⟨balancedProfile, balancedProfile_admissible⟩ huniform)

end

end ErdosMinimum
