import FlatAutoconvolutionS1.AffineScore
import FlatAutoconvolutionS1.GridBridge
import FlatAutoconvolutionS1.StepBasic

/-!
# Structural bridges for equal-grid and binary steps

These are exact representation results: arbitrary grid origin, mesh, and
amplitude are reduced to the canonical unit-grid finite profile, while Boolean
profiles are realized by genuine nonzero `BinaryStep`s.
-/

open scoped BigOperators
open Set

namespace FlatAutoconvolutionS1

open Finite Bridge

/-- The finite coefficient profile carried by an equal-grid step. -/
def EqualGridStep.profile (g : EqualGridStep) : Profile g.cells := g.weight

/-- The strictly positive sum of the coefficients of an equal-grid step. -/
def EqualGridStep.profileMass (g : EqualGridStep) : ℝ := mass g.profile

theorem EqualGridStep.profileMass_pos (g : EqualGridStep) : 0 < g.profileMass := by
  obtain ⟨i, hi⟩ := g.weight_nonzero
  unfold profileMass profile Finite.mass
  exact hi.trans_le
    (Finset.single_le_sum (fun j _ ↦ g.weight_nonneg j) (Finset.mem_univ i))

/-- Normalize the profile of a nonzero nonnegative step to coefficient mass one. -/
noncomputable def EqualGridStep.normalizedProfile (g : EqualGridStep) : Profile g.cells :=
  fun i ↦ g.weight i / g.profileMass

theorem EqualGridStep.normalizedProfile_nonnegative (g : EqualGridStep) :
    Nonnegative g.normalizedProfile := by
  intro i
  exact div_nonneg (g.weight_nonneg i) g.profileMass_pos.le

@[simp] theorem EqualGridStep.mass_normalizedProfile (g : EqualGridStep) :
    mass g.normalizedProfile = 1 := by
  rw [mass]
  simp only [normalizedProfile, div_eq_mul_inv, ← Finset.sum_mul]
  rw [show (∑ i, g.weight i) = g.profileMass by rfl]
  exact mul_inv_cancel₀ g.profileMass_pos.ne'

theorem EqualGridStep.normalizedProfile_le_one (g : EqualGridStep) (i : Fin g.cells) :
    g.normalizedProfile i ≤ 1 := by
  have hi : g.normalizedProfile i ≤ mass g.normalizedProfile := by
    unfold mass
    exact Finset.single_le_sum
      (fun j _ ↦ g.normalizedProfile_nonnegative j) (Finset.mem_univ i)
  simpa using hi

theorem profileSignal_smul {n : ℕ} (a : ℝ) (w : Profile n) :
    profileSignal (fun i ↦ a * w i) = a • profileSignal w := by
  funext x
  simp [profileSignal, Finset.mul_sum, mul_assoc]

/-- Exact affine-coordinate representation of an arbitrary equal-grid step. -/
theorem EqualGridStep.toSignal_eq_profileSignal_affine (g : EqualGridStep) (x : ℝ) :
    g.toSignal x = profileSignal g.profile ((x - g.origin) / g.mesh) := by
  unfold EqualGridStep.toSignal profileSignal EqualGridStep.profile
  apply Finset.sum_congr rfl
  intro i _
  rw [shiftedUnitCell_eq_indicator]
  congr 1
  by_cases hx : x ∈ Ico
      (g.origin + (i : ℕ) * g.mesh)
      (g.origin + ((i : ℕ) + 1) * g.mesh)
  · have hy : (x - g.origin) / g.mesh ∈ Ico (i : ℝ) (i + 1 : ℝ) := by
      constructor
      · exact (le_div_iff₀ g.mesh_pos).2 (by linarith [hx.1])
      · exact (div_lt_iff₀ g.mesh_pos).2 (by
          linarith [hx.2])
    simp [indicator_of_mem hx, indicator_of_mem hy]
  · have hy : (x - g.origin) / g.mesh ∉ Ico (i : ℝ) (i + 1 : ℝ) := by
      intro hy
      apply hx
      constructor
      · have := (le_div_iff₀ g.mesh_pos).1 hy.1
        linarith
      · have := (div_lt_iff₀ g.mesh_pos).1 hy.2
        norm_num only [Nat.cast_add, Nat.cast_one] at this ⊢
        linarith
    simp [indicator_of_notMem hx, indicator_of_notMem hy]

theorem EqualGridStep.toSignal_eq_affine_profile (g : EqualGridStep) :
    g.toSignal = affineSignal 1 g.origin g.mesh (profileSignal g.profile) := by
  funext x
  simpa [affineSignal] using g.toSignal_eq_profileSignal_affine x

/-- Exact affine representation with coefficient mass normalized to one. -/
theorem EqualGridStep.toSignal_eq_affine_normalizedProfile (g : EqualGridStep) :
    g.toSignal = affineSignal g.profileMass g.origin g.mesh
      (profileSignal g.normalizedProfile) := by
  funext x
  rw [g.toSignal_eq_profileSignal_affine]
  unfold affineSignal
  change profileSignal g.profile ((x - g.origin) / g.mesh) =
    (g.profileMass • profileSignal g.normalizedProfile) ((x - g.origin) / g.mesh)
  rw [← profileSignal_smul]
  congr 2
  funext i
  simp only [normalizedProfile, EqualGridStep.profile]
  field_simp [g.profileMass_pos.ne']

/-- Hence the score of any equal-grid step is exactly the score of its
mass-one canonical unit-grid profile. -/
theorem EqualGridStep.score_toSignal_eq_normalizedProfile (g : EqualGridStep) :
    score g.toSignal = score (profileSignal g.normalizedProfile) := by
  rw [g.toSignal_eq_affine_normalizedProfile]
  exact score_affineSignal g.profileMass g.origin g.mesh
    g.profileMass_pos.ne' g.mesh_pos _

/-- The zero-one real profile associated to a Boolean cell selector. -/
def boolProfile {n : ℕ} (s : Fin n → Bool) : Profile n :=
  fun i ↦ if s i then 1 else 0

theorem boolProfile_binary {n : ℕ} (s : Fin n → Bool) : Binary (boolProfile s) := by
  intro i
  by_cases h : s i = true
  · right
    simp [boolProfile, h]
  · left
    simp [boolProfile, h]

/-- Turn a nonempty Boolean profile into a binary step on mesh `1/T`. -/
noncomputable def binaryStepOfBoolProfile {n T : ℕ} (hT : 0 < T)
    (s : Fin n → Bool) (hs : ∃ i, s i = true) : BinaryStep where
  cells := n
  cells_pos := by
    obtain ⟨i, _⟩ := hs
    exact Nat.pos_of_ne_zero fun hn ↦ Fin.elim0 (hn ▸ i)
  origin := 0
  mesh := (T : ℝ)⁻¹
  mesh_pos := inv_pos.mpr (Nat.cast_pos.mpr hT)
  selected := s
  selected_nonempty := hs

/-- The binary step constructed from a Boolean fine profile is exactly its
canonical profile compressed spatially by `T`. -/
theorem binaryStepOfBoolProfile_toSignal {n T : ℕ} (hT : 0 < T)
    (s : Fin n → Bool) (hs : ∃ i, s i = true) :
    (binaryStepOfBoolProfile hT s hs).toSignal =
      scaledProfileSignal (T : ℝ) (boolProfile s) := by
  funext x
  rw [← BinaryStep.toEqualGridStep_toSignal]
  rw [EqualGridStep.toSignal_eq_profileSignal_affine]
  change profileSignal (boolProfile s) ((x - 0) / (T : ℝ)⁻¹) =
    profileSignal (boolProfile s) ((T : ℝ) * x)
  congr 2
  field_simp [Nat.cast_ne_zero.mpr hT.ne']
  ring

end FlatAutoconvolutionS1
