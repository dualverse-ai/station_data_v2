import ErdosMinimum.NumericRow
import Mathlib.Data.List.SplitLengths

/-!
# Exact interval replay of the Fourier support charge
-/

namespace ErdosMinimum

open RatInterval

def atomChargeInterval (a : RatAtom) : RatInterval :=
  mulCompressed trigPrecision
    (mulCompressed trigPrecision
      (scaleCompressed trigPrecision (1 / a.frequency) (trigAt a.frequency).1)
      (scaleCompressed trigPrecision (1 / a.frequency) (trigAt a.frequency).1))
    (point (a.alpha + a.beta ^ 2 / a.alpha))

def supportChargeInterval (row : RatRow) : RatInterval :=
  sumIntervals trigPrecision (row.atoms.map atomChargeInterval)

def SupportReady (row : RatRow) : Prop :=
  ∀ a ∈ row.atoms, trigReady a.frequency ∧ a.frequency ≠ 0

instance (row : RatRow) : Decidable (SupportReady row) := by
  unfold SupportReady
  infer_instance

private theorem atomChargeInterval_contains (a : RatAtom)
    (hready : trigReady a.frequency) (hfreq : a.frequency ≠ 0) :
    (atomChargeInterval a).Contains (atomCharge a.toDual) := by
  have ht := trigAt_contains a.frequency hready
  have hsinc : (scaleCompressed trigPrecision (1 / a.frequency)
      (trigAt a.frequency).1).Contains (Real.sinc (a.frequency : ℝ)) := by
    rw [Real.sinc_of_ne_zero (by exact_mod_cast hfreq)]
    convert contains_scaleCompressed (1 / a.frequency) ht.1 trigPrecision using 1
    norm_num [div_eq_mul_inv, mul_comm]
  have hsquare := contains_mulCompressed hsinc hsinc trigPrecision
  have hgamma : (point (a.alpha + a.beta ^ 2 / a.alpha)).Contains
      ((a.alpha : ℝ) + (a.beta : ℝ) ^ 2 / (a.alpha : ℝ)) := by
    convert contains_point (a.alpha + a.beta ^ 2 / a.alpha) using 1
    norm_num
  simpa [atomChargeInterval, atomCharge, RatAtom.toDual, pow_two] using
    contains_mulCompressed hsquare hgamma trigPrecision

theorem atoms_charge_contains (atoms : List RatAtom)
    (hready : ∀ a ∈ atoms, trigReady a.frequency ∧ a.frequency ≠ 0) :
    (sumIntervals trigPrecision (atoms.map atomChargeInterval)).Contains
      (atoms.map fun a ↦ atomCharge a.toDual).sum := by
  induction atoms with
  | nil => simpa [sumIntervals] using contains_point 0
  | cons a atoms ih =>
      have ha := atomChargeInterval_contains a
        (hready a (by simp)).1 (hready a (by simp)).2
      have htail := ih (fun b hb ↦ hready b (by simp [hb]))
      simpa [sumIntervals] using contains_addCompressed ha htail trigPrecision

theorem supportChargeInterval_contains (row : RatRow) (hready : SupportReady row) :
    (supportChargeInterval row).Contains
      (∑ i, atomCharge (row.dualAtoms i)) := by
  change (supportChargeInterval row).Contains
    (∑ i, atomCharge ((row.atoms.get i).toDual))
  have hsum := list_sum_map_eq_fin_sum (l := row.atoms)
    (fun a ↦ atomCharge a.toDual)
  rw [← hsum]
  unfold supportChargeInterval
  exact atoms_charge_contains row.atoms hready

/-- Sum upper endpoints independently on moderate-size chunks.  This is
mathematically a slightly weaker enclosure than one monolithic accumulator,
but it gives the kernel small, balanced rational computations to check. -/
def chunkedSupportChargeUpper (row : RatRow) (sizes : List ℕ) : ℚ :=
  ((sizes.splitLengths row.atoms).map fun chunk ↦
    (sumIntervals trigPrecision (chunk.map atomChargeInterval)).hi).sum

theorem sum_atomCharge_le_chunkedSupportChargeUpper (row : RatRow)
    (sizes : List ℕ) (hlen : row.atoms.length ≤ sizes.sum)
    (hready : SupportReady row) :
    (∑ i, atomCharge (row.dualAtoms i)) ≤
      (chunkedSupportChargeUpper row sizes : ℝ) := by
  let chunks := sizes.splitLengths row.atoms
  have hflatten : chunks.flatten = row.atoms :=
    List.flatten_splitLengths row.atoms sizes hlen
  have hchunkReady : ∀ chunk ∈ chunks, ∀ a ∈ chunk,
      trigReady a.frequency ∧ a.frequency ≠ 0 := by
    intro chunk hchunk a ha
    apply hready a
    rw [← hflatten]
    exact List.mem_flatten.mpr ⟨chunk, hchunk, ha⟩
  have hchunks :
      (chunks.map fun chunk ↦
          (chunk.map fun a ↦ atomCharge a.toDual).sum).sum ≤
        (chunks.map fun chunk ↦
          ((sumIntervals trigPrecision
            (chunk.map atomChargeInterval)).hi : ℝ)).sum := by
    have go : ∀ cs : List (List RatAtom),
        (∀ chunk ∈ cs, ∀ a ∈ chunk,
          trigReady a.frequency ∧ a.frequency ≠ 0) →
        (cs.map fun chunk ↦
            (chunk.map fun a ↦ atomCharge a.toDual).sum).sum ≤
          (cs.map fun chunk ↦
            ((sumIntervals trigPrecision
              (chunk.map atomChargeInterval)).hi : ℝ)).sum := by
      intro cs hcs
      induction cs with
      | nil => simp
      | cons chunk chunks ih =>
        simp only [List.map_cons, List.sum_cons]
        have hc := atoms_charge_contains chunk (hcs chunk (by simp))
        have ht := ih (fun c hc' a ha ↦ hcs c (by simp [hc']) a ha)
        exact add_le_add hc.2 ht
    exact go chunks hchunkReady
  change (∑ i, atomCharge ((row.atoms.get i).toDual)) ≤ _
  rw [← list_sum_map_eq_fin_sum (l := row.atoms)
    (fun a ↦ atomCharge a.toDual)]
  rw [← hflatten]
  simp only [List.map_flatten, List.sum_flatten]
  simpa [chunkedSupportChargeUpper, chunks] using hchunks

end ErdosMinimum
