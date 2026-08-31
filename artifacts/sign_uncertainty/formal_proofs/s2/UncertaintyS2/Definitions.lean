import UncertaintyS2.Polynomial
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace UncertaintyS2

open Polynomial Set

/-- A nonnegative point from which the polynomial is nonpositive forever. -/
def TailSet (P : Polynomial ℝ) : Set ℝ :=
  {r | 0 ≤ r ∧ ∀ t, r ≤ t → P.eval t ≤ 0}

/-- The last-sign-change score in the notebook, expressed intrinsically as the
infimum of all eventual-nonpositivity thresholds. -/
noncomputable def tailThreshold (P : Polynomial ℝ) : ℝ := sInf (TailSet P)

def InEvenLaguerreSpan (k : ℕ) (P : Polynomial ℝ) : Prop :=
  ∃ c : ℕ → ℝ,
    P = ∑ j ∈ Finset.range (2 * k + 2), C (c j) * laguerreHalfR (2 * j)

/-- The normalized prescribed-double-root family with at most twenty contacts.
The tail hypothesis is the intrinsic form of the notebook's legality condition. -/
structure DR20Polynomial (P : Polynomial ℝ) : Type where
  k : ℕ
  k_le : k ≤ 20
  roots : Fin k → ℝ
  roots_pos : ∀ i, 0 < roots i
  roots_strictMono : StrictMono roots
  value_at_roots : ∀ i, P.eval (roots i) = 0
  derivative_at_roots : ∀ i, P.derivative.eval (roots i) = 0
  in_span : InEvenLaguerreSpan k P
  at_zero : P.eval 0 = 0
  derivative_at_zero : P.derivative.eval 0 = 1
  tail_nonempty : (TailSet P).Nonempty

def DR20Scores : Set ℝ :=
  {a | ∃ P : Polynomial ℝ, Nonempty (DR20Polynomial P) ∧
    a = tailThreshold P / (2 * Real.pi)}

/-- The formal counterpart of `C_{DR,20}` in Spotlight 2. -/
noncomputable def C_DR_20 : ℝ := sInf DR20Scores

lemma tailSet_bddBelow (P : Polynomial ℝ) : BddBelow (TailSet P) := by
  exact ⟨0, fun _ hr => hr.1⟩

lemma tailThreshold_le {P : Polynomial ℝ} {r : ℝ} (hr : r ∈ TailSet P) :
    tailThreshold P ≤ r := by
  exact csInf_le (tailSet_bddBelow P) hr

lemma tailThreshold_nonneg {P : Polynomial ℝ} (hP : (TailSet P).Nonempty) :
    0 ≤ tailThreshold P := by
  exact le_csInf hP fun _ hr => hr.1

end UncertaintyS2
