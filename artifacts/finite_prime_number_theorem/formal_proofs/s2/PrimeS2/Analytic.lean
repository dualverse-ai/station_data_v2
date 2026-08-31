import PrimeS2.Main
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Analytic completion of Spotlight 2

The novel finite argument is unconditional in `PrimeS2.Main`.  This file gives
a kernel-checked interface from the standard analytic estimates used in
the notebook to the complete asymptotic conclusion.  The estimates are fields
of a structure—not axioms—because they are absent from the pinned mathlib.
-/

namespace PrimeS2

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

/-- The unscaled objective `A(f_D)` from the paper. -/
noncomputable def cutoffObjective (D : ℕ) : ℝ :=
  -(∑ k ∈ Icc 1 D,
    (directCutoffWeight D k : ℝ) * Real.log k / k)

/-- The objective has the standard truncated Möbius-logarithm form. -/
theorem cutoffObjective_eq (D : ℕ) (hD : 1 ≤ D) :
    cutoffObjective D =
      -(∑ d ∈ Icc 2 D, (μ d : ℝ) * Real.log d / d) := by
  rw [cutoffObjective, ← Finset.insert_Icc_succ_left_eq_Icc hD]
  rw [Finset.sum_insert (by simp)]
  rw [show Order.succ (1 : ℕ) = 2 by rfl]
  norm_num
  apply Finset.sum_congr rfl
  intro d hd
  have hd2 : 2 ≤ d := (Finset.mem_Icc.mp hd).1
  have hd1 : d ≠ 1 := by omega
  simp [directCutoffWeight, hd, hd1]

/-- The growth scale `D / log(D)^2`. -/
noncomputable def obstructionRate (D : ℕ) : ℝ :=
  (D : ℝ) / (Real.log D) ^ 2

/-- The reciprocal score scale `log(D)^2 / D`. -/
noncomputable def scoreRate (D : ℕ) : ℝ :=
  (Real.log D) ^ 2 / (D : ℝ)

/-- The exact prime-band term `E_D(n*)`, viewed in `ℝ`. -/
noncomputable def bandTerm (D : ℕ) : ℝ :=
  ((1 - ((primeBand D).card : ℤ) + ((primeBand D).card.choose 2 : ℤ) : ℤ) : ℝ)

/-- The global roof and the roof-rescaled score, viewed in `ℝ`. -/
noncomputable def roofReal (D : ℕ) : ℝ := (cutoffRoof D : ℝ)

noncomputable def rescaledScore (D : ℕ) : ℝ :=
  cutoffObjective D / roofReal D

/-- Elementary eventual lower-bound formulation of `f = Ω(g)` for the
nonnegative scales used here. -/
def GrowsAtLeast (f g : ℕ → ℝ) : Prop :=
  ∃ c > 0, ∃ N, ∀ D ≥ N, c * g D ≤ f D

/-- Elementary eventual upper-bound formulation of `f = O(g)`. -/
def BoundedBy (f g : ℕ → ℝ) : Prop :=
  ∃ C > 0, ∃ N, ∀ D ≥ N, |f D| ≤ C * g D

/-- Sequential epsilon formulation of convergence to zero. -/
def TendsToZero (f : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ D ≥ N, |f D| < ε

/-- Sequential epsilon formulation of convergence to one. -/
def TendsToOne (f : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ D ≥ N, |f D - 1| < ε

/-- The classical analytic inputs used after the finite prime-band argument,
plus the elementary reciprocal-rate limit. They are deliberately explicit
because the pinned mathlib does not yet prove them. -/
structure ClassicalAnalyticInputs where
  constant : ℝ
  constant_pos : 0 < constant
  start : ℕ
  start_ge_two : 2 ≤ start
  band_lower : ∀ D ≥ start, constant * obstructionRate D ≤ bandTerm D
  mertens_small : ∀ D ≥ start,
    |((mertens D : ℤ) : ℝ)| ≤ (constant / 2) * obstructionRate D
  objective_tends_one : TendsToOne cutoffObjective
  reciprocal_rate_tends_zero : TendsToZero scoreRate

private theorem rate_mul_scoreRate {D : ℕ} (hD : 2 ≤ D) :
    obstructionRate D * scoreRate D = 1 := by
  have hDreal : (0 : ℝ) < D := by positivity
  have hlog : Real.log (D : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < D by omega)))
  rw [obstructionRate, scoreRate]
  field_simp

private theorem obstructionRate_pos {D : ℕ} (hD : 2 ≤ D) :
    0 < obstructionRate D := by
  rw [obstructionRate]
  have hlog : 0 < Real.log (D : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < D by omega))
  exact div_pos (by positivity) (sq_pos_of_pos hlog)

private theorem exact_roof_bound_real (D : ℕ) (hD : 1 ≤ D) :
    (bandTerm D - ((mertens D : ℤ) : ℝ)) / 2 ≤ roofReal D := by
  have hq := mobius_cutoff_primeBand_obstruction D hD
  rw [bandTerm, roofReal]
  exact_mod_cast hq

/-- **Complete conditional formalization of PNT Spotlight 2.**

From the exact finite theorem plus precisely the standard analytic inputs used
in the paper, the direct cutoff roof is `Ω(D/log²D)`, its unscaled objective
tends to `1`, the rescaled score is `O(log²D/D)`, and that score tends to zero.
-/
theorem mobius_cutoff_spotlight2 (h : ClassicalAnalyticInputs) :
    GrowsAtLeast roofReal obstructionRate ∧
      TendsToOne cutoffObjective ∧
      BoundedBy rescaledScore scoreRate ∧
      TendsToZero rescaledScore := by
  let c₀ := h.constant / 4
  have hc₀ : 0 < c₀ := by dsimp [c₀]; exact div_pos h.constant_pos (by norm_num)
  have hroof : ∀ D ≥ h.start, c₀ * obstructionRate D ≤ roofReal D := by
    intro D hDs
    have hD2 : 2 ≤ D := h.start_ge_two.trans hDs
    have hband := h.band_lower D hDs
    have hmertens := h.mertens_small D hDs
    have hmertens_le : ((mertens D : ℤ) : ℝ) ≤
        (h.constant / 2) * obstructionRate D :=
      le_trans (le_abs_self _) hmertens
    have hexact := exact_roof_bound_real D (by omega)
    dsimp [c₀]
    linarith
  have hbig : BoundedBy rescaledScore scoreRate := by
    obtain ⟨Nobj, hNobj⟩ := h.objective_tends_one 1 (by norm_num)
    let N := max h.start Nobj
    let C := 8 / h.constant
    have hC : 0 < C := by dsimp [C]; exact div_pos (by norm_num) h.constant_pos
    refine ⟨C, hC, N, ?_⟩
    intro D hDN
    have hDs : h.start ≤ D := le_trans (le_max_left _ _) hDN
    have hDo : Nobj ≤ D := le_trans (le_max_right _ _) hDN
    have hD2 : 2 ≤ D := h.start_ge_two.trans hDs
    have hratepos : 0 < obstructionRate D := obstructionRate_pos hD2
    have hrecip : obstructionRate D * scoreRate D = 1 := rate_mul_scoreRate hD2
    have hscorepos : 0 < scoreRate D := by nlinarith
    have hroofD := hroof D hDs
    have hroofpos : 0 < roofReal D := lt_of_lt_of_le (mul_pos hc₀ hratepos) hroofD
    have hobjclose := hNobj D hDo
    have hobj : |cutoffObjective D| ≤ 2 := by
      have htri := abs_add_le (cutoffObjective D - 1) 1
      norm_num at htri
      linarith
    rw [rescaledScore, abs_div, abs_of_pos hroofpos]
    apply (div_le_iff₀ hroofpos).2
    have hmult : c₀ * obstructionRate D * (C * scoreRate D) ≤
        roofReal D * (C * scoreRate D) := by
      gcongr
    have hidentity : c₀ * obstructionRate D * (C * scoreRate D) = 2 := by
      dsimp [c₀, C]
      field_simp [ne_of_gt h.constant_pos]
      nlinarith
    rw [mul_comm (C * scoreRate D) (roofReal D)]
    linarith
  refine ⟨⟨c₀, hc₀, h.start, hroof⟩, h.objective_tends_one, hbig, ?_⟩
  · intro ε hε
    obtain ⟨C, hC, Nbig, hNbig⟩ := hbig
    obtain ⟨Nzero, hNzero⟩ :=
      h.reciprocal_rate_tends_zero (ε / C) (div_pos hε hC)
    refine ⟨max Nbig Nzero, ?_⟩
    intro D hDmax
    have hb := hNbig D (le_trans (le_max_left _ _) hDmax)
    have hz := hNzero D (le_trans (le_max_right _ _) hDmax)
    have hrate_nonneg : 0 ≤ scoreRate D := by
      rw [scoreRate]
      positivity
    rw [abs_of_nonneg hrate_nonneg] at hz
    have hz' : C * scoreRate D < ε := by
      calc
        C * scoreRate D < C * (ε / C) := mul_lt_mul_of_pos_left hz hC
        _ = ε := by field_simp [ne_of_gt hC]
    exact lt_of_le_of_lt hb hz'

end PrimeS2
