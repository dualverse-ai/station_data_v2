import ErdosMinimum.OverlapContinuity

/-!
# Paper-facing formulation of the minimum-overlap problem

The paper states the problem for Lebesgue-measurable profiles and uses the
`L∞` norm of their overlaps.  Such profiles are naturally defined only up to
null sets.  `PaperAdmissible` therefore imposes measurability and the pointwise
range/support constraints almost everywhere.

This file constructs a Borel-measurable representative satisfying all bounds
everywhere, proves that changing a profile on a null set changes none of its
translated overlaps, and identifies the paper-facing constant exactly with
`erdosMinimum`.
-/

open MeasureTheory Set Filter

namespace ErdosMinimum

noncomputable section

/-- The paper's admissible class, expressed invariantly under changes on a
Lebesgue-null set.  The inequality against `activeInterval` simultaneously
encodes `0 ≤ f ≤ 1` on `[-1,1]` and zero support outside it. -/
def PaperAdmissible (f : ℝ → ℝ) : Prop :=
  AEMeasurable f volume ∧
  (∀ᵐ x ∂volume, 0 ≤ f x ∧ f x ≤ activeInterval x) ∧
  ∫ x, f x = 1

/-- A canonical Borel-measurable version of an a.e.-measurable profile,
clipped into the admissible pointwise range. -/
noncomputable def paperRepresentative (f : ℝ → ℝ)
    (hfm : AEMeasurable f volume) (x : ℝ) : ℝ :=
  max 0 (min (activeInterval x) (hfm.mk f x))

theorem paperRepresentative_measurable (f : ℝ → ℝ)
    (hfm : AEMeasurable f volume) :
    Measurable (paperRepresentative f hfm) := by
  apply Measurable.max measurable_const
  apply Measurable.min
  · exact measurable_const.indicator measurableSet_Icc
  · exact hfm.measurable_mk

theorem paperRepresentative_bounds (f : ℝ → ℝ)
    (hfm : AEMeasurable f volume) (x : ℝ) :
    0 ≤ paperRepresentative f hfm x ∧
      paperRepresentative f hfm x ≤ activeInterval x := by
  dsimp [paperRepresentative]
  constructor
  · exact le_max_left _ _
  · rw [max_le_iff]
    exact ⟨activeInterval_nonneg x, min_le_left _ _⟩

/-- The canonical representative agrees almost everywhere with an admissible
paper profile. -/
theorem paperRepresentative_ae_eq {f : ℝ → ℝ} (hf : PaperAdmissible f) :
    f =ᵐ[volume] paperRepresentative f hf.1 := by
  filter_upwards [hf.1.ae_eq_mk, hf.2.1] with x hmk hbounds
  simp only [paperRepresentative]
  rw [← hmk, min_eq_right hbounds.2, max_eq_right hbounds.1]

/-- Every a.e.-admissible paper profile has an everywhere-admissible Borel
representative. -/
theorem PaperAdmissible.toAdmissible {f : ℝ → ℝ} (hf : PaperAdmissible f) :
    Admissible (paperRepresentative f hf.1) := by
  refine ⟨paperRepresentative_measurable f hf.1, paperRepresentative_bounds f hf.1, ?_⟩
  exact (integral_congr_ae (paperRepresentative_ae_eq hf)).symm.trans hf.2.2

/-- The pointwise formulation is a special case of the paper's a.e.
formulation. -/
theorem Admissible.toPaperAdmissible {f : ℝ → ℝ} (hf : Admissible f) :
    PaperAdmissible f := by
  exact ⟨hf.1.aemeasurable, Eventually.of_forall hf.2.1, hf.2.2⟩

/-- Altering a profile on a null set does not alter any translated overlap.
Translation invariance of Lebesgue measure is used for the shifted factor. -/
theorem overlap_congr_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) :
    overlap f = overlap g := by
  funext x
  rw [overlap, overlap]
  have hshift : ∀ᵐ t ∂volume, f (t + x) = g (t + x) := by
    simpa only [add_comm] using (eventually_add_left_iff volume x).2 hfg
  apply integral_congr_ae
  filter_upwards [hfg, hshift] with t ht htx
  rw [ht]
  simp only [complementProfile, htx]

theorem overlapMaximum_congr_ae {f g : ℝ → ℝ} (hfg : f =ᵐ[volume] g) :
    overlapMaximum f = overlapMaximum g := by
  rw [overlapMaximum, overlapMaximum, overlap_congr_ae hfg]

/-- The overlap of an a.e.-admissible profile is itself continuous; this also
shows directly that its pointwise and essential suprema agree. -/
theorem PaperAdmissible.overlap_continuous {f : ℝ → ℝ} (hf : PaperAdmissible f) :
    Continuous (overlap f) := by
  rw [overlap_congr_ae (paperRepresentative_ae_eq hf)]
  exact ErdosMinimum.overlap_continuous hf.toAdmissible

/-- The real-valued measure-theoretic `L∞` seminorm appearing in the paper. -/
noncomputable def paperOverlapLInfty (f : ℝ → ℝ) : ℝ :=
  (eLpNorm (overlap f) ⊤ volume).toReal

/-- On the paper's a.e.-admissible class, the `L∞` seminorm is exactly the
pointwise overlap supremum. -/
theorem paperOverlapLInfty_eq_overlapMaximum {f : ℝ → ℝ} (hf : PaperAdmissible f) :
    paperOverlapLInfty f = overlapMaximum f := by
  rw [paperOverlapLInfty, overlap_congr_ae (paperRepresentative_ae_eq hf),
    eLpNorm_top_overlap_eq_overlapMaximum hf.toAdmissible,
    ENNReal.toReal_ofReal (overlapMaximum_nonneg hf.toAdmissible)]
  exact (overlapMaximum_congr_ae (paperRepresentative_ae_eq hf)).symm

/-- The minimum-overlap constant in the paper's a.e.-invariant,
measure-theoretic `L∞` formulation. -/
noncomputable def paperErdosMinimum : ℝ :=
  sInf {r : ℝ | ∃ f : ℝ → ℝ, PaperAdmissible f ∧ r = paperOverlapLInfty f}

/-- The paper-facing constant and the representative-based constant used by
the certificate proof are exactly equal. -/
theorem paperErdosMinimum_eq_erdosMinimum :
    paperErdosMinimum = erdosMinimum := by
  unfold paperErdosMinimum erdosMinimum
  congr 1
  ext r
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨paperRepresentative f hf.1, hf.toAdmissible,
      (paperOverlapLInfty_eq_overlapMaximum hf).trans
        (overlapMaximum_congr_ae (paperRepresentative_ae_eq hf))⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, hf.toPaperAdmissible,
      (paperOverlapLInfty_eq_overlapMaximum hf.toPaperAdmissible).symm⟩

end

end ErdosMinimum
