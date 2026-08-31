import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set

namespace HardyLittlewoodS1

noncomputable section

/-- A bounded open interval, stored by its endpoints. -/
structure OpenInterval where
  left : ℝ
  right : ℝ

local instance : DecidableEq OpenInterval := Classical.decEq _

namespace OpenInterval

/-- The set carried by an open interval. -/
def carrier (I : OpenInterval) : Set ℝ := Ioo I.left I.right

theorem isOpen_carrier (I : OpenInterval) : IsOpen I.carrier := isOpen_Ioo

theorem subset_of_endpoints_le {I J : OpenInterval}
    (hl : J.left ≤ I.left) (hr : I.right ≤ J.right) : I.carrier ⊆ J.carrier := by
  intro z hz
  exact ⟨lt_of_le_of_lt hl hz.1, lt_of_lt_of_le hz.2 hr⟩

/-- Three real intervals with a common point cannot all be essential: one is contained in the
union of the other two.  This is the geometric core of the sharp multiplicity-two cover. -/
theorem three_common_point_redundant (A B C : OpenInterval) {x : ℝ}
    (hA : x ∈ A.carrier) (hB : x ∈ B.carrier) (hC : x ∈ C.carrier) :
    A.carrier ⊆ B.carrier ∪ C.carrier ∨
      B.carrier ⊆ A.carrier ∪ C.carrier ∨
      C.carrier ⊆ A.carrier ∪ B.carrier := by
  have ordered (I J K : OpenInterval) (hxI : x ∈ I.carrier)
      (hxJ : x ∈ J.carrier) (hxK : x ∈ K.carrier)
      (hIJ : I.left ≤ J.left) (hJK : J.left ≤ K.left) :
      I.carrier ⊆ J.carrier ∪ K.carrier ∨
        J.carrier ⊆ I.carrier ∪ K.carrier ∨
        K.carrier ⊆ I.carrier ∪ J.carrier := by
    by_cases hJI : J.right ≤ I.right
    · exact Or.inr (Or.inl fun z hz => Or.inl
        ⟨lt_of_le_of_lt hIJ hz.1, lt_of_lt_of_le hz.2 hJI⟩)
    · have hIJr : I.right < J.right := lt_of_not_ge hJI
      by_cases hKJ : K.right ≤ J.right
      · exact Or.inr (Or.inr fun z hz => Or.inr
          ⟨lt_of_le_of_lt hJK hz.1, lt_of_lt_of_le hz.2 hKJ⟩)
      · have hJKr : J.right < K.right := lt_of_not_ge hKJ
        exact Or.inr (Or.inl fun z hz => by
          by_cases hzI : z < I.right
          · exact Or.inl ⟨lt_of_le_of_lt hIJ hz.1, hzI⟩
          · exact Or.inr ⟨lt_trans hxK.1 (lt_of_lt_of_le hxI.2 (le_of_not_gt hzI)),
              lt_trans hz.2 hJKr⟩)
  by_cases hAB : A.left ≤ B.left
  · by_cases hBC : B.left ≤ C.left
    · exact ordered A B C hA hB hC hAB hBC
    · have hCB : C.left ≤ B.left := le_of_not_ge hBC
      by_cases hAC : A.left ≤ C.left
      · rcases ordered A C B hA hC hB hAC hCB with h | h | h
        · exact Or.inl (by simpa [union_comm] using h)
        · exact Or.inr (Or.inr (by simpa [union_comm] using h))
        · exact Or.inr (Or.inl (by simpa [union_comm] using h))
      · have hCA : C.left ≤ A.left := le_of_not_ge hAC
        rcases ordered C A B hC hA hB hCA hAB with h | h | h
        · exact Or.inr (Or.inr (by simpa [union_comm] using h))
        · exact Or.inl (by simpa [union_comm] using h)
        · exact Or.inr (Or.inl (by simpa [union_comm] using h))
  · have hBA : B.left ≤ A.left := le_of_not_ge hAB
    by_cases hAC : A.left ≤ C.left
    · rcases ordered B A C hB hA hC hBA hAC with h | h | h
      · exact Or.inr (Or.inl (by simpa [union_comm] using h))
      · exact Or.inl (by simpa [union_comm] using h)
      · exact Or.inr (Or.inr (by simpa [union_comm] using h))
    · have hCA : C.left ≤ A.left := le_of_not_ge hAC
      by_cases hBC : B.left ≤ C.left
      · rcases ordered B C A hB hC hA hBC hCA with h | h | h
        · exact Or.inr (Or.inl (by simpa [union_comm] using h))
        · exact Or.inr (Or.inr (by simpa [union_comm] using h))
        · exact Or.inl (by simpa [union_comm] using h)
      · have hCB : C.left ≤ B.left := le_of_not_ge hBC
        rcases ordered C B A hC hB hA hCB hBA with h | h | h
        · exact Or.inr (Or.inr (by simpa [union_comm] using h))
        · exact Or.inr (Or.inl (by simpa [union_comm] using h))
        · exact Or.inl (by simpa [union_comm] using h)

end OpenInterval

/-- A finite interval family covers `K`. -/
def Covers (K : Set ℝ) (s : Finset OpenInterval) : Prop :=
  K ⊆ ⋃ I ∈ s, I.carrier

/-- A cover is irredundant on `K` if deleting any selected interval destroys the cover. -/
def IrredundantOn (K : Set ℝ) (s : Finset OpenInterval) : Prop :=
  Covers K s ∧ ∀ I ∈ s, ¬ Covers K (s.erase I)

/-- Every finite cover has an irredundant subcover. -/
theorem exists_irredundant_subcover (K : Set ℝ) (s : Finset OpenInterval)
    (hs : Covers K s) :
    ∃ t : Finset OpenInterval, t ⊆ s ∧ IrredundantOn K t := by
  classical
  let P : ℕ → Prop := fun n => ∃ t : Finset OpenInterval, t ⊆ s ∧ Covers K t ∧ t.card = n
  have hP : ∃ n, P n := ⟨s.card, s, Subset.rfl, hs, rfl⟩
  let n := Nat.find hP
  obtain ⟨t, hts, htK, htcard⟩ := Nat.find_spec hP
  refine ⟨t, hts, htK, ?_⟩
  intro I hIt hremove
  have herase : t.erase I ⊆ s := (Finset.erase_subset _ _).trans hts
  have hcard : (t.erase I).card < t.card := Finset.card_erase_lt_of_mem hIt
  have : P (t.erase I).card := ⟨t.erase I, herase, hremove, rfl⟩
  have hmin := Nat.find_min' hP this
  omega

/-- In an irredundant finite interval cover, no point belongs to more than two intervals. -/
theorem card_filter_mem_le_two {K : Set ℝ} {s : Finset OpenInterval}
    (hs : IrredundantOn K s) (x : ℝ) :
    (s.filter fun I => I.left < x ∧ x < I.right).card ≤ 2 := by
  classical
  by_contra h
  have hthree : 2 < (s.filter fun I => I.left < x ∧ x < I.right).card := by omega
  obtain ⟨A, B, C, hA, hB, hC, hAB, hAC, hBC⟩ :=
    Finset.two_lt_card_iff.mp hthree
  simp only [Finset.mem_filter] at hA hB hC
  rcases OpenInterval.three_common_point_redundant A B C hA.2 hB.2 hC.2 with hred | hred | hred
  · exact hs.2 A hA.1 (by
      intro z hz
      have hz' := hs.1 hz
      simp only [mem_iUnion, exists_prop] at hz' ⊢
      obtain ⟨I, hIs, hzI⟩ := hz'
      by_cases hIA : I = A
      · subst I
        rcases hred hzI with hzB | hzC
        · exact ⟨B, Finset.mem_erase.mpr ⟨hAB.symm, hB.1⟩, hzB⟩
        · exact ⟨C, Finset.mem_erase.mpr ⟨hAC.symm, hC.1⟩, hzC⟩
      · exact ⟨I, Finset.mem_erase.mpr ⟨hIA, hIs⟩, hzI⟩)
  · exact hs.2 B hB.1 (by
      intro z hz
      have hz' := hs.1 hz
      simp only [mem_iUnion, exists_prop] at hz' ⊢
      obtain ⟨I, hIs, hzI⟩ := hz'
      by_cases hIB : I = B
      · subst I
        rcases hred hzI with hzA | hzC
        · exact ⟨A, Finset.mem_erase.mpr ⟨hAB, hA.1⟩, hzA⟩
        · exact ⟨C, Finset.mem_erase.mpr ⟨hBC.symm, hC.1⟩, hzC⟩
      · exact ⟨I, Finset.mem_erase.mpr ⟨hIB, hIs⟩, hzI⟩)
  · exact hs.2 C hC.1 (by
      intro z hz
      have hz' := hs.1 hz
      simp only [mem_iUnion, exists_prop] at hz' ⊢
      obtain ⟨I, hIs, hzI⟩ := hz'
      by_cases hIC : I = C
      · subst I
        rcases hred hzI with hzA | hzB
        · exact ⟨A, Finset.mem_erase.mpr ⟨hAC, hA.1⟩, hzA⟩
        · exact ⟨B, Finset.mem_erase.mpr ⟨hBC, hB.1⟩, hzB⟩
      · exact ⟨I, Finset.mem_erase.mpr ⟨hIC, hIs⟩, hzI⟩)

end

end HardyLittlewoodS1
