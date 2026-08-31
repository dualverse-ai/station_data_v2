import KakeyaNeedleC3C4.Slices

namespace KakeyaNeedleC3C4
open Set MeasureTheory
open scoped ENNReal
noncomputable section

def equalInterval (a w : ℝ) : Set ℝ := Icc a (a+w)

theorem equalInterval_inter_of_le {a b w : ℝ} (hab : a ≤ b) :
    equalInterval a w ∩ equalInterval b w = Icc b (a+w) := by
  ext z
  simp [equalInterval]
  constructor
  · rintro ⟨⟨ha, haw⟩, hb, hbw⟩
    exact ⟨hb, haw⟩
  · rintro ⟨hb, haw⟩
    exact ⟨⟨hab.trans hb, haw⟩, hb, by linarith⟩

theorem equalInterval_inter_subset_inter {a b c w : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    equalInterval a w ∩ equalInterval c w ⊆
      equalInterval b w ∩ equalInterval c w := by
  rintro z ⟨⟨ha, haw⟩, hc⟩
  exact ⟨⟨hbc.trans hc.1, by linarith⟩, hc⟩

theorem equalInterval_union_inter_next {a b c w : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) :
    (equalInterval a w ∪ equalInterval b w) ∩ equalInterval c w =
      equalInterval b w ∩ equalInterval c w := by
  rw [union_inter_distrib_right]
  exact union_eq_right.mpr (equalInterval_inter_subset_inter hab hbc)

theorem volume_real_equalInterval {a w : ℝ} (hw : 0 ≤ w) :
    volume.real (equalInterval a w) = w := by
  rw [equalInterval, Real.volume_real_Icc, max_eq_left]
  · ring
  · linarith

theorem volume_real_equalInterval_inter {a b w : ℝ} (hab : a ≤ b) :
    volume.real (equalInterval a w ∩ equalInterval b w) =
      max 0 (w - (b-a)) := by
  rw [equalInterval_inter_of_le hab, Real.volume_real_Icc]
  rw [max_comm]
  congr 1 <;> ring

theorem volume_real_union2_equalIntervals {a b w : ℝ}
    (hw : 0 ≤ w) (hab : a ≤ b) :
    volume.real (equalInterval a w ∪ equalInterval b w) =
      2*w - max 0 (w-(b-a)) := by
  have hfinite (z : ℝ) : volume (equalInterval z w) ≠ ∞ := by
    rw [equalInterval, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have h := measureReal_union_add_inter (s := equalInterval a w)
    (t := equalInterval b w) (μ := volume) measurableSet_Icc (hfinite a) (hfinite b)
  rw [volume_real_equalInterval hw, volume_real_equalInterval hw,
    volume_real_equalInterval_inter hab] at h
  linarith

theorem volume_real_union3_equalIntervals {a b c w : ℝ}
    (hw : 0 ≤ w) (hab : a ≤ b) (hbc : b ≤ c) :
    volume.real (equalInterval a w ∪ equalInterval b w ∪ equalInterval c w) =
      3*w - max 0 (w-(b-a)) - max 0 (w-(c-b)) := by
  have hfinite (z : ℝ) : volume (equalInterval z w) ≠ ∞ := by
    rw [equalInterval, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have habfinite : volume (equalInterval a w ∪ equalInterval b w) ≠ ∞ :=
    (measure_union_lt_top (hfinite a).lt_top (hfinite b).lt_top).ne
  have h := measureReal_union_add_inter
    (s := equalInterval a w ∪ equalInterval b w)
    (t := equalInterval c w) (μ := volume) measurableSet_Icc habfinite (hfinite c)
  rw [equalInterval_union_inter_next hab hbc,
    volume_real_union2_equalIntervals hw hab,
    volume_real_equalInterval hw,
    volume_real_equalInterval_inter hbc] at h
  linarith

theorem volume_real_union4_equalIntervals {a b c d w : ℝ}
    (hw : 0 ≤ w) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    volume.real (equalInterval a w ∪ equalInterval b w ∪
      equalInterval c w ∪ equalInterval d w) =
      4*w - max 0 (w-(b-a)) - max 0 (w-(c-b)) - max 0 (w-(d-c)) := by
  have hinter :
      (equalInterval a w ∪ equalInterval b w ∪ equalInterval c w) ∩
        equalInterval d w = equalInterval c w ∩ equalInterval d w := by
    ext z
    simp only [mem_inter_iff, mem_union, equalInterval, mem_Icc]
    constructor
    · rintro ⟨(⟨ha | hb⟩ | hc), hd⟩
      · exact ⟨⟨hcd.trans hd.1, by linarith⟩, hd⟩
      · exact ⟨⟨hcd.trans hd.1, by linarith⟩, hd⟩
      · exact ⟨hc, hd⟩
    · rintro ⟨hc, hd⟩
      exact ⟨Or.inr hc, hd⟩
  have hfinite (z : ℝ) : volume (equalInterval z w) ≠ ∞ := by
    rw [equalInterval, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have habfinite : volume (equalInterval a w ∪ equalInterval b w) ≠ ∞ :=
    (measure_union_lt_top (hfinite a).lt_top (hfinite b).lt_top).ne
  have habcfinite :
      volume (equalInterval a w ∪ equalInterval b w ∪ equalInterval c w) ≠ ∞ :=
    (measure_union_lt_top habfinite.lt_top (hfinite c).lt_top).ne
  have h := measureReal_union_add_inter
    (s := equalInterval a w ∪ equalInterval b w ∪ equalInterval c w)
    (t := equalInterval d w) (μ := volume) measurableSet_Icc habcfinite (hfinite d)
  rw [hinter, volume_real_union3_equalIntervals hw hab hbc,
    volume_real_equalInterval hw, volume_real_equalInterval_inter hcd] at h
  linarith

theorem sliceInterval_eq_equalInterval (n : ℕ) (hn : 0 < n)
    (x : Fin n → ℝ) (j : Fin n) (y : ℝ) :
    Icc (leftEndpoint n x j y) (rightEndpoint n x j y) =
      equalInterval (leftEndpoint n x j y) ((1-y)/n) := by
  congr 1
  unfold leftEndpoint rightEndpoint
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp
  simp only [Nat.cast_add, Nat.cast_one]
  ring

private theorem iUnion_fin3_perm (A : Fin 3 → Set ℝ) (σ : Equiv.Perm (Fin 3)) :
    (⋃ j, A j) = A (σ 0) ∪ A (σ 1) ∪ A (σ 2) := by
  ext z
  simp only [mem_iUnion, mem_union]
  constructor
  · rintro ⟨j, hj⟩
    have hk : σ.symm j = 0 ∨ σ.symm j = 1 ∨ σ.symm j = 2 := by omega
    rcases hk with hk | hk | hk
    · left; left
      simpa [← hk] using hj
    · left; right
      simpa [← hk] using hj
    · right
      simpa [← hk] using hj
  · rintro ((h | h) | h)
    · exact ⟨σ 0, h⟩
    · exact ⟨σ 1, h⟩
    · exact ⟨σ 2, h⟩

private theorem iUnion_fin4_perm (A : Fin 4 → Set ℝ) (σ : Equiv.Perm (Fin 4)) :
    (⋃ j, A j) = A (σ 0) ∪ A (σ 1) ∪ A (σ 2) ∪ A (σ 3) := by
  ext z
  simp only [mem_iUnion, mem_union]
  constructor
  · rintro ⟨j, hj⟩
    have hk : σ.symm j = 0 ∨ σ.symm j = 1 ∨ σ.symm j = 2 ∨ σ.symm j = 3 := by omega
    rcases hk with hk | hk | hk | hk
    · left; left; left
      simpa [← hk] using hj
    · left; left; right
      simpa [← hk] using hj
    · left; right
      simpa [← hk] using hj
    · right
      simpa [← hk] using hj
  · rintro (((h | h) | h) | h)
    · exact ⟨σ 0, h⟩
    · exact ⟨σ 1, h⟩
    · exact ⟨σ 2, h⟩
    · exact ⟨σ 3, h⟩

/-- Exact slice length once the three left endpoints are given in sorted
order.  All three intervals have the common width `(1-y)/3`. -/
theorem sliceLength_three_of_order (x : Fin 3 → ℝ) (y : ℝ)
    (hy : y ∈ Icc (0 : ℝ) 1) (σ : Equiv.Perm (Fin 3))
    (h01 : leftEndpoint 3 x (σ 0) y ≤ leftEndpoint 3 x (σ 1) y)
    (h12 : leftEndpoint 3 x (σ 1) y ≤ leftEndpoint 3 x (σ 2) y) :
    sliceLength 3 x y =
      3*((1-y)/3) -
        max 0 ((1-y)/3 - (leftEndpoint 3 x (σ 1) y - leftEndpoint 3 x (σ 0) y)) -
        max 0 ((1-y)/3 - (leftEndpoint 3 x (σ 2) y - leftEndpoint 3 x (σ 1) y)) := by
  unfold sliceLength sliceUnion
  rw [iUnion_fin3_perm]
  simp_rw [sliceInterval_eq_equalInterval 3 (by norm_num) x]
  exact volume_real_union3_equalIntervals
    (div_nonneg (sub_nonneg.mpr hy.2) (by norm_num)) h01 h12

/-- Exact slice length once the four left endpoints are given in sorted
order. -/
theorem sliceLength_four_of_order (x : Fin 4 → ℝ) (y : ℝ)
    (hy : y ∈ Icc (0 : ℝ) 1) (σ : Equiv.Perm (Fin 4))
    (h01 : leftEndpoint 4 x (σ 0) y ≤ leftEndpoint 4 x (σ 1) y)
    (h12 : leftEndpoint 4 x (σ 1) y ≤ leftEndpoint 4 x (σ 2) y)
    (h23 : leftEndpoint 4 x (σ 2) y ≤ leftEndpoint 4 x (σ 3) y) :
    sliceLength 4 x y =
      4*((1-y)/4) -
        max 0 ((1-y)/4 - (leftEndpoint 4 x (σ 1) y - leftEndpoint 4 x (σ 0) y)) -
        max 0 ((1-y)/4 - (leftEndpoint 4 x (σ 2) y - leftEndpoint 4 x (σ 1) y)) -
        max 0 ((1-y)/4 - (leftEndpoint 4 x (σ 3) y - leftEndpoint 4 x (σ 2) y)) := by
  unfold sliceLength sliceUnion
  rw [iUnion_fin4_perm]
  simp_rw [sliceInterval_eq_equalInterval 4 (by norm_num) x]
  exact volume_real_union4_equalIntervals
    (div_nonneg (sub_nonneg.mpr hy.2) (by norm_num)) h01 h12 h23

end
end KakeyaNeedleC3C4
