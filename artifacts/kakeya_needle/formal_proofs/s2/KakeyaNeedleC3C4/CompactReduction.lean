import KakeyaNeedleC3C4.TriangleArea

namespace KakeyaNeedleC3C4
open Set MeasureTheory
open scoped ENNReal
noncomputable section

theorem isCompact_triangleUnion (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) :
    IsCompact (triangleUnion n x) := by
  unfold triangleUnion
  exact isCompact_iUnion fun j ↦ isCompact_triangle n hn x j

theorem triangleUnion_volume_lt_top (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) :
    volume (triangleUnion n x) < ∞ :=
  (isCompact_triangleUnion n hn x).measure_lt_top

theorem triangle_horizontal_bounds (n : ℕ) (hn : 0 < n)
    (x : Fin n → ℝ) (j : Fin n) {p : ℝ × ℝ} (hp : p ∈ triangle n x j) :
    x j ≤ p.2 ∧ p.2 ≤ x j + 1 := by
  rcases hp with ⟨hy, hlo, hhi⟩
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · unfold leftEndpoint at hlo
    have hcoef : 0 ≤ ((j.1 + 1 : ℕ) : ℝ) / n :=
      div_nonneg (Nat.cast_nonneg _) (le_of_lt hnR)
    exact (le_add_of_nonneg_right (mul_nonneg hcoef hy.1)).trans hlo
  · have hj : ((j.1 : ℝ) + 1) ≤ n := by exact_mod_cast j.2
    unfold rightEndpoint at hhi
    have hfrac : 1 / (n : ℝ) + (j.1 : ℝ) / n * p.1 ≤ 1 := by
      calc
        1 / (n : ℝ) + (j.1 : ℝ) / n * p.1 ≤
            1 / (n : ℝ) + (j.1 : ℝ) / n := by
              gcongr
              simpa using mul_le_mul_of_nonneg_left hy.2
                (div_nonneg (Nat.cast_nonneg j.1) (le_of_lt hnR))
        _ = ((j.1 : ℝ) + 1) / n := by field_simp; ring
        _ ≤ 1 := (div_le_one hnR).2 hj
    exact hhi.trans (by linarith)

theorem triangles_disjoint_of_separated (n : ℕ) (hn : 0 < n)
    (x : Fin n → ℝ) (i j : Fin n) (hsep : x i + 1 < x j) :
    Disjoint (triangle n x i) (triangle n x j) := by
  rw [Set.disjoint_left]
  intro p hpi hpj
  have hi := triangle_horizontal_bounds n hn x i hpi
  have hj := triangle_horizontal_bounds n hn x j hpj
  linarith

theorem unionArea_ge_pair_of_disjoint (n : ℕ) (hn : 0 < n)
    (x : Fin n → ℝ) (i j : Fin n)
    (hd : Disjoint (triangle n x i) (triangle n x j)) :
    1 / (n : ℝ) ≤ unionArea n x := by
  have hsub : triangle n x i ∪ triangle n x j ⊆ triangleUnion n x := by
    intro p hp
    rcases hp with hp | hp
    · exact mem_iUnion.mpr ⟨i, hp⟩
    · exact mem_iUnion.mpr ⟨j, hp⟩
  calc
    1 / (n : ℝ) = volume.real (triangle n x i) + volume.real (triangle n x j) := by
      rw [triangle_area n hn x i, triangle_area n hn x j]
      field_simp
      ring
    _ = volume.real (triangle n x i ∪ triangle n x j) := by
      symm
      exact measureReal_union hd (measurableSet_triangle n x j)
        (triangle_volume_lt_top n hn x i).ne (triangle_volume_lt_top n hn x j).ne
    _ ≤ volume.real (triangleUnion n x) :=
      measureReal_mono hsub (triangleUnion_volume_lt_top n hn x).ne
    _ = unionArea n x := rfl

/-- Gauge-fixed four-triangle offsets, with the last offset equal to zero. -/
def offsets4 (p : Fin 3 → ℝ) : Fin 4 → ℝ := Fin.snoc p 0

@[simp] theorem offsets4_castSucc (p : Fin 3 → ℝ) (i : Fin 3) :
    offsets4 p i.castSucc = p i := by simp [offsets4]

@[simp] theorem offsets4_last (p : Fin 3 → ℝ) :
    offsets4 p (Fin.last 3) = 0 := by
  exact Fin.snoc_last (n := 3) (α := fun _ : Fin 4 ↦ ℝ) 0 p

/-- Outside the compact cube, two component triangles are horizontally
separated, so their combined area already gives the required `n=4` lower
bound. -/
theorem unionArea_offsets4_ge_of_outside_cube (p : Fin 3 → ℝ)
    (hout : ∃ i, p i < -1 ∨ 1 < p i) :
    (1 : ℝ) / 4 ≤ unionArea 4 (offsets4 p) := by
  obtain ⟨i, hi | hi⟩ := hout
  · apply unionArea_ge_pair_of_disjoint 4 (by norm_num) (offsets4 p)
      i.castSucc (Fin.last 3)
    apply triangles_disjoint_of_separated 4 (by norm_num)
    simp only [offsets4_castSucc, offsets4_last]
    linarith
  · apply unionArea_ge_pair_of_disjoint 4 (by norm_num) (offsets4 p)
      (Fin.last 3) i.castSucc
    apply triangles_disjoint_of_separated 4 (by norm_num)
    simp only [offsets4_castSucc, offsets4_last]
    linarith

/-- Gauge-fixed three-triangle offsets. -/
def offsets3 (p : Fin 2 → ℝ) : Fin 3 → ℝ := Fin.snoc p 0

@[simp] theorem offsets3_castSucc (p : Fin 2 → ℝ) (i : Fin 2) :
    offsets3 p i.castSucc = p i := by simp [offsets3]

@[simp] theorem offsets3_last (p : Fin 2 → ℝ) :
    offsets3 p (Fin.last 2) = 0 := by
  exact Fin.snoc_last (n := 2) (α := fun _ : Fin 3 ↦ ℝ) 0 p

theorem unionArea_offsets3_ge_of_outside_cube (p : Fin 2 → ℝ)
    (hout : ∃ i, p i < -1 ∨ 1 < p i) :
    (5 : ℝ) / 18 ≤ unionArea 3 (offsets3 p) := by
  obtain ⟨i, hi | hi⟩ := hout
  · have hpair := unionArea_ge_pair_of_disjoint 3 (by norm_num) (offsets3 p)
      i.castSucc (Fin.last 2) (triangles_disjoint_of_separated 3 (by norm_num)
        (offsets3 p) i.castSucc (Fin.last 2) (by
          simp only [offsets3_castSucc, offsets3_last]
          linarith))
    norm_num at hpair ⊢
    linarith
  · have hpair := unionArea_ge_pair_of_disjoint 3 (by norm_num) (offsets3 p)
      (Fin.last 2) i.castSucc (triangles_disjoint_of_separated 3 (by norm_num)
        (offsets3 p) (Fin.last 2) i.castSucc (by
          simp only [offsets3_castSucc, offsets3_last]
          linarith))
    norm_num at hpair ⊢
    linarith

def gaugeParams3 (x : Fin 3 → ℝ) : Fin 2 → ℝ :=
  fun i ↦ x i.castSucc - x (Fin.last 2)

def gaugeParams4 (x : Fin 4 → ℝ) : Fin 3 → ℝ :=
  fun i ↦ x i.castSucc - x (Fin.last 3)

theorem unionArea_eq_offsets3_gauge (x : Fin 3 → ℝ) :
    unionArea 3 x = unionArea 3 (offsets3 (gaugeParams3 x)) := by
  have heq : (fun j ↦ offsets3 (gaugeParams3 x) j + x (Fin.last 2)) = x := by
    funext j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · rw [offsets3_last]; simp
    · simp [gaugeParams3]
  calc
    unionArea 3 x = unionArea 3
        (fun j ↦ offsets3 (gaugeParams3 x) j + x (Fin.last 2)) := by rw [heq]
    _ = unionArea 3 (offsets3 (gaugeParams3 x)) := unionArea_add_const ..

theorem unionArea_eq_offsets4_gauge (x : Fin 4 → ℝ) :
    unionArea 4 x = unionArea 4 (offsets4 (gaugeParams4 x)) := by
  have heq : (fun j ↦ offsets4 (gaugeParams4 x) j + x (Fin.last 3)) = x := by
    funext j
    refine Fin.lastCases ?_ (fun i ↦ ?_) j
    · rw [offsets4_last]; simp
    · simp [gaugeParams4]
  calc
    unionArea 4 x = unionArea 4
        (fun j ↦ offsets4 (gaugeParams4 x) j + x (Fin.last 3)) := by rw [heq]
    _ = unionArea 4 (offsets4 (gaugeParams4 x)) := unionArea_add_const ..

end
end KakeyaNeedleC3C4
