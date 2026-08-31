import KakeyaNeedleC3C4.Definitions

namespace KakeyaNeedleC3C4

open Set

noncomputable section

/-- The three vertices of the `j`th triangle, in the height-first coordinate
order used by the formalization. -/
def paperTriangleVertices (n : ℕ) (x : Fin n → ℝ) (j : Fin n) : Set (ℝ × ℝ) :=
  {((0 : ℝ), x j), ((0 : ℝ), x j + 1 / (n : ℝ)),
    ((1 : ℝ), x j + ((j.1 + 1 : ℕ) : ℝ) / (n : ℝ))}

private theorem convex_triangle (n : ℕ) (x : Fin n → ℝ) (j : Fin n) :
    Convex ℝ (triangle n x j) := by
  intro p hp q hq a b ha hb hab
  rcases hp with ⟨⟨hp0, hp1⟩, hpL, hpR⟩
  rcases hq with ⟨⟨hq0, hq1⟩, hqL, hqR⟩
  constructor
  · constructor
    · change 0 ≤ a * p.1 + b * q.1
      nlinarith
    · change a * p.1 + b * q.1 ≤ 1
      nlinarith
  · constructor
    · change leftEndpoint n x j (a * p.1 + b * q.1) ≤ a * p.2 + b * q.2
      calc
        leftEndpoint n x j (a * p.1 + b * q.1) =
            a * leftEndpoint n x j p.1 + b * leftEndpoint n x j q.1 := by
              unfold leftEndpoint
              have hb_eq : b = 1 - a := by linarith
              rw [hb_eq]
              ring
        _ ≤ a * p.2 + b * q.2 :=
          add_le_add (mul_le_mul_of_nonneg_left hpL ha)
            (mul_le_mul_of_nonneg_left hqL hb)
    · change a * p.2 + b * q.2 ≤ rightEndpoint n x j (a * p.1 + b * q.1)
      calc
        a * p.2 + b * q.2 ≤
            a * rightEndpoint n x j p.1 + b * rightEndpoint n x j q.1 :=
          add_le_add (mul_le_mul_of_nonneg_left hpR ha)
            (mul_le_mul_of_nonneg_left hqR hb)
        _ = rightEndpoint n x j (a * p.1 + b * q.1) := by
          unfold rightEndpoint
          have hb_eq : b = 1 - a := by linarith
          rw [hb_eq]
          ring

/-- The closed-slice definition is exactly the convex hull of the three
swapped-coordinate vertices appearing in the paper. -/
theorem triangle_eq_convexHull_paperVertices (n : ℕ) (hn : 0 < n)
    (x : Fin n → ℝ) (j : Fin n) :
    triangle n x j = convexHull ℝ (paperTriangleVertices n x j) := by
  apply Set.Subset.antisymm
  · intro p hp
    rcases hp with ⟨⟨hy0, hy1⟩, hu0, hu1⟩
    let L : ℝ := leftEndpoint n x j p.1
    let d : ℝ := (n : ℝ) * (p.2 - L)
    let w : Fin 3 → ℝ := ![1 - p.1 - d, d, p.1]
    let z : Fin 3 → ℝ × ℝ :=
      ![((0 : ℝ), x j), ((0 : ℝ), x j + 1 / (n : ℝ)),
        ((1 : ℝ), x j + ((j.1 + 1 : ℕ) : ℝ) / (n : ℝ))]
    have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hwidth : (n : ℝ) * (rightEndpoint n x j p.1 - L) = 1 - p.1 := by
      dsimp [L, leftEndpoint, rightEndpoint]
      field_simp
      push_cast
      ring
    have hd0 : 0 ≤ d := by
      dsimp [d, L]
      exact mul_nonneg hnR.le (sub_nonneg.mpr hu0)
    have hd1 : d ≤ 1 - p.1 := by
      dsimp [d]
      nlinarith [mul_nonneg hnR.le (sub_nonneg.mpr hu1)]
    apply mem_convexHull_of_exists_fintype w z
    · intro i
      fin_cases i <;> simp [w] <;> linarith
    · rw [Fin.sum_univ_three]
      simp [w]
    · intro i
      fin_cases i <;> simp [z, paperTriangleVertices]
    · rw [Fin.sum_univ_three]
      simp [w, z, d, L, leftEndpoint]
      ext <;> dsimp <;> field_simp <;> push_cast <;> ring
  · apply convexHull_min
    · intro v hv
      simp only [paperTriangleVertices, mem_insert_iff, mem_singleton_iff] at hv
      rcases hv with rfl | rfl | rfl <;>
        simp [triangle, leftEndpoint, rightEndpoint] <;>
        field_simp <;> push_cast <;> nlinarith [show (0 : ℝ) < n by exact_mod_cast hn]
    · exact convex_triangle n x j

end

end KakeyaNeedleC3C4
