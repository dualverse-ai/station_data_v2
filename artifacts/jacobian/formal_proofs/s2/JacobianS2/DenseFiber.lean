import JacobianS2.Definitions

/-!
# The cubic inverse and the three sheets

The main result is `three_sheeted_fiber`: if the target inverse cubic has three
distinct simple roots, its affine fiber consists of exactly the three points
given by the paper's recovery formula.  This is an exact, checkable version of
the paper's word "generic".
-/

namespace JacobianS2

section Field

variable {K : Type*} [Field K] [CharZero K]

theorem dense_P (a : K) (p : Point K) :
    P a p.x p.y p.z = X a p := by
  simp only [P, X, A, u, w]
  ring

theorem dense_Q (a : K) (p : Point K) :
    X a p * Q a p.x p.y p.z = I a p := by
  simp only [X, Q, I, t, A, u, w]
  ring

theorem dense_R (a : K) (p : Point K) :
    X a p ^ 2 * R a p.x p.y p.z = J a p := by
  simp only [X, R, J, t, A, u, w]
  ring

/-- Every source point supplies a root of the inverse cubic of its image. -/
theorem source_cubic (a : K) (p : Point K) :
    cubic a (map a p) (t a p) = 0 := by
  change t a p ^ 3 + a * t a p ^ 2 -
    3 * (P a p.x p.y p.z * Q a p.x p.y p.z) * t a p +
    2 * (P a p.x p.y p.z ^ 2 * R a p.x p.y p.z) = 0
  rw [dense_P, dense_Q, dense_R]
  simp only [I, J]
  ring

/-- At a source point, the derivative of the inverse cubic is `a*A`. -/
theorem source_cubicDeriv (a : K) (p : Point K) :
    cubicDeriv a (map a p) (t a p) = a * A a p := by
  change 3 * t a p ^ 2 + 2 * a * t a p -
    3 * (P a p.x p.y p.z * Q a p.x p.y p.z) = a * A a p
  rw [dense_P, dense_Q]
  simp only [I]
  ring

theorem source_A_ne_zero {a : K} {p q : Point K}
    (hmap : map a p = q) (hX : q.x ≠ 0) : A a p ≠ 0 := by
  intro hA
  apply hX
  rw [← hmap]
  change P a p.x p.y p.z = 0
  rw [dense_P, X, hA, mul_zero]

theorem source_x_ne_zero {a : K} {p q : Point K}
    (hmap : map a p = q) (hX : q.x ≠ 0) : p.x ≠ 0 := by
  intro hx
  apply hX
  rw [← hmap]
  change P a p.x p.y p.z = 0
  rw [dense_P, X, hx, zero_mul]

/-- A multiple inverse-cubic root cannot come from an affine preimage when `X ≠ 0`. -/
theorem source_root_is_simple {a : K} {p q : Point K}
    (ha : a ≠ 0) (hX : q.x ≠ 0) (hmap : map a p = q) :
    cubic a q (t a p) = 0 ∧ cubicDeriv a q (t a p) ≠ 0 := by
  constructor
  · rw [← hmap]
    exact source_cubic a p
  · rw [← hmap, source_cubicDeriv]
    exact mul_ne_zero ha (source_A_ne_zero hmap hX)

private theorem recover_A {a : K} {q : Point K} {s : K}
    (ha : a ≠ 0) (hX : q.x ≠ 0) (hD : cubicDeriv a q s ≠ 0) :
    A a (recover a q s) = cubicDeriv a q s / a := by
  simp only [recover, A, u, w]
  field_simp
  ring

private theorem recover_x {a : K} {q : Point K} {s : K} :
    (recover a q s).x = q.x / (cubicDeriv a q s / a) := by
  rfl

private theorem recover_u {a : K} {q : Point K} {s : K}
    (ha : a ≠ 0) (hX : q.x ≠ 0) (hD : cubicDeriv a q s ≠ 0) :
    u (recover a q s) = 1 + s / (cubicDeriv a q s / a) := by
  simp only [recover, u]
  field_simp

private theorem recover_w {a : K} {q : Point K} {s : K}
    (ha : a ≠ 0) (hX : q.x ≠ 0) (hD : cubicDeriv a q s ≠ 0) :
    w (recover a q s) =
      cubicDeriv a q s / a - a - (3 * a / 2) *
        (1 + s / (cubicDeriv a q s / a)) := by
  simp only [recover, w]
  field_simp

private theorem recover_t {a : K} {q : Point K} {s : K}
    (ha : a ≠ 0) (hX : q.x ≠ 0) (hD : cubicDeriv a q s ≠ 0) :
    t a (recover a q s) = s := by
  rw [t, recover_A ha hX hD, recover_u ha hX hD]
  field_simp
  ring

private theorem recover_X {a : K} {q : Point K} {s : K}
    (ha : a ≠ 0) (hX : q.x ≠ 0) (hD : cubicDeriv a q s ≠ 0) :
    X a (recover a q s) = q.x := by
  rw [X, recover_x, recover_A ha hX hD]
  field_simp

private theorem recover_I {a : K} {q : Point K} {s : K}
    (ha : a ≠ 0) (hX : q.x ≠ 0) (hD : cubicDeriv a q s ≠ 0) :
    I a (recover a q s) = q.x * q.y := by
  rw [I, recover_t ha hX hD, recover_A ha hX hD]
  simp only [cubicDeriv]
  field_simp
  ring

private theorem recover_J {a : K} {q : Point K} {s : K}
    (ha : a ≠ 0) (hX : q.x ≠ 0) (hD : cubicDeriv a q s ≠ 0)
    (hroot : cubic a q s = 0) :
    J a (recover a q s) = q.x ^ 2 * q.z := by
  rw [J, recover_t ha hX hD, recover_A ha hX hD]
  simp only [cubicDeriv] at *
  simp only [cubic] at hroot
  field_simp
  ring_nf at hroot ⊢
  linear_combination -hroot

/-- Every simple root of the target cubic recovers an actual affine preimage. -/
theorem map_recover {a : K} {q : Point K} {s : K}
    (ha : a ≠ 0) (hX : q.x ≠ 0)
    (hroot : cubic a q s = 0) (hD : cubicDeriv a q s ≠ 0) :
    map a (recover a q s) = q := by
  apply Point.ext
  · change P a _ _ _ = q.x
    rw [dense_P, recover_X ha hX hD]
  · change Q a _ _ _ = q.y
    apply (mul_left_cancel₀ hX)
    calc
      q.x * Q a (recover a q s).x (recover a q s).y (recover a q s).z =
          X a (recover a q s) * Q a (recover a q s).x
            (recover a q s).y (recover a q s).z := by rw [recover_X ha hX hD]
      _ = I a (recover a q s) := dense_Q a (recover a q s)
      _ = q.x * q.y := recover_I ha hX hD
  · change R a _ _ _ = q.z
    apply (mul_left_cancel₀ (pow_ne_zero 2 hX))
    calc
      q.x ^ 2 * R a (recover a q s).x (recover a q s).y (recover a q s).z =
          X a (recover a q s) ^ 2 * R a (recover a q s).x
            (recover a q s).y (recover a q s).z := by rw [recover_X ha hX hD]
      _ = J a (recover a q s) := dense_R a (recover a q s)
      _ = q.x ^ 2 * q.z := recover_J ha hX hD hroot

/-- On `X ≠ 0`, the cubic parameter determines an affine preimage uniquely. -/
theorem source_eq_recover {a : K} {p q : Point K}
    (ha : a ≠ 0) (hX : q.x ≠ 0) (hmap : map a p = q) :
    p = recover a q (t a p) := by
  have hA : A a p ≠ 0 := source_A_ne_zero hmap hX
  have hx : p.x ≠ 0 := source_x_ne_zero hmap hX
  have hDq : cubicDeriv a q (t a p) = a * A a p := by
    rw [← hmap]
    exact source_cubicDeriv a p
  have hD : cubicDeriv a q (t a p) ≠ 0 := hDq.symm ▸ mul_ne_zero ha hA
  have hP : p.x * A a p = q.x := by
    rw [← hmap]
    exact (dense_P a p).symm
  apply Point.ext
  · simp only [recover]
    rw [hDq, ← hP]
    field_simp
  · simp only [recover]
    rw [hDq, ← hP]
    field_simp
    simp only [t, u]
    field_simp
    ring
  · simp only [recover]
    rw [hDq, ← hP]
    field_simp
    simp only [t, A, u, w]
    field_simp
    ring

/-- Exact three-sheeted fiber theorem on the dense chart.

The factorization hypothesis says that the inverse cubic splits into the three
listed roots; the derivative hypotheses say they are simple.  The conclusion
both constructs the three preimages and proves that there are no others.
-/
theorem three_sheeted_fiber {a : K} {q : Point K} {r₁ r₂ r₃ : K}
    (ha : a ≠ 0) (hX : q.x ≠ 0)
    (hfactor : ∀ s, cubic a q s = (s - r₁) * (s - r₂) * (s - r₃))
    (hne₁₂ : r₁ ≠ r₂) (hne₁₃ : r₁ ≠ r₃) (hne₂₃ : r₂ ≠ r₃)
    (hD₁ : cubicDeriv a q r₁ ≠ 0)
    (hD₂ : cubicDeriv a q r₂ ≠ 0)
    (hD₃ : cubicDeriv a q r₃ ≠ 0) :
    let p₁ := recover a q r₁
    let p₂ := recover a q r₂
    let p₃ := recover a q r₃
    map a p₁ = q ∧ map a p₂ = q ∧ map a p₃ = q ∧
      p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
      ∀ p, map a p = q → p = p₁ ∨ p = p₂ ∨ p = p₃ := by
  dsimp
  have hr₁ : cubic a q r₁ = 0 := by rw [hfactor]; ring
  have hr₂ : cubic a q r₂ = 0 := by rw [hfactor]; ring
  have hr₃ : cubic a q r₃ = 0 := by rw [hfactor]; ring
  have hm₁ := map_recover ha hX hr₁ hD₁
  have hm₂ := map_recover ha hX hr₂ hD₂
  have hm₃ := map_recover ha hX hr₃ hD₃
  refine ⟨hm₁, hm₂, hm₃, ?_, ?_, ?_, ?_⟩
  · intro heq
    have ht := congrArg (t a) heq
    rw [recover_t ha hX hD₁, recover_t ha hX hD₂] at ht
    exact hne₁₂ ht
  · intro heq
    have ht := congrArg (t a) heq
    rw [recover_t ha hX hD₁, recover_t ha hX hD₃] at ht
    exact hne₁₃ ht
  · intro heq
    have ht := congrArg (t a) heq
    rw [recover_t ha hX hD₂, recover_t ha hX hD₃] at ht
    exact hne₂₃ ht
  · intro p hp
    have hroot := (source_root_is_simple ha hX hp).1
    rw [hfactor] at hroot
    rcases mul_eq_zero.mp hroot with h12 | h3
    · rcases mul_eq_zero.mp h12 with h1 | h2
      · left
        rw [source_eq_recover ha hX hp, sub_eq_zero.mp h1]
      · right; left
        rw [source_eq_recover ha hX hp, sub_eq_zero.mp h2]
    · right; right
      rw [source_eq_recover ha hX hp, sub_eq_zero.mp h3]

end Field

end JacobianS2
