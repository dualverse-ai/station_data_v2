import JacobianS2.DenseFiber
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The nonzero-discriminant generic locus

Over an algebraically closed characteristic-zero field, a nonzero discriminant
turns the conditional split/simple-root theorem into an unconditional theorem
on the standard Zariski-open generic locus.
-/

namespace JacobianS2

section Field

variable {K : Type*} [Field K] [CharZero K]

/-- Cubic structure corresponding to `cubic a q`. -/
def fiberCubic (a : K) (q : Point K) : Cubic K :=
  ⟨1, a, -3 * (q.x * q.y), 2 * (q.x ^ 2 * q.z)⟩

/-- Discriminant of the inverse cubic. -/
def fiberDiscr (a : K) (q : Point K) : K := (fiberCubic a q).discr

theorem fiberCubic_eval (a : K) (q : Point K) (s : K) :
    (fiberCubic a q).toPoly.eval s = cubic a q s := by
  simp only [fiberCubic, Cubic.toPoly, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow, cubic]
  ring

/-- At a cubic root, nonzero discriminant forces the formal derivative to be nonzero. -/
theorem cubicDeriv_ne_zero_of_discr_ne_zero {a : K} {q : Point K} {s : K}
    (hroot : cubic a q s = 0) (hdisc : fiberDiscr a q ≠ 0) :
    cubicDeriv a q s ≠ 0 := by
  intro hD
  apply hdisc
  have hid : fiberDiscr a q =
      -(cubicDeriv a q s) ^ 2 *
        (3 * s ^ 2 + 2 * a * s - a ^ 2 - 12 * (q.x * q.y)) := by
    simp only [fiberDiscr, fiberCubic, Cubic.discr, cubic, cubicDeriv] at *
    linear_combination
      (-54 * (q.x * q.y) * a - 81 * (q.x * q.y) * s -
        54 * (q.x ^ 2 * q.z) - 4 * a ^ 3 + 27 * a * s ^ 2 + 27 * s ^ 3) * hroot
  rw [hid, hD]
  ring

/-- On `X ≠ 0` and nonzero inverse-cubic discriminant, the fiber has exactly
three distinct affine points.  This is the precise generic-locus form of S2. -/
theorem generic_three_sheeted_fiber [IsAlgClosed K] {a : K} {q : Point K}
    (ha : a ≠ 0) (hX : q.x ≠ 0) (hdisc : fiberDiscr a q ≠ 0) :
    ∃ r₁ r₂ r₃ : K,
      let p₁ := recover a q r₁
      let p₂ := recover a q r₂
      let p₃ := recover a q r₃
      map a p₁ = q ∧ map a p₂ = q ∧ map a p₃ = q ∧
        p₁ ≠ p₂ ∧ p₁ ≠ p₃ ∧ p₂ ≠ p₃ ∧
        ∀ p, map a p = q → p = p₁ ∨ p = p₂ ∨ p = p₃ := by
  let C : Cubic K := fiberCubic a q
  have hsplit : C.toPoly.Splits := IsAlgClosed.splits C.toPoly
  have hsplit' : (C.toPoly.map (RingHom.id K)).Splits := by simpa using hsplit
  have hlead : C.a ≠ 0 := by simp [C, fiberCubic]
  obtain ⟨r₁, r₂, r₃, hroots⟩ :=
    (Cubic.splits_iff_roots_eq_three (φ := RingHom.id K) hlead).mp hsplit'
  have hdistinct : r₁ ≠ r₂ ∧ r₁ ≠ r₃ ∧ r₂ ≠ r₃ := by
    have hdC : C.discr ≠ 0 := by simpa [C, fiberDiscr] using hdisc
    exact (Cubic.discr_ne_zero_iff_roots_ne (φ := RingHom.id K) hlead hroots).mp hdC
  have hpoly := Cubic.eq_prod_three_roots (φ := RingHom.id K) hlead hroots
  have hfactor : ∀ s : K, cubic a q s = (s - r₁) * (s - r₂) * (s - r₃) := by
    intro s
    have heval := congrArg (fun p : Polynomial K => p.eval s) hpoly
    simp only [C, fiberCubic, Cubic.map, Cubic.toPoly, RingHom.id_apply,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_X] at heval
    rw [← fiberCubic_eval a q s]
    simpa [fiberCubic, Cubic.map, Cubic.toPoly] using heval
  have hr₁ : cubic a q r₁ = 0 := by rw [hfactor]; ring
  have hr₂ : cubic a q r₂ = 0 := by rw [hfactor]; ring
  have hr₃ : cubic a q r₃ = 0 := by rw [hfactor]; ring
  refine ⟨r₁, r₂, r₃, ?_⟩
  exact three_sheeted_fiber ha hX hfactor hdistinct.1 hdistinct.2.1 hdistinct.2.2
    (cubicDeriv_ne_zero_of_discr_ne_zero hr₁ hdisc)
    (cubicDeriv_ne_zero_of_discr_ne_zero hr₂ hdisc)
    (cubicDeriv_ne_zero_of_discr_ne_zero hr₃ hdisc)

end Field

end JacobianS2
