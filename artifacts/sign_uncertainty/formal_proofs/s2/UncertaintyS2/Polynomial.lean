import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Real.Basic

namespace UncertaintyS2

open Polynomial

noncomputable def polynomialOfArray {R : Type*} [Semiring R] [Inhabited R]
    (coeffs : Array R) : Polynomial R :=
  ∑ i ∈ Finset.range coeffs.size, C coeffs[i]! * X ^ i

theorem coeff_polynomialOfArray {R : Type*} [Semiring R] [Inhabited R]
    (coeffs : Array R) (n : ℕ) :
    (polynomialOfArray coeffs).coeff n = if n < coeffs.size then coeffs[n]! else 0 := by
  simp only [polynomialOfArray]
  by_cases h : n < coeffs.size
  · rw [if_pos h]
    simp [h]
  · rw [if_neg h]
    simp [h]

lemma eval_polynomialOfArray {R : Type*} [CommSemiring R] [Inhabited R]
    (coeffs : Array R) (x : R) :
    (polynomialOfArray coeffs).eval x =
      ∑ i ∈ Finset.range coeffs.size, coeffs[i]! * x ^ i := by
  unfold polynomialOfArray
  change (evalRingHom x) (∑ i ∈ Finset.range coeffs.size, C coeffs[i]! * X ^ i) = _
  rw [map_sum]
  simp

def coeffAt (p : Array ℚ) (i : ℕ) : ℚ := (p[i]?).getD 0

theorem coeffAt_eq (p : Array ℚ) (i : ℕ) :
    coeffAt p i = if i < p.size then p[i]! else 0 := by
  by_cases hi : i < p.size
  · simp [coeffAt, hi, Array.getElem?_eq_getElem]
  · simp [coeffAt, hi, Array.getElem?_eq_none]

def addCoeffs (p q : Array ℚ) : Array ℚ :=
  (Array.range (max p.size q.size)).map fun i => coeffAt p i + coeffAt q i

def scaleCoeffs (c : ℚ) (p : Array ℚ) : Array ℚ := p.map fun x => c * x

def shiftCoeffs (p : Array ℚ) : Array ℚ := #[0] ++ p

/-- Coefficients of the generalized Laguerre polynomial `L_n^(-1/2)`. -/
def laguerreStep (state : Array ℚ × Array ℚ) (n : ℕ) : Array ℚ × Array ℚ :=
  let previous := state.1
  let current := state.2
  let next := scaleCoeffs (1 / (n + 1 : ℚ)) <|
    addCoeffs
      (addCoeffs
        (scaleCoeffs (2 * (n : ℚ) + 1 / 2) current)
        (scaleCoeffs (-1) (shiftCoeffs current)))
      (scaleCoeffs (-((n : ℚ) - 1 / 2)) previous)
  (current, next)

def laguerreHalfCoeffs (degree : ℕ) : Array ℚ :=
  if degree = 0 then #[1]
  else
    ((Array.range (degree - 1)).foldl
      (fun state k => laguerreStep state (k + 1)) (#[1], #[1 / 2, -1])).2

noncomputable def laguerreHalfQ (n : ℕ) : Polynomial ℚ :=
  polynomialOfArray (laguerreHalfCoeffs n)

noncomputable def laguerreHalfR (n : ℕ) : Polynomial ℝ :=
  (laguerreHalfQ n).map (Rat.castHom ℝ)

/-- The paper's common ambient space `span {L_0, L_2, ..., L_82}`. -/
def InEvenLaguerreSpan82 (P : Polynomial ℝ) : Prop :=
  ∃ c : Fin 42 → ℝ, P = ∑ j : Fin 42, C (c j) * laguerreHalfR (2 * (j : ℕ))

end UncertaintyS2
