import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Definitions for the direct Möbius cutoff

These are exact rational versions of the quantities in Spotlight 2 of the
paper's Prime number theorem section.
-/

namespace PrimeS2

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

/-- The centered fractional part `{n/d} - 1/2`, represented exactly in `ℚ`. -/
def centeredResidue (n d : ℕ) : ℚ := ((n % d : ℕ) : ℚ) / d - 1 / 2

/-- The centered direct Möbius-cutoff path. -/
def mobiusPath (D n : ℕ) : ℚ :=
  ∑ d ∈ Icc 2 D, (μ d : ℚ) * centeredResidue n d

/-- The incomplete Möbius divisor sum `E_D(n)`. -/
def incompleteMobius (D n : ℕ) : ℤ :=
  ∑ d ∈ Icc 1 D, if d ∣ n then μ d else 0

/-- The Mertens sum `M(D)`. -/
def mertens (D : ℕ) : ℤ := ∑ d ∈ Icc 1 D, μ d

/-- The balanced direct Möbius-cutoff weight from the paper. -/
def directCutoffWeight (D k : ℕ) : ℚ :=
  if k = 1 then -(∑ d ∈ Icc 2 D, (μ d : ℚ) / d)
  else if k ∈ Icc 2 D then (μ k : ℚ) else 0

/-- The paper's original finite floor sum `F_{f_D}(n)`. -/
def weightedFloorSum (D n : ℕ) : ℚ :=
  ∑ k ∈ Icc 1 D, directCutoffWeight D k * (((n / k : ℕ) : ℚ))

/-- The balanced direct-cutoff floor sum, using the exact identity from the paper. -/
def cutoffFloorSum (D n : ℕ) : ℚ :=
  -mobiusPath D n - ((mertens D : ℚ) - 1) / 2

end PrimeS2
