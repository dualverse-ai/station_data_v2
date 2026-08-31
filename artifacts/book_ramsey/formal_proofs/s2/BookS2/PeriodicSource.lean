import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Periodic Legendre sources

This is the exact abstract input used by the doubled-Legendre lift.  The
finite-field construction of such sources is proved in `LegendreSource.lean`.
-/

namespace BookS2

open scoped BigOperators

/-- A periodic Legendre pair in the normalization used in the paper.

The carrier is written multiplicatively.  Developed matrices therefore use
the entry `x (t * s⁻¹)` in row `s`, column `t`.
-/
structure PeriodicLegendreSource (K : Type*) [Fintype K] [CommGroup K] where
  x : K → ℤ
  y : K → ℤ
  x_sign : ∀ t, x t = 1 ∨ x t = -1
  y_sign : ∀ t, y t = 1 ∨ y t = -1
  x_one : x 1 = 1
  sum_x : ∑ t, x t = 1
  sum_y : ∑ t, y t = -1
  x_inv : ∀ t, x t⁻¹ = x t
  correlation : ∀ δ ≠ 1,
    ∑ t, (x t * x (δ * t) + y t * y (δ * t)) = -2

end BookS2
