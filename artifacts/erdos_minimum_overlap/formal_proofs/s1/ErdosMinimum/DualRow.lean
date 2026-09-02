import ErdosMinimum.PhaseSupport

/-!
# Algebra of one dual certificate row

The measure-theoretic argument in the paper first produces `hraw`, while the
phase inequality bounds each Fourier atom by `charge`.  This lemma checks the
finite summation and the moment substitution exactly.
-/

namespace ErdosMinimum

theorem one_dual_row
    {ι : Type*} [Fintype ι]
    (M m a0 a1 a2 : ℝ)
    (P Q α β charge : ι → ℝ)
    (hraw :
      a0 + a1 * m + a2 * (2 / 3 + m ^ 2 / 2) -
          ∑ i, (α i * P i + β i * Q i) ≤ M)
    (hsupport : ∀ i, α i * P i + β i * Q i ≤ charge i) :
    a0 + a1 * m + a2 * (2 / 3 + m ^ 2 / 2) - ∑ i, charge i ≤ M := by
  have hsum : ∑ i, (α i * P i + β i * Q i) ≤ ∑ i, charge i :=
    Finset.sum_le_sum fun i _ => hsupport i
  linarith

end ErdosMinimum
