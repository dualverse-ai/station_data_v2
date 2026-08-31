import Mathlib

/-!
# Arithmetic for the Yamada--Pott book-Ramsey lift

This file isolates the elementary arithmetic used after the correlation counts have
been established.  Counts involving `H` are stated over `ℤ`, since `H` is a signed
correlation.  The first section connects those statements to the natural-number
parameters of the graph.
-/

namespace BookS3.CodegreeArithmetic

/-- The field order in terms of the odd square-subgroup order `m`. -/
def fieldOrder (m : ℕ) : ℕ := 2 * m + 1

/-- The book parameter in terms of the odd square-subgroup order `m`. -/
def bookParameter (m : ℕ) : ℕ := m ^ 2 + (m + 1) / 2

theorem two_mul_halfSucc_of_odd {m : ℕ} (hm : Odd m) :
    2 * ((m + 1) / 2) = m + 1 := by
  obtain ⟨k, rfl⟩ := hm
  omega

theorem vertex_count {m : ℕ} (hm : Odd m) :
    fieldOrder m * (fieldOrder m - 1) = 4 * bookParameter m - 2 := by
  obtain ⟨k, rfl⟩ := hm
  have hdiv : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  simp [fieldOrder, bookParameter]
  rw [hdiv]
  ring_nf
  omega

theorem degree_count {m : ℕ} (hm : Odd m) :
    m * fieldOrder m - 1 = 2 * bookParameter m - 2 := by
  obtain ⟨k, rfl⟩ := hm
  have hdiv : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  simp [fieldOrder, bookParameter]
  rw [hdiv]
  ring_nf
  omega

theorem bookParameter_int_relation {m : ℕ} (hm : Odd m) :
    2 * (bookParameter m : ℤ) = 2 * (m : ℤ) ^ 2 + m + 1 := by
  have hhalf : 2 * (((m + 1) / 2 : ℕ) : ℤ) = (m : ℤ) + 1 := by
    exact_mod_cast two_mul_halfSucc_of_odd hm
  change 2 * ((m : ℤ) ^ 2 + (((m + 1) / 2 : ℕ) : ℤ)) =
    2 * (m : ℤ) ^ 2 + (m : ℤ) + 1
  nlinarith

section SignedCorrelations

variable {m n H I RA RB RC s : ℤ}

/-- Equation (6), together with the generic signs in (8) and the cross-fibre
correlation (9), gives the same-fibre count in the first fibre.  The result is
left in a sign-uniform form; substituting `s = 1` gives `n - 2`, while
substituting `s = -1` gives `n - 1`. -/
theorem sameFiberA_nonzero_general
    (hn : 2 * n = 2 * m ^ 2 + m + 1)
    (hsource : H + 2 * I = m)
    (hRA : 4 * RA = (m - 2) * (2 * m + 3) - H - 2 * s)
    (hRC : 2 * RC = (m + 1) ^ 2 - I) :
    2 * (RA + RC) = 2 * n - 3 - s := by
  nlinarith

theorem sameFiberA_nonzero_edge
    (hn : 2 * n = 2 * m ^ 2 + m + 1)
    (hsource : H + 2 * I = m)
    (hRA : 4 * RA = (m - 2) * (2 * m + 3) - H - 2)
    (hRC : 2 * RC = (m + 1) ^ 2 - I) :
    RA + RC = n - 2 := by
  nlinarith

theorem sameFiberA_nonzero_nonedge
    (hn : 2 * n = 2 * m ^ 2 + m + 1)
    (hsource : H + 2 * I = m)
    (hRA : 4 * RA = (m - 2) * (2 * m + 3) - H + 2)
    (hRC : 2 * RC = (m + 1) ^ 2 - I) :
    RA + RC = n - 1 := by
  nlinarith

/-- The second fibre has the opposite sign in (8). -/
theorem sameFiberB_nonzero_general
    (hn : 2 * n = 2 * m ^ 2 + m + 1)
    (hsource : H + 2 * I = m)
    (hRB : 4 * RB = (m - 2) * (2 * m + 3) - H + 2 * s)
    (hRC : 2 * RC = (m + 1) ^ 2 - I) :
    2 * (RB + RC) = 2 * n - 3 + s := by
  nlinarith

theorem sameFiberB_nonzero_edge
    (hn : 2 * n = 2 * m ^ 2 + m + 1)
    (hsource : H + 2 * I = m)
    (hRB : 4 * RB = (m - 2) * (2 * m + 3) - H - 2)
    (hRC : 2 * RC = (m + 1) ^ 2 - I) :
    RB + RC = n - 2 := by
  nlinarith

theorem sameFiberB_nonzero_nonedge
    (hn : 2 * n = 2 * m ^ 2 + m + 1)
    (hsource : H + 2 * I = m)
    (hRB : 4 * RB = (m - 2) * (2 * m + 3) - H + 2)
    (hRC : 2 * RC = (m + 1) ^ 2 - I) :
    RB + RC = n - 1 := by
  nlinarith

/-- The `a ≠ 0, b = 0` line of (10). -/
theorem sameFiber_nonzero_zero_value
    (hsource : H + 2 * I = m)
    (hR : 2 * RA = m ^ 2 - 4 + m * H)
    (hRC : RC = m * I) :
    RA + RC = m ^ 2 - 2 := by
  have hmul := congrArg (fun z : ℤ => m * z) hsource
  nlinarith

theorem sameFiber_nonzero_zero_bound
    (hm : 3 ≤ m)
    (hn : 2 * n = 2 * m ^ 2 + m + 1)
    (hsource : H + 2 * I = m)
    (hR : 2 * RA = m ^ 2 - 4 + m * H)
    (hRC : RC = m * I) :
    RA + RC ≤ n - 2 := by
  have hvalue : RA + RC = m ^ 2 - 2 :=
    sameFiber_nonzero_zero_value hsource hR hRC
  nlinarith

/-- The `a = 0, b ≠ 0` line of (10).  Such a within-fibre pair is a red
nonedge, and its red codegree is exactly `n - 1`. -/
theorem sameFiber_zero_nonzero_value
    (hn : 2 * n = 2 * m ^ 2 + m + 1)
    (hR : 2 * RA = m ^ 2 - 1)
    (hRC : 2 * RC = m * (m + 1)) :
    RA + RC = n - 1 := by
  nlinarith

/-- For a cross-fibre pair with zero field coordinate the common-red count is
`m² - 1`, hence at most the red-nonedge threshold. -/
theorem cross_zero_bound
    (hm : 1 ≤ m)
    (hn : 2 * n = 2 * m ^ 2 + m + 1) :
    m ^ 2 - 1 ≤ n - 1 := by
  nlinarith

/-- For a nonzero field coordinate, membership in `C` subtracts one from the
cross-fibre convolution and gives the red-edge value `n - 2`. -/
theorem cross_nonzero_edge_value
    (hn : n = m ^ 2 + s) :
    m ^ 2 - 1 + s - 1 = n - 2 := by
  omega

/-- For a nonzero field coordinate outside `C`, the cross-fibre convolution is
the red-nonedge value `n - 1`. -/
theorem cross_nonzero_nonedge_value
    (hn : n = m ^ 2 + s) :
    m ^ 2 - 1 + s = n - 1 := by
  omega

end SignedCorrelations

section NaturalInstantiation

variable {m : ℕ}

theorem halfSucc_int_relation (hm : Odd m) :
    2 * ((((m + 1) / 2 : ℕ) : ℤ)) = (m : ℤ) + 1 := by
  exact_mod_cast two_mul_halfSucc_of_odd hm

theorem cross_nonzero_edge_at_parameters (m : ℕ) :
    (m : ℤ) ^ 2 - 1 + ((m + 1) / 2 : ℕ) - 1 =
      (bookParameter m : ℤ) - 2 := by
  rw [bookParameter]
  push_cast
  ring

theorem cross_nonzero_nonedge_at_parameters (m : ℕ) :
    (m : ℤ) ^ 2 - 1 + ((m + 1) / 2 : ℕ) =
      (bookParameter m : ℤ) - 1 := by
  rw [bookParameter]
  push_cast
  ring

end NaturalInstantiation

end BookS3.CodegreeArithmetic
