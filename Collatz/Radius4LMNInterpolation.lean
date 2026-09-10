import Collatz.Radius4LMNZeroLemma

namespace Collatz

/-- The finite auxiliary function used by the algebraic side of an
interpolation construction.  The later quantitative LMN argument will choose
the coefficients and degrees; this definition deliberately keeps that choice
explicit. -/
noncomputable def interpolationAuxiliary
    {ι : Type*} [Fintype ι] (coefficient : ι → ℂ) (degree : ι → ℕ) : ℂ → ℂ :=
  fun z => ∑ i, coefficient i * z ^ degree i

/-- The entrywise first-derivative matrix for a family of monomial
interpolation rows.  Row `i` has degree `degree i`; column `j` supplies its
coefficient. -/
noncomputable def interpolationDerivativeMatrix
    {ι κ : Type*} [Fintype ι]
    (coefficient : Matrix ι κ ℂ) (degree : ι → ℕ) (z : ℂ) : Matrix ι κ ℂ :=
  fun i j => coefficient i j * (degree i : ℂ) * z ^ (degree i - 1)

/-- The displayed derivative matrix is genuinely the derivative of each
monomial interpolation row. -/
theorem hasDerivAt_interpolation_row
    {ι κ : Type*} [Fintype ι]
    (coefficient : Matrix ι κ ℂ) (degree : ι → ℕ) (i : ι) (j : κ) (z : ℂ) :
    HasDerivAt (fun w => coefficient i j * w ^ degree i)
      (interpolationDerivativeMatrix coefficient degree z i j) z := by
  simpa [interpolationDerivativeMatrix, mul_assoc] using
    (hasDerivAt_pow (degree i) z).const_mul (coefficient i j)

/-- The derivative of the finite auxiliary function is the sum of the
corresponding derivative rows. -/
theorem hasDerivAt_interpolationAuxiliary
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℂ) (degree : ι → ℕ) (z : ℂ) :
    HasDerivAt (interpolationAuxiliary coefficient degree)
      (∑ i, coefficient i * (degree i : ℂ) * z ^ (degree i - 1)) z := by
  change HasDerivAt (fun w => ∑ i, coefficient i * w ^ degree i)
    (∑ i, coefficient i * (degree i : ℂ) * z ^ (degree i - 1)) z
  simpa [mul_assoc] using
    (HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
      (hasDerivAt_pow (degree i) z).const_mul (coefficient i))

/-- If every monomial in the interpolation auxiliary function has positive
degree, then the auxiliary function vanishes at the origin.  This is the
function-level base case of the interpolation multiplicity argument. -/
theorem interpolationAuxiliary_zero_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℂ) (degree : ι → ℕ)
    (hdegree : ∀ i, 0 < degree i) :
    interpolationAuxiliary coefficient degree 0 = 0 := by
  simp only [interpolationAuxiliary]
  apply Finset.sum_eq_zero
  intro i _
  rw [zero_pow (Nat.ne_of_gt (hdegree i))]
  ring

/-- If every monomial degree is at least two, then the first derivative of
the auxiliary function also vanishes at the origin.  Together with the
previous lemma this proves a genuine order-two zero condition without any
analytic LMN estimate. -/
theorem interpolationAuxiliary_derivative_zero_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (coefficient : ι → ℂ) (degree : ι → ℕ)
    (hdegree : ∀ i, 2 ≤ degree i) :
    deriv (interpolationAuxiliary coefficient degree) 0 = 0 := by
  rw [(hasDerivAt_interpolationAuxiliary coefficient degree 0).deriv]
  apply Finset.sum_eq_zero
  intro i _
  have htwo : 2 ≤ degree i := hdegree i
  have hpos : 0 < degree i - 1 := by omega
  rw [zero_pow (Nat.ne_of_gt hpos)]
  ring

end Collatz
