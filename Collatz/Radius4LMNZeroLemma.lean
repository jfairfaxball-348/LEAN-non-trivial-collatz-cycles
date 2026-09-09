import Collatz.Radius4LMNDeterminants

namespace Collatz

/-- Rowwise monomial factors pull out of an interpolation determinant.  This
is the algebraic core of the zero-multiplicity calculation: when row `i` has
a factor `z ^ degree i`, the determinant has their product as a factor. -/
theorem interpolationDeterminant_row_power_factor
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (z : ℂ) (degree : ι → ℕ) :
    ((Matrix.diagonal fun i => z ^ degree i) * A).det =
      (∏ i, z ^ degree i) * A.det := by
  rw [Matrix.det_mul, Matrix.det_diagonal]

/-- A positive row degree forces the row-scaled interpolation determinant to
vanish at the origin. This is the base zero assertion in the multiplicity
argument for interpolation determinants. -/
theorem interpolationDeterminant_row_power_zero_at_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (degree : ι → ℕ)
    (hdegree : ∃ i, 0 < degree i) :
    ((Matrix.diagonal fun i => (0 : ℂ) ^ degree i) * A).det = 0 := by
  rw [interpolationDeterminant_row_power_factor]
  rcases hdegree with ⟨i, hi⟩
  apply mul_eq_zero_of_left
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi]

end Collatz
