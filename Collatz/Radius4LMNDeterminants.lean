import Collatz.Radius4LogDefect
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

namespace Collatz

/-- The analytic upper-bound primitive used by interpolation-determinant
arguments: bounding every complex entry by `x` bounds the determinant by
`card(ι)! * x^card(ι)`.  The later LMN construction must provide its specific
matrix and the complementary nonzero arithmetic lower bound. -/
theorem interpolationDeterminant_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (x : ℝ) (hentries : ∀ i j, ‖A i j‖ ≤ x) :
    ‖A.det‖ ≤ (Fintype.card ι).factorial * x ^ Fintype.card ι := by
  change (IsAbsoluteValue.toAbsoluteValue (‖·‖ : ℂ → ℝ)) A.det ≤
    (Fintype.card ι).factorial * x ^ Fintype.card ι
  simpa only [nsmul_eq_mul] using
    (Matrix.det_le (A := A)
      (abv := IsAbsoluteValue.toAbsoluteValue (‖·‖ : ℂ → ℝ)) hentries)

end Collatz
