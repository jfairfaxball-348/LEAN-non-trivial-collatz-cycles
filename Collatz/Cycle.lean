import Collatz.Basic

namespace Collatz

/-- The characteristic denominator appearing in the arithmetic of an odd-to-odd
Collatz cycle description.

If a hypothetical odd cycle has `L` odd nodes and the exact powers of two
removed after those odd steps sum to `A`, then the associated denominator is
`2^A - 3^L`.

This definition alone does not assert that any pair `(A, L)` comes from an
actual Collatz cycle. -/
def cycleDenominator (A L : ℕ) : ℤ :=
  (2 : ℤ) ^ A - (3 : ℤ) ^ L

/-- The positive-denominator region used by the intended local cycle theorem.
We state the strict condition explicitly instead of hiding it in notation. -/
def PositiveCycleDenominator (A L : ℕ) : Prop :=
  1 < cycleDenominator A L

/-- A small arithmetic sanity check for the denominator definition. -/
example : cycleDenominator 4 2 = 7 := by
  norm_num [cycleDenominator]

/-- The same sanity-check parameters lie in the strict positive-denominator region. -/
example : PositiveCycleDenominator 4 2 := by
  norm_num [PositiveCycleDenominator, cycleDenominator]

/-- Exact divisibility by the complete cycle denominator.

This is only a generic arithmetic relation. A later Collatz-specific theorem
must identify the exact integer expression to which the full-denominator
condition applies. -/
def FullDenominatorDivides (A L : ℕ) (x : ℤ) : Prop :=
  cycleDenominator A L ∣ x

end Collatz
