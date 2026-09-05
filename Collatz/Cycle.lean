import Collatz.OddCycle

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

This generic relation becomes Collatz-specific only when a theorem derives it
from an `OddCycle`; `OddCycle.fullDenominatorDivides_numerator` below supplies
that bridge for the composed cycle numerator. -/
def FullDenominatorDivides (A L : ℕ) (x : ℤ) : Prop :=
  cycleDenominator A L ∣ x

namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- The characteristic denominator identity derived from the full composed
cycle equation. No denominator formula is assumed in the `OddCycle` data. -/
theorem denominator_mul_base_eq_numerator (c : OddCycle L) :
    cycleDenominator c.totalExponent L * (c.node 0 : ℤ) =
      (c.prefixNumerator L : ℤ) := by
  have hfull :
      (2 : ℤ) ^ c.totalExponent * (c.node 0 : ℤ) =
        (3 : ℤ) ^ L * (c.node 0 : ℤ) + (c.prefixNumerator L : ℤ) := by
    exact_mod_cast c.full_cycle_identity
  rw [cycleDenominator, sub_mul]
  linarith

/-- Every positive odd cycle has strictly positive characteristic denominator
`2^A - 3^L`. This is a consequence of the cycle equations and positivity, not
an eligibility assumption. -/
theorem cycleDenominator_pos (c : OddCycle L) :
    0 < cycleDenominator c.totalExponent L := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hnumNat : 0 < c.prefixNumerator L := c.prefixNumerator_pos hL
  have hnode : (0 : ℤ) < (c.node 0 : ℤ) := by
    exact_mod_cast c.node_pos 0
  have hnum : (0 : ℤ) < (c.prefixNumerator L : ℤ) := by
    exact_mod_cast hnumNat
  have hid := c.denominator_mul_base_eq_numerator
  nlinarith

/-- The complete denominator divides the exact inhomogeneous numerator produced
by composing the cycle equations. This is the first genuine Collatz-specific
instance of `FullDenominatorDivides` in the repository. -/
theorem fullDenominatorDivides_numerator (c : OddCycle L) :
    FullDenominatorDivides c.totalExponent L (c.prefixNumerator L : ℤ) := by
  refine ⟨(c.node 0 : ℤ), ?_⟩
  exact c.denominator_mul_base_eq_numerator.symm

end OddCycle

end Collatz
