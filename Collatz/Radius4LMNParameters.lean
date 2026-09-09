import Collatz.Radius4LogDefect

namespace Collatz

/-- The explicit parameter in the Laurent--Mignotte--Nesterenko specialization
for the logarithmic form `A log 2 - L log 3`. -/
noncomputable def twoThreeLMNParameter (A L : ℕ) : ℝ :=
  max
    (Real.log ((A : ℝ) / Real.log 3 + (L : ℝ) / Real.log 2) + (3 / 50 : ℝ))
    21

/-- The exact quantitative lower-bound proposition needed by the Radius-4
cutoff.  It is a proposition, not an axiom or an extra hypothesis of the
eventual impossibility theorem. -/
def HasTwoThreeLMNLowerBound (A L : ℕ) : Prop :=
  -(22 : ℝ) * (twoThreeLMNParameter A L) ^ 2 * Real.log 2 * Real.log 3 ≤
    Real.log |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3|

/-- The complete specialized LMN theorem to be proved.  Its hypotheses are
kept explicit so the analytic theorem cannot be silently used outside its
intended nonzero two-logarithm regime. -/
def TwoThreeLMNStatement : Prop :=
  ∀ A L : ℕ, 0 < A → 0 < L →
    (A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3 ≠ 0 →
    HasTwoThreeLMNLowerBound A L

/-- The maximum in the LMN parameter supplies its fixed lower threshold. -/
theorem twoThreeLMNParameter_twentyOne_le (A L : ℕ) :
    21 ≤ twoThreeLMNParameter A L := by
  exact le_max_right _ _

/-- In particular, the LMN parameter is positive. -/
theorem twoThreeLMNParameter_pos (A L : ℕ) : 0 < twoThreeLMNParameter A L := by
  calc
    0 < (21 : ℝ) := by norm_num
    _ ≤ twoThreeLMNParameter A L := twoThreeLMNParameter_twentyOne_le A L

/-- Once the specialized LMN theorem is established, its nonvanishing premise
is discharged internally for the `2`--`3` logarithmic form. -/
theorem hasTwoThreeLMNLowerBound_of_statement
    (hLMN : TwoThreeLMNStatement) {A L : ℕ}
    (hA : 0 < A) (hL : 0 < L) :
    HasTwoThreeLMNLowerBound A L :=
  hLMN A L hA hL (log_two_three_defect_ne_zero hA)

end Collatz
