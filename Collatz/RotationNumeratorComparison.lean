import Collatz.RotationArithmetic
import Collatz.WordAppendArithmetic

namespace Collatz
namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- A canonical `ZMod A` shift is always a valid natural split point of the
full `A`-step parity period. -/
theorem zmodShift_val_le_totalExponent (c : OddCycle L)
    (shift : ZMod c.encodingPeriod) :
    shift.val ≤ c.totalExponent := by
  have hlt : shift.val < c.totalExponent := by
    simpa [encodingPeriod] using shift.val_lt
  exact Nat.le_of_lt hlt

/-- The numerator difference between the actual full-period parity list read
from an advanced orbit origin and the base full-period parity list is exactly
the finite block-swap formula. No divisibility hypothesis is assumed here. -/
theorem shifted_wordNumerator_sub_base_eq_swap_formula (c : OddCycle L)
    {shift : ℕ} (hshift : shift ≤ c.totalExponent) :
    (wordNumerator
        (orbitBits ((halfStep^[shift]) (c.node 0)) c.totalExponent) : ℤ) -
      (wordNumerator (orbitBits (c.node 0) c.totalExponent) : ℤ) =
        ((3 : ℤ) ^ listOnes (orbitBits (c.node 0) shift) -
            (2 : ℤ) ^ (orbitBits (c.node 0) shift).length) *
          (wordNumerator
            (orbitBits ((halfStep^[shift]) (c.node 0))
              (c.totalExponent - shift)) : ℤ) +
        ((2 : ℤ) ^
              (orbitBits ((halfStep^[shift]) (c.node 0))
                (c.totalExponent - shift)).length -
            (3 : ℤ) ^
              listOnes
                (orbitBits ((halfStep^[shift]) (c.node 0))
                  (c.totalExponent - shift))) *
          (wordNumerator (orbitBits (c.node 0) shift) : ℤ) := by
  rw [c.orbitBits_period_split hshift, c.orbitBits_shift_period_split hshift]
  exact wordNumerator_swap_difference
    (orbitBits (c.node 0) shift)
    (orbitBits ((halfStep^[shift]) (c.node 0)) (c.totalExponent - shift))

/-- Subtracting the two genuine full-denominator identities yields an exact
full-`D` comparison: `D` multiplies the difference between the advanced state
and the base state to the difference of their actual parity-word numerators. -/
theorem cycleDenominator_mul_shiftedState_sub_base_eq_wordNumerator_difference
    (c : OddCycle L) {shift : ℕ} (hshift : shift ≤ c.totalExponent) :
    cycleDenominator c.totalExponent L *
        ((((halfStep^[shift]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ)) =
      (wordNumerator
        (orbitBits ((halfStep^[shift]) (c.node 0)) c.totalExponent) : ℤ) -
      (wordNumerator (orbitBits (c.node 0) c.totalExponent) : ℤ) := by
  rw [mul_sub, c.cycleDenominator_mul_shiftedState_eq_wordNumerator hshift,
    c.cycleDenominator_mul_base_eq_wordNumerator]

/-- The preceding exact full-denominator comparison, with the numerator
difference expanded by the proved prefix/tail swap identity. -/
theorem cycleDenominator_mul_shiftedState_sub_base_eq_swap_formula
    (c : OddCycle L) {shift : ℕ} (hshift : shift ≤ c.totalExponent) :
    cycleDenominator c.totalExponent L *
        ((((halfStep^[shift]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ)) =
        ((3 : ℤ) ^ listOnes (orbitBits (c.node 0) shift) -
            (2 : ℤ) ^ (orbitBits (c.node 0) shift).length) *
          (wordNumerator
            (orbitBits ((halfStep^[shift]) (c.node 0))
              (c.totalExponent - shift)) : ℤ) +
        ((2 : ℤ) ^
              (orbitBits ((halfStep^[shift]) (c.node 0))
                (c.totalExponent - shift)).length -
            (3 : ℤ) ^
              listOnes
                (orbitBits ((halfStep^[shift]) (c.node 0))
                  (c.totalExponent - shift))) *
          (wordNumerator (orbitBits (c.node 0) shift) : ℤ) := by
  calc
    cycleDenominator c.totalExponent L *
        ((((halfStep^[shift]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ)) =
      (wordNumerator
        (orbitBits ((halfStep^[shift]) (c.node 0)) c.totalExponent) : ℤ) -
      (wordNumerator (orbitBits (c.node 0) c.totalExponent) : ℤ) :=
        c.cycleDenominator_mul_shiftedState_sub_base_eq_wordNumerator_difference hshift
    _ = _ := c.shifted_wordNumerator_sub_base_eq_swap_formula hshift

/-- The actual base-versus-advanced numerator difference is divisible by the
entire cycle denominator, with quotient the literal difference of the two
orbit states. This is derived from the cycle and parity orbit rather than
inserted as a generic eligibility assumption. -/
theorem fullDenominatorDivides_shifted_sub_base_wordNumerator
    (c : OddCycle L) {shift : ℕ} (hshift : shift ≤ c.totalExponent) :
    FullDenominatorDivides c.totalExponent L
      ((wordNumerator
          (orbitBits ((halfStep^[shift]) (c.node 0)) c.totalExponent) : ℤ) -
        (wordNumerator (orbitBits (c.node 0) c.totalExponent) : ℤ)) := by
  refine ⟨(((halfStep^[shift]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ), ?_⟩
  exact
    (c.cycleDenominator_mul_shiftedState_sub_base_eq_wordNumerator_difference
      hshift).symm

end OddCycle
end Collatz
