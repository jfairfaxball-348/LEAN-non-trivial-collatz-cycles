import Collatz.WordArithmetic

namespace Collatz

/-- Exact composition law for the inhomogeneous numerator under concatenation.
The suffix contributes its odd-count multiplier to the prefix numerator, while
the prefix length contributes its power-of-two multiplier to the suffix
numerator. -/
theorem wordNumerator_append (xs ys : List Bool) :
    wordNumerator (xs ++ ys) =
      3 ^ listOnes ys * wordNumerator xs +
        2 ^ xs.length * wordNumerator ys := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
      rw [List.cons_append, wordNumerator_cons, listOnes_append, ih,
        wordNumerator_cons, List.length_cons, pow_succ, pow_add]
      ring

/-- Swapping two consecutive parity blocks has an exact integer numerator
comparison. This is the algebraic form naturally produced when a cyclic period
is read from a shifted origin as `tail ++ prefix`. -/
theorem wordNumerator_swap_difference (xs ys : List Bool) :
    (wordNumerator (ys ++ xs) : ℤ) - (wordNumerator (xs ++ ys) : ℤ) =
      ((3 : ℤ) ^ listOnes xs - (2 : ℤ) ^ xs.length) *
          (wordNumerator ys : ℤ) +
        ((2 : ℤ) ^ ys.length - (3 : ℤ) ^ listOnes ys) *
          (wordNumerator xs : ℤ) := by
  rw [wordNumerator_append, wordNumerator_append]
  push_cast
  ring

end Collatz
