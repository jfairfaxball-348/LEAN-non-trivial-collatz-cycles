import Collatz.WordArithmetic

namespace Collatz

/-- The individual weighted contributions of the true bits of a finite parity
word, starting at a supplied power-of-two offset.

A true bit at chronological offset `j` contributes
`2^(offset+j) * 3^(number of true bits strictly after it)`. False bits contribute
no term. This representation exposes the positional weights hidden inside the
recursive definition of `wordNumerator`. -/
def weightedOddTerms : ℕ → List Bool → List ℕ
  | _, [] => []
  | offset, b :: bs =>
      (if b then [2 ^ offset * 3 ^ listOnes bs] else []) ++
        weightedOddTerms (offset + 1) bs

/-- The weighted contribution list has one entry for every true bit. -/
theorem weightedOddTerms_length (offset : ℕ) (bits : List Bool) :
    (weightedOddTerms offset bits).length = listOnes bits := by
  induction bits generalizing offset with
  | nil => simp [weightedOddTerms, listOnes]
  | cons b bs ih =>
      cases b <;> simp [weightedOddTerms, listOnes, ih]

/-- Summing all weighted true-bit contributions recovers the exact word
numerator, with an overall power-of-two offset. -/
theorem weightedOddTerms_sum (offset : ℕ) (bits : List Bool) :
    (weightedOddTerms offset bits).sum = 2 ^ offset * wordNumerator bits := by
  induction bits generalizing offset with
  | nil => simp [weightedOddTerms, wordNumerator]
  | cons b bs ih =>
      cases b with
      | false =>
          simp [weightedOddTerms, wordNumerator, bitOffset, ih, pow_succ]
          ring
      | true =>
          simp [weightedOddTerms, wordNumerator, bitOffset, ih, pow_succ]
          ring

/-- Closed weighted-term form of the parity-word numerator. -/
theorem wordNumerator_eq_weightedOddTerms_sum (bits : List Bool) :
    wordNumerator bits = (weightedOddTerms 0 bits).sum := by
  have h := weightedOddTerms_sum 0 bits
  simpa using h.symm

end Collatz
