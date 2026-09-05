import Collatz.CycleWordArithmetic

namespace Collatz

/-- A shift of a periodic `halfStep` state has the same period. -/
theorem halfStep_periodic_shift {x A : ℕ}
    (hperiod : (halfStep^[A]) x = x) (s : ℕ) :
    (halfStep^[A]) ((halfStep^[s]) x) = (halfStep^[s]) x := by
  calc
    (halfStep^[A]) ((halfStep^[s]) x) = (halfStep^[A + s]) x := by
      rw [Function.iterate_add_apply]
    _ = (halfStep^[s + A]) x := by rw [Nat.add_comm]
    _ = (halfStep^[s]) ((halfStep^[A]) x) := by
      rw [Function.iterate_add_apply]
    _ = (halfStep^[s]) x := by rw [hperiod]

/-- For a closed `A`-step `halfStep` orbit, every shifted length-`A` parity
block has the same number of true bits as the base block.

The proof compares the two decompositions of the same length `A+s` orbit list:
first `A` then `s`, or first `s` then `A`. -/
theorem orbitBits_shift_ones_eq {x A : ℕ}
    (hperiod : (halfStep^[A]) x = x) (s : ℕ) :
    listOnes (orbitBits ((halfStep^[s]) x) A) =
      listOnes (orbitBits x A) := by
  have hleft := orbitBits_add x A s
  rw [hperiod] at hleft
  have hright := orbitBits_add x s A
  have hseq :
      orbitBits x A ++ orbitBits x s =
        orbitBits x s ++ orbitBits ((halfStep^[s]) x) A := by
    calc
      orbitBits x A ++ orbitBits x s = orbitBits x (A + s) := hleft.symm
      _ = orbitBits x (s + A) := by rw [Nat.add_comm]
      _ = orbitBits x s ++ orbitBits ((halfStep^[s]) x) A := hright
  have hcount := congrArg listOnes hseq
  simp only [listOnes_append] at hcount
  omega

namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- Every natural shift of the base state closes again after the same
`A = totalExponent` one-division steps. -/
theorem shifted_halfStep_periodic (c : OddCycle L) (s : ℕ) :
    (halfStep^[c.totalExponent]) ((halfStep^[s]) (c.node 0)) =
      (halfStep^[s]) (c.node 0) :=
  halfStep_periodic_shift c.node_zero_halfStep_periodic s

/-- Every shifted full-period parity block of an `OddCycle L` has exactly `L`
odd source bits. -/
theorem shifted_orbitBits_ones (c : OddCycle L) (s : ℕ) :
    listOnes
        (orbitBits ((halfStep^[s]) (c.node 0)) c.totalExponent) = L := by
  rw [orbitBits_shift_ones_eq c.node_zero_halfStep_periodic s]
  exact c.orbitBits_total_ones

/-- The genuine parity word beginning at any shifted state has the same full
cycle denominator `2^A - 3^L`. -/
theorem shifted_wordDenominator_eq_cycleDenominator (c : OddCycle L) (s : ℕ) :
    wordDenominator
        (orbitBits ((halfStep^[s]) (c.node 0)) c.totalExponent) =
      cycleDenominator c.totalExponent L := by
  rw [wordDenominator, orbitBits_length, c.shifted_orbitBits_ones s,
    cycleDenominator]

/-- Full-denominator identity for the parity numerator based at an arbitrary
natural shift of the periodic orbit. -/
theorem cycleDenominator_mul_shift_eq_wordNumerator
    (c : OddCycle L) (s : ℕ) :
    cycleDenominator c.totalExponent L *
        (((halfStep^[s]) (c.node 0) : ℕ) : ℤ) =
      (wordNumerator
        (orbitBits ((halfStep^[s]) (c.node 0)) c.totalExponent) : ℤ) := by
  have h := periodic_word_denominator_identity (c.shifted_halfStep_periodic s)
  rw [c.shifted_wordDenominator_eq_cycleDenominator s] at h
  exact h

/-- Subtracting the base and shifted full-period identities gives the exact
shift-specific arithmetic relation. This is the denominator statement that a
future Radius-4 four-boundary calculation must contradict. -/
theorem cycleDenominator_mul_shift_difference
    (c : OddCycle L) (s : ℕ) :
    cycleDenominator c.totalExponent L *
        ((((halfStep^[s]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ)) =
      (wordNumerator
          (orbitBits ((halfStep^[s]) (c.node 0)) c.totalExponent) : ℤ) -
        (wordNumerator (orbitBits (c.node 0) c.totalExponent) : ℤ) := by
  have hs := c.cycleDenominator_mul_shift_eq_wordNumerator s
  have h0 := c.cycleDenominator_mul_base_eq_wordNumerator
  calc
    cycleDenominator c.totalExponent L *
        ((((halfStep^[s]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ)) =
      cycleDenominator c.totalExponent L *
          (((halfStep^[s]) (c.node 0) : ℕ) : ℤ) -
        cycleDenominator c.totalExponent L * (c.node 0 : ℤ) := by ring
    _ = (wordNumerator
          (orbitBits ((halfStep^[s]) (c.node 0)) c.totalExponent) : ℤ) -
        cycleDenominator c.totalExponent L * (c.node 0 : ℤ) := by rw [hs]
    _ = (wordNumerator
          (orbitBits ((halfStep^[s]) (c.node 0)) c.totalExponent) : ℤ) -
        (wordNumerator (orbitBits (c.node 0) c.totalExponent) : ℤ) := by rw [h0]

/-- Consequently the complete cycle denominator divides the difference between
the shifted and base parity numerators. -/
theorem fullDenominatorDivides_shiftNumeratorDifference
    (c : OddCycle L) (s : ℕ) :
    cycleDenominator c.totalExponent L ∣
      (wordNumerator
          (orbitBits ((halfStep^[s]) (c.node 0)) c.totalExponent) : ℤ) -
        (wordNumerator (orbitBits (c.node 0) c.totalExponent) : ℤ) := by
  refine ⟨(((halfStep^[s]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ), ?_⟩
  exact (c.cycleDenominator_mul_shift_difference s).symm

end OddCycle

end Collatz
