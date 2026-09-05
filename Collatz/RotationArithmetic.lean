import Collatz.CycleWordArithmetic
import Collatz.Encoding

namespace Collatz

/-- The Boolean parity bit used by the word arithmetic is true exactly for odd
natural numbers. This identifies the operational mod-two bit with the oddness
predicate used by the Collatz parity word. -/
theorem stateBit_eq_true_iff (n : ℕ) : stateBit n = true ↔ Odd n := by
  constructor
  · intro hbit
    have hmod_ne : n % 2 ≠ 0 := by
      simpa [stateBit] using hbit
    have hmod_lt : n % 2 < 2 := Nat.mod_lt n (by norm_num)
    have hmod : n % 2 = 1 := by omega
    refine ⟨n / 2, ?_⟩
    have hdiv := Nat.mod_add_div n 2
    omega
  · intro hn
    exact stateBit_of_odd hn

/-- A period of an iterated map remains a period after advancing the starting
point by any number of iterations. -/
theorem iterate_periodic_after_shift {α : Type*} (f : α → α) (x : α)
    {period : ℕ} (hperiod : (f^[period]) x = x) (shift : ℕ) :
    (f^[period]) ((f^[shift]) x) = (f^[shift]) x := by
  calc
    (f^[period]) ((f^[shift]) x) = (f^[period + shift]) x := by
      rw [Function.iterate_add_apply]
    _ = (f^[shift + period]) x := by rw [Nat.add_comm]
    _ = (f^[shift]) ((f^[period]) x) := by
      rw [Function.iterate_add_apply]
    _ = (f^[shift]) x := by rw [hperiod]

/-- If `shift ≤ period`, advancing by `shift` and then by the remaining
`period-shift` iterations reaches the original periodic point. -/
theorem iterate_remaining_after_shift {α : Type*} (f : α → α) (x : α)
    {period shift : ℕ} (hperiod : (f^[period]) x = x)
    (hshift : shift ≤ period) :
    (f^[period - shift]) ((f^[shift]) x) = x := by
  calc
    (f^[period - shift]) ((f^[shift]) x) =
        (f^[(period - shift) + shift]) x := by
      rw [Function.iterate_add_apply]
    _ = (f^[period]) x := by
      rw [show period - shift + shift = period by omega]
    _ = x := hperiod

namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- Every advanced state of the denominator-compatible cycle is again
`A`-periodic under `halfStep`. This is the dynamical half of the rotation
bridge; it does not yet identify the corresponding cyclic word rotation. -/
theorem halfStep_shift_periodic (c : OddCycle L) (shift : ℕ) :
    (halfStep^[c.totalExponent]) ((halfStep^[shift]) (c.node 0)) =
      (halfStep^[shift]) (c.node 0) := by
  exact iterate_periodic_after_shift halfStep (c.node 0)
    c.node_zero_halfStep_periodic shift

/-- Split the base parity list at a representative shift. The second block is
the parity list of the advanced state for the remaining `A-shift` steps. -/
theorem orbitBits_period_split (c : OddCycle L) {shift : ℕ}
    (hshift : shift ≤ c.totalExponent) :
    orbitBits (c.node 0) c.totalExponent =
      orbitBits (c.node 0) shift ++
        orbitBits ((halfStep^[shift]) (c.node 0)) (c.totalExponent - shift) := by
  calc
    orbitBits (c.node 0) c.totalExponent =
        orbitBits (c.node 0) (shift + (c.totalExponent - shift)) := by
      rw [show shift + (c.totalExponent - shift) = c.totalExponent by omega]
    _ = orbitBits (c.node 0) shift ++
        orbitBits ((halfStep^[shift]) (c.node 0)) (c.totalExponent - shift) := by
      exact orbitBits_add (c.node 0) shift (c.totalExponent - shift)

/-- Reading one complete period from the advanced state swaps the two blocks:
first the old tail, then the old prefix after periodic wraparound. -/
theorem orbitBits_shift_period_split (c : OddCycle L) {shift : ℕ}
    (hshift : shift ≤ c.totalExponent) :
    orbitBits ((halfStep^[shift]) (c.node 0)) c.totalExponent =
      orbitBits ((halfStep^[shift]) (c.node 0)) (c.totalExponent - shift) ++
        orbitBits (c.node 0) shift := by
  calc
    orbitBits ((halfStep^[shift]) (c.node 0)) c.totalExponent =
        orbitBits ((halfStep^[shift]) (c.node 0))
          ((c.totalExponent - shift) + shift) := by
      rw [show c.totalExponent - shift + shift = c.totalExponent by omega]
    _ = orbitBits ((halfStep^[shift]) (c.node 0)) (c.totalExponent - shift) ++
        orbitBits
          ((halfStep^[c.totalExponent - shift])
            ((halfStep^[shift]) (c.node 0))) shift := by
      exact orbitBits_add ((halfStep^[shift]) (c.node 0))
        (c.totalExponent - shift) shift
    _ = orbitBits ((halfStep^[shift]) (c.node 0)) (c.totalExponent - shift) ++
        orbitBits (c.node 0) shift := by
      rw [iterate_remaining_after_shift halfStep (c.node 0)
        c.node_zero_halfStep_periodic hshift]

/-- Every representative cyclic shift of the genuine `A`-step parity orbit
still contains exactly the same `L` odd source bits. -/
theorem orbitBits_shift_total_ones (c : OddCycle L) {shift : ℕ}
    (hshift : shift ≤ c.totalExponent) :
    listOnes
      (orbitBits ((halfStep^[shift]) (c.node 0)) c.totalExponent) = L := by
  have hbase := congrArg listOnes (c.orbitBits_period_split hshift)
  have hrot := congrArg listOnes (c.orbitBits_shift_period_split hshift)
  rw [c.orbitBits_total_ones, listOnes_append] at hbase
  rw [listOnes_append] at hrot
  omega

/-- The word denominator computed from a full period beginning at an advanced
state is still the complete cycle denominator `2^A - 3^L`. -/
theorem shifted_wordDenominator_eq_cycleDenominator (c : OddCycle L)
    {shift : ℕ} (hshift : shift ≤ c.totalExponent) :
    wordDenominator
        (orbitBits ((halfStep^[shift]) (c.node 0)) c.totalExponent) =
      cycleDenominator c.totalExponent L := by
  rw [wordDenominator, orbitBits_length, c.orbitBits_shift_total_ones hshift,
    cycleDenominator]

/-- Full-denominator identity for every advanced starting state of the same
periodic `halfStep` orbit. This is the arithmetic half of the rotation bridge:
what remains is to identify the corresponding parity list/cyclic word with
`rotate c.parityWord shift`. -/
theorem cycleDenominator_mul_shiftedState_eq_wordNumerator (c : OddCycle L)
    {shift : ℕ} (hshift : shift ≤ c.totalExponent) :
    cycleDenominator c.totalExponent L *
        (((halfStep^[shift]) (c.node 0) : ℕ) : ℤ) =
      (wordNumerator
        (orbitBits ((halfStep^[shift]) (c.node 0)) c.totalExponent) : ℤ) := by
  have h := periodic_word_denominator_identity (c.halfStep_shift_periodic shift)
  rw [c.shifted_wordDenominator_eq_cycleDenominator hshift] at h
  exact h

/-- Consequently the complete cycle denominator divides the exact numerator
of every advanced full-period parity list. -/
theorem fullDenominatorDivides_shifted_wordNumerator (c : OddCycle L)
    {shift : ℕ} (hshift : shift ≤ c.totalExponent) :
    FullDenominatorDivides c.totalExponent L
      (wordNumerator
        (orbitBits ((halfStep^[shift]) (c.node 0)) c.totalExponent) : ℤ) := by
  refine ⟨(((halfStep^[shift]) (c.node 0) : ℕ) : ℤ), ?_⟩
  exact (c.cycleDenominator_mul_shiftedState_eq_wordNumerator hshift).symm

end OddCycle
end Collatz
