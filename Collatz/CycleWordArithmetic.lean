import Collatz.Cycle
import Collatz.WordArithmetic

namespace Collatz

namespace OddToOddStep

variable {x y a : ℕ}

/-- The parity list of one exact odd-to-odd block contains exactly one odd
source state. The first source `x` is odd, and after that first `halfStep` the
remaining `a-1` transitions start from an explicit power-of-two multiple of
the odd target, so all their source bits are even. -/
theorem orbitBits_ones (h : OddToOddStep x y a) :
    listOnes (orbitBits x a) = 1 := by
  obtain ⟨b, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h.exponent_pos)
  have hfirst : halfStep x = 2 ^ b * y := by
    rw [halfStep_of_odd h.source_odd]
    have hfactor : 2 ^ (b + 1) * y = 2 * (2 ^ b * y) := by
      rw [pow_succ]
      ring
    rw [h.equation, hfactor]
    simp
  rw [orbitBits]
  rw [stateBit_of_odd h.source_odd]
  rw [hfirst]
  simp [listOnes, orbitBits_pow_two_mul_ones]

end OddToOddStep

namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- The first `k` odd-to-odd blocks contribute exactly `k` odd source bits to
the chronological `halfStep` parity list. -/
theorem orbitBits_prefix_ones (c : OddCycle L) (k : ℕ) :
    listOnes (orbitBits (c.node 0) (c.prefixExponent k)) = k := by
  induction k with
  | zero =>
      simp [prefixExponent, orbitBits]
  | succ k ih =>
      rw [c.prefixExponent_succ k]
      rw [orbitBits_add]
      rw [listOnes_append, ih]
      rw [c.halfStep_reaches_prefix_node k]
      rw [(c.edge (k : ZMod L)).orbitBits_ones]

/-- Over one complete denominator-compatible period `A`, the actual parity
orbit contains exactly `L` odd source states. This is the missing exponent-to-
parity count bridge needed to turn the word denominator into `2^A - 3^L`. -/
theorem orbitBits_total_ones (c : OddCycle L) :
    listOnes (orbitBits (c.node 0) c.totalExponent) = L := by
  simpa [totalExponent] using c.orbitBits_prefix_ones L

/-- The denominator computed from the genuine chronological parity word is
exactly the characteristic Collatz cycle denominator already derived from the
odd-to-odd equations. -/
theorem wordDenominator_eq_cycleDenominator (c : OddCycle L) :
    wordDenominator (orbitBits (c.node 0) c.totalExponent) =
      cycleDenominator c.totalExponent L := by
  rw [wordDenominator, orbitBits_length, c.orbitBits_total_ones, cycleDenominator]

/-- The complete cycle denominator multiplies the base odd node to the exact
inhomogeneous numerator obtained directly from the genuine parity word. -/
theorem cycleDenominator_mul_base_eq_wordNumerator (c : OddCycle L) :
    cycleDenominator c.totalExponent L * (c.node 0 : ℤ) =
      (wordNumerator (orbitBits (c.node 0) c.totalExponent) : ℤ) := by
  have h := periodic_word_denominator_identity c.node_zero_halfStep_periodic
  rw [c.wordDenominator_eq_cycleDenominator] at h
  exact h

/-- Genuine Collatz-specific full-denominator divisibility for the parity-word
numerator: the entire integer `2^A - 3^L` divides it. -/
theorem fullDenominatorDivides_wordNumerator (c : OddCycle L) :
    FullDenominatorDivides c.totalExponent L
      (wordNumerator (orbitBits (c.node 0) c.totalExponent) : ℤ) := by
  refine ⟨(c.node 0 : ℤ), ?_⟩
  exact c.cycleDenominator_mul_base_eq_wordNumerator.symm

/-- The numerator obtained from chronological parity-word composition agrees
exactly with the numerator obtained by composing the odd-to-odd exponent
blocks. This proves the two independently formalised arithmetic routes are
coherent. -/
theorem wordNumerator_eq_prefixNumerator (c : OddCycle L) :
    wordNumerator (orbitBits (c.node 0) c.totalExponent) = c.prefixNumerator L := by
  have hword := c.cycleDenominator_mul_base_eq_wordNumerator
  have hblock := c.denominator_mul_base_eq_numerator
  have hz :
      (wordNumerator (orbitBits (c.node 0) c.totalExponent) : ℤ) =
        (c.prefixNumerator L : ℤ) :=
    hword.symm.trans hblock
  exact_mod_cast hz

end OddCycle

end Collatz
