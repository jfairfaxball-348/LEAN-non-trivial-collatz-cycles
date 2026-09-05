import Collatz.DifferenceForcingRangeSum
import Collatz.Radius4FourTermSum

namespace Collatz

/-- Summing a function over all residues modulo a positive natural number is
exactly the same as summing its canonical natural representatives `0, ..., n-1`.
This is the bookkeeping bridge between the chronological range sums used by the
orbit calculation and the cyclic sums used by the Radius-4 support theorem. -/
theorem zmod_sum_eq_sum_range {n : ℕ} [NeZero n] {α : Type*}
    [AddCommMonoid α] (f : ZMod n → α) :
    (∑ i : ZMod n, f i) =
      (Finset.range n).sum (fun j => f (j : ZMod n)) := by
  rw [← Fin.sum_univ_eq_sum_range]
  cases n with
  | zero =>
      exact (neZero_zero_iff_false.mp ‹_›).elim
  | succ n =>
      exact Fintype.sum_equiv (ZMod.finEquiv (n + 1)).symm.toEquiv _ _ (fun x => by
        apply congrArg f
        exact (ZMod.natCast_zmod_val x).symm)

namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- The genuine shifted-minus-base parity-word numerator difference is exactly
the full cyclic sum of the Collatz-derived weighted local difference terms. -/
theorem shifted_wordNumerator_difference_eq_radiusWeightedCyclicSum
    (c : OddCycle L) (shift : ZMod c.encodingPeriod) :
    (wordNumerator
        (orbitBits ((halfStep^[shift.val]) (c.node 0)) c.totalExponent) : ℤ) -
      (wordNumerator (orbitBits (c.node 0) c.totalExponent) : ℤ) =
        ∑ i : ZMod c.encodingPeriod,
          c.radiusWeightedDifferenceTerm shift i := by
  calc
    (wordNumerator
        (orbitBits ((halfStep^[shift.val]) (c.node 0)) c.totalExponent) : ℤ) -
      (wordNumerator (orbitBits (c.node 0) c.totalExponent) : ℤ) =
        (Finset.range c.totalExponent).sum (fun j =>
          c.radiusWeightedDifferenceTerm shift (j : ZMod c.encodingPeriod)) :=
      c.shifted_wordNumerator_difference_eq_radiusWeightedRangeSum shift
    _ = ∑ i : ZMod c.encodingPeriod,
          c.radiusWeightedDifferenceTerm shift i := by
      simpa [encodingPeriod] using
        (zmod_sum_eq_sum_range
          (fun i : ZMod c.encodingPeriod =>
            c.radiusWeightedDifferenceTerm shift i)).symm

/-- Under exact Radius 4, the actual genuine shifted-minus-base parity-word
numerator difference is the exact four-boundary expression: two positive odd
forcings and two negative odd forcings, each carrying its genuine positional
and shifted-suffix weight. No ordering, minimality, or primitivity hypothesis is
used in this representation theorem. -/
theorem radiusFour_shifted_wordNumerator_difference_eq_four_terms
    (c : OddCycle L) (shift : ZMod c.encodingPeriod)
    (hfour : IsRadiusFour c.parityWord shift) :
    ∃ d₁ d₂ u₁ u₂ : ZMod c.encodingPeriod,
      d₁ ≠ d₂ ∧ u₁ ≠ u₂ ∧
      d₁ ≠ u₁ ∧ d₁ ≠ u₂ ∧ d₂ ≠ u₁ ∧ d₂ ≠ u₂ ∧
      (wordNumerator
          (orbitBits ((halfStep^[shift.val]) (c.node 0)) c.totalExponent) : ℤ) -
        (wordNumerator (orbitBits (c.node 0) c.totalExponent) : ℤ) =
          c.radiusDifferenceWeight shift u₁ *
              (2 * (c.baseStateAt u₁ : ℤ) + 1) +
            c.radiusDifferenceWeight shift u₂ *
              (2 * (c.baseStateAt u₂ : ℤ) + 1) -
            c.radiusDifferenceWeight shift d₁ *
              (2 * (c.baseStateAt d₁ : ℤ) + 1) -
            c.radiusDifferenceWeight shift d₂ *
              (2 * (c.baseStateAt d₂ : ℤ) + 1) := by
  rcases c.radiusFour_weighted_difference_sum_eq_four_terms shift hfour with
    ⟨d₁, d₂, u₁, u₂, hdne, hune, hd₁u₁, hd₁u₂, hd₂u₁, hd₂u₂,
      _hsumFour, hsumSigned⟩
  refine ⟨d₁, d₂, u₁, u₂, hdne, hune, hd₁u₁, hd₁u₂, hd₂u₁, hd₂u₂, ?_⟩
  calc
    (wordNumerator
        (orbitBits ((halfStep^[shift.val]) (c.node 0)) c.totalExponent) : ℤ) -
      (wordNumerator (orbitBits (c.node 0) c.totalExponent) : ℤ) =
        ∑ i : ZMod c.encodingPeriod,
          c.radiusWeightedDifferenceTerm shift i :=
      c.shifted_wordNumerator_difference_eq_radiusWeightedCyclicSum shift
    _ = c.radiusDifferenceWeight shift u₁ *
            (2 * (c.baseStateAt u₁ : ℤ) + 1) +
          c.radiusDifferenceWeight shift u₂ *
            (2 * (c.baseStateAt u₂ : ℤ) + 1) -
          c.radiusDifferenceWeight shift d₁ *
            (2 * (c.baseStateAt d₁ : ℤ) + 1) -
          c.radiusDifferenceWeight shift d₂ *
            (2 * (c.baseStateAt d₂ : ℤ) + 1) := hsumSigned

end OddCycle
end Collatz
