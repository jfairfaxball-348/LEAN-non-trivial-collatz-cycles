import Collatz.Radius4WeightedBoundarySupport

namespace Collatz
namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- Exact Radius 4 collapses the sum of all cyclic weighted difference terms
onto the four genuine mismatch boundaries.  This is a purely finite support
collapse on top of the already-proved Collatz-derived weights and forcings. -/
theorem radiusFour_weighted_difference_sum_eq_four_terms
    (c : OddCycle L) (shift : ZMod c.encodingPeriod)
    (hfour : IsRadiusFour c.parityWord shift) :
    ∃ d₁ d₂ u₁ u₂ : ZMod c.encodingPeriod,
      d₁ ≠ d₂ ∧ u₁ ≠ u₂ ∧
      d₁ ≠ u₁ ∧ d₁ ≠ u₂ ∧ d₂ ≠ u₁ ∧ d₂ ≠ u₂ ∧
      (∑ i : ZMod c.encodingPeriod,
          c.radiusWeightedDifferenceTerm shift i) =
        c.radiusWeightedDifferenceTerm shift d₁ +
          c.radiusWeightedDifferenceTerm shift d₂ +
          c.radiusWeightedDifferenceTerm shift u₁ +
          c.radiusWeightedDifferenceTerm shift u₂ ∧
      (∑ i : ZMod c.encodingPeriod,
          c.radiusWeightedDifferenceTerm shift i) =
        c.radiusDifferenceWeight shift u₁ *
            (2 * (c.baseStateAt u₁ : ℤ) + 1) +
          c.radiusDifferenceWeight shift u₂ *
            (2 * (c.baseStateAt u₂ : ℤ) + 1) -
          c.radiusDifferenceWeight shift d₁ *
            (2 * (c.baseStateAt d₁ : ℤ) + 1) -
          c.radiusDifferenceWeight shift d₂ *
            (2 * (c.baseStateAt d₂ : ℤ) + 1) := by
  classical
  rcases c.radiusFour_weighted_difference_support shift hfour with
    ⟨d₁, d₂, u₁, u₂, hdne, hune, hd₁u₁, hd₁u₂, hd₂u₁, hd₂u₂,
      hsupport, hd₁, hd₂, hu₁, hu₂⟩
  let s : Finset (ZMod c.encodingPeriod) := {d₁, d₂, u₁, u₂}
  have hzero : ∀ i : ZMod c.encodingPeriod, i ∉ s →
      c.radiusWeightedDifferenceTerm shift i = 0 := by
    intro i hi
    by_contra hne
    have hs := (hsupport i).1 hne
    apply hi
    simp [s, hs]
  have hsum_support :
      (∑ i : ZMod c.encodingPeriod,
          c.radiusWeightedDifferenceTerm shift i) =
        ∑ i ∈ s, c.radiusWeightedDifferenceTerm shift i := by
    calc
      (∑ i : ZMod c.encodingPeriod,
          c.radiusWeightedDifferenceTerm shift i) =
          ∑ i : ZMod c.encodingPeriod,
            if i ∈ s then c.radiusWeightedDifferenceTerm shift i else 0 := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases his : i ∈ s
              · simp [his]
              · simp [his, hzero i his]
      _ = ∑ i ∈ s, c.radiusWeightedDifferenceTerm shift i := by
            rw [← Finset.sum_filter]
            congr 1
            ext i
            simp [s]
  have hsum_four :
      (∑ i : ZMod c.encodingPeriod,
          c.radiusWeightedDifferenceTerm shift i) =
        c.radiusWeightedDifferenceTerm shift d₁ +
          c.radiusWeightedDifferenceTerm shift d₂ +
          c.radiusWeightedDifferenceTerm shift u₁ +
          c.radiusWeightedDifferenceTerm shift u₂ := by
    rw [hsum_support]
    simp [s, hdne, hune, hd₁u₁, hd₁u₂, hd₂u₁, hd₂u₂, add_assoc]
  refine ⟨d₁, d₂, u₁, u₂, hdne, hune, hd₁u₁, hd₁u₂, hd₂u₁, hd₂u₂,
    hsum_four, ?_⟩
  rw [hsum_four, hd₁, hd₂, hu₁, hu₂]
  ring

end OddCycle
end Collatz
