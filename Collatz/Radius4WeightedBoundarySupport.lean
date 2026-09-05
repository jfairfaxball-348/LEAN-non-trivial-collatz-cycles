import Collatz.DifferenceForcingComposition

namespace Collatz
namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- The exact positive arithmetic weight attached to a local state-difference
forcing at cyclic position `t`.  The power of two records chronological
position.  The power of three records the odd bits strictly after `t` in the
advanced full-period orbit, so common odd bits between Radius-4 boundaries are
retained rather than discarded. -/
def radiusDifferenceWeight (c : OddCycle L)
    (shift t : ZMod c.encodingPeriod) : ℤ :=
  (2 : ℤ) ^ t.val *
    (3 : ℤ) ^ listOnes
      (orbitBits (halfStep (c.shiftedStateAt shift t))
        (c.totalExponent - (t.val + 1)))

/-- The weighted local contribution at a cyclic position. -/
def radiusWeightedDifferenceTerm (c : OddCycle L)
    (shift t : ZMod c.encodingPeriod) : ℤ :=
  c.radiusDifferenceWeight shift t * c.radiusDifferenceOffset shift t

/-- Every positional/suffix weight is nonzero. -/
theorem radiusDifferenceWeight_ne_zero (c : OddCycle L)
    (shift t : ZMod c.encodingPeriod) :
    c.radiusDifferenceWeight shift t ≠ 0 := by
  unfold radiusDifferenceWeight
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))

/-- Weighting cannot create or remove support: a weighted term is nonzero
exactly when its underlying local forcing is nonzero. -/
theorem radiusWeightedDifferenceTerm_ne_zero_iff (c : OddCycle L)
    (shift t : ZMod c.encodingPeriod) :
    c.radiusWeightedDifferenceTerm shift t ≠ 0 ↔
      c.radiusDifferenceOffset shift t ≠ 0 := by
  constructor
  · intro hterm hoff
    apply hterm
    simp [radiusWeightedDifferenceTerm, hoff]
  · intro hoff
    exact mul_ne_zero (c.radiusDifferenceWeight_ne_zero shift t) hoff

/-- Exact Radius 4 therefore gives a genuinely four-supported weighted local
arithmetic expression.  The two down-boundaries carry the negative odd
forcings and the two up-boundaries carry the positive odd forcings, each with
its exact positional/suffix weight. -/
theorem radiusFour_weighted_difference_support (c : OddCycle L)
    (shift : ZMod c.encodingPeriod) (hfour : IsRadiusFour c.parityWord shift) :
    ∃ d₁ d₂ u₁ u₂ : ZMod c.encodingPeriod,
      d₁ ≠ d₂ ∧ u₁ ≠ u₂ ∧
      d₁ ≠ u₁ ∧ d₁ ≠ u₂ ∧ d₂ ≠ u₁ ∧ d₂ ≠ u₂ ∧
      (∀ i : ZMod c.encodingPeriod,
        c.radiusWeightedDifferenceTerm shift i ≠ 0 ↔
          i = d₁ ∨ i = d₂ ∨ i = u₁ ∨ i = u₂) ∧
      c.radiusWeightedDifferenceTerm shift d₁ =
        c.radiusDifferenceWeight shift d₁ *
          (-(2 * (c.baseStateAt d₁ : ℤ) + 1)) ∧
      c.radiusWeightedDifferenceTerm shift d₂ =
        c.radiusDifferenceWeight shift d₂ *
          (-(2 * (c.baseStateAt d₂ : ℤ) + 1)) ∧
      c.radiusWeightedDifferenceTerm shift u₁ =
        c.radiusDifferenceWeight shift u₁ *
          (2 * (c.baseStateAt u₁ : ℤ) + 1) ∧
      c.radiusWeightedDifferenceTerm shift u₂ =
        c.radiusDifferenceWeight shift u₂ *
          (2 * (c.baseStateAt u₂ : ℤ) + 1) := by
  rcases c.radiusFour_sparse_difference_offsets shift hfour with
    ⟨d₁, d₂, u₁, u₂, hdne, hune, hd₁u₁, hd₁u₂, hd₂u₁, hd₂u₂,
      hsupport, hd₁, hd₂, hu₁, hu₂⟩
  refine ⟨d₁, d₂, u₁, u₂, hdne, hune, hd₁u₁, hd₁u₂, hd₂u₁, hd₂u₂,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [c.radiusWeightedDifferenceTerm_ne_zero_iff]
    exact hsupport i
  · simp [radiusWeightedDifferenceTerm, hd₁]
  · simp [radiusWeightedDifferenceTerm, hd₂]
  · simp [radiusWeightedDifferenceTerm, hu₁]
  · simp [radiusWeightedDifferenceTerm, hu₂]

end OddCycle
end Collatz
