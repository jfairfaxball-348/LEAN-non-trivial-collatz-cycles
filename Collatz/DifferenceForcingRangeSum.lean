import Collatz.Radius4WeightedBoundarySupport

namespace Collatz

/-- One more `halfStep` after `j` iterations is the `(j+1)`st iterate. -/
theorem halfStep_iterate_succ_right (x j : ℕ) :
    (halfStep^[j + 1]) x = halfStep ((halfStep^[j]) x) := by
  rw [show j + 1 = 1 + j by omega, Function.iterate_add_apply]
  rfl

/-- The power of three contributed by a nonempty actual orbit word splits into
its initial parity multiplier and the contribution from the remaining suffix. -/
theorem three_pow_orbitBits_succ_multiplier (y n : ℕ) :
    (3 : ℤ) ^ listOnes (orbitBits y (n + 1)) =
      (3 : ℤ) ^ listOnes (orbitBits (halfStep y) n) *
        (bitMultiplier (stateBit y) : ℤ) := by
  cases hy : stateBit y with
  | false =>
      simp [orbitBits, hy, bitMultiplier]
  | true =>
      rw [orbitBits, listOnes, hy]
      simp only [ite_true, bitMultiplier]
      rw [show 1 + listOnes (orbitBits (halfStep y) n) =
          listOnes (orbitBits (halfStep y) n) + 1 by omega,
        pow_succ]
      ring

/-- Telescoping potential for a pair of actual `halfStep` orbits.  At time `j`
it contains the current state difference, the chronological power of two, and
the complete odd-count weight from time `j` through the end of the chosen
finite horizon. -/
def orbitDifferencePotential (x y total j : ℕ) : ℤ :=
  (2 : ℤ) ^ j *
    (3 : ℤ) ^ listOnes (orbitBits ((halfStep^[j]) y) (total - j)) *
      ((((halfStep^[j]) y : ℕ) : ℤ) - (((halfStep^[j]) x : ℕ) : ℤ))

/-- Natural-indexed form of the exact weighted local difference forcing.  The
suffix starts strictly after position `j`. -/
def orbitWeightedDifferenceTerm (x y total j : ℕ) : ℤ :=
  (2 : ℤ) ^ j *
    (3 : ℤ) ^ listOnes
      (orbitBits (halfStep ((halfStep^[j]) y)) (total - (j + 1))) *
    affineDifferenceOffset ((halfStep^[j]) x)
      (stateBit ((halfStep^[j]) x)) (stateBit ((halfStep^[j]) y))

/-- Each exact weighted local forcing is one adjacent difference of the
potential. This is the local telescoping form of the difference recurrence. -/
theorem orbitWeightedDifferenceTerm_eq_potential_sub
    (x y total j : ℕ) (hj : j < total) :
    orbitWeightedDifferenceTerm x y total j =
      orbitDifferencePotential x y total (j + 1) -
        orbitDifferencePotential x y total j := by
  have hlen : total - j = (total - (j + 1)) + 1 := by
    omega
  have hstep :=
    halfStep_difference_step ((halfStep^[j]) x) ((halfStep^[j]) y)
  have hoff :
      affineDifferenceOffset ((halfStep^[j]) x)
          (stateBit ((halfStep^[j]) x)) (stateBit ((halfStep^[j]) y)) =
        (2 : ℤ) *
            ((halfStep ((halfStep^[j]) y) : ℤ) -
              (halfStep ((halfStep^[j]) x) : ℤ)) -
          (bitMultiplier (stateBit ((halfStep^[j]) y)) : ℤ) *
            ((((halfStep^[j]) y : ℕ) : ℤ) - (((halfStep^[j]) x : ℕ) : ℤ)) := by
    linarith
  unfold orbitWeightedDifferenceTerm orbitDifferencePotential
  rw [halfStep_iterate_succ_right x j, halfStep_iterate_succ_right y j]
  rw [hlen, three_pow_orbitBits_succ_multiplier]
  rw [show (2 : ℤ) ^ (j + 1) = (2 : ℤ) ^ j * 2 by rw [pow_succ]]
  rw [hoff]
  ring

/-- Elementary finite telescoping identity over a natural range. -/
theorem sum_range_potential_sub (P : ℕ → ℤ) (n : ℕ) :
    (Finset.range n).sum (fun j => P (j + 1) - P j) = P n - P 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- The complete natural-indexed weighted forcing sum is exactly the endpoint
potential difference. -/
theorem orbitWeightedDifferenceSum_eq_potential_sub (x y total : ℕ) :
    (Finset.range total).sum (fun j => orbitWeightedDifferenceTerm x y total j) =
      orbitDifferencePotential x y total total - orbitDifferencePotential x y total 0 := by
  calc
    (Finset.range total).sum (fun j => orbitWeightedDifferenceTerm x y total j) =
        (Finset.range total).sum (fun j =>
          orbitDifferencePotential x y total (j + 1) -
            orbitDifferencePotential x y total j) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact orbitWeightedDifferenceTerm_eq_potential_sub x y total j
        (Finset.mem_range.mp hj)
    _ = orbitDifferencePotential x y total total -
        orbitDifferencePotential x y total 0 :=
      sum_range_potential_sub (orbitDifferencePotential x y total) total

namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- For an in-range natural representative, the natural-indexed weighted term
is literally the cyclic weighted Radius-4 term. -/
theorem orbitWeightedDifferenceTerm_eq_radiusWeightedDifferenceTerm
    (c : OddCycle L) (shift : ZMod c.encodingPeriod) {j : ℕ}
    (hj : j < c.totalExponent) :
    orbitWeightedDifferenceTerm (c.node 0)
        ((halfStep^[shift.val]) (c.node 0)) c.totalExponent j =
      c.radiusWeightedDifferenceTerm shift (j : ZMod c.encodingPeriod) := by
  have hjenc : j < c.encodingPeriod := by
    simpa [encodingPeriod] using hj
  have hval : ((j : ZMod c.encodingPeriod).val) = j :=
    ZMod.val_natCast_of_lt hjenc
  rw [radiusWeightedDifferenceTerm, radiusDifferenceWeight, radiusDifferenceOffset,
    baseStateAt, shiftedStateAt, hval]
  rfl

/-- The terminal potential over one complete cycle is `2^A` times the literal
shifted-minus-base state difference. -/
theorem orbitDifferencePotential_total (c : OddCycle L)
    (shift : ZMod c.encodingPeriod) :
    orbitDifferencePotential (c.node 0)
        ((halfStep^[shift.val]) (c.node 0)) c.totalExponent c.totalExponent =
      (2 : ℤ) ^ c.totalExponent *
        ((((halfStep^[shift.val]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ)) := by
  change
    (2 : ℤ) ^ c.totalExponent *
        ((((halfStep^[c.totalExponent])
            ((halfStep^[shift.val]) (c.node 0)) : ℕ) : ℤ) -
          (((halfStep^[c.totalExponent]) (c.node 0) : ℕ) : ℤ)) =
      (2 : ℤ) ^ c.totalExponent *
        ((((halfStep^[shift.val]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ))
  rw [c.node_zero_halfStep_periodic, c.halfStep_shift_periodic shift.val]

/-- The initial potential is `3^L` times the same state difference. -/
theorem orbitDifferencePotential_zero (c : OddCycle L)
    (shift : ZMod c.encodingPeriod) :
    orbitDifferencePotential (c.node 0)
        ((halfStep^[shift.val]) (c.node 0)) c.totalExponent 0 =
      (3 : ℤ) ^ L *
        ((((halfStep^[shift.val]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ)) := by
  have hshift : shift.val ≤ c.totalExponent :=
    c.zmodShift_val_le_totalExponent shift
  change
    (3 : ℤ) ^ listOnes
        (orbitBits ((halfStep^[shift.val]) (c.node 0)) c.totalExponent) *
      ((((halfStep^[shift.val]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ)) =
    (3 : ℤ) ^ L *
      ((((halfStep^[shift.val]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ))
  rw [c.orbitBits_shift_total_ones hshift]

/-- Over one complete genuine cycle, the natural-indexed weighted local
forcings sum to the complete denominator times the literal shifted-minus-base
state difference. -/
theorem cycleDenominator_mul_shiftedState_sub_base_eq_orbitWeightedRangeSum
    (c : OddCycle L) (shift : ZMod c.encodingPeriod) :
    cycleDenominator c.totalExponent L *
        ((((halfStep^[shift.val]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ)) =
      (Finset.range c.totalExponent).sum (fun j =>
        orbitWeightedDifferenceTerm (c.node 0)
          ((halfStep^[shift.val]) (c.node 0)) c.totalExponent j) := by
  have hsum := orbitWeightedDifferenceSum_eq_potential_sub
    (c.node 0) ((halfStep^[shift.val]) (c.node 0)) c.totalExponent
  rw [c.orbitDifferencePotential_total shift,
    c.orbitDifferencePotential_zero shift] at hsum
  rw [cycleDenominator]
  linarith

/-- Cyclic-position form of the preceding exact full-denominator weighted sum. -/
theorem cycleDenominator_mul_shiftedState_sub_base_eq_radiusWeightedRangeSum
    (c : OddCycle L) (shift : ZMod c.encodingPeriod) :
    cycleDenominator c.totalExponent L *
        ((((halfStep^[shift.val]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ)) =
      (Finset.range c.totalExponent).sum (fun j =>
        c.radiusWeightedDifferenceTerm shift (j : ZMod c.encodingPeriod)) := by
  rw [c.cycleDenominator_mul_shiftedState_sub_base_eq_orbitWeightedRangeSum shift]
  apply Finset.sum_congr rfl
  intro j hj
  exact c.orbitWeightedDifferenceTerm_eq_radiusWeightedDifferenceTerm shift
    (Finset.mem_range.mp hj)

/-- The genuine shifted-minus-base parity-word numerator difference is exactly
the sum of the cyclic weighted local terms over one complete chronological
period. -/
theorem shifted_wordNumerator_difference_eq_radiusWeightedRangeSum
    (c : OddCycle L) (shift : ZMod c.encodingPeriod) :
    (wordNumerator
        (orbitBits ((halfStep^[shift.val]) (c.node 0)) c.totalExponent) : ℤ) -
      (wordNumerator (orbitBits (c.node 0) c.totalExponent) : ℤ) =
        (Finset.range c.totalExponent).sum (fun j =>
          c.radiusWeightedDifferenceTerm shift (j : ZMod c.encodingPeriod)) := by
  have hshift : shift.val ≤ c.totalExponent :=
    c.zmodShift_val_le_totalExponent shift
  rw [← c.cycleDenominator_mul_shiftedState_sub_base_eq_wordNumerator_difference hshift]
  exact c.cycleDenominator_mul_shiftedState_sub_base_eq_radiusWeightedRangeSum shift

end OddCycle
end Collatz
