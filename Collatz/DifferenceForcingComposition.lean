import Collatz.Radius4SparseDifference
import Collatz.RotationNumeratorComparison

namespace Collatz

/-- The exact inhomogeneous numerator obtained by composing a list of local
state-difference forcings against the parity multipliers of the second orbit.
The leading forcing is multiplied by the power of three contributed by all
later true bits; later forcings acquire powers of two exactly as in the usual
word numerator. -/
def differenceForcingNumerator : List Bool → List ℤ → ℤ
  | [], _ => 0
  | _, [] => 0
  | _ :: bs, z :: zs =>
      (3 : ℤ) ^ listOnes bs * z + 2 * differenceForcingNumerator bs zs

/-- Explicit weighted contribution list for a difference-forcing numerator.
The contribution at chronological position `j` is weighted by `2^(offset+j)`
and by the number of true bits strictly after that position in the second
orbit. -/
def weightedDifferenceForcingTerms : ℕ → List Bool → List ℤ → List ℤ
  | _, [], _ => []
  | _, _, [] => []
  | offset, _ :: bs, z :: zs =>
      ((2 : ℤ) ^ offset * (3 : ℤ) ^ listOnes bs * z) ::
        weightedDifferenceForcingTerms (offset + 1) bs zs

/-- The weighted forcing terms sum to the exact recursive forcing numerator. -/
theorem weightedDifferenceForcingTerms_sum
    (offset : ℕ) (bits : List Bool) (forces : List ℤ) :
    (weightedDifferenceForcingTerms offset bits forces).sum =
      (2 : ℤ) ^ offset * differenceForcingNumerator bits forces := by
  induction bits generalizing offset forces with
  | nil => simp [weightedDifferenceForcingTerms, differenceForcingNumerator]
  | cons b bs ih =>
      cases forces with
      | nil => simp [weightedDifferenceForcingTerms, differenceForcingNumerator]
      | cons z zs =>
          simp [weightedDifferenceForcingTerms, differenceForcingNumerator, ih,
            pow_succ]
          ring

/-- Chronological list of the local forcings obtained by comparing two actual
`halfStep` orbits for the first `k` transitions. -/
def orbitDifferenceForces : ℕ → ℕ → ℕ → List ℤ
  | _, _, 0 => []
  | x, y, k + 1 =>
      affineDifferenceOffset x (stateBit x) (stateBit y) ::
        orbitDifferenceForces (halfStep x) (halfStep y) k

@[simp]
theorem orbitDifferenceForces_length (x y k : ℕ) :
    (orbitDifferenceForces x y k).length = k := by
  induction k generalizing x y with
  | zero => simp [orbitDifferenceForces]
  | succ k ih => simp [orbitDifferenceForces, ih]

/-- Full finite-orbit composition of the one-step state-difference recurrence.
This is the difference analogue of `realizes_composed_identity`: every local
forcing is retained with its exact power-of-two position and the exact
power-of-three suffix count from the second orbit. -/
theorem halfStep_difference_composed_identity (x y k : ℕ) :
    (2 : ℤ) ^ k *
        ((((halfStep^[k]) y : ℕ) : ℤ) - (((halfStep^[k]) x : ℕ) : ℤ)) =
      (3 : ℤ) ^ listOnes (orbitBits y k) * ((y : ℤ) - (x : ℤ)) +
        differenceForcingNumerator (orbitBits y k)
          (orbitDifferenceForces x y k) := by
  induction k generalizing x y with
  | zero =>
      simp [orbitBits, orbitDifferenceForces, differenceForcingNumerator]
  | succ k ih =>
      have htail := ih (x := halfStep x) (y := halfStep y)
      have hstep := halfStep_difference_step x y
      have hcoeff :
          (3 : ℤ) ^ listOnes (orbitBits y (k + 1)) =
            (3 : ℤ) ^ listOnes (orbitBits (halfStep y) k) *
              (bitMultiplier (stateBit y) : ℤ) := by
        cases hy : stateBit y with
        | false =>
            simp [orbitBits, hy, bitMultiplier]
        | true =>
            rw [orbitBits, listOnes, hy]
            simp only [ite_true, bitMultiplier]
            rw [show 1 + listOnes (orbitBits (halfStep y) k) =
                listOnes (orbitBits (halfStep y) k) + 1 by omega,
              pow_succ]
            ring
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, pow_succ]
      calc
        (2 : ℤ) ^ k * 2 *
            ((((halfStep^[k]) (halfStep y) : ℕ) : ℤ) -
              (((halfStep^[k]) (halfStep x) : ℕ) : ℤ)) =
            2 * ((2 : ℤ) ^ k *
              ((((halfStep^[k]) (halfStep y) : ℕ) : ℤ) -
                (((halfStep^[k]) (halfStep x) : ℕ) : ℤ))) := by ring
        _ = 2 *
            ((3 : ℤ) ^ listOnes (orbitBits (halfStep y) k) *
                ((halfStep y : ℤ) - (halfStep x : ℤ)) +
              differenceForcingNumerator (orbitBits (halfStep y) k)
                (orbitDifferenceForces (halfStep x) (halfStep y) k)) := by
              rw [htail]
        _ = (3 : ℤ) ^ listOnes (orbitBits (halfStep y) k) *
              (2 * ((halfStep y : ℤ) - (halfStep x : ℤ))) +
            2 * differenceForcingNumerator (orbitBits (halfStep y) k)
              (orbitDifferenceForces (halfStep x) (halfStep y) k) := by ring
        _ = (3 : ℤ) ^ listOnes (orbitBits (halfStep y) k) *
              ((bitMultiplier (stateBit y) : ℤ) * ((y : ℤ) - (x : ℤ)) +
                affineDifferenceOffset x (stateBit x) (stateBit y)) +
            2 * differenceForcingNumerator (orbitBits (halfStep y) k)
              (orbitDifferenceForces (halfStep x) (halfStep y) k) := by
              rw [hstep]
        _ = (3 : ℤ) ^ listOnes (orbitBits y (k + 1)) *
              ((y : ℤ) - (x : ℤ)) +
            differenceForcingNumerator (orbitBits y (k + 1))
              (orbitDifferenceForces x y (k + 1)) := by
              rw [hcoeff]
              simp only [orbitBits, orbitDifferenceForces,
                differenceForcingNumerator]
              ring

/-- Closed weighted-term form of the actual orbit-difference forcing numerator. -/
theorem orbitDifferenceForcingNumerator_eq_weighted_sum (x y k : ℕ) :
    differenceForcingNumerator (orbitBits y k) (orbitDifferenceForces x y k) =
      (weightedDifferenceForcingTerms 0 (orbitBits y k)
        (orbitDifferenceForces x y k)).sum := by
  have h := weightedDifferenceForcingTerms_sum 0 (orbitBits y k)
    (orbitDifferenceForces x y k)
  simpa using h.symm

namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- Composing the local difference recurrence over one complete genuine cycle
recovers the complete cycle denominator multiplying the literal advanced-minus-
base state difference. -/
theorem cycleDenominator_mul_shiftedState_sub_base_eq_differenceForcingNumerator
    (c : OddCycle L) (shift : ZMod c.encodingPeriod) :
    cycleDenominator c.totalExponent L *
        ((((halfStep^[shift.val]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ)) =
      differenceForcingNumerator
        (orbitBits ((halfStep^[shift.val]) (c.node 0)) c.totalExponent)
        (orbitDifferenceForces (c.node 0)
          ((halfStep^[shift.val]) (c.node 0)) c.totalExponent) := by
  have hshift : shift.val ≤ c.totalExponent :=
    c.zmodShift_val_le_totalExponent shift
  have hcomp := halfStep_difference_composed_identity
    (c.node 0) ((halfStep^[shift.val]) (c.node 0)) c.totalExponent
  rw [c.node_zero_halfStep_periodic,
    c.halfStep_shift_periodic shift.val,
    c.orbitBits_shift_total_ones hshift] at hcomp
  rw [cycleDenominator]
  calc
    ((2 : ℤ) ^ c.totalExponent - (3 : ℤ) ^ L) *
        ((((halfStep^[shift.val]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ)) =
      (2 : ℤ) ^ c.totalExponent *
          ((((halfStep^[shift.val]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ)) -
        (3 : ℤ) ^ L *
          ((((halfStep^[shift.val]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ)) := by
            ring
    _ = differenceForcingNumerator
        (orbitBits ((halfStep^[shift.val]) (c.node 0)) c.totalExponent)
        (orbitDifferenceForces (c.node 0)
          ((halfStep^[shift.val]) (c.node 0)) c.totalExponent) := by
            linarith

/-- The composed local forcing numerator is exactly the already-proved genuine
shifted-minus-base parity-word numerator difference. Thus the local forcing
route and the independent full-word route are formally identical. -/
theorem differenceForcingNumerator_eq_shifted_wordNumerator_difference
    (c : OddCycle L) (shift : ZMod c.encodingPeriod) :
    differenceForcingNumerator
        (orbitBits ((halfStep^[shift.val]) (c.node 0)) c.totalExponent)
        (orbitDifferenceForces (c.node 0)
          ((halfStep^[shift.val]) (c.node 0)) c.totalExponent) =
      (wordNumerator
          (orbitBits ((halfStep^[shift.val]) (c.node 0)) c.totalExponent) : ℤ) -
        (wordNumerator (orbitBits (c.node 0) c.totalExponent) : ℤ) := by
  have hshift : shift.val ≤ c.totalExponent :=
    c.zmodShift_val_le_totalExponent shift
  exact
    (c.cycleDenominator_mul_shiftedState_sub_base_eq_differenceForcingNumerator
      shift).symm.trans
      (c.cycleDenominator_mul_shiftedState_sub_base_eq_wordNumerator_difference
        hshift)

/-- Exact weighted local-forcing representation of the genuine numerator
difference. This is the key accounting theorem for Radius 4: common odd bits
between mismatch boundaries are not discarded; they contribute through the
suffix powers of three in these weights. -/
theorem shifted_wordNumerator_difference_eq_weighted_differenceForcings
    (c : OddCycle L) (shift : ZMod c.encodingPeriod) :
    (wordNumerator
        (orbitBits ((halfStep^[shift.val]) (c.node 0)) c.totalExponent) : ℤ) -
      (wordNumerator (orbitBits (c.node 0) c.totalExponent) : ℤ) =
        (weightedDifferenceForcingTerms 0
          (orbitBits ((halfStep^[shift.val]) (c.node 0)) c.totalExponent)
          (orbitDifferenceForces (c.node 0)
            ((halfStep^[shift.val]) (c.node 0)) c.totalExponent)).sum := by
  rw [← c.differenceForcingNumerator_eq_shifted_wordNumerator_difference shift]
  exact orbitDifferenceForcingNumerator_eq_weighted_sum
    (c.node 0) ((halfStep^[shift.val]) (c.node 0)) c.totalExponent

end OddCycle
end Collatz
