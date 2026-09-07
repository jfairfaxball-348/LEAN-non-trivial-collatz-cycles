import Collatz.WordAppendArithmetic

namespace Collatz

/-- Replacing a block by another block with the same length and number of
ones multiplies its integer numerator difference by the prefix's power of two
and the suffix's power of three. -/
theorem wordNumerator_localReplacement_difference
    (pre source target suffix : List Bool)
    (hlength : source.length = target.length)
    (hones : listOnes source = listOnes target) :
    (wordNumerator (pre ++ target ++ suffix) : ℤ) -
        (wordNumerator (pre ++ source ++ suffix) : ℤ) =
      (2 : ℤ) ^ pre.length * (3 : ℤ) ^ listOnes suffix *
        ((wordNumerator target : ℤ) - (wordNumerator source : ℤ)) := by
  simp only [wordNumerator_append, List.length_append, hlength, hones]
  push_cast
  ring

/-- The eight exact coefficients of the connected four-edge move
`1abc0 → 0abc1`, in the order `000,001,010,011,100,101,110,111`. -/
def transportConnectedFourCoefficient : Bool → Bool → Bool → ℕ
  | false, false, false => 15
  | false, false, true => 29
  | false, true, false => 21
  | false, true, true => 47
  | true, false, false => 17
  | true, false, true => 35
  | true, true, false => 27
  | true, true, true => 65

/-- The connected four-edge local coefficient is exactly one of the eight
RL238 coefficients. -/
theorem transportConnectedFourCoefficient_mem (a b c : Bool) :
    transportConnectedFourCoefficient a b c ∈
      ([15, 29, 21, 47, 17, 35, 27, 65] : List ℕ) := by
  cases a <;> cases b <;> cases c <;> decide

/-- Direct evaluation of the connected four-edge numerator difference. -/
theorem wordNumerator_connectedFour_difference (a b c : Bool) :
    (wordNumerator [false, a, b, c, true] : ℤ) -
        (wordNumerator [true, a, b, c, false] : ℤ) =
      (transportConnectedFourCoefficient a b c : ℤ) := by
  cases a <;> cases b <;> cases c <;>
    norm_num [transportConnectedFourCoefficient, wordNumerator, listOnes, bitOffset]

/-- Direct evaluation of the height-two `(1,2,1)` move `0011 → 1100`. -/
theorem wordNumerator_heightTwo_difference :
    (wordNumerator [true, true, false, false] : ℤ) -
        (wordNumerator [false, false, true, true] : ℤ) = -15 := by
  norm_num [wordNumerator, listOnes, bitOffset]

/-- Exact connected four-edge numerator difference in an arbitrary unchanged
prefix and suffix. -/
theorem wordNumerator_connectedFour_context_difference
    (pre suffix : List Bool) (a b c : Bool) :
    (wordNumerator (pre ++ [false, a, b, c, true] ++ suffix) : ℤ) -
        (wordNumerator (pre ++ [true, a, b, c, false] ++ suffix) : ℤ) =
      (2 : ℤ) ^ pre.length * (3 : ℤ) ^ listOnes suffix *
        (transportConnectedFourCoefficient a b c : ℤ) := by
  rw [wordNumerator_localReplacement_difference pre
    [true, a, b, c, false] [false, a, b, c, true] suffix rfl]
  · rw [wordNumerator_connectedFour_difference]
  · simp [listOnes, Nat.add_comm, Nat.add_left_comm]

/-- Exact height-two numerator difference in an arbitrary unchanged prefix
and suffix. -/
theorem wordNumerator_heightTwo_context_difference (pre suffix : List Bool) :
    (wordNumerator (pre ++ [true, true, false, false] ++ suffix) : ℤ) -
        (wordNumerator (pre ++ [false, false, true, true] ++ suffix) : ℤ) =
      (2 : ℤ) ^ pre.length * (3 : ℤ) ^ listOnes suffix * (-15) := by
  rw [wordNumerator_localReplacement_difference pre
    [false, false, true, true] [true, true, false, false] suffix rfl (by decide)]
  rw [wordNumerator_heightTwo_difference]

end Collatz
