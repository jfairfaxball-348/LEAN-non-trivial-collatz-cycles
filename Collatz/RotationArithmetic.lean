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

end OddCycle
end Collatz
