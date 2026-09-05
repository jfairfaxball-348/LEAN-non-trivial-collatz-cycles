import Collatz.Encoding
import Collatz.WordArithmetic

namespace Collatz

/-- The mod-two `stateBit` used by word arithmetic is true exactly for odd
natural numbers. This identifies the arithmetic bit convention with the
`Odd` predicate used by `OddCycle.parityWord`. -/
theorem stateBit_eq_true_iff_odd (n : ℕ) : stateBit n = true ↔ Odd n := by
  constructor
  · intro hbit
    have hmod : n % 2 ≠ 0 := by
      intro hz
      simp [stateBit, hz] at hbit
    have hlt : n % 2 < 2 := Nat.mod_lt n (by norm_num)
    have hone : n % 2 = 1 := by omega
    refine ⟨n / 2, ?_⟩
    have hdiv := Nat.mod_add_div n 2
    omega
  · intro hodd
    exact stateBit_of_odd hodd

namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- Before wrap-around, the `ZMod A` parity word and the chronological
`stateBit` convention agree at the same natural index. This is the first
pointwise bridge between the cyclic Radius-4 object and the linear parity list
used by the full-denominator arithmetic. -/
theorem parityWord_natCast_true_iff (c : OddCycle L) {i : ℕ}
    (hi : i < c.encodingPeriod) :
    c.parityWord (i : ZMod c.encodingPeriod) = true ↔
      stateBit ((halfStep^[i]) (c.node 0)) = true := by
  have hval : ((i : ZMod c.encodingPeriod).val) = i := by
    simp [Nat.mod_eq_of_lt hi]
  rw [c.parityWord_eq_true_iff, hval]
  exact (stateBit_eq_true_iff_odd _).symm

end OddCycle

end Collatz
