import Collatz.OddCycle

namespace Collatz

/-- The ordinary Collatz map preserves positivity. -/
theorem step_pos {n : ℕ} (hn : 0 < n) : 0 < step n := by
  by_cases heven : n % 2 = 0
  · have htwo : 2 ≤ n := by
      have hne : n ≠ 1 := by
        intro h
        subst n
        norm_num at heven
      omega
    simp [step, heven]
    exact Nat.div_pos (by omega) (by omega)
  · simp [step, heven]

/-- Every finite iterate of `step` from a positive state remains positive. -/
theorem iterate_step_pos {n : ℕ} (hn : 0 < n) (k : ℕ) :
    0 < (step^[k]) n := by
  induction k with
  | zero => simpa using hn
  | succ k ih =>
      rw [show k + 1 = 1 + k by omega]
      rw [Function.iterate_add_apply]
      simpa using step_pos ih

/-- A positive even input strictly decreases under one ordinary Collatz step. -/
theorem step_lt_of_pos_even {n : ℕ} (hn : 0 < n) (heven : Even n) :
    step n < n := by
  rcases heven with ⟨k, rfl⟩
  have hk : 0 < k := by omega
  rw [show k + k = 2 * k by ring]
  rw [step_two_mul]
  omega

/-- If every source state in the first `period` transitions is even, then a
positive starting value strictly decreases over the nonzero period. -/
theorem iterate_step_lt_of_all_even {n period : ℕ}
    (hn : 0 < n) (hperiod : 0 < period)
    (hall : ∀ k : ℕ, k < period → Even ((step^[k]) n)) :
    (step^[period]) n < n := by
  have hprefix : ∀ k : ℕ, k ≤ period → k = 0 ∨ (step^[k]) n < n := by
    intro k hk
    induction k with
    | zero => exact Or.inl rfl
    | succ k ih =>
        have hklt : k < period := by omega
        have heven := hall k hklt
        have hpos := iterate_step_pos hn k
        have hlocal : (step^[k + 1]) n < (step^[k]) n := by
          rw [show k + 1 = 1 + k by omega]
          rw [Function.iterate_add_apply]
          simpa using step_lt_of_pos_even hpos heven
        have hprev := ih (by omega)
        rcases hprev with hzero | hstrict
        · subst k
          exact Or.inr hlocal
        · exact Or.inr (lt_trans hlocal hstrict)
  rcases hprefix period (le_refl period) with hzero | hstrict
  · omega
  · exact hstrict

/-- Every positive periodic point of the ordinary Collatz map encounters an
odd state during one nonzero period.

This is the first reverse-direction bridge from an arbitrary ordinary periodic
orbit toward the odd-to-odd cycle representation. It does not yet construct
the complete compressed `OddCycle`; that requires enumerating all odd visits
and proving the exact exponents between successive visits. -/
theorem positivePeriodicPoint_has_odd_state {n period : ℕ}
    (h : IsPositivePeriodicPoint n period) :
    ∃ k : ℕ, k < period ∧ Odd ((step^[k]) n) := by
  rcases h with ⟨hn, hperiod, hclose⟩
  by_contra hno
  push_neg at hno
  have hallEven : ∀ k : ℕ, k < period → Even ((step^[k]) n) := by
    intro k hk
    rcases Nat.even_or_odd ((step^[k]) n) with heven | hodd
    · exact heven
    · exact False.elim (hno k hk hodd)
  have hlt := iterate_step_lt_of_all_even hn hperiod hallEven
  rw [hclose] at hlt
  omega

end Collatz
