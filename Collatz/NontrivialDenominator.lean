import Collatz.Cycle

namespace Collatz

/-- Powers of three have only the residues `1` and `3` modulo eight. -/
theorem three_pow_mod_eight (n : ℕ) :
    3 ^ n % 8 = 1 ∨ 3 ^ n % 8 = 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h
      · right
        rw [h]
        norm_num
      · left
        rw [h]
        norm_num

namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- If the characteristic denominator of a positive odd cycle were exactly
one, then the total exponent and odd-node count would have to be `A=2, L=1`.
The exclusion of `A≥3` is the elementary mod-eight observation that `2^A` is
zero mod eight while `3^L+1` is either two or four mod eight. -/
theorem denominator_eq_one_forces_counts (c : OddCycle L)
    (hD : cycleDenominator c.totalExponent L = 1) :
    c.totalExponent = 2 ∧ L = 1 := by
  have hpowZ :
      (2 : ℤ) ^ c.totalExponent = (3 : ℤ) ^ L + 1 := by
    rw [cycleDenominator] at hD
    linarith
  have hpow : 2 ^ c.totalExponent = 3 ^ L + 1 := by
    exact_mod_cast hpowZ
  have hApos : 0 < c.totalExponent := c.totalExponent_pos
  have hLpos : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hLA : L ≤ c.totalExponent := c.length_le_totalExponent
  have hAlt : c.totalExponent < 3 := by
    by_contra hnot
    have hA3 : 3 ≤ c.totalExponent := by omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hA3
    have htwo : 2 ^ c.totalExponent % 8 = 0 := by
      rw [hd, pow_add]
      norm_num [Nat.mul_mod]
    have hm := congrArg (fun n : ℕ => n % 8) hpow
    rw [htwo, Nat.add_mod] at hm
    rcases three_pow_mod_eight L with hthree | hthree
    · rw [hthree] at hm
      norm_num at hm
    · rw [hthree] at hm
      norm_num at hm
  have hA : c.totalExponent = 1 ∨ c.totalExponent = 2 := by omega
  rcases hA with hA | hA
  · have hL : L = 1 := by omega
    rw [hA, hL] at hpow
    norm_num at hpow
  · have hL : L = 1 ∨ L = 2 := by omega
    rcases hL with hL | hL
    · exact ⟨hA, hL⟩
    · rw [hA, hL] at hpow
      norm_num at hpow

/-- Denominator one forces the formal cycle itself to be the familiar trivial
odd cycle. -/
theorem denominator_eq_one_forces_trivial (c : OddCycle L)
    (hD : cycleDenominator c.totalExponent L = 1) :
    ¬ c.IsNontrivial := by
  obtain ⟨hA, hL⟩ := c.denominator_eq_one_forces_counts hD
  subst L
  have hexp : c.exponent 0 = 2 := by
    simpa [totalExponent, prefixExponent] using hA
  have hstep := c.step_eq (0 : ZMod 1)
  have hx : c.node 0 = 1 := by
    have hs : 3 * c.node 0 + 1 = 4 * c.node 0 := by
      simpa [hexp] using hstep
    omega
  intro hnontrivial
  rcases hnontrivial with ⟨i, hi⟩
  have hi0 : i = 0 := Subsingleton.elim _ _
  rw [hi0, hx] at hi
  exact hi rfl

/-- Every non-trivial positive odd cycle automatically lies in the strict
positive-denominator region `1 < 2^A - 3^L`. Thus the scaffolded eligibility
predicate is derived from cycle data plus non-triviality, rather than assumed. -/
theorem positiveCycleDenominator_of_nontrivial (c : OddCycle L)
    (hnontrivial : c.IsNontrivial) :
    PositiveCycleDenominator c.totalExponent L := by
  unfold PositiveCycleDenominator
  have hpos := c.cycleDenominator_pos
  by_contra hnot
  have hle : cycleDenominator c.totalExponent L ≤ 1 := le_of_not_gt hnot
  have hD : cycleDenominator c.totalExponent L = 1 := by omega
  exact (c.denominator_eq_one_forces_trivial hD) hnontrivial

end OddCycle
end Collatz
