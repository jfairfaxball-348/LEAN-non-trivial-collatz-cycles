import Collatz.Cycle

namespace Collatz

/-- The logarithmic defect used in RL238 is the logarithm of the exact
full-denominator ratio. This identity is elementary and contains no
two-logarithm lower-bound assumption. -/
theorem cycleDenominator_log_defect_eq (A L : ℕ) :
    (A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3 =
      Real.log (1 + (cycleDenominator A L : ℝ) / (3 : ℝ) ^ L) := by
  have hratio :
      1 + (cycleDenominator A L : ℝ) / (3 : ℝ) ^ L =
        (2 : ℝ) ^ A / (3 : ℝ) ^ L := by
    simp only [cycleDenominator, Int.cast_sub, Int.cast_pow, Int.cast_ofNat]
    field_simp
    ring
  rw [hratio, Real.log_div (by positivity) (by positivity), Real.log_pow,
    Real.log_pow]

/-- Positive full denominator gives a positive logarithmic defect. -/
theorem cycleDenominator_log_defect_pos {A L : ℕ}
    (hD : 0 < cycleDenominator A L) :
    0 < (A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3 := by
  rw [cycleDenominator_log_defect_eq]
  apply Real.log_pos
  have hD' : (0 : ℝ) < (cycleDenominator A L : ℝ) := by exact_mod_cast hD
  have hquot : 0 < (cycleDenominator A L : ℝ) / (3 : ℝ) ^ L := by positivity
  linarith

/-- RL238's elementary exponential upper bound for the logarithmic defect.
The full denominator is retained exactly. -/
theorem cycleDenominator_log_defect_lt_ratio {A L : ℕ}
    (hD : 0 < cycleDenominator A L) :
    (A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3 <
      (cycleDenominator A L : ℝ) / (3 : ℝ) ^ L := by
  rw [cycleDenominator_log_defect_eq]
  have hD' : (0 : ℝ) < (cycleDenominator A L : ℝ) := by exact_mod_cast hD
  have hquot : 0 < (cycleDenominator A L : ℝ) / (3 : ℝ) ^ L := by positivity
  have h := Real.log_lt_sub_one_of_pos
    (show 0 < 1 + (cycleDenominator A L : ℝ) / (3 : ℝ) ^ L by linarith)
    (show 1 + (cycleDenominator A L : ℝ) / (3 : ℝ) ^ L ≠ 1 by linarith)
  linarith

/-- The connected-branch coefficient bound gives exactly the exponential
defect used before RL238's external LMN cutoff. This theorem does not assert
that cutoff. -/
theorem cycleDenominator_log_defect_lt_sixty_five {A L : ℕ}
    (hD : 0 < cycleDenominator A L) (hsmall : cycleDenominator A L ≤ 65) :
    (A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3 <
      65 / (3 : ℝ) ^ L := by
  apply lt_of_lt_of_le (cycleDenominator_log_defect_lt_ratio hD)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast hsmall

private theorem three_pow_add_sixty_five_lt_four_pow {L : ℕ} (hL : 4 ≤ L) :
    3 ^ L + 65 < 4 ^ L := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hL
  clear hL
  induction m with
  | zero => norm_num
  | succ m ih =>
      simp only [Nat.add_succ, pow_succ]
      nlinarith [pow_pos (by norm_num : 0 < (4 : ℕ)) (4 + m)]

/-- The elementary exponent reduction used by RL238 before enlarging the
LMN parameter: denominators at most sixty-five and `L ≥ 4` force `A < 2L`. -/
theorem cycleDenominator_exponent_lt_twice_of_le_sixty_five {A L : ℕ}
    (hsmall : cycleDenominator A L ≤ 65) (hL : 4 ≤ L) :
    A < 2 * L := by
  have hpowZ : (2 : ℤ) ^ A ≤ (3 : ℤ) ^ L + 65 := by
    unfold cycleDenominator at hsmall
    omega
  have hpowNat : 2 ^ A ≤ 3 ^ L + 65 := by exact_mod_cast hpowZ
  have hlt := lt_of_le_of_lt hpowNat (three_pow_add_sixty_five_lt_four_pow hL)
  have hfour : (4 : ℕ) ^ L = 2 ^ (2 * L) := by norm_num [pow_mul]
  rw [hfour] at hlt
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hlt

end Collatz
