import Collatz.Cycle

namespace Collatz

/-- Positive powers of two and three cannot agree.  This elementary
multiplicative-independence fact supplies the nonvanishing side condition of
the two-logarithm lower bound without importing it as an assumption. -/
theorem two_pow_ne_three_pow {A L : ℕ} (hA : 0 < A) : 2 ^ A ≠ 3 ^ L := by
  intro hpow
  have heven : Even (2 ^ A) :=
    (show Even (2 : ℕ) by norm_num).pow_of_ne_zero (Nat.ne_of_gt hA)
  have hodd : Odd (3 ^ L) := (show Odd (3 : ℕ) by norm_num).pow
  exact (Nat.not_even_iff_odd.mpr hodd) (hpow ▸ heven)

/-- The `2`--`3` logarithmic form is nonzero for a positive coefficient of
`log 2`.  Thus the corresponding nonvanishing requirement is a proved
arithmetic fact, not an additional analytic hypothesis. -/
theorem log_two_three_defect_ne_zero {A L : ℕ} (hA : 0 < A) :
    (A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3 ≠ 0 := by
  intro hzero
  have hratio : (2 : ℝ) ^ A / (3 : ℝ) ^ L = 1 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2),
      ← Real.exp_log (by norm_num : (0 : ℝ) < 3),
      ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_sub, hzero]
    norm_num
  have hpowR : (2 : ℝ) ^ A = (3 : ℝ) ^ L := by
    calc
      (2 : ℝ) ^ A = 1 * (3 : ℝ) ^ L :=
        (div_eq_iff (by positivity)).mp hratio
      _ = (3 : ℝ) ^ L := one_mul _
  have hpow : 2 ^ A = 3 ^ L := by exact_mod_cast hpowR
  exact two_pow_ne_three_pow hA hpow

/-- The logarithmic defect is the logarithm of the exact
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

/-- An elementary exponential upper bound for the logarithmic defect.
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
defect needed for the quantitative two-logarithm cutoff. This theorem does not assert
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

/-- The elementary exponent reduction used before enlarging the
two-logarithm parameter: denominators at most sixty-five and `L ≥ 4` force `A < 2L`. -/
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
