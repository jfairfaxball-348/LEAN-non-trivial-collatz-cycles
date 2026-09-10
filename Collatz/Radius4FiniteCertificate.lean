import Collatz.Radius4SmallCases
import Mathlib.GroupTheory.OrderOfElement

namespace Collatz

/- The modular calculations below use repeated squaring with kernel-checked
arithmetic proofs. The single `decide` checks only two unequal residues. -/
private theorem three_order_mod_65536 : orderOf (3 : ZMod 65536) = 16384 := by
  have hnot : (3 : ZMod 65536) ^ (2 ^ 13) ≠ 1 := by reduce_mod_char; decide
  have hfin : (3 : ZMod 65536) ^ (2 ^ (13 + 1)) = 1 := by reduce_mod_char
  exact orderOf_eq_prime_pow (p := 2) hnot hfin

private theorem three_pow_add_mod_of_equation {A L d k : ℕ}
    (heq : 2 ^ A = 3 ^ L + d) (hk : k ≤ A) :
    (3 : ZMod (2 ^ k)) ^ L + (d : ZMod (2 ^ k)) = 0 := by
  have hcast : (3 : ZMod (2 ^ k)) ^ L + (d : ZMod (2 ^ k)) =
      (2 : ZMod (2 ^ k)) ^ A := by
    simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat] using
      congrArg (fun x : ℕ => (x : ZMod (2 ^ k))) heq.symm
  exact hcast.trans (ZMod.natCast_pow_eq_zero_of_le 2 hk)

private theorem three_pow_residue_mod_16384 {L d r : ℕ}
    (hL : (3 : ZMod 65536) ^ L + (d : ZMod 65536) = 0)
    (hr : (3 : ZMod 65536) ^ r + (d : ZMod 65536) = 0) :
    L % 16384 = r % 16384 := by
  have hfin : IsOfFinOrder (3 : ZMod 65536) :=
    orderOf_pos_iff.mp (by rw [three_order_mod_65536]; norm_num)
  have heq : (3 : ZMod 65536) ^ L = (3 : ZMod 65536) ^ r :=
    add_right_cancel (hL.trans hr.symm)
  simpa only [three_order_mod_65536] using hfin.pow_inj_mod.mp heq

private theorem small_denominator_mod_eight {A L d : ℕ}
    (heq : 2 ^ A = 3 ^ L + d) (hA : 3 ≤ A)
    (hd : d = 5 ∨ d = 7 ∨ d = 13 ∨ d = 17 ∨ d = 29 ∨ d = 35 ∨
      d = 47 ∨ d = 65) : d = 5 ∨ d = 7 ∨ d = 13 ∨ d = 29 ∨ d = 47 := by
  have h8 : (3 : ZMod 8) ^ L + (d : ZMod 8) = 0 :=
    three_pow_add_mod_of_equation heq hA
  rw [pow_eq_pow_mod L (show (3 : ZMod 8) ^ 2 = 1 by reduce_mod_char)] at h8
  have hlt : L % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | omega | (
    interval_cases h : L % 2 <;>
      reduce_mod_char at h8 <;>
      have hval := congrArg ZMod.val h8 <;>
      norm_num [ZMod.val_ofNat] at hval)

/-- The finite small-denominator problem below weight 7000 has period less than sixteen. -/
theorem two_pow_eq_three_pow_add_small_exponent_lt_sixteen {A L d : ℕ}
    (hproper : L < A) (hsmall : L < 7000)
    (hd : d = 5 ∨ d = 7 ∨ d = 13 ∨ d = 17 ∨ d = 29 ∨ d = 35 ∨
      d = 47 ∨ d = 65)
    (heq : 2 ^ A = 3 ^ L + d) : A < 16 := by
  by_contra hlarge
  have hA : 16 ≤ A := by omega
  have hmod : (3 : ZMod 65536) ^ L + (d : ZMod 65536) = 0 :=
    three_pow_add_mod_of_equation heq hA
  have hres : L % 16384 = L := Nat.mod_eq_of_lt (by omega)
  rcases small_denominator_mod_eight heq (by omega) hd with
    rfl | rfl | rfl | rfl | rfl
  · have h := three_pow_residue_mod_16384 hmod
      (show (3 : ZMod 65536) ^ 15627 + (5 : ℕ) = 0 by reduce_mod_char)
    norm_num [hres] at h
    omega
  · have h := three_pow_residue_mod_16384 hmod
      (show (3 : ZMod 65536) ^ 1198 + (7 : ℕ) = 0 by reduce_mod_char)
    norm_num [hres] at h
    subst L
    have h21 : (3 : ZMod (2 ^ 21)) ^ 1198 + (7 : ℕ) = 0 :=
      three_pow_add_mod_of_equation heq (by omega)
    reduce_mod_char at h21
    have hval := congrArg ZMod.val h21
    norm_num [ZMod.val_ofNat] at hval
  · have h := three_pow_residue_mod_16384 hmod
      (show (3 : ZMod 65536) ^ 10821 + (13 : ℕ) = 0 by reduce_mod_char)
    norm_num [hres] at h
    omega
  · have h := three_pow_residue_mod_16384 hmod
      (show (3 : ZMod 65536) ^ 4425 + (29 : ℕ) = 0 by reduce_mod_char)
    norm_num [hres] at h
    subst L
    have h20 : (3 : ZMod (2 ^ 20)) ^ 4425 + (29 : ℕ) = 0 :=
      three_pow_add_mod_of_equation heq (by omega)
    reduce_mod_char at h20
    have hval := congrArg ZMod.val h20
    norm_num [ZMod.val_ofNat] at hval
  · have h := three_pow_residue_mod_16384 hmod
      (show (3 : ZMod 65536) ^ 10084 + (47 : ℕ) = 0 by reduce_mod_char)
    norm_num [hres] at h
    omega

/-- The complete finite denominator certificate in the proposed analytic
cutoff range. The bound `L < 7000` is a hypothesis of this finite statement;
this theorem does not assert the unproved analytic cutoff. -/
theorem cycleDenominator_small_list_of_ones_lt_seven_thousand {A L : ℕ}
    (hL : 0 < L) (hproper : L < A) (hsmall : L < 7000)
    (hD : cycleDenominator A L = 5 ∨ cycleDenominator A L = 7 ∨
      cycleDenominator A L = 13 ∨ cycleDenominator A L = 17 ∨
      cycleDenominator A L = 29 ∨ cycleDenominator A L = 35 ∨
      cycleDenominator A L = 47 ∨ cycleDenominator A L = 65) :
    (A = 3 ∧ L = 1 ∧ cycleDenominator A L = 5) ∨
    (A = 4 ∧ L = 1 ∧ cycleDenominator A L = 13) ∨
    (A = 5 ∧ L = 1 ∧ cycleDenominator A L = 29) ∨
    (A = 4 ∧ L = 2 ∧ cycleDenominator A L = 7) ∨
    (A = 5 ∧ L = 3 ∧ cycleDenominator A L = 5) ∨
    (A = 7 ∧ L = 4 ∧ cycleDenominator A L = 47) ∨
    (A = 8 ∧ L = 5 ∧ cycleDenominator A L = 13) := by
  have hA : 0 < A := by omega
  by_cases hbase : L ≤ 6
  · exact cycleDenominator_small_list_of_ones_le_six hA hL hbase hD
  let d := (cycleDenominator A L).toNat
  have hdcast : (d : ℤ) = cycleDenominator A L :=
    Int.toNat_of_nonneg (by omega)
  have hd : d = 5 ∨ d = 7 ∨ d = 13 ∨ d = 17 ∨ d = 29 ∨ d = 35 ∨
      d = 47 ∨ d = 65 := by omega
  have heqZ : (2 : ℤ) ^ A = (3 : ℤ) ^ L + (d : ℤ) := by
    unfold cycleDenominator at hdcast
    omega
  have heq : 2 ^ A = 3 ^ L + d := by exact_mod_cast heqZ
  have hAbound := two_pow_eq_three_pow_add_small_exponent_lt_sixteen hproper hsmall hd heq
  have hLle : L ≤ 9 := by
    by_contra hlarge
    have hthree : 3 ^ 10 ≤ 3 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    have htwo : 2 ^ A ≤ 2 ^ 15 := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at hthree htwo
    omega
  interval_cases L <;> interval_cases A <;> norm_num [cycleDenominator] at hD

/-- The height-two denominator has no Radius-4 instance throughout the
finite cutoff range, without a primitivity assumption. -/
theorem transportHeightTwo_no_ones_lt_seven_thousand {n : ℕ} [NeZero n]
    (w : CyclicWord n) (shift : ZMod n)
    (hones : 0 < ones w) (hproper : ones w < n) (hsmall : ones w < 7000)
    (hD : cycleDenominator n (ones w) = 5)
    (hdiv : cycleDenominator n (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hradius : IsTransportRadiusFour w shift) : False := by
  have hcases := cycleDenominator_small_list_of_ones_lt_seven_thousand
    hones hproper hsmall (Or.inl hD)
  have hsmallSix : ones w ≤ 6 := by
    rcases hcases with h | h | h | h | h | h | h <;> omega
  exact transportHeightTwo_no_ones_le_six w shift hones hsmallSix hD hdiv hradius

/-- Applying the actual height-two denominator bridge excludes the entire
height-two subcase below weight 7000. The weight bound remains explicit. -/
theorem transportHeightTwo_no_ones_lt_seven_thousand_of_cost_four
    {n : ℕ} [NeZero n] (w : CyclicWord n) (shift : ZMod n)
    (hones : 0 < ones w) (hproper : ones w < n) (hsmall : ones w < 7000)
    (hD : 1 < cycleDenominator n (ones w))
    (hdiv : cycleDenominator n (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hradius : IsTransportRadiusFour w shift)
    (hcost : transportCostAtCut w (rotate w shift) 0 = 4)
    {k : ℕ} (hkpos : 0 < k) (hklt : k < n)
    (hk : transportFlowMagnitude w (rotate w shift) 0 k = 2) : False := by
  apply transportHeightTwo_no_ones_lt_seven_thousand
    w shift hones hproper hsmall _ hdiv hradius
  exact transportHeightTwo_fullDenominator_eq_five
    w shift hones hD hdiv hcost hkpos hklt hk

/-- Every generic Radius-4 word whose full denominator belongs to the
connected coefficient list is excluded in the finite cutoff range. This
uses the exact exponent certificate and the previously verified word spaces;
it assumes neither an analytic theorem nor an unverified word certificate. -/
theorem transportRadiusFour_no_small_denominator_of_ones_lt_seven_thousand
    {n : ℕ} [NeZero n] (w : CyclicWord n) (shift : ZMod n)
    (hones : 0 < ones w) (hproper : ones w < n) (hsmall : ones w < 7000)
    (hD : cycleDenominator n (ones w) = 5 ∨ cycleDenominator n (ones w) = 7 ∨
      cycleDenominator n (ones w) = 13 ∨ cycleDenominator n (ones w) = 17 ∨
      cycleDenominator n (ones w) = 29 ∨ cycleDenominator n (ones w) = 35 ∨
      cycleDenominator n (ones w) = 47 ∨ cycleDenominator n (ones w) = 65)
    (hdiv : cycleDenominator n (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hprimitive : IsPrimitive w) (hshift : shift ≠ 0)
    (hradius : IsTransportRadiusFour w shift) : False := by
  have hcases := cycleDenominator_small_list_of_ones_lt_seven_thousand
    hones hproper hsmall hD
  rcases hcases with h | h | h | h | h | h | h
  all_goals rcases h with ⟨rfl, hweight, hdenom⟩
  · exact transportHeightTwo_no_ones_le_six
      w shift hones (by omega) hdenom hdiv hradius
  · exact transportRadiusFour_no_generic_length_four
      w shift hones hproper (by omega) hdiv hprimitive hshift hradius
  · exact transportRadiusFour_no_generic_length_five
      w shift hones hproper (by omega) hdiv hprimitive hshift hradius
  · exact transportRadiusFour_no_generic_length_four
      w shift hones hproper (by omega) hdiv hprimitive hshift hradius
  · exact transportRadiusFour_no_generic_length_five
      w shift hones hproper (by omega) hdiv hprimitive hshift hradius
  · exact transportRadiusFour_no_generic_length_seven
      w shift hones hproper (by omega) hdiv hprimitive hshift hradius
  · exact transportRadiusFour_no_generic_length_eight
      w shift hones hproper (by omega) hdiv hprimitive hshift hradius

end Collatz
