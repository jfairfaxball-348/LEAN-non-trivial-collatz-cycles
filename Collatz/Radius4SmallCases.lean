import Collatz.Radius4ConnectedBounds

namespace Collatz

private def decidableIsTransportRadiusFour {n : ℕ} [NeZero n]
    (w : CyclicWord n) (shift : ZMod n) : Decidable (IsTransportRadiusFour w shift) := by
  unfold IsTransportRadiusFour IsExactTransportRadius
  letI : Decidable (∀ cut : ZMod n,
      4 ≤ transportCostAtCut w (rotate w shift) cut) :=
    Fintype.decidableForallFintype
  letI : Decidable (∃ cut : ZMod n,
      transportCostAtCut w (rotate w shift) cut = 4) :=
    Fintype.decidableExistsFintype
  infer_instance

set_option linter.style.haveILetI false in
private theorem no_transportRadiusFour_length_three :
    ∀ w : CyclicWord 3, ∀ shift : ZMod 3, ¬ IsTransportRadiusFour w shift := by
  letI : ∀ w : CyclicWord 3, ∀ shift : ZMod 3,
      Decidable (IsTransportRadiusFour w shift) := decidableIsTransportRadiusFour
  letI : ∀ w : CyclicWord 3,
      Decidable (∀ shift : ZMod 3, ¬ IsTransportRadiusFour w shift) :=
    fun _ => Fintype.decidableForallFintype
  letI : Decidable (∀ w : CyclicWord 3, ∀ shift : ZMod 3,
      ¬ IsTransportRadiusFour w shift) := Fintype.decidableForallFintype
  decide

set_option linter.style.haveILetI false in
private theorem no_transportRadiusFour_length_five_weight_three :
    ∀ w : CyclicWord 5, ∀ shift : ZMod 5,
      ones w = 3 → cycleDenominator 5 3 ∣ (wordNumerator (cyclicWordList w) : ℤ) →
        ¬ IsTransportRadiusFour w shift := by
  letI : ∀ w : CyclicWord 5, ∀ shift : ZMod 5,
      Decidable (IsTransportRadiusFour w shift) := decidableIsTransportRadiusFour
  letI : ∀ w : CyclicWord 5, ∀ shift : ZMod 5,
      Decidable (ones w = 3 → cycleDenominator 5 3 ∣
        (wordNumerator (cyclicWordList w) : ℤ) → ¬ IsTransportRadiusFour w shift) :=
    fun _ _ => inferInstance
  letI : ∀ w : CyclicWord 5,
      Decidable (∀ shift : ZMod 5, ones w = 3 → cycleDenominator 5 3 ∣
        (wordNumerator (cyclicWordList w) : ℤ) → ¬ IsTransportRadiusFour w shift) :=
    fun _ => Fintype.decidableForallFintype
  letI : Decidable (∀ w : CyclicWord 5, ∀ shift : ZMod 5,
      ones w = 3 → cycleDenominator 5 3 ∣ (wordNumerator (cyclicWordList w) : ℤ) →
        ¬ IsTransportRadiusFour w shift) := Fintype.decidableForallFintype
  decide

/-- The only positive small-weight solutions of `2^A - 3^L = 5` are the
two explicitly displayed exponent pairs. -/
theorem cycleDenominator_eq_five_of_ones_le_three {A L : ℕ}
    (hA : 0 < A) (hL : 0 < L) (hLsmall : L ≤ 3)
    (hD : cycleDenominator A L = 5) :
    (A = 3 ∧ L = 1) ∨ (A = 5 ∧ L = 3) := by
  have hEqZ : (2 : ℤ) ^ A = (3 : ℤ) ^ L + 5 := by
    unfold cycleDenominator at hD
    omega
  have hEq : 2 ^ A = 3 ^ L + 5 := by exact_mod_cast hEqZ
  have hle : 2 ^ A ≤ 32 := by
    calc
      2 ^ A = 3 ^ L + 5 := hEq
      _ ≤ 3 ^ 3 + 5 := Nat.add_le_add_right
        (Nat.pow_le_pow_right (by decide) hLsmall) 5
      _ = 32 := by norm_num
  have hAle : A ≤ 5 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    norm_num at hle ⊢
    exact hle
  interval_cases L <;> interval_cases A <;>
    norm_num [cycleDenominator] at hD <;> simp_all

/-- The exact height-two denominator `D = 5` has no transport-radius-four
instance when the word has at most three odd positions.  This is the fully
checked finite base case before the quantitative cutoff handles larger weight. -/
theorem transportHeightTwo_no_small_ones {n : ℕ} [NeZero n]
    (w : CyclicWord n) (shift : ZMod n)
    (hones : 0 < ones w) (hsmall : ones w ≤ 3)
    (hD : cycleDenominator n (ones w) = 5)
    (hdiv : cycleDenominator n (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hradius : IsTransportRadiusFour w shift) : False := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rcases cycleDenominator_eq_five_of_ones_le_three hn hones hsmall hD with
    hthree | hfive
  · rcases hthree with ⟨rfl, honesEq⟩
    exact no_transportRadiusFour_length_three w shift hradius
  · rcases hfive with ⟨rfl, honesEq⟩
    rw [honesEq] at hdiv
    exact no_transportRadiusFour_length_five_weight_three w shift honesEq hdiv hradius

/-- The local height-two bridge closes every candidate whose odd-word weight
is at most three.  The remaining height-two branch is therefore entirely in
the large-weight range addressed by the quantitative logarithmic cutoff. -/
theorem transportHeightTwo_no_small_ones_of_cost_four {n : ℕ} [NeZero n]
    (w : CyclicWord n) (shift : ZMod n)
    (hones : 0 < ones w) (hsmall : ones w ≤ 3)
    (hD : 1 < cycleDenominator n (ones w))
    (hdiv : cycleDenominator n (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hradius : IsTransportRadiusFour w shift)
    (hcost : transportCostAtCut w (rotate w shift) 0 = 4)
    {k : ℕ} (hkpos : 0 < k) (hklt : k < n)
    (hk : transportFlowMagnitude w (rotate w shift) 0 k = 2) : False := by
  apply transportHeightTwo_no_small_ones w shift hones hsmall _ hdiv hradius
  exact transportHeightTwo_fullDenominator_eq_five w shift hones hD hdiv hcost hkpos hklt hk

end Collatz
