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

/- The complete generic Radius-4 eligibility condition is impossible at
period four.  Unlike the height-two lemma, this finite check retains positive
weight, a strict positive full denominator, source-numerator divisibility,
primitivity, and a nonzero rotation. -/
set_option linter.style.haveILetI false in
private theorem no_generic_transportRadiusFour_length_four :
    ∀ w : CyclicWord 4, ∀ shift : ZMod 4,
      0 < ones w → ones w < 4 → 1 < cycleDenominator 4 (ones w) →
      cycleDenominator 4 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
      IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift := by
  letI : ∀ w : CyclicWord 4, ∀ shift : ZMod 4,
      Decidable (IsTransportRadiusFour w shift) := decidableIsTransportRadiusFour
  letI : ∀ w : CyclicWord 4, Decidable (IsPrimitive w) := fun w => by
    unfold IsPrimitive
    exact Fintype.decidableForallFintype
  letI : ∀ w : CyclicWord 4, ∀ shift : ZMod 4,
      Decidable (0 < ones w → ones w < 4 → 1 < cycleDenominator 4 (ones w) →
        cycleDenominator 4 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
        IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift) :=
    fun _ _ => inferInstance
  letI : ∀ w : CyclicWord 4,
      Decidable (∀ shift : ZMod 4,
        0 < ones w → ones w < 4 → 1 < cycleDenominator 4 (ones w) →
        cycleDenominator 4 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
        IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift) :=
    fun _ => Fintype.decidableForallFintype
  letI : Decidable (∀ w : CyclicWord 4, ∀ shift : ZMod 4,
      0 < ones w → ones w < 4 → 1 < cycleDenominator 4 (ones w) →
      cycleDenominator 4 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
      IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift) :=
    Fintype.decidableForallFintype
  decide

/-- Full generic Radius-4 exclusion at period four. -/
theorem transportRadiusFour_no_generic_length_four
    (w : CyclicWord 4) (shift : ZMod 4)
    (hones : 0 < ones w) (hproper : ones w < 4)
    (hD : 1 < cycleDenominator 4 (ones w))
    (hdiv : cycleDenominator 4 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hprimitive : IsPrimitive w) (hshift : shift ≠ 0)
    (hradius : IsTransportRadiusFour w shift) : False :=
  no_generic_transportRadiusFour_length_four w shift hones hproper hD hdiv hprimitive hshift hradius

/- The complete generic Radius-4 eligibility condition is impossible at
period five. -/
set_option linter.style.haveILetI false in
private theorem no_generic_transportRadiusFour_length_five :
    ∀ w : CyclicWord 5, ∀ shift : ZMod 5,
      0 < ones w → ones w < 5 → 1 < cycleDenominator 5 (ones w) →
      cycleDenominator 5 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
      IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift := by
  letI : ∀ w : CyclicWord 5, ∀ shift : ZMod 5,
      Decidable (IsTransportRadiusFour w shift) := decidableIsTransportRadiusFour
  letI : ∀ w : CyclicWord 5, Decidable (IsPrimitive w) := fun w => by
    unfold IsPrimitive
    exact Fintype.decidableForallFintype
  letI : ∀ w : CyclicWord 5, ∀ shift : ZMod 5,
      Decidable (0 < ones w → ones w < 5 → 1 < cycleDenominator 5 (ones w) →
        cycleDenominator 5 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
        IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift) :=
    fun _ _ => inferInstance
  letI : ∀ w : CyclicWord 5,
      Decidable (∀ shift : ZMod 5,
        0 < ones w → ones w < 5 → 1 < cycleDenominator 5 (ones w) →
        cycleDenominator 5 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
        IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift) :=
    fun _ => Fintype.decidableForallFintype
  letI : Decidable (∀ w : CyclicWord 5, ∀ shift : ZMod 5,
      0 < ones w → ones w < 5 → 1 < cycleDenominator 5 (ones w) →
      cycleDenominator 5 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
      IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift) :=
    Fintype.decidableForallFintype
  decide

/-- Full generic Radius-4 exclusion at period five. -/
theorem transportRadiusFour_no_generic_length_five
    (w : CyclicWord 5) (shift : ZMod 5)
    (hones : 0 < ones w) (hproper : ones w < 5)
    (hD : 1 < cycleDenominator 5 (ones w))
    (hdiv : cycleDenominator 5 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hprimitive : IsPrimitive w) (hshift : shift ≠ 0)
    (hradius : IsTransportRadiusFour w shift) : False :=
  no_generic_transportRadiusFour_length_five w shift hones hproper hD hdiv hprimitive hshift hradius

/- The complete generic Radius-4 eligibility condition is impossible at
period six. -/
set_option linter.style.haveILetI false in
private theorem no_generic_transportRadiusFour_length_six :
    ∀ w : CyclicWord 6, ∀ shift : ZMod 6,
      0 < ones w → ones w < 6 → 1 < cycleDenominator 6 (ones w) →
      cycleDenominator 6 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
      IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift := by
  letI : ∀ w : CyclicWord 6, ∀ shift : ZMod 6,
      Decidable (IsTransportRadiusFour w shift) := decidableIsTransportRadiusFour
  letI : ∀ w : CyclicWord 6, Decidable (IsPrimitive w) := fun w => by
    unfold IsPrimitive
    exact Fintype.decidableForallFintype
  letI : ∀ w : CyclicWord 6, ∀ shift : ZMod 6,
      Decidable (0 < ones w → ones w < 6 → 1 < cycleDenominator 6 (ones w) →
        cycleDenominator 6 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
        IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift) :=
    fun _ _ => inferInstance
  letI : ∀ w : CyclicWord 6,
      Decidable (∀ shift : ZMod 6,
        0 < ones w → ones w < 6 → 1 < cycleDenominator 6 (ones w) →
        cycleDenominator 6 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
        IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift) :=
    fun _ => Fintype.decidableForallFintype
  letI : Decidable (∀ w : CyclicWord 6, ∀ shift : ZMod 6,
      0 < ones w → ones w < 6 → 1 < cycleDenominator 6 (ones w) →
      cycleDenominator 6 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
      IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift) :=
    Fintype.decidableForallFintype
  decide

/-- Full generic Radius-4 exclusion at period six. -/
theorem transportRadiusFour_no_generic_length_six
    (w : CyclicWord 6) (shift : ZMod 6)
    (hones : 0 < ones w) (hproper : ones w < 6)
    (hD : 1 < cycleDenominator 6 (ones w))
    (hdiv : cycleDenominator 6 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hprimitive : IsPrimitive w) (hshift : shift ≠ 0)
    (hradius : IsTransportRadiusFour w shift) : False :=
  no_generic_transportRadiusFour_length_six w shift hones hproper hD hdiv hprimitive hshift hradius

/- The complete generic Radius-4 eligibility condition is impossible at
period seven. -/
set_option maxRecDepth 100000 in
set_option linter.style.haveILetI false in
private theorem no_generic_transportRadiusFour_length_seven :
    ∀ w : CyclicWord 7, ∀ shift : ZMod 7,
      0 < ones w → ones w < 7 → 1 < cycleDenominator 7 (ones w) →
      cycleDenominator 7 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
      IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift := by
  letI : ∀ w : CyclicWord 7, ∀ shift : ZMod 7,
      Decidable (IsTransportRadiusFour w shift) := decidableIsTransportRadiusFour
  letI : ∀ w : CyclicWord 7, Decidable (IsPrimitive w) := fun w => by
    unfold IsPrimitive
    exact Fintype.decidableForallFintype
  letI : ∀ w : CyclicWord 7, ∀ shift : ZMod 7,
      Decidable (0 < ones w → ones w < 7 → 1 < cycleDenominator 7 (ones w) →
        cycleDenominator 7 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
        IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift) :=
    fun _ _ => inferInstance
  letI : ∀ w : CyclicWord 7,
      Decidable (∀ shift : ZMod 7,
        0 < ones w → ones w < 7 → 1 < cycleDenominator 7 (ones w) →
        cycleDenominator 7 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
        IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift) :=
    fun _ => Fintype.decidableForallFintype
  letI : Decidable (∀ w : CyclicWord 7, ∀ shift : ZMod 7,
      0 < ones w → ones w < 7 → 1 < cycleDenominator 7 (ones w) →
      cycleDenominator 7 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
      IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift) :=
    Fintype.decidableForallFintype
  decide

/-- Full generic Radius-4 exclusion at period seven. -/
theorem transportRadiusFour_no_generic_length_seven
    (w : CyclicWord 7) (shift : ZMod 7)
    (hones : 0 < ones w) (hproper : ones w < 7)
    (hD : 1 < cycleDenominator 7 (ones w))
    (hdiv : cycleDenominator 7 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hprimitive : IsPrimitive w) (hshift : shift ≠ 0)
    (hradius : IsTransportRadiusFour w shift) : False :=
  no_generic_transportRadiusFour_length_seven w shift hones hproper hD hdiv hprimitive hshift hradius

/- The complete generic Radius-4 eligibility condition is impossible at
period eight.  This remains a kernel reduction over the finite word and shift
spaces, retaining every arithmetic and primitivity hypothesis. -/
set_option maxRecDepth 100000 in
set_option linter.style.haveILetI false in
private theorem no_generic_transportRadiusFour_length_eight :
    ∀ w : CyclicWord 8, ∀ shift : ZMod 8,
      0 < ones w → ones w < 8 → 1 < cycleDenominator 8 (ones w) →
      cycleDenominator 8 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
      IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift := by
  letI : ∀ w : CyclicWord 8, ∀ shift : ZMod 8,
      Decidable (IsTransportRadiusFour w shift) := decidableIsTransportRadiusFour
  letI : ∀ w : CyclicWord 8, Decidable (IsPrimitive w) := fun w => by
    unfold IsPrimitive
    exact Fintype.decidableForallFintype
  letI : ∀ w : CyclicWord 8, ∀ shift : ZMod 8,
      Decidable (0 < ones w → ones w < 8 → 1 < cycleDenominator 8 (ones w) →
        cycleDenominator 8 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
        IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift) :=
    fun _ _ => inferInstance
  letI : ∀ w : CyclicWord 8,
      Decidable (∀ shift : ZMod 8,
        0 < ones w → ones w < 8 → 1 < cycleDenominator 8 (ones w) →
        cycleDenominator 8 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
        IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift) :=
    fun _ => Fintype.decidableForallFintype
  letI : Decidable (∀ w : CyclicWord 8, ∀ shift : ZMod 8,
      0 < ones w → ones w < 8 → 1 < cycleDenominator 8 (ones w) →
      cycleDenominator 8 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ) →
      IsPrimitive w → shift ≠ 0 → ¬ IsTransportRadiusFour w shift) :=
    Fintype.decidableForallFintype
  decide

/-- Full generic Radius-4 exclusion at period eight. -/
theorem transportRadiusFour_no_generic_length_eight
    (w : CyclicWord 8) (shift : ZMod 8)
    (hones : 0 < ones w) (hproper : ones w < 8)
    (hD : 1 < cycleDenominator 8 (ones w))
    (hdiv : cycleDenominator 8 (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hprimitive : IsPrimitive w) (hshift : shift ≠ 0)
    (hradius : IsTransportRadiusFour w shift) : False :=
  no_generic_transportRadiusFour_length_eight w shift hones hproper hD hdiv hprimitive hshift hradius

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

/-- The same two solutions of `2^A - 3^L = 5` remain the only ones through
odd-word weight six. -/
theorem cycleDenominator_eq_five_of_ones_le_six {A L : ℕ}
    (hA : 0 < A) (hL : 0 < L) (hLsmall : L ≤ 6)
    (hD : cycleDenominator A L = 5) :
    (A = 3 ∧ L = 1) ∨ (A = 5 ∧ L = 3) := by
  have hEqZ : (2 : ℤ) ^ A = (3 : ℤ) ^ L + 5 := by
    unfold cycleDenominator at hD
    omega
  have hEq : 2 ^ A = 3 ^ L + 5 := by exact_mod_cast hEqZ
  have hle : 2 ^ A ≤ 734 := by
    calc
      2 ^ A = 3 ^ L + 5 := hEq
      _ ≤ 3 ^ 6 + 5 := Nat.add_le_add_right
        (Nat.pow_le_pow_right (by decide) hLsmall) 5
      _ = 734 := by norm_num
  have hAle : A ≤ 9 := by
    have hAlt : A < 10 := by
      apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
      norm_num at hle ⊢
      omega
    omega
  interval_cases L <;> interval_cases A <;>
    norm_num [cycleDenominator] at hD <;> simp_all

/-- The finite-denominator list has exactly the expected solutions through
odd-word weight five.  This is the kernel-checked base segment of the larger
finite certificate required after the logarithmic cutoff. -/
theorem cycleDenominator_small_list_of_ones_le_five {A L : ℕ}
    (hA : 0 < A) (hL : 0 < L) (hLsmall : L ≤ 5)
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
  have hDle : cycleDenominator A L ≤ 65 := by omega
  have hEqZ : (2 : ℤ) ^ A ≤ (3 : ℤ) ^ L + 65 := by
    unfold cycleDenominator at hDle
    omega
  have hEq : 2 ^ A ≤ 3 ^ L + 65 := by exact_mod_cast hEqZ
  have hle : 2 ^ A ≤ 308 := by
    calc
      2 ^ A ≤ 3 ^ L + 65 := hEq
      _ ≤ 3 ^ 5 + 65 := Nat.add_le_add_right
        (Nat.pow_le_pow_right (by decide) hLsmall) 65
      _ = 308 := by norm_num
  have hAle : A ≤ 9 := by
    apply (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    norm_num
    omega
  interval_cases L
  all_goals interval_cases A
  all_goals norm_num [cycleDenominator] at hD
  all_goals norm_num [cycleDenominator]

/-- Extending the finite denominator certificate by one odd-word weight adds
no new solution: the same seven triples are the only possibilities for
`L ≤ 6`.  This is a kernel-checked fragment of the finite enumeration needed
after the logarithmic cutoff. -/
theorem cycleDenominator_small_list_of_ones_le_six {A L : ℕ}
    (hA : 0 < A) (hL : 0 < L) (hLsmall : L ≤ 6)
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
  have hDle : cycleDenominator A L ≤ 65 := by omega
  have hEqZ : (2 : ℤ) ^ A ≤ (3 : ℤ) ^ L + 65 := by
    unfold cycleDenominator at hDle
    omega
  have hEq : 2 ^ A ≤ 3 ^ L + 65 := by exact_mod_cast hEqZ
  have hle : 2 ^ A ≤ 794 := by
    calc
      2 ^ A ≤ 3 ^ L + 65 := hEq
      _ ≤ 3 ^ 6 + 65 := Nat.add_le_add_right
        (Nat.pow_le_pow_right (by decide) hLsmall) 65
      _ = 794 := by norm_num
  have hAle : A ≤ 9 := by
    have hAlt : A < 10 := by
      apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
      norm_num at hle ⊢
      omega
    omega
  interval_cases L
  all_goals interval_cases A
  all_goals norm_num [cycleDenominator] at hD
  all_goals norm_num [cycleDenominator]

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

/-- The finite height-two exclusion extends through six odd positions: the
only possible `D = 5` exponent pairs are still the already-excluded periods
three and five. -/
theorem transportHeightTwo_no_ones_le_six {n : ℕ} [NeZero n]
    (w : CyclicWord n) (shift : ZMod n)
    (hones : 0 < ones w) (hsmall : ones w ≤ 6)
    (hD : cycleDenominator n (ones w) = 5)
    (hdiv : cycleDenominator n (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hradius : IsTransportRadiusFour w shift) : False := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rcases cycleDenominator_eq_five_of_ones_le_six hn hones hsmall hD with
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
