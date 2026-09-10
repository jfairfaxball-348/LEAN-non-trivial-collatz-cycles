import Collatz.Radius4FullDenominatorWord

namespace Collatz

/-- The exact numerator difference for two disjoint equal-length,
equal-weight replacements. The first contribution is weighted by the ones
to its right, and the second by the positions to its left. -/
theorem wordNumerator_twoReplacement_difference
    (pre source₁ target₁ middle source₂ target₂ suffix : List Bool)
    (hlen₁ : source₁.length = target₁.length)
    (hones₁ : listOnes source₁ = listOnes target₁)
    (hlen₂ : source₂.length = target₂.length)
    (hones₂ : listOnes source₂ = listOnes target₂) :
    (wordNumerator (pre ++ target₁ ++ middle ++ target₂ ++ suffix) : ℤ) -
        (wordNumerator (pre ++ source₁ ++ middle ++ source₂ ++ suffix) : ℤ) =
      (2 : ℤ) ^ pre.length * (3 : ℤ) ^ listOnes suffix *
        ((3 : ℤ) ^ (listOnes middle + listOnes source₂) *
            ((wordNumerator target₁ : ℤ) - (wordNumerator source₁ : ℤ)) +
          (2 : ℤ) ^ (source₁.length + middle.length) *
            ((wordNumerator target₂ : ℤ) - (wordNumerator source₂ : ℤ))) := by
  simp only [wordNumerator_append, List.length_append,
    hlen₁, hones₁, hlen₂, hones₂]
  push_cast
  simp only [pow_add]
  ring

/-- Sign of an endpoint exchange: a source leading one gives the positive
move `1...0 → 0...1`; a source leading zero gives its inverse. -/
def transportExchangeSign (b : Bool) : ℤ := if b then 1 else -1

/-- The four coefficients for a three-edge exchange, in the order
`00,01,10,11` of its two unchanged internal bits. -/
def transportThreeRunCoefficient : Bool → Bool → ℕ
  | false, false => 7
  | false, true => 13
  | true, false => 9
  | true, true => 19

/-- Both orientations of the three-edge exchange have the displayed signed
coefficient. -/
theorem wordNumerator_threeRun_difference (direction a b : Bool) :
    (wordNumerator [!direction, a, b, direction] : ℤ) -
        (wordNumerator [direction, a, b, !direction] : ℤ) =
      transportExchangeSign direction * (transportThreeRunCoefficient a b : ℤ) := by
  cases direction <;> cases a <;> cases b <;>
    norm_num [transportExchangeSign, transportThreeRunCoefficient,
      wordNumerator, listOnes, bitOffset]

/-- The isolated exchange has coefficient one with the same orientation
convention as the longer exchange. -/
theorem wordNumerator_isolatedRun_difference (direction : Bool) :
    (wordNumerator [!direction, direction] : ℤ) -
        (wordNumerator [direction, !direction] : ℤ) =
      transportExchangeSign direction := by
  cases direction <;>
    norm_num [transportExchangeSign, wordNumerator, listOnes, bitOffset]

/-- The triple-first joint coefficient is nonzero for every gap and every
choice of orientations: its first term is odd and its second is even. -/
theorem threeOne_tripleFirst_coefficient_ne_zero
    (gapLength gapOnes : ℕ) (triple isolated a b : Bool) :
    (3 : ℤ) ^ (gapOnes + 1) * transportExchangeSign triple *
        (transportThreeRunCoefficient a b : ℤ) +
      (2 : ℤ) ^ (4 + gapLength) * transportExchangeSign isolated ≠ 0 := by
  have hthree : Odd ((3 : ℤ) ^ (gapOnes + 1)) := (by decide : Odd (3 : ℤ)).pow
  have hsign : Odd (transportExchangeSign triple) := by
    cases triple <;> norm_num [transportExchangeSign]
  have hcoefficient : Odd (transportThreeRunCoefficient a b : ℤ) := by
    cases a <;> cases b <;> norm_num [transportThreeRunCoefficient]
  have htwo : Even ((2 : ℤ) ^ (4 + gapLength)) :=
    (by decide : Even (2 : ℤ)).pow_of_ne_zero (by omega)
  have hodd := ((hthree.mul hsign).mul hcoefficient).add_even
    (htwo.mul_right (transportExchangeSign isolated))
  intro hzero
  rw [hzero] at hodd
  norm_num at hodd

/-- The triple-last joint coefficient is also nonzero, independently of
the signs and of the two unchanged internal bits. -/
theorem threeOne_tripleLast_coefficient_ne_zero
    (gapLength gapOnes : ℕ) (triple isolated a b : Bool) :
    (3 : ℤ) ^ (gapOnes + listOnes [a, b] + 1) * transportExchangeSign isolated +
      (2 : ℤ) ^ (2 + gapLength) * transportExchangeSign triple *
        (transportThreeRunCoefficient a b : ℤ) ≠ 0 := by
  have hthree : Odd ((3 : ℤ) ^ (gapOnes + listOnes [a, b] + 1)) :=
    (by decide : Odd (3 : ℤ)).pow
  have hsign : Odd (transportExchangeSign isolated) := by
    cases isolated <;> norm_num [transportExchangeSign]
  have htwo : Even ((2 : ℤ) ^ (2 + gapLength)) :=
    (by decide : Even (2 : ℤ)).pow_of_ne_zero (by omega)
  have hodd := (hthree.mul hsign).add_even
    ((htwo.mul_right (transportExchangeSign triple)).mul_right
      (transportThreeRunCoefficient a b : ℤ))
  intro hzero
  rw [hzero] at hodd
  norm_num at hodd

/-- Joint `[3,1]` difference when the three-edge component comes first.
The signs of the two components are independent. -/
theorem wordNumerator_threeOne_tripleFirst_context_difference
    (pre middle suffix : List Bool) (triple isolated a b : Bool) :
    (wordNumerator (pre ++ [!triple, a, b, triple] ++ middle ++
      [!isolated, isolated] ++ suffix) : ℤ) -
        (wordNumerator (pre ++ [triple, a, b, !triple] ++ middle ++
          [isolated, !isolated] ++ suffix) : ℤ) =
      (2 : ℤ) ^ pre.length * (3 : ℤ) ^ listOnes suffix *
        ((3 : ℤ) ^ (listOnes middle + 1) * transportExchangeSign triple *
            (transportThreeRunCoefficient a b : ℤ) +
          (2 : ℤ) ^ (4 + middle.length) * transportExchangeSign isolated) := by
  have hone₁ : listOnes [triple, a, b, !triple] =
      listOnes [!triple, a, b, triple] := by
    cases triple <;> cases a <;> cases b <;> norm_num [listOnes]
  have hone₂ : listOnes [isolated, !isolated] = listOnes [!isolated, isolated] := by
    cases isolated <;> norm_num [listOnes]
  have hweight : listOnes [isolated, !isolated] = 1 := by
    cases isolated <;> norm_num [listOnes]
  rw [wordNumerator_twoReplacement_difference pre
    [triple, a, b, !triple] [!triple, a, b, triple] middle
    [isolated, !isolated] [!isolated, isolated] suffix rfl hone₁ rfl hone₂]
  rw [wordNumerator_threeRun_difference, wordNumerator_isolatedRun_difference, hweight]
  simp only [List.length_cons, List.length_nil]
  ring

/-- Joint `[3,1]` difference when the isolated component comes first. -/
theorem wordNumerator_threeOne_tripleLast_context_difference
    (pre middle suffix : List Bool) (triple isolated a b : Bool) :
    (wordNumerator (pre ++ [!isolated, isolated] ++ middle ++
      [!triple, a, b, triple] ++ suffix) : ℤ) -
        (wordNumerator (pre ++ [isolated, !isolated] ++ middle ++
          [triple, a, b, !triple] ++ suffix) : ℤ) =
      (2 : ℤ) ^ pre.length * (3 : ℤ) ^ listOnes suffix *
        ((3 : ℤ) ^ (listOnes middle + listOnes [a, b] + 1) *
            transportExchangeSign isolated +
          (2 : ℤ) ^ (2 + middle.length) * transportExchangeSign triple *
            (transportThreeRunCoefficient a b : ℤ)) := by
  have hone₁ : listOnes [isolated, !isolated] = listOnes [!isolated, isolated] := by
    cases isolated <;> norm_num [listOnes]
  have hone₂ : listOnes [triple, a, b, !triple] =
      listOnes [!triple, a, b, triple] := by
    cases triple <;> cases a <;> cases b <;> norm_num [listOnes]
  have hweight : listOnes [triple, a, b, !triple] = listOnes [a, b] + 1 := by
    cases triple <;> cases a <;> cases b <;> norm_num [listOnes]
  rw [wordNumerator_twoReplacement_difference pre
    [isolated, !isolated] [!isolated, isolated] middle
    [triple, a, b, !triple] [!triple, a, b, triple] suffix rfl hone₁ rfl hone₂]
  rw [wordNumerator_threeRun_difference, wordNumerator_isolatedRun_difference, hweight]
  simp only [List.length_cons, List.length_nil, Nat.add_assoc]
  ring

/-- A generic self-rotation with the triple-first common-context lists
forces divisibility of their joint coefficient by the full denominator.
Only the source numerator's divisibility is assumed. -/
theorem transportThreeOne_tripleFirst_dvd_coefficient_of_context
    {n : ℕ} [NeZero n] (w : CyclicWord n) (shift : ZMod n)
    (hones : 0 < ones w)
    (hdiv : cycleDenominator n (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (pre middle suffix : List Bool) (triple isolated a b : Bool)
    (hsource : cyclicWordList w = pre ++ [triple, a, b, !triple] ++ middle ++
      [isolated, !isolated] ++ suffix)
    (htarget : cyclicWordList (rotate w shift) = pre ++ [!triple, a, b, triple] ++ middle ++
      [!isolated, isolated] ++ suffix) :
    cycleDenominator n (ones w) ∣
      (3 : ℤ) ^ (listOnes middle + 1) * transportExchangeSign triple *
          (transportThreeRunCoefficient a b : ℤ) +
        (2 : ℤ) ^ (4 + middle.length) * transportExchangeSign isolated := by
  have hdiff := cycleDenominator_dvd_cyclicWordList_rotate_sub w shift hones hdiv
  rw [hsource, htarget, wordNumerator_threeOne_tripleFirst_context_difference] at hdiff
  exact (cycleDenominator_dvd_transport_context_iff
    (Nat.pos_of_ne_zero (NeZero.ne n)) hones _ _ _).mp hdiff

/-- The corresponding full-denominator divisibility in the triple-last
component order, again derived from the original source hypothesis. -/
theorem transportThreeOne_tripleLast_dvd_coefficient_of_context
    {n : ℕ} [NeZero n] (w : CyclicWord n) (shift : ZMod n)
    (hones : 0 < ones w)
    (hdiv : cycleDenominator n (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (pre middle suffix : List Bool) (triple isolated a b : Bool)
    (hsource : cyclicWordList w = pre ++ [isolated, !isolated] ++ middle ++
      [triple, a, b, !triple] ++ suffix)
    (htarget : cyclicWordList (rotate w shift) = pre ++ [!isolated, isolated] ++ middle ++
      [!triple, a, b, triple] ++ suffix) :
    cycleDenominator n (ones w) ∣
      (3 : ℤ) ^ (listOnes middle + listOnes [a, b] + 1) *
          transportExchangeSign isolated +
        (2 : ℤ) ^ (2 + middle.length) * transportExchangeSign triple *
          (transportThreeRunCoefficient a b : ℤ) := by
  have hdiff := cycleDenominator_dvd_cyclicWordList_rotate_sub w shift hones hdiv
  rw [hsource, htarget, wordNumerator_threeOne_tripleLast_context_difference] at hdiff
  exact (cycleDenominator_dvd_transport_context_iff
    (Nat.pos_of_ne_zero (NeZero.ne n)) hones _ _ _).mp hdiff

end Collatz
