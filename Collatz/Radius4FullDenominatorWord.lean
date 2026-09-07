import Collatz.CyclicWordList
import Collatz.Radius4WordRotation

namespace Collatz

/-- Full-denominator divisibility is preserved when the origin of an arbitrary
cyclic word is rotated. The original source-numerator hypothesis is retained. -/
theorem cycleDenominator_dvd_cyclicWordList_rotate
    {n : ℕ} [NeZero n] (w : CyclicWord n) (shift : ZMod n)
    (hones : 0 < ones w)
    (hdiv : cycleDenominator n (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ)) :
    cycleDenominator n (ones w) ∣
      (wordNumerator (cyclicWordList (rotate w shift)) : ℤ) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hrot := cycleDenominator_dvd_wordNumerator_rotate (cyclicWordList w) shift.val
    (by simpa only [length_cyclicWordList] using hn)
    (by simpa only [listOnes_cyclicWordList] using hones)
    (by simpa only [length_cyclicWordList, listOnes_cyclicWordList] using hdiv)
  simpa only [cyclicWordList_rotate, length_cyclicWordList, listOnes_cyclicWordList]
    using hrot

/-- The rotated-minus-source difference is divisible by the complete
denominator, as a consequence of divisibility of the source numerator. -/
theorem cycleDenominator_dvd_cyclicWordList_rotate_sub
    {n : ℕ} [NeZero n] (w : CyclicWord n) (shift : ZMod n)
    (hones : 0 < ones w)
    (hdiv : cycleDenominator n (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ)) :
    cycleDenominator n (ones w) ∣
      (wordNumerator (cyclicWordList (rotate w shift)) : ℤ) -
        (wordNumerator (cyclicWordList w) : ℤ) := by
  exact dvd_sub (cycleDenominator_dvd_cyclicWordList_rotate w shift hones hdiv) hdiv

private theorem strict_cycleDenominator_natAbs_conditions {A L : ℕ}
    (hA : 0 < A) (hL : 0 < L) (hD : 1 < cycleDenominator A L) :
    1 < (cycleDenominator A L).natAbs ∧
      (cycleDenominator A L).natAbs.Coprime 6 ∧
      ((cycleDenominator A L).natAbs : ℤ) = cycleDenominator A L := by
  have hcast : ((cycleDenominator A L).natAbs : ℤ) = cycleDenominator A L :=
    Int.natAbs_of_nonneg (by omega)
  have hgt : (1 : ℤ) < ((cycleDenominator A L).natAbs : ℤ) := by
    simpa only [hcast] using hD
  refine ⟨by exact_mod_cast hgt, ?_, hcast⟩
  apply IsCoprime.natCoprime
  simpa [hcast] using cycleDenominator_isCoprime_six hA hL

/-- The finite connected divisor list applies to the absolute value of the
actual full denominator. Strict positivity identifies it with that denominator,
so this is not a statement about an arbitrary factor. -/
theorem cycleDenominator_natAbs_mem_of_dvd_connectedFourCoefficient
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L) (hD : 1 < cycleDenominator A L)
    (a b c : Bool)
    (hdiv : cycleDenominator A L ∣ (transportConnectedFourCoefficient a b c : ℤ)) :
    (cycleDenominator A L).natAbs ∈ ([5, 7, 13, 17, 29, 35, 47, 65] : List ℕ) := by
  obtain ⟨hgt, hcoprime, hcast⟩ := strict_cycleDenominator_natAbs_conditions hA hL hD
  have hdivCast : ((cycleDenominator A L).natAbs : ℤ) ∣
      (transportConnectedFourCoefficient a b c : ℤ) := by
    simpa only [hcast] using hdiv
  exact transportConnectedFour_denominator_mem hgt hcoprime a b c
    (by exact_mod_cast hdivCast)

/-- Connected coefficient divisibility bounds the strict positive full
denominator by sixty-five. -/
theorem cycleDenominator_le_sixty_five_of_dvd_connectedFourCoefficient
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L) (hD : 1 < cycleDenominator A L)
    (a b c : Bool)
    (hdiv : cycleDenominator A L ∣ (transportConnectedFourCoefficient a b c : ℤ)) :
    cycleDenominator A L ≤ 65 := by
  have hmem := cycleDenominator_natAbs_mem_of_dvd_connectedFourCoefficient
    hA hL hD a b c hdiv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  have hle : (cycleDenominator A L).natAbs ≤ 65 := by omega
  have hleCast : ((cycleDenominator A L).natAbs : ℤ) ≤ 65 := by exact_mod_cast hle
  simpa only [Int.natAbs_of_nonneg (by omega : 0 ≤ cycleDenominator A L)] using hleCast

/-- For the height-two coefficient, the strict positive full denominator
itself must equal five. -/
theorem cycleDenominator_eq_five_of_dvd_fifteen
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L) (hD : 1 < cycleDenominator A L)
    (hdiv : cycleDenominator A L ∣ 15) :
    cycleDenominator A L = 5 := by
  obtain ⟨hgt, hcoprime, hcast⟩ := strict_cycleDenominator_natAbs_conditions hA hL hD
  have hdivCast : ((cycleDenominator A L).natAbs : ℤ) ∣ (15 : ℤ) := by
    simpa only [hcast] using hdiv
  have heq := transportHeightTwo_denominator_eq_five hgt hcoprime
    (by exact_mod_cast hdivCast)
  have heqCast : ((cycleDenominator A L).natAbs : ℤ) = 5 := by exact_mod_cast heq
  simpa only [hcast] using heqCast

end Collatz
