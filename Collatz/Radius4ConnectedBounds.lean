import Collatz.Radius4FullDenominatorWord
import Collatz.Radius4TransportLocalWords

namespace Collatz

/-- An eligible generic self-rotation in the connected four-edge unit-height
family has full denominator at most sixty-five. The actual local words and
their numerator divisibility are derived, rather than added as hypotheses. -/
theorem transportConnectedFour_fullDenominator_le_sixty_five
    {n : ℕ} [NeZero n] (w : CyclicWord n) (shift : ZMod n)
    (hones : 0 < ones w) (hD : 1 < cycleDenominator n (ones w))
    (hdiv : cycleDenominator n (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hcost : transportCostAtCut w (rotate w shift) 0 = 4)
    (hunit : ∀ j ∈ Finset.range (n - 1),
      transportFlowMagnitude w (rotate w shift) 0 (j + 1) ≤ 1)
    (hconnected : (transportActiveEdgeRunLengths w (rotate w shift) 0).Perm [4]) :
    cycleDenominator n (ones w) ≤ 65 := by
  obtain ⟨pre, suffix, b, a₁, a₂, a₃, hs, ht⟩ :=
    transportConnectedFour_exists_word_context_of_cost_four
      (ones_rotate w shift).symm hcost hunit hconnected
  have htarget := cycleDenominator_dvd_cyclicWordList_rotate w shift hones hdiv
  rw [hs] at hdiv
  rw [ht] at htarget
  apply cycleDenominator_le_sixty_five_of_dvd_connectedFourCoefficient
    (Nat.pos_of_ne_zero (NeZero.ne n)) hones hD a₁ a₂ a₃
  cases b with
  | false =>
      exact cycleDenominator_dvd_connectedFourCoefficient_of_context_difference
        (Nat.pos_of_ne_zero (NeZero.ne n)) hones pre suffix a₁ a₂ a₃
        (dvd_sub hdiv htarget)
  | true =>
      exact cycleDenominator_dvd_connectedFourCoefficient_of_context_difference
        (Nat.pos_of_ne_zero (NeZero.ne n)) hones pre suffix a₁ a₂ a₃
        (dvd_sub htarget hdiv)

/-- An eligible generic self-rotation with a height-two edge at a cost-four
cut has full denominator exactly five. No local replacement or difference
divisibility is assumed separately. -/
theorem transportHeightTwo_fullDenominator_eq_five
    {n : ℕ} [NeZero n] (w : CyclicWord n) (shift : ZMod n)
    (hones : 0 < ones w) (hD : 1 < cycleDenominator n (ones w))
    (hdiv : cycleDenominator n (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hcost : transportCostAtCut w (rotate w shift) 0 = 4)
    {k : ℕ} (hkpos : 0 < k) (hklt : k < n)
    (hk : transportFlowMagnitude w (rotate w shift) 0 k = 2) :
    cycleDenominator n (ones w) = 5 := by
  obtain ⟨pre, suffix, b, hs, ht⟩ :=
    transportHeightTwo_exists_word_context_of_cost_four
      (ones_rotate w shift).symm hcost hkpos hklt hk
  have htarget := cycleDenominator_dvd_cyclicWordList_rotate w shift hones hdiv
  rw [hs] at hdiv
  rw [ht] at htarget
  apply cycleDenominator_eq_five_of_dvd_fifteen
    (Nat.pos_of_ne_zero (NeZero.ne n)) hones hD
  cases b with
  | false =>
      exact cycleDenominator_dvd_fifteen_of_heightTwo_context_difference
        (Nat.pos_of_ne_zero (NeZero.ne n)) hones pre suffix (dvd_sub htarget hdiv)
  | true =>
      exact cycleDenominator_dvd_fifteen_of_heightTwo_context_difference
        (Nat.pos_of_ne_zero (NeZero.ne n)) hones pre suffix (dvd_sub hdiv htarget)

end Collatz
