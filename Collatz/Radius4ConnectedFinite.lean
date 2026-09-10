import Collatz.Radius4FiniteCertificate
import Collatz.Radius4TransportSelfRotationCases

namespace Collatz

/-- The full denominator of an eligible connected four-edge self-rotation
belongs to the exact coefficient-divisor list. The local words and coefficient
divisibility are derived from the given geometry and source divisibility. -/
theorem transportConnectedFour_fullDenominator_mem
    {n : ℕ} [NeZero n] (w : CyclicWord n) (shift : ZMod n)
    (hones : 0 < ones w) (hD : 1 < cycleDenominator n (ones w))
    (hdiv : cycleDenominator n (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hcost : transportCostAtCut w (rotate w shift) 0 = 4)
    (hunit : ∀ j ∈ Finset.range (n - 1),
      transportFlowMagnitude w (rotate w shift) 0 (j + 1) ≤ 1)
    (hconnected : (transportActiveEdgeRunLengths w (rotate w shift) 0).Perm [4]) :
    cycleDenominator n (ones w) ∈ ([5, 7, 13, 17, 29, 35, 47, 65] : List ℤ) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  obtain ⟨pre, suffix, b, a₁, a₂, a₃, hs, ht⟩ :=
    transportConnectedFour_exists_word_context_of_cost_four
      (ones_rotate w shift).symm hcost hunit hconnected
  have htarget := cycleDenominator_dvd_cyclicWordList_rotate w shift hones hdiv
  rw [hs] at hdiv
  rw [ht] at htarget
  have hcoefficient : cycleDenominator n (ones w) ∣
      (transportConnectedFourCoefficient a₁ a₂ a₃ : ℤ) := by
    cases b with
    | false =>
        exact cycleDenominator_dvd_connectedFourCoefficient_of_context_difference
          hn hones pre suffix a₁ a₂ a₃ (dvd_sub hdiv htarget)
    | true =>
        exact cycleDenominator_dvd_connectedFourCoefficient_of_context_difference
          hn hones pre suffix a₁ a₂ a₃ (dvd_sub htarget hdiv)
  have hmem := cycleDenominator_natAbs_mem_of_dvd_connectedFourCoefficient
    hn hones hD a₁ a₂ a₃ hcoefficient
  have hcast : ((cycleDenominator n (ones w)).natAbs : ℤ) =
      cycleDenominator n (ones w) := Int.natAbs_of_nonneg (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem ⊢
  omega

/-- The connected four-edge family is impossible in the certified finite
weight range under the generic word hypotheses. No separate denominator-list
or coefficient-divisibility assumption is needed. -/
theorem transportConnectedFour_no_ones_lt_seven_thousand
    {n : ℕ} [NeZero n] (w : CyclicWord n) (shift : ZMod n)
    (hones : 0 < ones w) (hproper : ones w < n) (hsmall : ones w < 7000)
    (hD : 1 < cycleDenominator n (ones w))
    (hdiv : cycleDenominator n (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hprimitive : IsPrimitive w) (hshift : shift ≠ 0)
    (hradius : IsTransportRadiusFour w shift)
    (hcost : transportCostAtCut w (rotate w shift) 0 = 4)
    (hunit : ∀ j ∈ Finset.range (n - 1),
      transportFlowMagnitude w (rotate w shift) 0 (j + 1) ≤ 1)
    (hconnected : (transportActiveEdgeRunLengths w (rotate w shift) 0).Perm [4]) : False := by
  have hmem := transportConnectedFour_fullDenominator_mem
    w shift hones hD hdiv hcost hunit hconnected
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  exact transportRadiusFour_no_small_denominator_of_ones_lt_seven_thousand
    w shift hones hproper hsmall hmem hdiv hprimitive hshift hradius

/-- Below weight 7000, a hypothetical generic Radius-4 self-rotation has
only the four disconnected unit-height families after normalization. Both
height two and the connected `[4]` alternative are excluded arithmetically.
This leaves the four displayed families open. -/
theorem transportRadiusFour_exists_rotated_disconnected_family_of_ones_lt_seven_thousand
    {n : ℕ} [NeZero n] {w : CyclicWord n} {shift : ZMod n}
    (hones : 0 < ones w) (hproper : ones w < n) (hsmall : ones w < 7000)
    (hD : 1 < cycleDenominator n (ones w))
    (hdiv : cycleDenominator n (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hprimitive : IsPrimitive w) (hshift : shift ≠ 0)
    (hradius : IsTransportRadiusFour w shift) :
    ∃ cut : ZMod n,
      transportCostAtCut (rotate w cut) (rotate (rotate w cut) shift) 0 = 4 ∧
      (∀ j ∈ Finset.range (n - 1),
        transportFlowMagnitude (rotate w cut) (rotate (rotate w cut) shift) 0 (j + 1) ≤ 1) ∧
      ((transportActiveEdgeRunLengths (rotate w cut) (rotate (rotate w cut) shift) 0).Perm [3, 1] ∨
        (transportActiveEdgeRunLengths (rotate w cut) (rotate (rotate w cut) shift) 0).Perm [2, 2] ∨
        (transportActiveEdgeRunLengths (rotate w cut) (rotate (rotate w cut) shift) 0).Perm [2, 1, 1] ∨
        (transportActiveEdgeRunLengths (rotate w cut) (rotate (rotate w cut) shift) 0).Perm [1, 1, 1, 1]) := by
  obtain ⟨cut, hcost, hcases⟩ := transportRadiusFour_exists_rotated_geometric_case hradius
  have hones' : 0 < ones (rotate w cut) := by simpa only [ones_rotate] using hones
  have hD' : 1 < cycleDenominator n (ones (rotate w cut)) := by
    simpa only [ones_rotate] using hD
  have hdiv' : cycleDenominator n (ones (rotate w cut)) ∣
      (wordNumerator (cyclicWordList (rotate w cut)) : ℤ) := by
    simpa only [ones_rotate] using
      cycleDenominator_dvd_cyclicWordList_rotate w cut hones hdiv
  refine ⟨cut, hcost, ?_⟩
  rcases hcases with ⟨k, hkpos, hklt, hk⟩ | ⟨hunit, hfamilies⟩
  · have hfive : cycleDenominator n (ones w) = 5 := by
      simpa only [ones_rotate] using transportHeightTwo_fullDenominator_eq_five
        (rotate w cut) shift hones' hD' hdiv' hcost hkpos hklt hk
    exact (transportHeightTwo_no_ones_lt_seven_thousand
      w shift hones hproper hsmall hfive hdiv hradius).elim
  · refine ⟨hunit, ?_⟩
    rcases hfamilies with hconnected | hother
    · have hmem := transportConnectedFour_fullDenominator_mem
        (rotate w cut) shift hones' hD' hdiv' hcost hunit hconnected
      simp only [ones_rotate, List.mem_cons, List.not_mem_nil, or_false] at hmem
      exact (transportRadiusFour_no_small_denominator_of_ones_lt_seven_thousand
        w shift hones hproper hsmall hmem hdiv hprimitive hshift hradius).elim
    · exact hother

end Collatz
