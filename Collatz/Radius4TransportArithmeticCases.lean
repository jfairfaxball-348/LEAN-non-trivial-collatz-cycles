import Collatz.Radius4ConnectedBounds
import Collatz.Radius4TransportSelfRotationCases

namespace Collatz

/-- In the generic full-denominator setting, an exact transport-Radius-4
self-rotation can be cut-normalized so that the height-two branch has
denominator exactly five, while the connected unit-height `[4]` branch has
denominator at most sixty-five.  The other unit-height component families are
retained explicitly for their separate local analyses. -/
theorem transportRadiusFour_exists_rotated_arithmetic_case {n : ℕ} [NeZero n]
    {w : CyclicWord n} {shift : ZMod n}
    (hones : 0 < ones w) (hD : 1 < cycleDenominator n (ones w))
    (hdiv : cycleDenominator n (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hradius : IsTransportRadiusFour w shift) :
    ∃ cut : ZMod n,
      ((∃ k : ℕ, 0 < k ∧ k < n ∧
        transportFlowMagnitude (rotate w cut) (rotate (rotate w cut) shift) 0 k = 2) ∧
        cycleDenominator n (ones w) = 5) ∨
      ((∀ j ∈ Finset.range (n - 1),
        transportFlowMagnitude (rotate w cut) (rotate (rotate w cut) shift) 0 (j + 1) ≤ 1) ∧
        (((transportActiveEdgeRunLengths (rotate w cut) (rotate (rotate w cut) shift) 0).Perm [4] ∧
            cycleDenominator n (ones w) ≤ 65) ∨
          (transportActiveEdgeRunLengths (rotate w cut) (rotate (rotate w cut) shift) 0).Perm [3, 1] ∨
          (transportActiveEdgeRunLengths (rotate w cut) (rotate (rotate w cut) shift) 0).Perm [2, 2] ∨
          (transportActiveEdgeRunLengths (rotate w cut) (rotate (rotate w cut) shift) 0).Perm [2, 1, 1] ∨
          (transportActiveEdgeRunLengths (rotate w cut) (rotate (rotate w cut) shift) 0).Perm [1, 1, 1, 1])) := by
  rcases transportRadiusFour_exists_rotated_geometric_case hradius with ⟨cut, hcost, hcases⟩
  have hones' : 0 < ones (rotate w cut) := by
    simpa only [ones_rotate] using hones
  have hD' : 1 < cycleDenominator n (ones (rotate w cut)) := by
    simpa only [ones_rotate] using hD
  have hdiv' : cycleDenominator n (ones (rotate w cut)) ∣
      (wordNumerator (cyclicWordList (rotate w cut)) : ℤ) := by
    simpa only [ones_rotate] using
      cycleDenominator_dvd_cyclicWordList_rotate w cut hones hdiv
  refine ⟨cut, ?_⟩
  rcases hcases with hheight | ⟨hunit, hfamilies⟩
  · left
    rcases hheight with ⟨k, hkpos, hklt, hk⟩
    refine ⟨⟨k, hkpos, hklt, hk⟩, ?_⟩
    have hfive := transportHeightTwo_fullDenominator_eq_five
      (w := rotate w cut) (shift := shift) hones' hD' hdiv' hcost hkpos hklt hk
    simpa only [ones_rotate] using hfive
  · right
    refine ⟨hunit, ?_⟩
    rcases hfamilies with hconnected | hother
    · left
      refine ⟨hconnected, ?_⟩
      have hle := transportConnectedFour_fullDenominator_le_sixty_five
        (w := rotate w cut) (shift := shift) hones' hD' hdiv' hcost hunit hconnected
      simpa only [ones_rotate] using hle
    · exact Or.inr hother

end Collatz
