import Collatz.Radius4SmallCases
import Collatz.Radius4TransportCovariance

namespace Collatz

/-- The finite height-two exclusion is independent of the choice of the
minimizing cut.  Thus a generic exact transport-Radius-4 self-rotation with at
most three odd positions has no height-two edge at any cost-four cut. -/
theorem transportRadiusFour_no_minimizing_heightTwo_of_ones_le_three
    {n : ℕ} [NeZero n] (w : CyclicWord n) (shift : ZMod n)
    (hones : 0 < ones w) (hsmall : ones w ≤ 3)
    (hD : 1 < cycleDenominator n (ones w))
    (hdiv : cycleDenominator n (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hradius : IsTransportRadiusFour w shift) :
    ∀ cut : ZMod n, ∀ k : ℕ,
      transportCostAtCut w (rotate w shift) cut = 4 →
      0 < k → k < n → transportFlowMagnitude w (rotate w shift) cut k ≠ 2 := by
  intro cut k hcost hkpos hklt htwo
  have hones' : 0 < ones (rotate w cut) := by
    simpa only [ones_rotate] using hones
  have hsmall' : ones (rotate w cut) ≤ 3 := by
    simpa only [ones_rotate] using hsmall
  have hD' : 1 < cycleDenominator n (ones (rotate w cut)) := by
    simpa only [ones_rotate] using hD
  have hdiv' : cycleDenominator n (ones (rotate w cut)) ∣
      (wordNumerator (cyclicWordList (rotate w cut)) : ℤ) := by
    simpa only [ones_rotate] using
      cycleDenominator_dvd_cyclicWordList_rotate w cut hones hdiv
  have hradius' : IsTransportRadiusFour (rotate w cut) shift :=
    isTransportRadiusFour_rotate w shift cut hradius
  have hcost' : transportCostAtCut (rotate w cut)
      (rotate (rotate w cut) shift) 0 = 4 := by
    rw [← transportCostAtCut_selfRotation_rotate_cut w shift cut]
    exact hcost
  have htwo' : transportFlowMagnitude (rotate w cut)
      (rotate (rotate w cut) shift) 0 k = 2 := by
    rw [← rotate_rotate_comm w shift cut]
    unfold transportFlowMagnitude
    rw [← transportPrefixFlow_rotate_cut w (rotate w shift) cut k]
    exact htwo
  exact transportHeightTwo_no_small_ones_of_cost_four (rotate w cut) shift
    hones' hsmall' hD' hdiv' hradius' hcost' hkpos hklt htwo'

/-- In the small-weight generic Radius-4 case, every cost-four cut has only
unit-height internal transport edges.  The height-two branch is therefore
eliminated before the active-edge component partition is classified. -/
theorem transportRadiusFour_unit_flow_of_ones_le_three
    {n : ℕ} [NeZero n] (w : CyclicWord n) (shift : ZMod n)
    (hones : 0 < ones w) (hsmall : ones w ≤ 3)
    (hD : 1 < cycleDenominator n (ones w))
    (hdiv : cycleDenominator n (ones w) ∣ (wordNumerator (cyclicWordList w) : ℤ))
    (hradius : IsTransportRadiusFour w shift) :
    ∀ cut : ZMod n, transportCostAtCut w (rotate w shift) cut = 4 →
      ∀ j ∈ Finset.range (n - 1),
        transportFlowMagnitude w (rotate w shift) cut (j + 1) ≤ 1 := by
  intro cut hcost
  by_contra hnotunit
  obtain ⟨j, hj, htwo⟩ :=
    exists_transportFlowMagnitude_eq_two_of_cost_four_of_not_unit
      (ones_rotate w shift).symm cut hcost hnotunit
  have hjlt : j < n - 1 := Finset.mem_range.mp hj
  exact transportRadiusFour_no_minimizing_heightTwo_of_ones_le_three
    w shift hones hsmall hD hdiv hradius cut (j + 1) hcost (by omega) (by omega) htwo

end Collatz
