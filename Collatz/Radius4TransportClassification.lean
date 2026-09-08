import Collatz.Radius4TransportComponents
import Collatz.Radius4TransportHeightTwo

namespace Collatz

/-- The complete geometric case split at an equal-weight transport-cost-four
cut.  Either an internal edge has height two, or every internal edge has unit
height and the active edges have one of the five connected-component
partitions of four.  This is the common entry point for the branch-specific
Radius-4 arguments. -/
theorem transportCostFour_geometric_cases {n : ℕ} [NeZero n]
    {source target : CyclicWord n} (hones : ones source = ones target)
    (cut : ZMod n) (hcost : transportCostAtCut source target cut = 4) :
    (∃ k : ℕ, 0 < k ∧ k < n ∧
      transportFlowMagnitude source target cut k = 2) ∨
    (∀ j ∈ Finset.range (n - 1),
      transportFlowMagnitude source target cut (j + 1) ≤ 1) ∧
      ((transportActiveEdgeRunLengths source target cut).Perm [4] ∨
        (transportActiveEdgeRunLengths source target cut).Perm [3, 1] ∨
        (transportActiveEdgeRunLengths source target cut).Perm [2, 2] ∨
        (transportActiveEdgeRunLengths source target cut).Perm [2, 1, 1] ∨
        (transportActiveEdgeRunLengths source target cut).Perm [1, 1, 1, 1]) := by
  by_cases hunit : ∀ j ∈ Finset.range (n - 1),
      transportFlowMagnitude source target cut (j + 1) ≤ 1
  · right
    exact ⟨hunit,
      transportActiveEdgeRunLengths_family_of_cost_four_of_unit source target cut hcost hunit⟩
  · left
    obtain ⟨j, hj, htwo⟩ :=
      exists_transportFlowMagnitude_eq_two_of_cost_four_of_not_unit
        hones cut hcost hunit
    have hjlt : j < n - 1 := Finset.mem_range.mp hj
    exact ⟨j + 1, by omega, by omega, htwo⟩

end Collatz
