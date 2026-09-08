import Collatz.Radius4TransportClassification
import Collatz.Radius4TransportCovariance

namespace Collatz

/-- Every exact transport-Radius-4 self-rotation has a cut-normalized word at
which the complete cost-four geometric classification applies.  The relative
shift is unchanged, so each resulting branch is a genuine self-rotation
branch rather than a comparison of unrelated words. -/
theorem transportRadiusFour_exists_rotated_geometric_case {n : ℕ} [NeZero n]
    {w : CyclicWord n} {shift : ZMod n} (h : IsTransportRadiusFour w shift) :
    ∃ cut : ZMod n,
      transportCostAtCut (rotate w cut) (rotate (rotate w cut) shift) 0 = 4 ∧
      ((∃ k : ℕ, 0 < k ∧ k < n ∧
        transportFlowMagnitude (rotate w cut) (rotate (rotate w cut) shift) 0 k = 2) ∨
      (∀ j ∈ Finset.range (n - 1),
        transportFlowMagnitude (rotate w cut) (rotate (rotate w cut) shift) 0 (j + 1) ≤ 1) ∧
        ((transportActiveEdgeRunLengths (rotate w cut) (rotate (rotate w cut) shift) 0).Perm [4] ∨
          (transportActiveEdgeRunLengths (rotate w cut) (rotate (rotate w cut) shift) 0).Perm [3, 1] ∨
          (transportActiveEdgeRunLengths (rotate w cut) (rotate (rotate w cut) shift) 0).Perm [2, 2] ∨
          (transportActiveEdgeRunLengths (rotate w cut) (rotate (rotate w cut) shift) 0).Perm [2, 1, 1] ∨
          (transportActiveEdgeRunLengths (rotate w cut) (rotate (rotate w cut) shift) 0).Perm [1, 1, 1, 1])) := by
  rcases transportRadiusFour_exists_rotated_zero_cut h with ⟨cut, hcost⟩
  refine ⟨cut, hcost, ?_⟩
  apply transportCostFour_geometric_cases (cut := 0) ?_ hcost
  exact (ones_rotate (rotate w cut) shift).symm

end Collatz
