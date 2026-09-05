import Collatz.Radius4Transport

namespace Collatz

/-- Absolute prefix-flow height at one edge of a chosen cut. -/
def transportFlowMagnitude {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) (k : ℕ) : ℕ :=
  Int.natAbs (transportPrefixFlow source target cut k)

/-- Zero-based offsets of the charged internal edges whose prefix flow is
nonzero.  Offset `j` represents the internal edge `G_(j+1)`; the boundary
edges `G_0` and `G_n` are excluded exactly as in `transportCostAtCut`. -/
def transportActiveEdgeOffsets {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) : Finset ℕ :=
  (Finset.range (n - 1)).filter (fun j =>
    transportFlowMagnitude source target cut (j + 1) ≠ 0)

@[simp]
theorem mem_transportActiveEdgeOffsets_iff {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) (j : ℕ) :
    j ∈ transportActiveEdgeOffsets source target cut ↔
      j < n - 1 ∧ transportFlowMagnitude source target cut (j + 1) ≠ 0 := by
  simp [transportActiveEdgeOffsets]

/-- The cut cost is the sum of the absolute internal flow heights. -/
theorem transportCostAtCut_eq_sum_magnitudes {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) :
    transportCostAtCut source target cut =
      ∑ j in Finset.range (n - 1),
        transportFlowMagnitude source target cut (j + 1) := by
  rfl

/-- Removing zero-flow internal edges does not change transport cost. -/
theorem transportCostAtCut_eq_sum_active_magnitudes {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) :
    transportCostAtCut source target cut =
      ∑ j in transportActiveEdgeOffsets source target cut,
        transportFlowMagnitude source target cut (j + 1) := by
  classical
  calc
    transportCostAtCut source target cut =
        ∑ j in Finset.range (n - 1),
          transportFlowMagnitude source target cut (j + 1) :=
      transportCostAtCut_eq_sum_magnitudes source target cut
    _ = ∑ j in transportActiveEdgeOffsets source target cut,
          transportFlowMagnitude source target cut (j + 1) := by
      symm
      rw [transportActiveEdgeOffsets, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j hj
      by_cases h : transportFlowMagnitude source target cut (j + 1) ≠ 0 <;>
        simp [h]

/-- If every charged internal edge has flow height at most one, transport cost
is exactly the number of active internal edges.  This is the unit-height branch
of the RL238 Radius-4 topology classification. -/
theorem transportCostAtCut_eq_active_card_of_unit {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n)
    (hunit : ∀ j ∈ Finset.range (n - 1),
      transportFlowMagnitude source target cut (j + 1) ≤ 1) :
    transportCostAtCut source target cut =
      (transportActiveEdgeOffsets source target cut).card := by
  classical
  calc
    transportCostAtCut source target cut =
        ∑ j in transportActiveEdgeOffsets source target cut,
          transportFlowMagnitude source target cut (j + 1) :=
      transportCostAtCut_eq_sum_active_magnitudes source target cut
    _ = ∑ _j in transportActiveEdgeOffsets source target cut, 1 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' := (mem_transportActiveEdgeOffsets_iff source target cut j).mp hj
      have hle := hunit j (Finset.mem_range.mpr hj'.1)
      have hpos : 0 < transportFlowMagnitude source target cut (j + 1) :=
        Nat.pos_of_ne_zero hj'.2
      omega
    _ = (transportActiveEdgeOffsets source target cut).card := by
      simp

/-- At a cost-four cut, the unit-height branch has exactly four active internal
edges.  Their connected-component lengths are therefore a partition of four;
RL238's next classification step refines those four edges into `[4]`, `[3,1]`,
`[2,2]`, `[2,1,1]`, or `[1,1,1,1]`. -/
theorem transportActiveEdgeOffsets_card_eq_four_of_cost_four_of_unit
    {n : ℕ} [NeZero n] (source target : CyclicWord n) (cut : ZMod n)
    (hcost : transportCostAtCut source target cut = 4)
    (hunit : ∀ j ∈ Finset.range (n - 1),
      transportFlowMagnitude source target cut (j + 1) ≤ 1) :
    (transportActiveEdgeOffsets source target cut).card = 4 := by
  have hcard := transportCostAtCut_eq_active_card_of_unit source target cut hunit
  omega

end Collatz
