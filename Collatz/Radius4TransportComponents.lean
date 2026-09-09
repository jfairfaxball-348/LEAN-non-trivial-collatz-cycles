import Collatz.Radius4TransportTopology

namespace Collatz

/-- Continue one maximal run of consecutive natural-number offsets.
`currentRev` stores the current run in reverse order so extension is constant-time. -/
private def consecutiveOffsetRunsAux
    (currentRev : List ℕ) (previous : ℕ) : List ℕ → List (List ℕ)
  | [] => [currentRev.reverse]
  | x :: xs =>
      if x = previous + 1 then
        consecutiveOffsetRunsAux (x :: currentRev) x xs
      else
        currentRev.reverse :: consecutiveOffsetRunsAux [x] x xs

/-- Maximal consecutive runs in an ordered list of natural-number offsets.
For the transport application the input is the increasing ordering of the
active internal-edge offsets, so these are exactly the connected components
of the active-edge set in the path graph on offsets. -/
def consecutiveOffsetRuns : List ℕ → List (List ℕ)
  | [] => []
  | x :: xs => consecutiveOffsetRunsAux [x] x xs

/-- Lengths of the maximal consecutive runs. -/
def consecutiveOffsetRunLengths (xs : List ℕ) : List ℕ :=
  (consecutiveOffsetRuns xs).map List.length

/-- Active transport-edge offsets in their natural increasing order. -/
def transportActiveEdgeOffsetList {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) : List ℕ :=
  (transportActiveEdgeOffsets source target cut).sort (· ≤ ·)

/-- The actual connected runs of active internal-edge offsets at a cut. -/
def transportActiveEdgeRuns {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) : List (List ℕ) :=
  consecutiveOffsetRuns (transportActiveEdgeOffsetList source target cut)

/-- Connected-component lengths of the active internal-edge set at a cut. -/
def transportActiveEdgeRunLengths {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) : List ℕ :=
  consecutiveOffsetRunLengths (transportActiveEdgeOffsetList source target cut)

private theorem exists_four_elements_of_length_eq_four {α : Type*}
    (xs : List α) (h : xs.length = 4) :
    ∃ a b c d, xs = [a, b, c, d] := by
  cases xs with
  | nil => simp at h
  | cons a xs =>
      cases xs with
      | nil => simp at h
      | cons b xs =>
          cases xs with
          | nil => simp at h
          | cons c xs =>
              cases xs with
              | nil => simp at h
              | cons d xs =>
                  cases xs with
                  | nil => exact ⟨a, b, c, d, rfl⟩
                  | cons e xs => simp at h

/-- Four ordered offsets have one of the five unordered connected-run
partitions of four.  The `List.Perm` formulation deliberately forgets only the
left/right ordering of distinct components; `consecutiveOffsetRuns` itself
retains the actual component order for later topology-specific arguments. -/
private theorem consecutiveOffsetRunLengths_four_family
    (a b c d : ℕ) :
    (consecutiveOffsetRunLengths [a, b, c, d]).Perm [4] ∨
      (consecutiveOffsetRunLengths [a, b, c, d]).Perm [3, 1] ∨
      (consecutiveOffsetRunLengths [a, b, c, d]).Perm [2, 2] ∨
      (consecutiveOffsetRunLengths [a, b, c, d]).Perm [2, 1, 1] ∨
      (consecutiveOffsetRunLengths [a, b, c, d]).Perm [1, 1, 1, 1] := by
  simp only [consecutiveOffsetRunLengths, consecutiveOffsetRuns,
    consecutiveOffsetRunsAux]
  split_ifs <;>
    simp only [List.map_cons, List.map_nil, List.length_reverse,
      List.length_cons, List.length_nil] <;>
    decide

/-- The unit-height half of the cost-four transport topology classification.
At a cost-four unit-height cut there are four active internal edges, and their
connected-run lengths are exhaustively one of the five established families:
`[4]`, `[3,1]`, `[2,2]`, `[2,1,1]`, or `[1,1,1,1]`, up to the irrelevant
left/right ordering of disconnected components. -/
theorem transportActiveEdgeRunLengths_family_of_cost_four_of_unit
    {n : ℕ} [NeZero n] (source target : CyclicWord n) (cut : ZMod n)
    (hcost : transportCostAtCut source target cut = 4)
    (hunit : ∀ j ∈ Finset.range (n - 1),
      transportFlowMagnitude source target cut (j + 1) ≤ 1) :
    (transportActiveEdgeRunLengths source target cut).Perm [4] ∨
      (transportActiveEdgeRunLengths source target cut).Perm [3, 1] ∨
      (transportActiveEdgeRunLengths source target cut).Perm [2, 2] ∨
      (transportActiveEdgeRunLengths source target cut).Perm [2, 1, 1] ∨
      (transportActiveEdgeRunLengths source target cut).Perm [1, 1, 1, 1] := by
  have hcard := transportActiveEdgeOffsets_card_eq_four_of_cost_four_of_unit
    source target cut hcost hunit
  have hlen : (transportActiveEdgeOffsetList source target cut).length = 4 := by
    simpa [transportActiveEdgeOffsetList] using hcard
  obtain ⟨a, b, c, d, hlist⟩ :=
    exists_four_elements_of_length_eq_four
      (transportActiveEdgeOffsetList source target cut) hlen
  rw [transportActiveEdgeRunLengths, hlist]
  exact consecutiveOffsetRunLengths_four_family a b c d

/-- The single connected four-edge family retains the concrete three
successor relations between its ordered offsets. This is the local-word
refinement of the existing family label, not a new topology classification. -/
theorem consecutiveOffsetRunLengths_four_connected_iff (a b c d : ℕ) :
    (consecutiveOffsetRunLengths [a, b, c, d]).Perm [4] ↔
      b = a + 1 ∧ c = b + 1 ∧ d = c + 1 := by
  simp only [consecutiveOffsetRunLengths, consecutiveOffsetRuns,
    consecutiveOffsetRunsAux]
  split_ifs <;> simp_all

/-- The `[3,1]` family has exactly two ordered shapes.  Either the length-three
component occurs first, or it occurs last.  Recording this distinction is
essential for the later chronological-word and numerator arguments: a mere
permutation of component lengths does not retain which local replacement
comes first. -/
theorem consecutiveOffsetRunLengths_four_three_one_iff (a b c d : ℕ) :
    (consecutiveOffsetRunLengths [a, b, c, d]).Perm [3, 1] ↔
      (b = a + 1 ∧ c = b + 1 ∧ d ≠ c + 1) ∨
        (b ≠ a + 1 ∧ c = b + 1 ∧ d = c + 1) := by
  simp only [consecutiveOffsetRunLengths, consecutiveOffsetRuns,
    consecutiveOffsetRunsAux]
  split_ifs <;> simp_all <;> decide

/-- In the `[4]` branch, the actual ordered active-edge list is four
consecutive offsets. Offset `p` is edge `G_(p+1)`, so the corresponding local
word occupies the five positions `p` through `p+4`. -/
theorem transportActiveEdgeOffsetList_eq_four_consecutive_of_connected
    {n : ℕ} [NeZero n] (source target : CyclicWord n) (cut : ZMod n)
    (hcost : transportCostAtCut source target cut = 4)
    (hunit : ∀ j ∈ Finset.range (n - 1),
      transportFlowMagnitude source target cut (j + 1) ≤ 1)
    (hconnected : (transportActiveEdgeRunLengths source target cut).Perm [4]) :
    ∃ p, p + 4 < n ∧
      transportActiveEdgeOffsetList source target cut =
        [p, p + 1, p + 2, p + 3] := by
  have hcard := transportActiveEdgeOffsets_card_eq_four_of_cost_four_of_unit
    source target cut hcost hunit
  have hlen : (transportActiveEdgeOffsetList source target cut).length = 4 := by
    simpa [transportActiveEdgeOffsetList] using hcard
  obtain ⟨a, b, c, d, hlist⟩ := List.length_eq_four.mp hlen
  have hfamily : (consecutiveOffsetRunLengths [a, b, c, d]).Perm [4] := by
    simpa only [transportActiveEdgeRunLengths, hlist] using hconnected
  obtain ⟨rfl, rfl, rfl⟩ :=
    (consecutiveOffsetRunLengths_four_connected_iff a b c d).mp hfamily
  have hmem : a + 1 + 1 + 1 ∈ transportActiveEdgeOffsetList source target cut := by
    rw [hlist]
    simp
  have hmem' : a + 1 + 1 + 1 ∈ transportActiveEdgeOffsets source target cut := by
    simpa only [transportActiveEdgeOffsetList, Finset.mem_sort] using hmem
  have hlt := (mem_transportActiveEdgeOffsets_iff source target cut _).mp hmem'
  refine ⟨a, by omega, ?_⟩
  simpa [Nat.add_assoc] using hlist

/-- In the first disconnected family, the concrete ordered active-edge list
is either a consecutive triple followed by an isolated edge or an isolated
edge followed by a consecutive triple.  This preserves the left-to-right
order required to turn the flow information into two chronological local
word contexts. -/
theorem transportActiveEdgeOffsetList_three_one_shapes_of_cost_four
    {n : ℕ} [NeZero n] (source target : CyclicWord n) (cut : ZMod n)
    (hcost : transportCostAtCut source target cut = 4)
    (hunit : ∀ j ∈ Finset.range (n - 1),
      transportFlowMagnitude source target cut (j + 1) ≤ 1)
    (hthreeOne : (transportActiveEdgeRunLengths source target cut).Perm [3, 1]) :
    ∃ a b c d,
      transportActiveEdgeOffsetList source target cut = [a, b, c, d] ∧
        ((b = a + 1 ∧ c = b + 1 ∧ d ≠ c + 1) ∨
          (b ≠ a + 1 ∧ c = b + 1 ∧ d = c + 1)) := by
  have hcard := transportActiveEdgeOffsets_card_eq_four_of_cost_four_of_unit
    source target cut hcost hunit
  have hlen : (transportActiveEdgeOffsetList source target cut).length = 4 := by
    simpa [transportActiveEdgeOffsetList] using hcard
  obtain ⟨a, b, c, d, hlist⟩ := List.length_eq_four.mp hlen
  refine ⟨a, b, c, d, hlist, ?_⟩
  apply (consecutiveOffsetRunLengths_four_three_one_iff a b c d).mp
  simpa only [transportActiveEdgeRunLengths, hlist] using hthreeOne

end Collatz
