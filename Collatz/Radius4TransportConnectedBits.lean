import Collatz.Radius4TransportComponents
import Collatz.Radius4TransportSigned

namespace Collatz

/-- The connected four-edge unit-height family is exactly a local endpoint
exchange `1abc0 ↔ 0abc1`. Its three interior bits and every bit outside the
five-position window agree. The actual cyclic cut and ordered support are kept. -/
theorem transportConnectedFour_local_bits_of_cost_four
    {n : ℕ} [NeZero n] {source target : CyclicWord n}
    (hones : ones source = ones target) (cut : ZMod n)
    (hcost : transportCostAtCut source target cut = 4)
    (hunit : ∀ j ∈ Finset.range (n - 1),
      transportFlowMagnitude source target cut (j + 1) ≤ 1)
    (hconnected : (transportActiveEdgeRunLengths source target cut).Perm [4]) :
    ∃ (p : ℕ) (b : Bool), p + 4 < n ∧
      source (cut + (p : ZMod n)) = b ∧
      target (cut + (p : ZMod n)) = !b ∧
      source (cut + ((p + 4 : ℕ) : ZMod n)) = !b ∧
      target (cut + ((p + 4 : ℕ) : ZMod n)) = b ∧
      (∀ j, p < j → j < p + 4 →
        source (cut + (j : ZMod n)) = target (cut + (j : ZMod n))) ∧
      (∀ j, j < n → j < p ∨ p + 5 ≤ j →
        source (cut + (j : ZMod n)) = target (cut + (j : ZMod n))) := by
  obtain ⟨p, hp, hlist⟩ :=
    transportActiveEdgeOffsetList_eq_four_consecutive_of_connected
      source target cut hcost hunit hconnected
  have hzero : ∀ j, j ≤ n → j ≤ p ∨ p + 5 ≤ j →
      transportPrefixFlow source target cut j = 0 := by
    intro j hj houtside
    by_cases hj0 : j = 0
    · subst j
      exact transportPrefixFlow_zero source target cut
    by_cases hjn : j = n
    · subst j
      exact transportPrefixFlow_full_eq_zero_of_ones_eq hones cut
    have hz : transportFlowMagnitude source target cut j = 0 := by
      by_contra hne
      have hactive : j - 1 ∈ transportActiveEdgeOffsets source target cut := by
        apply (mem_transportActiveEdgeOffsets_iff source target cut _).mpr
        refine ⟨by omega, ?_⟩
        simpa only [show j - 1 + 1 = j by omega] using hne
      have hmem : j - 1 ∈ transportActiveEdgeOffsetList source target cut := by
        simpa only [transportActiveEdgeOffsetList, Finset.mem_sort] using hactive
      rw [hlist] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      omega
    exact Int.natAbs_eq_zero.mp hz
  have hmag : ∀ j, p < j → j ≤ p + 4 →
      transportFlowMagnitude source target cut j = 1 := by
    intro j hjlow hjhigh
    have hmem : j - 1 ∈ transportActiveEdgeOffsetList source target cut := by
      rw [hlist]
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    have hactive : j - 1 ∈ transportActiveEdgeOffsets source target cut := by
      simpa only [transportActiveEdgeOffsetList, Finset.mem_sort] using hmem
    obtain ⟨hbound, hne⟩ := (mem_transportActiveEdgeOffsets_iff source target cut _).mp hactive
    have hle := hunit (j - 1) (Finset.mem_range.mpr hbound)
    rw [show j - 1 + 1 = j by omega] at hne hle
    omega
  have heq : ∀ j, p < j → j < p + 4 →
      transportPrefixFlow source target cut (j + 1) =
        transportPrefixFlow source target cut j := by
    intro j hjlow hjhigh
    exact transportPrefixFlow_succ_eq_of_magnitudes_eq_one source target cut j
      (hmag j hjlow (by omega)) (hmag (j + 1) (by omega) (by omega))
  have h12 : transportPrefixFlow source target cut (p + 2) =
      transportPrefixFlow source target cut (p + 1) := by
    simpa only [Nat.add_assoc] using heq (p + 1) (by omega) (by omega)
  have h23 : transportPrefixFlow source target cut (p + 3) =
      transportPrefixFlow source target cut (p + 2) := by
    simpa only [Nat.add_assoc] using heq (p + 2) (by omega) (by omega)
  have h34 : transportPrefixFlow source target cut (p + 4) =
      transportPrefixFlow source target cut (p + 3) := by
    simpa only [Nat.add_assoc] using heq (p + 3) (by omega) (by omega)
  have hend := h34.trans (h23.trans h12)
  have hbefore := hzero p (by omega) (Or.inl (by omega))
  have hafter := hzero (p + 5) (by omega) (Or.inr (by omega))
  have hstep0 := transportPrefixFlow_succ source target cut p
  have hstep4 := transportPrefixFlow_succ source target cut (p + 4)
  rw [hbefore] at hstep0
  rw [show p + 4 + 1 = p + 5 by omega, hafter, hend] at hstep4
  have hinc0 : transportIncrement source target cut p =
      transportPrefixFlow source target cut (p + 1) := by omega
  have hinc4 : transportIncrement source target cut (p + 4) =
      -transportPrefixFlow source target cut (p + 1) := by omega
  have hmiddle : ∀ j, p < j → j < p + 4 →
      source (cut + (j : ZMod n)) = target (cut + (j : ZMod n)) := by
    intro j hjlow hjhigh
    exact transportBits_eq_of_adjacent_magnitudes_eq_one source target cut j
      (hmag j hjlow (by omega)) (hmag (j + 1) (by omega) (by omega))
  have houtside : ∀ j, j < n → j < p ∨ p + 5 ≤ j →
      source (cut + (j : ZMod n)) = target (cut + (j : ZMod n)) := by
    intro j hj hout
    apply (transportIncrement_eq_zero_iff source target cut j).mp
    have hz := hzero j (by omega) (by omega)
    have hzs := hzero (j + 1) (by omega) (by omega)
    have hstep := transportPrefixFlow_succ source target cut j
    rw [hz, hzs] at hstep
    omega
  rcases Int.natAbs_eq_iff.mp (hmag (p + 1) (by omega) (by omega)) with hs | hs
  · rw [hs] at hinc0 hinc4
    obtain ⟨h0s, h0t⟩ := (transportIncrement_eq_one_iff source target cut p).mp hinc0
    obtain ⟨h4s, h4t⟩ := (transportIncrement_eq_neg_one_iff source target cut (p + 4)).mp hinc4
    exact ⟨p, false, hp, h0s, h0t, h4s, h4t, hmiddle, houtside⟩
  · rw [hs] at hinc0 hinc4
    obtain ⟨h0s, h0t⟩ := (transportIncrement_eq_neg_one_iff source target cut p).mp hinc0
    obtain ⟨h4s, h4t⟩ := (transportIncrement_eq_one_iff source target cut (p + 4)).mp
      (by simpa using hinc4)
    exact ⟨p, true, hp, h0s, h0t, h4s, h4t, hmiddle, houtside⟩

end Collatz
