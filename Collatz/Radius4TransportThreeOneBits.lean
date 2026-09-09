import Collatz.Radius4TransportComponents
import Collatz.Radius4TransportSigned

namespace Collatz

/-- A consecutive triple of unit-height active edges, separated from the next
active edge, gives the local endpoint exchange `0ab1 ↔ 1ab0`.  This lemma is
deliberately independent of where the remaining isolated edge lies. -/
private theorem transportThreeRun_local_bits_of_offset_list
    {n : ℕ} [NeZero n] {source target : CyclicWord n}
    (hones : ones source = ones target) (cut : ZMod n)
    (hunit : ∀ j ∈ Finset.range (n - 1),
      transportFlowMagnitude source target cut (j + 1) ≤ 1)
    {p q : ℕ}
    (hsupport : ∀ r, r ∈ transportActiveEdgeOffsetList source target cut ↔
      r = p ∨ r = p + 1 ∨ r = p + 2 ∨ r = q)
    (hqbefore : 0 < p → q ≠ p - 1) (hqafter : q ≠ p + 3) :
    ∃ b : Bool, p + 3 < n ∧
      source (cut + (p : ZMod n)) = b ∧
      target (cut + (p : ZMod n)) = !b ∧
      source (cut + ((p + 3 : ℕ) : ZMod n)) = !b ∧
      target (cut + ((p + 3 : ℕ) : ZMod n)) = b ∧
      (∀ j, p < j → j < p + 3 →
        source (cut + (j : ZMod n)) = target (cut + (j : ZMod n))) := by
  have hactive : ∀ r, r ∈ transportActiveEdgeOffsetList source target cut →
      r ∈ transportActiveEdgeOffsets source target cut := by
    intro r hr
    simpa only [transportActiveEdgeOffsetList, Finset.mem_sort] using hr
  have hmag : ∀ j, p < j → j ≤ p + 3 →
      transportFlowMagnitude source target cut j = 1 := by
    intro j hjlow hjhigh
    have hmem : j - 1 ∈ transportActiveEdgeOffsetList source target cut := by
      apply (hsupport _).mpr
      omega
    obtain ⟨hbound, hne⟩ :=
      (mem_transportActiveEdgeOffsets_iff source target cut _).mp (hactive _ hmem)
    have hle := hunit (j - 1) (Finset.mem_range.mpr hbound)
    rw [show j - 1 + 1 = j by omega] at hne hle
    omega
  have hp3 : p + 3 < n := by
    have hmem : p + 2 ∈ transportActiveEdgeOffsetList source target cut := by
      apply (hsupport _).mpr
      omega
    have hbound := (mem_transportActiveEdgeOffsets_iff source target cut _).mp
      (hactive _ hmem)
    omega
  have hbefore : transportPrefixFlow source target cut p = 0 := by
    by_cases hp0 : p = 0
    · subst p
      exact transportPrefixFlow_zero source target cut
    · have hnot : p - 1 ∉ transportActiveEdgeOffsetList source target cut := by
        intro hm
        have hcases := (hsupport _).mp hm
        have hq := hqbefore (by omega)
        omega
      have hzero : transportFlowMagnitude source target cut p = 0 := by
        by_contra hne
        have hm : p - 1 ∈ transportActiveEdgeOffsets source target cut := by
          apply (mem_transportActiveEdgeOffsets_iff source target cut _).mpr
          refine ⟨by omega, ?_⟩
          simpa only [show p - 1 + 1 = p by omega] using hne
        exact hnot (by simpa only [transportActiveEdgeOffsetList, Finset.mem_sort] using hm)
      exact Int.natAbs_eq_zero.mp hzero
  have hafter : transportPrefixFlow source target cut (p + 4) = 0 := by
    by_cases hpn : p + 4 = n
    · subst n
      exact transportPrefixFlow_full_eq_zero_of_ones_eq hones cut
    · have hzero : transportFlowMagnitude source target cut (p + 4) = 0 := by
        by_contra hne
        have hm : p + 3 ∈ transportActiveEdgeOffsets source target cut := by
          apply (mem_transportActiveEdgeOffsets_iff source target cut _).mpr
          refine ⟨by omega, ?_⟩
          simpa only [show p + 3 + 1 = p + 4 by omega] using hne
        have hmem : p + 3 ∈ transportActiveEdgeOffsetList source target cut := by
          simpa only [transportActiveEdgeOffsetList, Finset.mem_sort] using hm
        have hcases := (hsupport _).mp hmem
        omega
      exact Int.natAbs_eq_zero.mp hzero
  have h12 := transportPrefixFlow_succ_eq_of_magnitudes_eq_one source target cut (p + 1)
    (hmag (p + 1) (by omega) (by omega)) (hmag (p + 2) (by omega) (by omega))
  have h23 := transportPrefixFlow_succ_eq_of_magnitudes_eq_one source target cut (p + 2)
    (hmag (p + 2) (by omega) (by omega)) (hmag (p + 3) (by omega) (by omega))
  have hstep0 := transportPrefixFlow_succ source target cut p
  have hstep3 := transportPrefixFlow_succ source target cut (p + 3)
  rw [hbefore] at hstep0
  rw [show p + 3 + 1 = p + 4 by omega, hafter, h23, h12] at hstep3
  have hinc0 : transportIncrement source target cut p =
      transportPrefixFlow source target cut (p + 1) := by omega
  have hinc3 : transportIncrement source target cut (p + 3) =
      -transportPrefixFlow source target cut (p + 1) := by omega
  have hmiddle : ∀ j, p < j → j < p + 3 →
      source (cut + (j : ZMod n)) = target (cut + (j : ZMod n)) := by
    intro j hjlow hjhigh
    exact transportBits_eq_of_adjacent_magnitudes_eq_one source target cut j
      (hmag j hjlow (by omega)) (hmag (j + 1) (by omega) (by omega))
  rcases Int.natAbs_eq_iff.mp (hmag (p + 1) (by omega) (by omega)) with hs | hs
  · rw [hs] at hinc0 hinc3
    obtain ⟨h0s, h0t⟩ := (transportIncrement_eq_one_iff source target cut p).mp hinc0
    obtain ⟨h3s, h3t⟩ :=
      (transportIncrement_eq_neg_one_iff source target cut (p + 3)).mp hinc3
    exact ⟨false, hp3, h0s, h0t, h3s, h3t, hmiddle⟩
  · rw [hs] at hinc0 hinc3
    obtain ⟨h0s, h0t⟩ := (transportIncrement_eq_neg_one_iff source target cut p).mp hinc0
    obtain ⟨h3s, h3t⟩ :=
      (transportIncrement_eq_one_iff source target cut (p + 3)).mp (by simpa using hinc3)
    exact ⟨true, hp3, h0s, h0t, h3s, h3t, hmiddle⟩

/-- The `[3,1]` transport family always contains a chronological local
replacement `0ab1 ↔ 1ab0`.  The theorem retains no artificial choice of
component order: it derives the triple-first/triple-last alternatives from
the ordered active-edge support. -/
theorem transportThreeOne_exists_three_run_local_bits_of_cost_four
    {n : ℕ} [NeZero n] {source target : CyclicWord n}
    (hones : ones source = ones target) (cut : ZMod n)
    (hcost : transportCostAtCut source target cut = 4)
    (hunit : ∀ j ∈ Finset.range (n - 1),
      transportFlowMagnitude source target cut (j + 1) ≤ 1)
    (hthreeOne : (transportActiveEdgeRunLengths source target cut).Perm [3, 1]) :
    ∃ (p : ℕ) (b : Bool), p + 3 < n ∧
      source (cut + (p : ZMod n)) = b ∧
      target (cut + (p : ZMod n)) = !b ∧
      source (cut + ((p + 3 : ℕ) : ZMod n)) = !b ∧
      target (cut + ((p + 3 : ℕ) : ZMod n)) = b ∧
      (∀ j, p < j → j < p + 3 →
        source (cut + (j : ZMod n)) = target (cut + (j : ZMod n))) := by
  obtain ⟨a, b, c, d, hlist, hshape⟩ :=
    transportActiveEdgeOffsetList_three_one_shapes_of_cost_four
      source target cut hcost hunit hthreeOne
  rcases hshape with hfirst | hlast
  · rcases hfirst with ⟨hba, hcb, hdc⟩
    subst b
    subst c
    have hsupport : ∀ r, r ∈ transportActiveEdgeOffsetList source target cut ↔
        r = a ∨ r = a + 1 ∨ r = a + 2 ∨ r = d := by
      intro r
      rw [hlist]
      simp [Nat.add_assoc]
    have hsorted : List.Pairwise (· ≤ ·) (transportActiveEdgeOffsetList source target cut) := by
      unfold transportActiveEdgeOffsetList
      exact (transportActiveEdgeOffsets source target cut).pairwise_sort _
    have hqbefore : 0 < a → d ≠ a - 1 := by
      intro ha
      rw [hlist] at hsorted
      simp at hsorted
      omega
    refine ⟨a, ?_⟩
    exact transportThreeRun_local_bits_of_offset_list hones cut hunit hsupport hqbefore hdc
  · rcases hlast with ⟨hba, hcb, hdc⟩
    subst c
    subst d
    have hsupport : ∀ r, r ∈ transportActiveEdgeOffsetList source target cut ↔
        r = b ∨ r = b + 1 ∨ r = b + 2 ∨ r = a := by
      intro r
      rw [hlist]
      simp [Nat.add_assoc, or_comm, or_left_comm]
    have hsorted : List.Pairwise (· ≤ ·) (transportActiveEdgeOffsetList source target cut) := by
      unfold transportActiveEdgeOffsetList
      exact (transportActiveEdgeOffsets source target cut).pairwise_sort _
    have hqbefore : 0 < b → a ≠ b - 1 := by
      intro hb h
      apply hba
      omega
    have hqafter : a ≠ b + 3 := by
      rw [hlist] at hsorted
      simp at hsorted
      omega
    refine ⟨b, ?_⟩
    exact transportThreeRun_local_bits_of_offset_list hones cut hunit hsupport hqbefore hqafter

end Collatz
