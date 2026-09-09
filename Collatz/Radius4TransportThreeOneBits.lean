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

/-- An isolated unit-height active edge gives the adjacent local exchange
`01 ↔ 10`.  The other active edges are represented only through the support
description, so this can be combined with any separated component. -/
private theorem transportIsolatedRun_local_bits_of_offset_list
    {n : ℕ} [NeZero n] {source target : CyclicWord n}
    (hones : ones source = ones target) (cut : ZMod n)
    (hunit : ∀ j ∈ Finset.range (n - 1),
      transportFlowMagnitude source target cut (j + 1) ≤ 1)
    {q : ℕ}
    (hqmem : q ∈ transportActiveEdgeOffsetList source target cut)
    (hbefore : 0 < q → q - 1 ∉ transportActiveEdgeOffsetList source target cut)
    (hafter : q + 1 ∉ transportActiveEdgeOffsetList source target cut) :
    ∃ b : Bool, q + 1 < n ∧
      source (cut + (q : ZMod n)) = b ∧
      target (cut + (q : ZMod n)) = !b ∧
      source (cut + ((q + 1 : ℕ) : ZMod n)) = !b ∧
      target (cut + ((q + 1 : ℕ) : ZMod n)) = b := by
  have hactive : ∀ r, r ∈ transportActiveEdgeOffsetList source target cut →
      r ∈ transportActiveEdgeOffsets source target cut := by
    intro r hr
    simpa only [transportActiveEdgeOffsetList, Finset.mem_sort] using hr
  have hqbound := (mem_transportActiveEdgeOffsets_iff source target cut _).mp
    (hactive _ hqmem)
  have hqlt : q + 1 < n := by omega
  have hle := hunit q (Finset.mem_range.mpr hqbound.1)
  have hflow : transportFlowMagnitude source target cut (q + 1) = 1 := by omega
  have hprev : transportPrefixFlow source target cut q = 0 := by
    by_cases hq0 : q = 0
    · subst q
      exact transportPrefixFlow_zero source target cut
    · have hzero : transportFlowMagnitude source target cut q = 0 := by
        by_contra hne
        have hm : q - 1 ∈ transportActiveEdgeOffsets source target cut := by
          apply (mem_transportActiveEdgeOffsets_iff source target cut _).mpr
          refine ⟨by omega, ?_⟩
          simpa only [show q - 1 + 1 = q by omega] using hne
        exact hbefore (by omega)
          (by simpa only [transportActiveEdgeOffsetList, Finset.mem_sort] using hm)
      exact Int.natAbs_eq_zero.mp hzero
  have hnext : transportPrefixFlow source target cut (q + 2) = 0 := by
    by_cases hqn : q + 2 = n
    · subst n
      exact transportPrefixFlow_full_eq_zero_of_ones_eq hones cut
    · have hzero : transportFlowMagnitude source target cut (q + 2) = 0 := by
        by_contra hne
        have hm : q + 1 ∈ transportActiveEdgeOffsets source target cut := by
          apply (mem_transportActiveEdgeOffsets_iff source target cut _).mpr
          refine ⟨by omega, ?_⟩
          simpa only [show q + 1 + 1 = q + 2 by omega] using hne
        exact hafter (by simpa only [transportActiveEdgeOffsetList, Finset.mem_sort] using hm)
      exact Int.natAbs_eq_zero.mp hzero
  have hstep0 := transportPrefixFlow_succ source target cut q
  have hstep1 := transportPrefixFlow_succ source target cut (q + 1)
  rw [hprev] at hstep0
  rw [show q + 1 + 1 = q + 2 by omega, hnext] at hstep1
  have hinc0 : transportIncrement source target cut q =
      transportPrefixFlow source target cut (q + 1) := by omega
  have hinc1 : transportIncrement source target cut (q + 1) =
      -transportPrefixFlow source target cut (q + 1) := by omega
  rcases Int.natAbs_eq_iff.mp hflow with hs | hs
  · rw [hs] at hinc0 hinc1
    obtain ⟨h0s, h0t⟩ := (transportIncrement_eq_one_iff source target cut q).mp hinc0
    obtain ⟨h1s, h1t⟩ :=
      (transportIncrement_eq_neg_one_iff source target cut (q + 1)).mp hinc1
    exact ⟨false, hqlt, h0s, h0t, h1s, h1t⟩
  · rw [hs] at hinc0 hinc1
    obtain ⟨h0s, h0t⟩ := (transportIncrement_eq_neg_one_iff source target cut q).mp hinc0
    obtain ⟨h1s, h1t⟩ :=
      (transportIncrement_eq_one_iff source target cut (q + 1)).mp (by simpa using hinc1)
    exact ⟨true, hqlt, h0s, h0t, h1s, h1t⟩

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

/-- The isolated component of the `[3,1]` transport family is a chronological
adjacent exchange `01 ↔ 10`. -/
theorem transportThreeOne_exists_isolated_run_local_bits_of_cost_four
    {n : ℕ} [NeZero n] {source target : CyclicWord n}
    (hones : ones source = ones target) (cut : ZMod n)
    (hcost : transportCostAtCut source target cut = 4)
    (hunit : ∀ j ∈ Finset.range (n - 1),
      transportFlowMagnitude source target cut (j + 1) ≤ 1)
    (hthreeOne : (transportActiveEdgeRunLengths source target cut).Perm [3, 1]) :
    ∃ (q : ℕ) (b : Bool), q + 1 < n ∧
      source (cut + (q : ZMod n)) = b ∧
      target (cut + (q : ZMod n)) = !b ∧
      source (cut + ((q + 1 : ℕ) : ZMod n)) = !b ∧
      target (cut + ((q + 1 : ℕ) : ZMod n)) = b := by
  obtain ⟨a, b, c, d, hlist, hshape⟩ :=
    transportActiveEdgeOffsetList_three_one_shapes_of_cost_four
      source target cut hcost hunit hthreeOne
  rcases hshape with hfirst | hlast
  · rcases hfirst with ⟨hba, hcb, hdc⟩
    subst b
    subst c
    have hsorted : List.Pairwise (· ≤ ·) (transportActiveEdgeOffsetList source target cut) := by
      unfold transportActiveEdgeOffsetList
      exact (transportActiveEdgeOffsets source target cut).pairwise_sort _
    have hnodup : (transportActiveEdgeOffsetList source target cut).Nodup := by
      unfold transportActiveEdgeOffsetList
      exact (transportActiveEdgeOffsets source target cut).sort_nodup _
    have hdc' : d ≠ a + 3 := by
      intro h
      apply hdc
      omega
    have hqmem : d ∈ transportActiveEdgeOffsetList source target cut := by
      rw [hlist]
      simp
    have hbefore : 0 < d → d - 1 ∉ transportActiveEdgeOffsetList source target cut := by
      intro hd hm
      rw [hlist] at hsorted hnodup hm
      simp at hsorted hnodup hm
      rcases hm with hm | hm | hm | hm <;> omega
    have hafter : d + 1 ∉ transportActiveEdgeOffsetList source target cut := by
      intro hm
      rw [hlist] at hsorted hnodup hm
      simp at hsorted hnodup hm
      rcases hm with hm | hm | hm | hm <;> omega
    exact ⟨d, transportIsolatedRun_local_bits_of_offset_list hones cut hunit
      hqmem hbefore hafter⟩
  · rcases hlast with ⟨hba, hcb, hdc⟩
    subst c
    subst d
    have hsorted : List.Pairwise (· ≤ ·) (transportActiveEdgeOffsetList source target cut) := by
      unfold transportActiveEdgeOffsetList
      exact (transportActiveEdgeOffsets source target cut).pairwise_sort _
    have hnodup : (transportActiveEdgeOffsetList source target cut).Nodup := by
      unfold transportActiveEdgeOffsetList
      exact (transportActiveEdgeOffsets source target cut).sort_nodup _
    have hqmem : a ∈ transportActiveEdgeOffsetList source target cut := by
      rw [hlist]
      simp
    have hbefore : 0 < a → a - 1 ∉ transportActiveEdgeOffsetList source target cut := by
      intro ha hm
      rw [hlist] at hsorted hnodup hm
      simp at hsorted hnodup hm
      rcases hm with hm | hm | hm | hm <;> omega
    have hafter : a + 1 ∉ transportActiveEdgeOffsetList source target cut := by
      intro hm
      rw [hlist] at hnodup hm
      simp at hnodup hm
      rcases hm with hm | hm | hm | hm <;> omega
    exact ⟨a, transportIsolatedRun_local_bits_of_offset_list hones cut hunit
      hqmem hbefore hafter⟩

end Collatz
