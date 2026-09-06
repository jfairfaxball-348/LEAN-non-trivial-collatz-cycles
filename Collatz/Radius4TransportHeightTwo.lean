import Collatz.Radius4TransportTopology

namespace Collatz

/-- The absolute transport-flow height can increase by at most one in one
chronological step. This is the magnitude form of the signed one-Lipschitz
prefix-flow estimate. -/
theorem transportFlowMagnitude_succ_le_add_one {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) (k : ℕ) :
    transportFlowMagnitude source target cut (k + 1) ≤
      transportFlowMagnitude source target cut k + 1 := by
  have hstep := transportPrefixFlow_step_natAbs_le_one source target cut k
  have htri :
      Int.natAbs (transportPrefixFlow source target cut (k + 1)) ≤
        Int.natAbs (transportPrefixFlow source target cut k) +
          Int.natAbs
            (transportPrefixFlow source target cut (k + 1) -
              transportPrefixFlow source target cut k) := by
    have := Int.natAbs_add_le
      (transportPrefixFlow source target cut k)
      (transportPrefixFlow source target cut (k + 1) -
        transportPrefixFlow source target cut k)
    convert this using 1 <;> ring
  simpa [transportFlowMagnitude] using
    (le_trans htri (Nat.add_le_add_left hstep _))

/-- The absolute transport-flow height can decrease by at most one in one
chronological step. -/
theorem transportFlowMagnitude_le_succ_add_one {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) (k : ℕ) :
    transportFlowMagnitude source target cut k ≤
      transportFlowMagnitude source target cut (k + 1) + 1 := by
  have hstep := transportPrefixFlow_step_natAbs_le_one source target cut k
  have htri :
      Int.natAbs (transportPrefixFlow source target cut k) ≤
        Int.natAbs (transportPrefixFlow source target cut (k + 1)) +
          Int.natAbs
            (transportPrefixFlow source target cut k -
              transportPrefixFlow source target cut (k + 1)) := by
    have := Int.natAbs_add_le
      (transportPrefixFlow source target cut (k + 1))
      (transportPrefixFlow source target cut k -
        transportPrefixFlow source target cut (k + 1))
    convert this using 1 <;> ring
  have hstep' :
      Int.natAbs
          (transportPrefixFlow source target cut k -
            transportPrefixFlow source target cut (k + 1)) ≤ 1 := by
    simpa [Int.natAbs_neg] using hstep
  simpa [transportFlowMagnitude] using
    (le_trans htri (Nat.add_le_add_left hstep' _))

/-- The first charged internal flow edge has absolute height at most one. -/
theorem transportFlowMagnitude_one_le_one {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) :
    transportFlowMagnitude source target cut 1 ≤ 1 := by
  have h := transportPrefixFlow_step_natAbs_le_one source target cut 0
  simpa [transportFlowMagnitude] using h

/-- For equal-weight words, the last internal flow edge also has absolute
height at most one because the full endpoint flow is zero. -/
theorem transportFlowMagnitude_last_le_one_of_ones_eq {n : ℕ} [NeZero n]
    {source target : CyclicWord n} (hones : ones source = ones target)
    (cut : ZMod n) :
    transportFlowMagnitude source target cut (n - 1) ≤ 1 := by
  have hn : 1 ≤ n := by
    exact Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  have h := transportPrefixFlow_step_natAbs_le_one source target cut (n - 1)
  have hend := transportPrefixFlow_full_eq_zero_of_ones_eq hones cut
  have hidx : n - 1 + 1 = n := Nat.sub_add_cancel hn
  rw [hidx, hend] at h
  simpa [transportFlowMagnitude] using h

/-- Any selected collection of charged internal edges contributes no more than
the total cut cost. This is the nonnegative bookkeeping lemma used to rule out
transport heights above two at cost four. -/
theorem transportMagnitudeSum_le_cost_of_subset {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) (s : Finset ℕ)
    (hsub : s ⊆ Finset.range (n - 1)) :
    s.sum (fun j => transportFlowMagnitude source target cut (j + 1)) ≤
      transportCostAtCut source target cut := by
  rw [transportCostAtCut_eq_sum_magnitudes]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun _ _ _ => Nat.zero_le _)

/-- At an equal-weight cost-four cut, no charged internal prefix-flow edge can
have absolute height greater than two. A height at least three would, by the
one-Lipschitz rule and the zero boundary flow, force predecessor heights at
least two and one, contributing at least six to the cost. -/
theorem transportFlowMagnitude_le_two_of_cost_four {n : ℕ} [NeZero n]
    {source target : CyclicWord n} (hones : ones source = ones target)
    (cut : ZMod n) (hcost : transportCostAtCut source target cut = 4)
    {k : ℕ} (hkpos : 0 < k) (hklt : k < n) :
    transportFlowMagnitude source target cut k ≤ 2 := by
  by_contra hnot
  have hthree : 3 ≤ transportFlowMagnitude source target cut k := by omega
  have hk_ne_one : k ≠ 1 := by
    intro hk
    subst k
    have hfirst := transportFlowMagnitude_one_le_one source target cut
    omega
  have hk_ne_two : k ≠ 2 := by
    intro hk
    subst k
    have hfirst := transportFlowMagnitude_one_le_one source target cut
    have hnext := transportFlowMagnitude_succ_le_add_one source target cut 1
    norm_num at hnext
    omega
  have hkthree : 3 ≤ k := by omega
  have hprev1raw :=
    transportFlowMagnitude_succ_le_add_one source target cut (k - 1)
  have hkprev1 : k - 1 + 1 = k := by omega
  rw [hkprev1] at hprev1raw
  have hprev1 :
      2 ≤ transportFlowMagnitude source target cut (k - 1) := by omega
  have hprev2raw :=
    transportFlowMagnitude_succ_le_add_one source target cut (k - 2)
  have hkprev2 : k - 2 + 1 = k - 1 := by omega
  rw [hkprev2] at hprev2raw
  have hprev2 :
      1 ≤ transportFlowMagnitude source target cut (k - 2) := by omega
  let s : Finset ℕ := {k - 3, k - 2, k - 1}
  have hsub : s ⊆ Finset.range (n - 1) := by
    intro j hj
    simp [s] at hj
    simp only [Finset.mem_range]
    rcases hj with rfl | rfl | rfl <;> omega
  have hsum := transportMagnitudeSum_le_cost_of_subset source target cut s hsub
  have hk0 : k - 3 + 1 = k - 2 := by omega
  have hk1 : k - 2 + 1 = k - 1 := by omega
  have hk2 : k - 1 + 1 = k := by omega
  have h01 : k - 3 ≠ k - 2 := by omega
  have h02 : k - 3 ≠ k - 1 := by omega
  have h12 : k - 2 ≠ k - 1 := by omega
  simp [s, hk0, hk1, hk2, h01, h02, h12, hcost] at hsum
  omega

/-- The non-unit branch of an equal-weight cost-four cut necessarily contains
an internal edge of absolute flow height exactly two. This is the existence
half of RL238's unique height-two topology. -/
theorem exists_transportFlowMagnitude_eq_two_of_cost_four_of_not_unit
    {n : ℕ} [NeZero n] {source target : CyclicWord n}
    (hones : ones source = ones target) (cut : ZMod n)
    (hcost : transportCostAtCut source target cut = 4)
    (hnotunit : ¬ ∀ j ∈ Finset.range (n - 1),
      transportFlowMagnitude source target cut (j + 1) ≤ 1) :
    ∃ j ∈ Finset.range (n - 1),
      transportFlowMagnitude source target cut (j + 1) = 2 := by
  push_neg at hnotunit
  obtain ⟨j, hj, hjgt⟩ := hnotunit
  have hjlt : j < n - 1 := Finset.mem_range.mp hj
  have hkpos : 0 < j + 1 := by omega
  have hklt : j + 1 < n := by omega
  have hle := transportFlowMagnitude_le_two_of_cost_four
    hones cut hcost hkpos hklt
  refine ⟨j, hj, ?_⟩
  omega

/-- A height-two internal edge at an equal-weight cost-four cut is rigid: it is
strictly internal, both neighbouring internal edges have height one, and these
three edges consume the entire transport budget. This is exactly the
`(1,2,1)` height profile certified in RL238. -/
theorem transportHeightTwo_rigid_of_cost_four {n : ℕ} [NeZero n]
    {source target : CyclicWord n} (hones : ones source = ones target)
    (cut : ZMod n) (hcost : transportCostAtCut source target cut = 4)
    {k : ℕ} (hkpos : 0 < k) (hklt : k < n)
    (hk : transportFlowMagnitude source target cut k = 2) :
    1 < k ∧ k + 1 < n ∧
      transportFlowMagnitude source target cut (k - 1) = 1 ∧
      transportFlowMagnitude source target cut (k + 1) = 1 ∧
      transportCostAtCut source target cut =
        transportFlowMagnitude source target cut (k - 1) +
          transportFlowMagnitude source target cut k +
          transportFlowMagnitude source target cut (k + 1) := by
  have hfirst := transportFlowMagnitude_one_le_one source target cut
  have hkgt : 1 < k := by
    by_contra h
    have hkone : k = 1 := by omega
    rw [hkone] at hk
    omega
  have hlast := transportFlowMagnitude_last_le_one_of_ones_eq hones cut
  have hknotlast : k ≠ n - 1 := by
    intro hklast
    rw [hklast] at hk
    omega
  have hksucc : k + 1 < n := by omega
  have hleftRaw :=
    transportFlowMagnitude_succ_le_add_one source target cut (k - 1)
  have hkleft : k - 1 + 1 = k := by omega
  rw [hkleft] at hleftRaw
  have hleftPos :
      1 ≤ transportFlowMagnitude source target cut (k - 1) := by omega
  have hrightRaw :=
    transportFlowMagnitude_le_succ_add_one source target cut k
  have hrightPos :
      1 ≤ transportFlowMagnitude source target cut (k + 1) := by omega
  let s : Finset ℕ := {k - 2, k - 1, k}
  have hsub : s ⊆ Finset.range (n - 1) := by
    intro j hj
    simp [s] at hj
    simp only [Finset.mem_range]
    rcases hj with rfl | rfl | rfl <;> omega
  have hsum := transportMagnitudeSum_le_cost_of_subset source target cut s hsub
  have hk0 : k - 2 + 1 = k - 1 := by omega
  have hk1 : k - 1 + 1 = k := by omega
  have h01 : k - 2 ≠ k - 1 := by omega
  have h02 : k - 2 ≠ k := by omega
  have h12 : k - 1 ≠ k := by omega
  simp [s, hk0, hk1, h01, h02, h12, hcost] at hsum
  have hleft : transportFlowMagnitude source target cut (k - 1) = 1 := by
    omega
  have hright : transportFlowMagnitude source target cut (k + 1) = 1 := by
    omega
  refine ⟨hkgt, hksucc, hleft, hright, ?_⟩
  rw [hcost, hleft, hk, hright]

/-- The complete non-unit branch of an equal-weight cost-four cut has the
unique RL238 height-two profile `(1,2,1)`. The final equality records that the
three displayed edges exhaust the full cost, so no additional positive-height
edge can occur outside the displayed excursion. -/
theorem exists_transportHeightTwo_pattern_of_cost_four_of_not_unit
    {n : ℕ} [NeZero n] {source target : CyclicWord n}
    (hones : ones source = ones target) (cut : ZMod n)
    (hcost : transportCostAtCut source target cut = 4)
    (hnotunit : ¬ ∀ j ∈ Finset.range (n - 1),
      transportFlowMagnitude source target cut (j + 1) ≤ 1) :
    ∃ k : ℕ, 1 < k ∧ k + 1 < n ∧
      transportFlowMagnitude source target cut (k - 1) = 1 ∧
      transportFlowMagnitude source target cut k = 2 ∧
      transportFlowMagnitude source target cut (k + 1) = 1 ∧
      transportCostAtCut source target cut =
        transportFlowMagnitude source target cut (k - 1) +
          transportFlowMagnitude source target cut k +
          transportFlowMagnitude source target cut (k + 1) := by
  obtain ⟨j, hj, hjtwo⟩ :=
    exists_transportFlowMagnitude_eq_two_of_cost_four_of_not_unit
      hones cut hcost hnotunit
  have hjlt : j < n - 1 := Finset.mem_range.mp hj
  have hkpos : 0 < j + 1 := by omega
  have hklt : j + 1 < n := by omega
  rcases transportHeightTwo_rigid_of_cost_four hones cut hcost hkpos hklt hjtwo with
    ⟨hkgt, hksucc, hleft, hright, hspent⟩
  exact ⟨j + 1, hkgt, hksucc, hleft, hjtwo, hright, hspent⟩

end Collatz
