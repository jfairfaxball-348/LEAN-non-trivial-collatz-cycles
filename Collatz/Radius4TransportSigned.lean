import Collatz.Radius4TransportHeightTwo

namespace Collatz

/-- A positive unit transport increment records exactly the local change
from a source zero to a target one. -/
theorem transportIncrement_eq_one_iff {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) (j : ℕ) :
    transportIncrement source target cut j = 1 ↔
      source (cut + (j : ZMod n)) = false ∧
        target (cut + (j : ZMod n)) = true := by
  unfold transportIncrement
  cases source (cut + (j : ZMod n)) <;>
    cases target (cut + (j : ZMod n)) <;> simp

/-- A negative unit transport increment records exactly the local change
from a source one to a target zero. -/
theorem transportIncrement_eq_neg_one_iff {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) (j : ℕ) :
    transportIncrement source target cut j = -1 ↔
      source (cut + (j : ZMod n)) = true ∧
        target (cut + (j : ZMod n)) = false := by
  unfold transportIncrement
  cases source (cut + (j : ZMod n)) <;>
    cases target (cut + (j : ZMod n)) <;> simp

/-- Zero transport increment means that the two bits agree. This is the
unchanged-interior condition for a connected unit-height run. -/
theorem transportIncrement_eq_zero_iff {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) (j : ℕ) :
    transportIncrement source target cut j = 0 ↔
      source (cut + (j : ZMod n)) = target (cut + (j : ZMod n)) := by
  unfold transportIncrement
  cases source (cut + (j : ZMod n)) <;>
    cases target (cut + (j : ZMod n)) <;> simp

/-- Adjacent unit-height nonzero edges have the same signed flow. Opposite
signs would require a step of magnitude two, contrary to the binary increment
bound. This is the signed refinement of a connected RL238 unit-height run. -/
theorem transportPrefixFlow_succ_eq_of_magnitudes_eq_one
    {n : ℕ} [NeZero n] (source target : CyclicWord n)
    (cut : ZMod n) (k : ℕ)
    (hk : transportFlowMagnitude source target cut k = 1)
    (hsucc : transportFlowMagnitude source target cut (k + 1) = 1) :
    transportPrefixFlow source target cut (k + 1) =
      transportPrefixFlow source target cut k := by
  have hstep := transportPrefixFlow_step_natAbs_le_one source target cut k
  rcases Int.natAbs_eq_iff.mp hk with hk | hk <;>
    rcases Int.natAbs_eq_iff.mp hsucc with hsucc | hsucc
  all_goals omega

/-- The bits between two adjacent unit-height edges agree, since the common
signed height has zero increment. -/
theorem transportBits_eq_of_adjacent_magnitudes_eq_one
    {n : ℕ} [NeZero n] (source target : CyclicWord n)
    (cut : ZMod n) (k : ℕ)
    (hk : transportFlowMagnitude source target cut k = 1)
    (hsucc : transportFlowMagnitude source target cut (k + 1) = 1) :
    source (cut + (k : ZMod n)) = target (cut + (k : ZMod n)) := by
  apply (transportIncrement_eq_zero_iff source target cut k).mp
  have heq := transportPrefixFlow_succ_eq_of_magnitudes_eq_one
    source target cut k hk hsucc
  rw [transportPrefixFlow_succ] at heq
  omega

/-- The three magnitudes `(1,2,1)` have a common sign: their signed values
are exactly `(s,2*s,s)` for `s=1` or `s=-1`. -/
theorem transportHeightTwo_signed_of_magnitudes
    {n : ℕ} [NeZero n] (source target : CyclicWord n)
    (cut : ZMod n) {k : ℕ} (hkpos : 0 < k)
    (hleft : transportFlowMagnitude source target cut (k - 1) = 1)
    (hcenter : transportFlowMagnitude source target cut k = 2)
    (hright : transportFlowMagnitude source target cut (k + 1) = 1) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      transportPrefixFlow source target cut (k - 1) = s ∧
      transportPrefixFlow source target cut k = 2 * s ∧
      transportPrefixFlow source target cut (k + 1) = s := by
  have hlstep := transportPrefixFlow_step_natAbs_le_one source target cut (k - 1)
  have hrstep := transportPrefixFlow_step_natAbs_le_one source target cut k
  rw [show k - 1 + 1 = k by omega] at hlstep
  rcases Int.natAbs_eq_iff.mp hcenter with hc | hc
  · refine ⟨1, Or.inl rfl, ?_, by simpa using hc, ?_⟩
    · rcases Int.natAbs_eq_iff.mp hleft with hl | hl
      · simpa using hl
      · norm_num [hc, hl] at hlstep
    · rcases Int.natAbs_eq_iff.mp hright with hr | hr
      · simpa using hr
      · norm_num [hc, hr] at hrstep
  · refine ⟨-1, Or.inr rfl, ?_, by simpa using hc, ?_⟩
    · rcases Int.natAbs_eq_iff.mp hleft with hl | hl
      · norm_num [hc, hl] at hlstep
      · simpa using hl
    · rcases Int.natAbs_eq_iff.mp hright with hr | hr
      · norm_num [hc, hr] at hrstep
      · simpa using hr

/-- The existing rigid cost-four height-two theorem supplies the signed
RL238 profile without adding any hypothesis to the equal-weight setting. -/
theorem transportHeightTwo_signed_of_cost_four
    {n : ℕ} [NeZero n] {source target : CyclicWord n}
    (hones : ones source = ones target) (cut : ZMod n)
    (hcost : transportCostAtCut source target cut = 4)
    {k : ℕ} (hkpos : 0 < k) (hklt : k < n)
    (hk : transportFlowMagnitude source target cut k = 2) :
    ∃ s : ℤ, (s = 1 ∨ s = -1) ∧
      transportPrefixFlow source target cut (k - 1) = s ∧
      transportPrefixFlow source target cut k = 2 * s ∧
      transportPrefixFlow source target cut (k + 1) = s := by
  obtain ⟨_, _, hleft, hright, _⟩ :=
    transportHeightTwo_rigid_of_cost_four hones cut hcost hkpos hklt hk
  exact transportHeightTwo_signed_of_magnitudes source target cut hkpos hleft hk hright

/-- The three rigid height-two edges exhaust the budget, so every other
internal flow is zero. This supplies the boundaries of the local word. -/
theorem transportHeightTwo_flow_eq_zero_outside
    {n : ℕ} [NeZero n] {source target : CyclicWord n}
    (hones : ones source = ones target) (cut : ZMod n)
    (hcost : transportCostAtCut source target cut = 4)
    {k : ℕ} (hkpos : 0 < k) (hklt : k < n)
    (hk : transportFlowMagnitude source target cut k = 2)
    {j : ℕ} (hjpos : 0 < j) (hjlt : j < n)
    (hjleft : j ≠ k - 1) (hjcenter : j ≠ k) (hjright : j ≠ k + 1) :
    transportPrefixFlow source target cut j = 0 := by
  obtain ⟨hkgt, hksucc, hleft, hright, _⟩ :=
    transportHeightTwo_rigid_of_cost_four hones cut hcost hkpos hklt hk
  let s : Finset ℕ := {k - 2, k - 1, k, j - 1}
  have hsub : s ⊆ Finset.range (n - 1) := by
    intro i hi
    simp only [s, Finset.mem_insert, Finset.mem_singleton] at hi
    simp only [Finset.mem_range]
    rcases hi with rfl | rfl | rfl | rfl <;> omega
  have hsum := transportMagnitudeSum_le_cost_of_subset source target cut s hsub
  have h01 : k - 2 ≠ k - 1 := by omega
  have h02 : k - 2 ≠ k := by omega
  have h03 : k - 2 ≠ j - 1 := by omega
  have h12 : k - 1 ≠ k := by omega
  have h13 : k - 1 ≠ j - 1 := by omega
  have h23 : k ≠ j - 1 := by omega
  have hk0 : k - 2 + 1 = k - 1 := by omega
  have hk1 : k - 1 + 1 = k := by omega
  have hj1 : j - 1 + 1 = j := by omega
  simp [s, h01, h02, h03, h12, h13, h23, hk0, hk1, hj1,
    hcost, hleft, hk, hright] at hsum
  have hz : transportFlowMagnitude source target cut j = 0 := by omega
  exact Int.natAbs_eq_zero.mp hz

/-- A rigid height-two excursion forces the actual local bits `0011 → 1100`
or its reverse. The Boolean witness is the repeated first source bit. -/
theorem transportHeightTwo_local_bits_of_cost_four
    {n : ℕ} [NeZero n] {source target : CyclicWord n}
    (hones : ones source = ones target) (cut : ZMod n)
    (hcost : transportCostAtCut source target cut = 4)
    {k : ℕ} (hkpos : 0 < k) (hklt : k < n)
    (hk : transportFlowMagnitude source target cut k = 2) :
    ∃ b : Bool,
      source (cut + ((k - 2 : ℕ) : ZMod n)) = b ∧
      source (cut + ((k - 1 : ℕ) : ZMod n)) = b ∧
      source (cut + (k : ZMod n)) = !b ∧
      source (cut + ((k + 1 : ℕ) : ZMod n)) = !b ∧
      target (cut + ((k - 2 : ℕ) : ZMod n)) = !b ∧
      target (cut + ((k - 1 : ℕ) : ZMod n)) = !b ∧
      target (cut + (k : ZMod n)) = b ∧
      target (cut + ((k + 1 : ℕ) : ZMod n)) = b := by
  obtain ⟨hkgt, hksucc, _, _, _⟩ :=
    transportHeightTwo_rigid_of_cost_four hones cut hcost hkpos hklt hk
  have hzero : ∀ j, j ≤ n → j ≠ k - 1 → j ≠ k → j ≠ k + 1 →
      transportPrefixFlow source target cut j = 0 := by
    intro j hj hl hc hr
    by_cases hj0 : j = 0
    · subst j
      exact transportPrefixFlow_zero source target cut
    by_cases hjn : j = n
    · subst j
      exact transportPrefixFlow_full_eq_zero_of_ones_eq hones cut
    exact transportHeightTwo_flow_eq_zero_outside hones cut hcost hkpos hklt hk
      (by omega) (by omega) hl hc hr
  have hbefore := hzero (k - 2) (by omega) (by omega) (by omega) (by omega)
  have hafter := hzero (k + 2) (by omega) (by omega) (by omega) (by omega)
  obtain ⟨s, hs, hleft, hcenter, hright⟩ :=
    transportHeightTwo_signed_of_cost_four hones cut hcost hkpos hklt hk
  have hstep0 := transportPrefixFlow_succ source target cut (k - 2)
  have hstep1 := transportPrefixFlow_succ source target cut (k - 1)
  have hstep2 := transportPrefixFlow_succ source target cut k
  have hstep3 := transportPrefixFlow_succ source target cut (k + 1)
  rw [show k - 2 + 1 = k - 1 by omega, hbefore, hleft] at hstep0
  rw [show k - 1 + 1 = k by omega, hleft, hcenter] at hstep1
  rw [hcenter, hright] at hstep2
  rw [show k + 1 + 1 = k + 2 by omega, hright, hafter] at hstep3
  have hinc0 : transportIncrement source target cut (k - 2) = s := by omega
  have hinc1 : transportIncrement source target cut (k - 1) = s := by omega
  have hinc2 : transportIncrement source target cut k = -s := by omega
  have hinc3 : transportIncrement source target cut (k + 1) = -s := by omega
  rcases hs with rfl | rfl
  · obtain ⟨h0s, h0t⟩ := (transportIncrement_eq_one_iff source target cut _).mp hinc0
    obtain ⟨h1s, h1t⟩ := (transportIncrement_eq_one_iff source target cut _).mp hinc1
    obtain ⟨h2s, h2t⟩ := (transportIncrement_eq_neg_one_iff source target cut _).mp hinc2
    obtain ⟨h3s, h3t⟩ := (transportIncrement_eq_neg_one_iff source target cut _).mp hinc3
    exact ⟨false, h0s, h1s, h2s, h3s, h0t, h1t, h2t, h3t⟩
  · obtain ⟨h0s, h0t⟩ := (transportIncrement_eq_neg_one_iff source target cut _).mp hinc0
    obtain ⟨h1s, h1t⟩ := (transportIncrement_eq_neg_one_iff source target cut _).mp hinc1
    obtain ⟨h2s, h2t⟩ := (transportIncrement_eq_one_iff source target cut _).mp (by simpa using hinc2)
    obtain ⟨h3s, h3t⟩ := (transportIncrement_eq_one_iff source target cut _).mp (by simpa using hinc3)
    exact ⟨true, h0s, h1s, h2s, h3s, h0t, h1t, h2t, h3t⟩

end Collatz
