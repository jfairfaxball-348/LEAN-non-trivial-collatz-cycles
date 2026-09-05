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

end Collatz
