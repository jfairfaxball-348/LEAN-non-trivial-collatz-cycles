import Collatz.Radius4Transport

namespace Collatz

/-- Moving the cyclic cut into both words leaves each local transport increment
unchanged, once the new cut is placed at zero.  This is the cut-normalisation
covariance needed for the transport-radius-four local proof. -/
theorem transportIncrement_rotate_cut {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) (j : ℕ) :
    transportIncrement source target cut j =
      transportIncrement (rotate source cut) (rotate target cut) 0 j := by
  simp [transportIncrement, rotate, add_comm]

/-- The complete prefix-flow profile is unchanged when a chosen cyclic cut is
absorbed into simultaneous rotation of source and target. -/
theorem transportPrefixFlow_rotate_cut {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) (k : ℕ) :
    transportPrefixFlow source target cut k =
      transportPrefixFlow (rotate source cut) (rotate target cut) 0 k := by
  unfold transportPrefixFlow
  apply Finset.sum_congr rfl
  intro j hj
  exact transportIncrement_rotate_cut source target cut j

/-- Consequently a cut cost may always be normalized to cut zero after
simultaneously rotating the two cyclic words. -/
theorem transportCostAtCut_rotate_cut {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) :
    transportCostAtCut source target cut =
      transportCostAtCut (rotate source cut) (rotate target cut) 0 := by
  unfold transportCostAtCut
  apply Finset.sum_congr rfl
  intro j hj
  rw [transportPrefixFlow_rotate_cut source target cut (j + 1)]

/-- Cyclic rotations commute.  This small identity is the self-rotation half
of cut normalization. -/
theorem rotate_rotate_comm {n : ℕ} (w : CyclicWord n)
    (a b : ZMod n) :
    rotate (rotate w a) b = rotate (rotate w b) a := by
  funext i
  simp [rotate, add_comm, add_left_comm]

/-- For a self-rotation, normalizing a cut preserves the same relative shift:
cutting at `cut` is the same cost as comparing the cut-rotated word with its
`shift` rotation at cut zero. -/
theorem transportCostAtCut_selfRotation_rotate_cut {n : ℕ} [NeZero n]
    (w : CyclicWord n) (shift cut : ZMod n) :
    transportCostAtCut w (rotate w shift) cut =
      transportCostAtCut (rotate w cut) (rotate (rotate w cut) shift) 0 := by
  calc
    transportCostAtCut w (rotate w shift) cut =
        transportCostAtCut (rotate w cut) (rotate (rotate w shift) cut) 0 :=
      transportCostAtCut_rotate_cut w (rotate w shift) cut
    _ = transportCostAtCut (rotate w cut) (rotate (rotate w cut) shift) 0 := by
      rw [rotate_rotate_comm w shift cut]

/-- Changing the cyclic origin translates the cut variable for a fixed
self-rotation. -/
theorem transportCostAtCut_rotate_selfRotation {n : ℕ} [NeZero n]
    (w : CyclicWord n) (shift origin cut : ZMod n) :
    transportCostAtCut (rotate w origin) (rotate (rotate w origin) shift) cut =
      transportCostAtCut w (rotate w shift) (origin + cut) := by
  calc
    transportCostAtCut (rotate w origin) (rotate (rotate w origin) shift) cut =
        transportCostAtCut (rotate (rotate w origin) cut)
          (rotate (rotate (rotate w origin) cut) shift) 0 :=
      transportCostAtCut_selfRotation_rotate_cut (rotate w origin) shift cut
    _ = transportCostAtCut (rotate w (origin + cut))
          (rotate (rotate w (origin + cut)) shift) 0 := by
      have hrotate : rotate (rotate w origin) cut = rotate w (origin + cut) := by
        funext i
        simp only [rotate]
        congr 1
        abel
      rw [hrotate]
    _ = transportCostAtCut w (rotate w shift) (origin + cut) :=
      (transportCostAtCut_selfRotation_rotate_cut w shift (origin + cut)).symm

/-- Exact transport radius for a self-rotation is invariant under changing the
cyclic origin. -/
theorem isTransportRadiusFour_rotate {n : ℕ} [NeZero n]
    (w : CyclicWord n) (shift origin : ZMod n)
    (h : IsTransportRadiusFour w shift) :
    IsTransportRadiusFour (rotate w origin) shift := by
  refine ⟨(ones_rotate (rotate w origin) shift).symm, ?_, ?_⟩
  · intro cut
    rw [transportCostAtCut_rotate_selfRotation]
    exact h.2.1 (origin + cut)
  · rcases h.2.2 with ⟨cut, hcut⟩
    refine ⟨cut - origin, ?_⟩
    rw [transportCostAtCut_rotate_selfRotation]
    have hsum : origin + (cut - origin) = cut := by abel
    simpa only [hsum] using hcut

/-- An exact transport-Radius-4 self-rotation therefore has a rotated origin
at which the same relative self-rotation has zero-cut transport cost exactly
four.  This is the precise combinatorial bridge from the minimum-over-cuts
model to the cut-normalized topology eliminations. -/
theorem transportRadiusFour_exists_rotated_zero_cut {n : ℕ} [NeZero n]
    {w : CyclicWord n} {shift : ZMod n}
    (h : IsTransportRadiusFour w shift) :
    ∃ cut : ZMod n,
      transportCostAtCut (rotate w cut) (rotate (rotate w cut) shift) 0 = 4 := by
  rcases transportRadiusFour_exists_minimizing_cut h with ⟨cut, hcut⟩
  refine ⟨cut, ?_⟩
  rw [← transportCostAtCut_selfRotation_rotate_cut w shift cut]
  exact hcut

namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- The cut-normalized Radius-4 witness for a genuine Collatz parity word can
be stated at the corresponding advanced parity origin.  The existing theorem
`rotate_parityWord_eq_advancedParityWord` supplies the semantic identification;
the identification follows entirely from the proved parity-word identity. -/
theorem cycleTransportRadiusFour_exists_advanced_zero_cut (c : OddCycle L)
    {shift : ZMod c.encodingPeriod}
    (h : c.IsCycleTransportRadiusFour shift) :
    ∃ cut : ZMod c.encodingPeriod,
      transportCostAtCut (c.advancedParityWord cut)
        (rotate (c.advancedParityWord cut) shift) 0 = 4 := by
  rcases transportRadiusFour_exists_rotated_zero_cut h with ⟨cut, hcut⟩
  refine ⟨cut, ?_⟩
  rw [← c.rotate_parityWord_eq_advancedParityWord cut]
  exact hcut

end OddCycle
end Collatz
