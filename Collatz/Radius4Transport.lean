import Collatz.RotationWord

namespace Collatz

/-- Integer value of a binary bit for transport-flow bookkeeping. -/
def transportBitValue (b : Bool) : ℤ :=
  if b = true then 1 else 0

@[simp]
theorem transportBitValue_false : transportBitValue false = 0 := by
  simp [transportBitValue]

@[simp]
theorem transportBitValue_true : transportBitValue true = 1 := by
  simp [transportBitValue]

/-- Signed local change in prefix mass when transporting `source` to `target`,
read from the cyclic cut `cut` at chronological offset `j`.

The sign convention matches the RL238 prefix flow:
`target-prefix-ones - source-prefix-ones`. -/
def transportIncrement {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) (j : ℕ) : ℤ :=
  transportBitValue (target (cut + (j : ZMod n))) -
    transportBitValue (source (cut + (j : ZMod n)))

/-- A binary transport increment is always `-1`, `0`, or `1`.  This is the
local one-Lipschitz input used by the Radius-4 flow-topology classification. -/
theorem transportIncrement_eq_neg_one_or_zero_or_one {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) (j : ℕ) :
    transportIncrement source target cut j = -1 ∨
      transportIncrement source target cut j = 0 ∨
      transportIncrement source target cut j = 1 := by
  unfold transportIncrement
  cases hs : source (cut + (j : ZMod n)) <;>
    cases ht : target (cut + (j : ZMod n)) <;>
      simp [hs, ht, transportBitValue]

/-- Prefix transport flow after `k` positions from a chosen cyclic cut.

For equal-weight words this is the standard one-dimensional transport flow
`G_k = (# target ones in the first k positions) -
       (# source ones in the first k positions)`.
The endpoint `k = n` is handled separately; this definition deliberately does
not bake equal weight into the data. -/
def transportPrefixFlow {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) (k : ℕ) : ℤ :=
  ∑ j in Finset.range k, transportIncrement source target cut j

@[simp]
theorem transportPrefixFlow_zero {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) :
    transportPrefixFlow source target cut 0 = 0 := by
  simp [transportPrefixFlow]

/-- Extending a prefix by one position adds exactly the local signed bit
increment at that position. -/
theorem transportPrefixFlow_succ {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) (k : ℕ) :
    transportPrefixFlow source target cut (k + 1) =
      transportPrefixFlow source target cut k +
        transportIncrement source target cut k := by
  simp [transportPrefixFlow, Finset.sum_range_succ]

/-- Consecutive prefix-flow values differ by at most one in absolute value. -/
theorem transportPrefixFlow_step_natAbs_le_one {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) (k : ℕ) :
    Int.natAbs
        (transportPrefixFlow source target cut (k + 1) -
          transportPrefixFlow source target cut k) ≤ 1 := by
  rw [transportPrefixFlow_succ]
  simp only [add_sub_cancel_left]
  rcases transportIncrement_eq_neg_one_or_zero_or_one source target cut k with
    h | h | h <;> rw [h] <;> norm_num

/-- Linear adjacent-transposition transport cost after cutting the cyclic word
at `cut`.  The internal flow edges are `G_1, ..., G_{n-1}`; `G_0` and `G_n`
are boundary edges and are not charged.

For equal-weight words, minimizing this quantity over cyclic cuts is the
prefix-flow description of cyclic adjacent-transposition distance used by
RL238. -/
def transportCostAtCut {n : ℕ} [NeZero n]
    (source target : CyclicWord n) (cut : ZMod n) : ℕ :=
  ∑ j in Finset.range (n - 1),
    Int.natAbs (transportPrefixFlow source target cut (j + 1))

/-- Exact cyclic transport radius stated directly in the prefix-flow language.

The words must have equal binary weight.  Exact radius `radius` means every
cyclic cut has linear prefix-flow cost at least `radius`, and at least one cut
attains that cost.  Thus this is a minimum-over-cuts transport notion, not the
Hamming-distance notion in `Collatz.Radius4`.

The equivalence between this prefix-flow minimum and adjacent cyclic
transpositions is the inherited one-dimensional transport identity that the
next formal layer will prove explicitly where needed; it is not assumed as an
axiom here. -/
def IsExactTransportRadius {n : ℕ} [NeZero n] (radius : ℕ)
    (source target : CyclicWord n) : Prop :=
  ones source = ones target ∧
    (∀ cut : ZMod n, radius ≤ transportCostAtCut source target cut) ∧
    ∃ cut : ZMod n, transportCostAtCut source target cut = radius

/-- The faithful transport-distance Radius-4 predicate for a specified cyclic
self-rotation.  This is intentionally distinct from the existing Hamming
predicate `IsRadiusFour`. -/
def IsTransportRadiusFour {n : ℕ} [NeZero n]
    (w : CyclicWord n) (shift : ZMod n) : Prop :=
  IsExactTransportRadius 4 w (rotate w shift)

@[simp]
theorem isTransportRadiusFour_iff {n : ℕ} [NeZero n]
    (w : CyclicWord n) (shift : ZMod n) :
    IsTransportRadiusFour w shift ↔
      ones w = ones (rotate w shift) ∧
        (∀ cut : ZMod n, 4 ≤ transportCostAtCut w (rotate w shift) cut) ∧
        ∃ cut : ZMod n,
          transportCostAtCut w (rotate w shift) cut = 4 := by
  rfl

/-- An exact transport-Radius-4 rotation has a cut attaining transport cost
four. -/
theorem transportRadiusFour_exists_minimizing_cut {n : ℕ} [NeZero n]
    {w : CyclicWord n} {shift : ZMod n}
    (h : IsTransportRadiusFour w shift) :
    ∃ cut : ZMod n,
      transportCostAtCut w (rotate w shift) cut = 4 := by
  exact h.2.2

/-- Every cut has cost at least four under exact cyclic transport Radius 4. -/
theorem transportRadiusFour_cost_ge_four {n : ℕ} [NeZero n]
    {w : CyclicWord n} {shift : ZMod n}
    (h : IsTransportRadiusFour w shift) (cut : ZMod n) :
    4 ≤ transportCostAtCut w (rotate w shift) cut := by
  exact h.2.1 cut

namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- RL238's transport-distance Radius-4 condition applied to the genuine
Collatz parity word.  This is a separate predicate from the older
Hamming-distance `IsCycleRadiusFour`. -/
def IsCycleTransportRadiusFour (c : OddCycle L)
    (shift : ZMod c.encodingPeriod) : Prop :=
  IsTransportRadiusFour c.parityWord shift

@[simp]
theorem isCycleTransportRadiusFour_iff (c : OddCycle L)
    (shift : ZMod c.encodingPeriod) :
    c.IsCycleTransportRadiusFour shift ↔
      IsTransportRadiusFour c.parityWord shift := by
  rfl

end OddCycle
end Collatz
