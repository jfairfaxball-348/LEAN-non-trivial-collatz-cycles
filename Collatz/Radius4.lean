import Collatz.Basic

namespace Collatz

/-- A specified cyclic rotation is at exact Radius 4 when the word and its
rotation differ at exactly four positions.

This is a purely combinatorial definition. By itself it says nothing about
whether `w` represents a Collatz trajectory or cycle. -/
def IsRadiusFour {n : ℕ} [NeZero n] (w : CyclicWord n) (shift : ZMod n) : Prop :=
  IsExactRadius 4 w shift

/-- A cyclic word has an exact Radius-4 rotation when some nonzero shift has
Hamming distance exactly four. -/
def HasRadiusFourRotation {n : ℕ} [NeZero n] (w : CyclicWord n) : Prop :=
  HasExactRadiusRotation 4 w

@[simp]
theorem isRadiusFour_iff {n : ℕ} [NeZero n] (w : CyclicWord n) (shift : ZMod n) :
    IsRadiusFour w shift ↔ hammingDistance w (rotate w shift) = 4 := by
  rfl

/-- Expands the existential Radius-4 definition into its shift, nonzero, and
distance components. -/
theorem hasRadiusFourRotation_iff {n : ℕ} [NeZero n] (w : CyclicWord n) :
    HasRadiusFourRotation w ↔
      ∃ shift : ZMod n, shift ≠ 0 ∧ hammingDistance w (rotate w shift) = 4 := by
  rfl

/-- An exact Radius-4 rotation cannot be equal to the original word.

This conclusion follows from distance four alone; primitivity and a separate
nonzero-shift hypothesis are not required for this elementary fact. -/
theorem radiusFour_rotation_ne {n : ℕ} [NeZero n]
    (w : CyclicWord n) {shift : ZMod n} (hRadius : IsRadiusFour w shift) :
    rotate w shift ≠ w := by
  intro hEq
  have hzero : hammingDistance w (rotate w shift) = 0 := by
    rw [hEq]
    exact hammingDistance_self w
  have hfour : hammingDistance w (rotate w shift) = 4 :=
    (isRadiusFour_iff w shift).mp hRadius
  omega

/-!
## Intended Collatz theorem boundary

The definitions above are the combinatorial Radius-4 layer only.

A future local Collatz theorem in this repository must first define and prove
all eligibility conditions connecting a cyclic word to a genuine hypothetical
positive Collatz cycle, including the exact full-denominator arithmetic
condition. Only then can a Radius-4 impossibility theorem be stated as a
Collatz result.

That local impossibility theorem would still be distinct from any global theorem
asserting that every hypothetical non-trivial cycle must encounter Radius 4.
-/

end Collatz
