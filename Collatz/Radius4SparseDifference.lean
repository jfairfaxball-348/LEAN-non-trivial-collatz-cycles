import Collatz.Radius4CycleBoundaries

namespace Collatz

/-- The inhomogeneous forcing term that appears when two one-step affine
Collatz recurrences are subtracted while the second recurrence is written in
terms of the state difference.  If the two parity bits agree this is zero; if
they disagree it is an explicit signed odd integer. -/
def affineDifferenceOffset (x : ℕ) (a b : Bool) : ℤ :=
  (bitMultiplier b : ℤ) * (x : ℤ) + (bitOffset b : ℤ) -
    ((bitMultiplier a : ℤ) * (x : ℤ) + (bitOffset a : ℤ))

@[simp]
theorem affineDifferenceOffset_same (x : ℕ) (b : Bool) :
    affineDifferenceOffset x b b = 0 := by
  simp [affineDifferenceOffset]

@[simp]
theorem affineDifferenceOffset_down (x : ℕ) :
    affineDifferenceOffset x true false = -(2 * (x : ℤ) + 1) := by
  simp [affineDifferenceOffset, bitMultiplier, bitOffset]
  ring

@[simp]
theorem affineDifferenceOffset_up (x : ℕ) :
    affineDifferenceOffset x false true = 2 * (x : ℤ) + 1 := by
  simp [affineDifferenceOffset, bitMultiplier, bitOffset]
  ring

/-- The local forcing term is nonzero exactly when the two parity bits differ. -/
theorem affineDifferenceOffset_ne_zero_iff (x : ℕ) (a b : Bool) :
    affineDifferenceOffset x a b ≠ 0 ↔ a ≠ b := by
  cases a <;> cases b <;>
    simp [affineDifferenceOffset, bitMultiplier, bitOffset] <;> omega

/-- Exact one-step difference recurrence for two actual `halfStep` states. -/
theorem halfStep_difference_step (x y : ℕ) :
    (2 : ℤ) * ((halfStep y : ℤ) - (halfStep x : ℤ)) =
      (bitMultiplier (stateBit y) : ℤ) * ((y : ℤ) - (x : ℤ)) +
        affineDifferenceOffset x (stateBit x) (stateBit y) := by
  have hx :
      (2 : ℤ) * (halfStep x : ℤ) =
        (bitMultiplier (stateBit x) : ℤ) * (x : ℤ) +
          (bitOffset (stateBit x) : ℤ) := by
    exact_mod_cast halfStep_affine x
  have hy :
      (2 : ℤ) * (halfStep y : ℤ) =
        (bitMultiplier (stateBit y) : ℤ) * (y : ℤ) +
          (bitOffset (stateBit y) : ℤ) := by
    exact_mod_cast halfStep_affine y
  rw [affineDifferenceOffset]
  linarith

namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- Base-orbit state at a cyclic encoding position. -/
def baseStateAt (c : OddCycle L) (t : ZMod c.encodingPeriod) : ℕ :=
  (halfStep^[t.val]) (c.node 0)

/-- State at the same cyclic position after first advancing the chosen origin
by `shift`. -/
def shiftedStateAt (c : OddCycle L) (shift t : ZMod c.encodingPeriod) : ℕ :=
  (halfStep^[t.val]) ((halfStep^[shift.val]) (c.node 0))

/-- The actual parity bit of the shifted state is literally the rotated genuine
parity word. -/
theorem shiftedStateBit_eq_rotatedParity (c : OddCycle L)
    (shift t : ZMod c.encodingPeriod) :
    stateBit (c.shiftedStateAt shift t) = rotate c.parityWord shift t := by
  rw [shiftedStateAt, ← c.halfStep_zmod_add_state t shift]
  simpa [rotate] using (c.parityWord_eq_stateBit (t + shift)).symm

/-- Local forcing term for the difference between the base orbit and the orbit
read from a shifted origin. -/
def radiusDifferenceOffset (c : OddCycle L)
    (shift t : ZMod c.encodingPeriod) : ℤ :=
  affineDifferenceOffset (c.baseStateAt t)
    (stateBit (c.baseStateAt t)) (stateBit (c.shiftedStateAt shift t))

/-- The shifted-orbit difference forcing is nonzero exactly at Hamming
mismatches of the genuine parity word and its rotation. -/
theorem radiusDifferenceOffset_ne_zero_iff (c : OddCycle L)
    (shift t : ZMod c.encodingPeriod) :
    c.radiusDifferenceOffset shift t ≠ 0 ↔
      c.parityWord t ≠ rotate c.parityWord shift t := by
  rw [radiusDifferenceOffset, affineDifferenceOffset_ne_zero_iff]
  rw [← c.parityWord_eq_stateBit t, c.shiftedStateBit_eq_rotatedParity shift t]

/-- Exact Radius 4 makes the local difference recurrence genuinely sparse:
there are exactly four positions with nonzero forcing.  At the two
`true → false` boundaries the forcing is `-(2*x+1)`; at the two
`false → true` boundaries it is `+(2*x+1)`, where `x` is the actual base-orbit
state at that boundary. -/
theorem radiusFour_sparse_difference_offsets (c : OddCycle L)
    (shift : ZMod c.encodingPeriod) (hfour : IsRadiusFour c.parityWord shift) :
    ∃ d₁ d₂ u₁ u₂ : ZMod c.encodingPeriod,
      d₁ ≠ d₂ ∧ u₁ ≠ u₂ ∧
      d₁ ≠ u₁ ∧ d₁ ≠ u₂ ∧ d₂ ≠ u₁ ∧ d₂ ≠ u₂ ∧
      (∀ i : ZMod c.encodingPeriod,
        c.radiusDifferenceOffset shift i ≠ 0 ↔
          i = d₁ ∨ i = d₂ ∨ i = u₁ ∨ i = u₂) ∧
      c.radiusDifferenceOffset shift d₁ = -(2 * (c.baseStateAt d₁ : ℤ) + 1) ∧
      c.radiusDifferenceOffset shift d₂ = -(2 * (c.baseStateAt d₂ : ℤ) + 1) ∧
      c.radiusDifferenceOffset shift u₁ = 2 * (c.baseStateAt u₁ : ℤ) + 1 ∧
      c.radiusDifferenceOffset shift u₂ = 2 * (c.baseStateAt u₂ : ℤ) + 1 := by
  rcases radiusFour_four_boundary_positions c.parityWord shift hfour with
    ⟨d₁, d₂, u₁, u₂, hdne, hune, hd₁u₁, hd₁u₂, hd₂u₁, hd₂u₂,
      hdown, hup⟩
  have hsupport : ∀ i : ZMod c.encodingPeriod,
      c.radiusDifferenceOffset shift i ≠ 0 ↔
        i = d₁ ∨ i = d₂ ∨ i = u₁ ∨ i = u₂ := by
    intro i
    rw [c.radiusDifferenceOffset_ne_zero_iff]
    constructor
    · intro hne
      cases hw : c.parityWord i <;>
        cases hr : rotate c.parityWord shift i <;>
        simp [hw, hr] at hne
      · rcases (hup i).1 ⟨hw, hr⟩ with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      · rcases (hdown i).1 ⟨hw, hr⟩ with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    · intro hi
      rcases hi with h | h | h | h
      · subst i
        have hd := (hdown d₁).2 (Or.inl rfl)
        simp [hd.1, hd.2]
      · subst i
        have hd := (hdown d₂).2 (Or.inr rfl)
        simp [hd.1, hd.2]
      · subst i
        have hu := (hup u₁).2 (Or.inl rfl)
        simp [hu.1, hu.2]
      · subst i
        have hu := (hup u₂).2 (Or.inr rfl)
        simp [hu.1, hu.2]
  have hd₁ := (hdown d₁).2 (Or.inl rfl)
  have hd₂ := (hdown d₂).2 (Or.inr rfl)
  have hu₁ := (hup u₁).2 (Or.inl rfl)
  have hu₂ := (hup u₂).2 (Or.inr rfl)
  refine ⟨d₁, d₂, u₁, u₂, hdne, hune, hd₁u₁, hd₁u₂, hd₂u₁, hd₂u₂,
    hsupport, ?_, ?_, ?_, ?_⟩
  · rw [radiusDifferenceOffset, ← c.parityWord_eq_stateBit d₁,
      c.shiftedStateBit_eq_rotatedParity shift d₁, hd₁.1, hd₁.2]
    exact affineDifferenceOffset_down (c.baseStateAt d₁)
  · rw [radiusDifferenceOffset, ← c.parityWord_eq_stateBit d₂,
      c.shiftedStateBit_eq_rotatedParity shift d₂, hd₂.1, hd₂.2]
    exact affineDifferenceOffset_down (c.baseStateAt d₂)
  · rw [radiusDifferenceOffset, ← c.parityWord_eq_stateBit u₁,
      c.shiftedStateBit_eq_rotatedParity shift u₁, hu₁.1, hu₁.2]
    exact affineDifferenceOffset_up (c.baseStateAt u₁)
  · rw [radiusDifferenceOffset, ← c.parityWord_eq_stateBit u₂,
      c.shiftedStateBit_eq_rotatedParity shift u₂, hu₂.1, hu₂.2]
    exact affineDifferenceOffset_up (c.baseStateAt u₂)

end OddCycle
end Collatz
