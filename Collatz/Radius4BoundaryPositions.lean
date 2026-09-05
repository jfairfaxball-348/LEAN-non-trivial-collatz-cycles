import Collatz.Radius4Structure

namespace Collatz

/-- Exact Radius 4 exposes the two distinct positions at which a true bit of a
word becomes false under the chosen rotation. The iff clause is exhaustive:
there are no other true-to-false mismatches. -/
theorem radiusFour_down_positions {n : ℕ} [NeZero n]
    (w : CyclicWord n) (shift : ZMod n) (hfour : IsRadiusFour w shift) :
    ∃ d₁ d₂ : ZMod n, d₁ ≠ d₂ ∧
      ∀ i : ZMod n,
        (w i = true ∧ rotate w shift i = false) ↔ i = d₁ ∨ i = d₂ := by
  classical
  let s := Finset.univ.filter
    (fun i : ZMod n => w i = true ∧ rotate w shift i = false)
  have hcard : s.card = 2 := by
    simpa [s, downMismatches] using
      (radiusFour_directional_counts w shift hfour).1
  rcases Finset.card_eq_two.mp hcard with ⟨d₁, d₂, hne, hs⟩
  refine ⟨d₁, d₂, hne, ?_⟩
  intro i
  have hi : i ∈ s ↔ w i = true ∧ rotate w shift i = false := by
    simp [s]
  rw [← hi, hs]
  simp

/-- Exact Radius 4 likewise exposes the two distinct positions at which a false
bit becomes true under the chosen rotation, again with an exhaustive iff
characterization. -/
theorem radiusFour_up_positions {n : ℕ} [NeZero n]
    (w : CyclicWord n) (shift : ZMod n) (hfour : IsRadiusFour w shift) :
    ∃ u₁ u₂ : ZMod n, u₁ ≠ u₂ ∧
      ∀ i : ZMod n,
        (w i = false ∧ rotate w shift i = true) ↔ i = u₁ ∨ i = u₂ := by
  classical
  let s := Finset.univ.filter
    (fun i : ZMod n => w i = false ∧ rotate w shift i = true)
  have hcard : s.card = 2 := by
    simpa [s, upMismatches] using
      (radiusFour_directional_counts w shift hfour).2
  rcases Finset.card_eq_two.mp hcard with ⟨u₁, u₂, hne, hs⟩
  refine ⟨u₁, u₂, hne, ?_⟩
  intro i
  have hi : i ∈ s ↔ w i = false ∧ rotate w shift i = true := by
    simp [s]
  rw [← hi, hs]
  simp

/-- Combined four-boundary form of exact Radius 4: two distinct disappearing
true positions and two distinct appearing true positions, each pair exhaustive
for its mismatch orientation. The two pairs are automatically disjoint because
a Boolean bit cannot be simultaneously true and false at one position. -/
theorem radiusFour_four_boundary_positions {n : ℕ} [NeZero n]
    (w : CyclicWord n) (shift : ZMod n) (hfour : IsRadiusFour w shift) :
    ∃ d₁ d₂ u₁ u₂ : ZMod n,
      d₁ ≠ d₂ ∧ u₁ ≠ u₂ ∧
      d₁ ≠ u₁ ∧ d₁ ≠ u₂ ∧ d₂ ≠ u₁ ∧ d₂ ≠ u₂ ∧
      (∀ i : ZMod n,
        (w i = true ∧ rotate w shift i = false) ↔ i = d₁ ∨ i = d₂) ∧
      (∀ i : ZMod n,
        (w i = false ∧ rotate w shift i = true) ↔ i = u₁ ∨ i = u₂) := by
  rcases radiusFour_down_positions w shift hfour with
    ⟨d₁, d₂, hdne, hdown⟩
  rcases radiusFour_up_positions w shift hfour with
    ⟨u₁, u₂, hune, hup⟩
  have hdu₁ : d₁ ≠ u₁ := by
    intro h
    have hd := (hdown d₁).2 (Or.inl rfl)
    have hu := (hup u₁).2 (Or.inl rfl)
    rw [← h] at hu
    simp [hd.1] at hu
  have hdu₂ : d₁ ≠ u₂ := by
    intro h
    have hd := (hdown d₁).2 (Or.inl rfl)
    have hu := (hup u₂).2 (Or.inr rfl)
    rw [← h] at hu
    simp [hd.1] at hu
  have hd₂u₁ : d₂ ≠ u₁ := by
    intro h
    have hd := (hdown d₂).2 (Or.inr rfl)
    have hu := (hup u₁).2 (Or.inl rfl)
    rw [← h] at hu
    simp [hd.1] at hu
  have hd₂u₂ : d₂ ≠ u₂ := by
    intro h
    have hd := (hdown d₂).2 (Or.inr rfl)
    have hu := (hup u₂).2 (Or.inr rfl)
    rw [← h] at hu
    simp [hd.1] at hu
  exact ⟨d₁, d₂, u₁, u₂, hdne, hune, hdu₁, hdu₂, hd₂u₁, hd₂u₂,
    hdown, hup⟩

end Collatz
