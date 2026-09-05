import Collatz.Radius4BoundaryPositions
import Collatz.RotationWord

namespace Collatz
namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- The four abstract Radius-4 boundary positions can be read directly on the
actual Collatz-derived `halfStep` orbit. At the two down-boundaries the base
origin is odd and the advanced origin is non-odd; at the two up-boundaries the
base origin is non-odd and the advanced origin is odd. This uses the proved
rotation/advance identity rather than silently identifying a rotation with an
advanced orbit. -/
theorem radiusFour_actual_orbit_boundaries (c : OddCycle L)
    (shift : ZMod c.encodingPeriod)
    (hfour : IsRadiusFour c.parityWord shift) :
    ∃ d₁ d₂ u₁ u₂ : ZMod c.encodingPeriod,
      d₁ ≠ d₂ ∧ u₁ ≠ u₂ ∧
      d₁ ≠ u₁ ∧ d₁ ≠ u₂ ∧ d₂ ≠ u₁ ∧ d₂ ≠ u₂ ∧
      Odd ((halfStep^[d₁.val]) (c.node 0)) ∧
      ¬ Odd ((halfStep^[d₁.val]) ((halfStep^[shift.val]) (c.node 0))) ∧
      Odd ((halfStep^[d₂.val]) (c.node 0)) ∧
      ¬ Odd ((halfStep^[d₂.val]) ((halfStep^[shift.val]) (c.node 0))) ∧
      ¬ Odd ((halfStep^[u₁.val]) (c.node 0)) ∧
      Odd ((halfStep^[u₁.val]) ((halfStep^[shift.val]) (c.node 0))) ∧
      ¬ Odd ((halfStep^[u₂.val]) (c.node 0)) ∧
      Odd ((halfStep^[u₂.val]) ((halfStep^[shift.val]) (c.node 0))):= by
  rcases radiusFour_four_boundary_positions c.parityWord shift hfour with
    ⟨d₁, d₂, u₁, u₂, hdne, hune, hdu₁, hdu₂, hd₂u₁, hd₂u₂, hdown, hup⟩
  have hrot := c.rotate_parityWord_eq_advancedParityWord shift
  have hd₁ := (hdown d₁).2 (Or.inl rfl)
  have hd₂ := (hdown d₂).2 (Or.inr rfl)
  have hu₁ := (hup u₁).2 (Or.inl rfl)
  have hu₂ := (hup u₂).2 (Or.inr rfl)
  have hd₁base : Odd ((halfStep^[d₁.val]) (c.node 0)) :=
    (c.parityWord_eq_true_iff d₁).1 hd₁.1
  have hd₂base : Odd ((halfStep^[d₂.val]) (c.node 0)) :=
    (c.parityWord_eq_true_iff d₂).1 hd₂.1
  have hu₁base : ¬ Odd ((halfStep^[u₁.val]) (c.node 0)) := by
    intro hodd
    have htrue := (c.parityWord_eq_true_iff u₁).2 hodd
    simp [hu₁.1] at htrue
  have hu₂base : ¬ Odd ((halfStep^[u₂.val]) (c.node 0)) := by
    intro hodd
    have htrue := (c.parityWord_eq_true_iff u₂).2 hodd
    simp [hu₂.1] at htrue
  have hd₁advanced :
      ¬ Odd ((halfStep^[d₁.val]) ((halfStep^[shift.val]) (c.node 0))) := by
    have hfalse : c.advancedParityWord shift d₁ = false := by
      rw [← congrFun hrot d₁]
      exact hd₁.2
    simpa [advancedParityWord] using hfalse
  have hd₂advanced :
      ¬ Odd ((halfStep^[d₂.val]) ((halfStep^[shift.val]) (c.node 0))) := by
    have hfalse : c.advancedParityWord shift d₂ = false := by
      rw [← congrFun hrot d₂]
      exact hd₂.2
    simpa [advancedParityWord] using hfalse
  have hu₁advanced :
      Odd ((halfStep^[u₁.val]) ((halfStep^[shift.val]) (c.node 0))) := by
    have htrue : c.advancedParityWord shift u₁ = true := by
      rw [← congrFun hrot u₁]
      exact hu₁.2
    simpa [advancedParityWord] using htrue
  have hu₂advanced :
      Odd ((halfStep^[u₂.val]) ((halfStep^[shift.val]) (c.node 0))) := by
    have htrue : c.advancedParityWord shift u₂ = true := by
      rw [← congrFun hrot u₂]
      exact hu₂.2
    simpa [advancedParityWord] using htrue
  exact ⟨d₁, d₂, u₁, u₂, hdne, hune, hdu₁, hdu₂, hd₂u₁, hd₂u₂,
    hd₁base, hd₁advanced, hd₂base, hd₂advanced,
    hu₁base, hu₁advanced, hu₂base, hu₂advanced⟩

end OddCycle
end Collatz
