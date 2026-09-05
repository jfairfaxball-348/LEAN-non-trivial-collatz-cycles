import Collatz.RotationWord
import Collatz.RotationNumeratorComparison

namespace Collatz
namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- An exact Radius-4 rotation cannot arise from advancing to the same
`halfStep` state. If the advanced state equalled the base state, its entire
parity word would be unchanged; the proved rotation/advance theorem would then
make the Radius-4 rotation equal to the original word, contradicting distance
four. No global primitivity assumption is needed for this conclusion. -/
theorem shiftedState_ne_base_of_radiusFour (c : OddCycle L)
    (shift : ZMod c.encodingPeriod)
    (hfour : IsRadiusFour c.parityWord shift) :
    (halfStep^[shift.val]) (c.node 0) ≠ c.node 0 := by
  intro hstate
  have hadvanced : c.advancedParityWord shift = c.parityWord := by
    funext t
    unfold advancedParityWord parityWord
    rw [hstate]
  have hrotation : rotate c.parityWord shift = c.parityWord := by
    rw [c.rotate_parityWord_eq_advancedParityWord, hadvanced]
  exact (radiusFour_rotation_ne c.parityWord hfour) hrotation

/-- Consequently, at a Radius-4 shift the exact full-denominator numerator
comparison is genuinely nonzero. This is not an assumed eligibility condition:
it follows from the actual advanced state, positivity of the complete cycle
denominator, and the proved shifted numerator identity. -/
theorem shifted_wordNumerator_difference_ne_zero_of_radiusFour
    (c : OddCycle L) (shift : ZMod c.encodingPeriod)
    (hfour : IsRadiusFour c.parityWord shift) :
    (wordNumerator
        (orbitBits ((halfStep^[shift.val]) (c.node 0)) c.totalExponent) : ℤ) -
      (wordNumerator (orbitBits (c.node 0) c.totalExponent) : ℤ) ≠ 0 := by
  have hshift : shift.val ≤ c.totalExponent := c.zmodShift_val_le_totalExponent shift
  have hstateNat :
      (halfStep^[shift.val]) (c.node 0) ≠ c.node 0 :=
    c.shiftedState_ne_base_of_radiusFour shift hfour
  have hstateZ :
      ((((halfStep^[shift.val]) (c.node 0) : ℕ) : ℤ) - (c.node 0 : ℤ)) ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hstateNat
  rw [← c.cycleDenominator_mul_shiftedState_sub_base_eq_wordNumerator_difference hshift]
  exact mul_ne_zero (ne_of_gt c.cycleDenominator_pos) hstateZ

end OddCycle
end Collatz
