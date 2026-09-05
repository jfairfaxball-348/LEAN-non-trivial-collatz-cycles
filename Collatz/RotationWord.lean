import Collatz.RotationArithmetic

namespace Collatz
namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- The cyclic parity word seen after advancing the same periodic `halfStep`
orbit by `shift`. -/
def advancedParityWord (c : OddCycle L)
    (shift : ZMod c.encodingPeriod) : CyclicWord c.encodingPeriod :=
  fun t => decide
    (Odd ((halfStep^[t.val]) ((halfStep^[shift.val]) (c.node 0))))

/-- Adding two `ZMod` orbit positions corresponds to adding their canonical
representatives and reducing modulo the encoding period. -/
theorem encoding_val_add (c : OddCycle L)
    (t shift : ZMod c.encodingPeriod) :
    (t + shift).val = (t.val + shift.val) % c.encodingPeriod := by
  simpa using ZMod.val_add t shift

/-- The actual state indexed by `t+shift` in the base periodic orbit is the
same state obtained by advancing by `shift` first and then by `t`. -/
theorem halfStep_zmod_add_state (c : OddCycle L)
    (t shift : ZMod c.encodingPeriod) :
    (halfStep^[(t + shift).val]) (c.node 0) =
      (halfStep^[t.val]) ((halfStep^[shift.val]) (c.node 0)) := by
  calc
    (halfStep^[(t + shift).val]) (c.node 0) =
        (halfStep^[(t.val + shift.val) % c.encodingPeriod]) (c.node 0) := by
      rw [c.encoding_val_add t shift]
    _ = (halfStep^[t.val + shift.val]) (c.node 0) := by
      exact iterate_mod_period halfStep (c.node 0) c.encodingPeriod_pos
        c.encodingPeriod_periodic (t.val + shift.val)
    _ = (halfStep^[t.val]) ((halfStep^[shift.val]) (c.node 0)) := by
      rw [Function.iterate_add_apply]

/-- Cyclic rotation of the genuine Collatz parity word is exactly the parity
word obtained by advancing the same periodic `halfStep` orbit. This closes the
semantic rotation/advance representation bridge pointwise. -/
theorem rotate_parityWord_eq_advancedParityWord (c : OddCycle L)
    (shift : ZMod c.encodingPeriod) :
    rotate c.parityWord shift = c.advancedParityWord shift := by
  funext t
  change decide (Odd ((halfStep^[(t + shift).val]) (c.node 0))) =
    decide (Odd ((halfStep^[t.val]) ((halfStep^[shift.val]) (c.node 0))))
  rw [c.halfStep_zmod_add_state t shift]

end OddCycle
end Collatz
