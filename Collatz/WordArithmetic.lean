import Collatz.Basic

namespace Collatz

/-- Multiplicative coefficient contributed by one parity bit in the
one-division Collatz recurrence `2*y = m*x + r`.

`false` represents an even state and contributes multiplier `1`; `true`
represents an odd state and contributes multiplier `3`. -/
def bitMultiplier : Bool → ℕ
  | false => 1
  | true => 3

/-- Inhomogeneous coefficient contributed by one parity bit. An even step has
no offset; an odd step contributes the `+1` in `3*x+1`. -/
def bitOffset : Bool → ℕ
  | false => 0
  | true => 1

/-- Number of odd (`true`) positions in a finite linear parity word. -/
def listOnes : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + listOnes bs

/-- The exact inhomogeneous numerator produced by composing the affine
relations encoded by a finite parity word.

The recursion is from the left edge. For a leading bit `b` followed by `bs`,
the leading offset is multiplied by the `3`-power contributed by the tail,
while the tail numerator is multiplied by `2`. -/
def wordNumerator : List Bool → ℕ
  | [] => 0
  | b :: bs => 3 ^ listOnes bs * bitOffset b + 2 * wordNumerator bs

/-- `Realizes bits x y` means that there is a chain from `x` to `y` whose
successive states satisfy exactly the affine equations specified by `bits`.

This predicate contains no Collatz assumption. A later theorem connects an
actual `halfStep` orbit to this relation using its genuine parity bits. -/
def Realizes : List Bool → ℕ → ℕ → Prop
  | [], x, y => x = y
  | b :: bs, x, y =>
      ∃ z : ℕ,
        2 * z = bitMultiplier b * x + bitOffset b ∧
        Realizes bs z y

@[simp]
theorem listOnes_nil : listOnes [] = 0 := by
  rfl

@[simp]
theorem listOnes_cons (b : Bool) (bs : List Bool) :
    listOnes (b :: bs) = (if b then 1 else 0) + listOnes bs := by
  rfl

@[simp]
theorem wordNumerator_nil : wordNumerator [] = 0 := by
  rfl

@[simp]
theorem wordNumerator_cons (b : Bool) (bs : List Bool) :
    wordNumerator (b :: bs) =
      3 ^ listOnes bs * bitOffset b + 2 * wordNumerator bs := by
  rfl

/-- Pure affine composition theorem for a binary word.

If the successive local equations are all realised, then the complete word
satisfies

`2^(length bits) * y = 3^(number of true bits) * x + wordNumerator bits`.

This is the word-level analogue of the odd-cycle denominator composition, and
it is proved here from the local affine equations rather than assumed. -/
theorem realizes_composed_identity {bits : List Bool} {x y : ℕ}
    (h : Realizes bits x y) :
    2 ^ bits.length * y = 3 ^ listOnes bits * x + wordNumerator bits := by
  induction bits generalizing x y with
  | nil =>
      simpa [Realizes] using h
  | cons b bs ih =>
      rcases h with ⟨z, hstep, htail⟩
      have hcomp := ih htail
      cases b <;>
        simp [listOnes, wordNumerator, bitMultiplier, bitOffset, pow_succ] at hstep ⊢ <;>
        nlinarith

end Collatz
