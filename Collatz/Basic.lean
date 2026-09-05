import Mathlib

namespace Collatz

/-- One step of the standard, unaccelerated Collatz map on natural numbers.

For even `n` this is `n / 2`; for odd `n` it is `3*n + 1`.
The mathematical problem studied in this repository concerns positive inputs. -/
def step (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

@[simp]
theorem step_one : step 1 = 4 := by
  norm_num [step]

@[simp]
theorem step_two : step 2 = 1 := by
  norm_num [step]

@[simp]
theorem step_four : step 4 = 2 := by
  norm_num [step]

/-- For an odd natural number, the ordinary Collatz map takes the `3n+1`
branch. -/
theorem step_of_odd {n : ℕ} (hn : Odd n) : step n = 3 * n + 1 := by
  rcases hn with ⟨k, rfl⟩
  simp [step]

/-- One ordinary Collatz step halves an explicitly even number `2*n`. -/
@[simp]
theorem step_two_mul (n : ℕ) : step (2 * n) = n := by
  simp [step]

/-- The one-division Collatz map.

Unlike `step`, this map divides by two on every transition: an even input maps
to `n/2`, while an odd input maps to `(3*n+1)/2`. This is introduced as a
derived encoding map because an odd-to-odd edge with exponent `a` takes exactly
`a` iterations of this map. Consequently its full cycle length is `A`, matching
the exponent in the denominator `2^A - 3^L`.

The repository continues to use `step` as the ordinary Collatz map; `halfStep`
is not a replacement for it. -/
def halfStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else (3 * n + 1) / 2

/-- On odd inputs the one-division map uses its `(3n+1)/2` branch. -/
theorem halfStep_of_odd {n : ℕ} (hn : Odd n) :
    halfStep n = (3 * n + 1) / 2 := by
  rcases hn with ⟨k, rfl⟩
  simp [halfStep]

/-- The one-division map halves an explicitly even input. -/
@[simp]
theorem halfStep_two_mul (n : ℕ) : halfStep (2 * n) = n := by
  simp [halfStep]

/-- On even inputs `halfStep` agrees with one ordinary Collatz step. -/
theorem halfStep_eq_step_of_even {n : ℕ} (hn : Even n) :
    halfStep n = step n := by
  rcases hn with ⟨k, rfl⟩
  simp [halfStep, step]

/-- A binary word indexed cyclically modulo `n`.

This is a purely combinatorial object. A separate theorem is required before a
particular cyclic word may be treated as encoding a Collatz-cycle candidate. -/
abbrev CyclicWord (n : ℕ) := ZMod n → Bool

/-- Rotate a cyclic word forward by `shift`. -/
def rotate {n : ℕ} (w : CyclicWord n) (shift : ZMod n) : CyclicWord n :=
  fun i => w (i + shift)

@[simp]
theorem rotate_zero {n : ℕ} (w : CyclicWord n) : rotate w 0 = w := by
  funext i
  simp [rotate]

/-- Hamming distance between two finite cyclic binary words. -/
def hammingDistance {n : ℕ} [NeZero n] (u v : CyclicWord n) : ℕ :=
  (Finset.univ.filter (fun i : ZMod n => u i ≠ v i)).card

@[simp]
theorem hammingDistance_self {n : ℕ} [NeZero n] (w : CyclicWord n) :
    hammingDistance w w = 0 := by
  simp [hammingDistance]

/-- Number of `true` entries in a finite cyclic binary word. -/
def ones {n : ℕ} [NeZero n] (w : CyclicWord n) : ℕ :=
  (Finset.univ.filter (fun i : ZMod n => w i = true)).card

/-- A specified rotation lies at exactly `radius` in cyclic Hamming distance. -/
def IsExactRadius {n : ℕ} [NeZero n] (radius : ℕ) (w : CyclicWord n)
    (shift : ZMod n) : Prop :=
  hammingDistance w (rotate w shift) = radius

/-- The word has a non-identity rotation at exactly the requested radius. -/
def HasExactRadiusRotation {n : ℕ} [NeZero n] (radius : ℕ)
    (w : CyclicWord n) : Prop :=
  ∃ shift : ZMod n, shift ≠ 0 ∧ IsExactRadius radius w shift

/-- Rotational primitivity: no nonzero cyclic shift fixes the word exactly. -/
def IsPrimitive {n : ℕ} (w : CyclicWord n) : Prop :=
  ∀ shift : ZMod n, rotate w shift = w → shift = 0

/-- A primitive word cannot be fixed by a nonzero rotation. -/
theorem primitive_nontrivial_rotation_ne {n : ℕ} (w : CyclicWord n)
    (hw : IsPrimitive w) {shift : ZMod n} (hshift : shift ≠ 0) :
    rotate w shift ≠ w := by
  intro hfix
  exact hshift (hw shift hfix)

end Collatz
