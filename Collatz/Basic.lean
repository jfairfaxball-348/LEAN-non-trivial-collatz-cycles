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
