import Collatz.Basic

namespace Collatz

/-- A positive periodic point of the ordinary, unaccelerated Collatz map.
The period is required to be nonzero, but not minimal. -/
def IsPositivePeriodicPoint (n period : ℕ) : Prop :=
  0 < n ∧ 0 < period ∧ (step^[period]) n = n

/-- A positive periodic point of the one-division map `halfStep`.
The period is required to be nonzero, but not minimal. -/
def IsPositiveHalfPeriodicPoint (n period : ℕ) : Prop :=
  0 < n ∧ 0 < period ∧ (halfStep^[period]) n = n

/-- Repeated ordinary Collatz steps remove an explicitly supplied power of two. -/
theorem iterate_step_pow_two_mul (a y : ℕ) :
    (step^[a]) (2 ^ a * y) = y := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Function.iterate_succ_apply]
      rw [pow_succ]
      have hrewrite : 2 ^ a * 2 * y = 2 * (2 ^ a * y) := by ring
      rw [hrewrite, step_two_mul]
      exact ih

/-- Repeated `halfStep` transitions remove an explicitly supplied power of two. -/
theorem iterate_halfStep_pow_two_mul (a y : ℕ) :
    (halfStep^[a]) (2 ^ a * y) = y := by
  induction a with
  | zero => simp
  | succ a ih =>
      rw [Function.iterate_succ_apply]
      rw [pow_succ]
      have hrewrite : 2 ^ a * 2 * y = 2 * (2 ^ a * y) := by ring
      rw [hrewrite, halfStep_two_mul]
      exact ih

/-- Arithmetic data for one exact odd-to-odd Collatz transition.

The equation records the odd `3x+1` step. The target is required to be odd, so
after the stated `a` halving steps the accelerated transition has genuinely
reached the next odd value rather than stopping early. -/
structure OddToOddStep (x y a : ℕ) : Prop where
  source_pos : 0 < x
  target_pos : 0 < y
  source_odd : Odd x
  target_odd : Odd y
  exponent_pos : 0 < a
  equation : 3 * x + 1 = 2 ^ a * y

namespace OddToOddStep

variable {x y a : ℕ}

/-- The first ordinary Collatz step of an odd-to-odd transition is exactly the
power-of-two multiple appearing in its defining arithmetic equation. -/
theorem first_step_eq (h : OddToOddStep x y a) : step x = 2 ^ a * y := by
  rw [step_of_odd h.source_odd]
  exact h.equation

/-- An exact odd-to-odd relation really is realised by the ordinary Collatz
map: one odd step followed by `a` halving steps reaches `y`. -/
theorem reaches_target (h : OddToOddStep x y a) :
    (step^[a + 1]) x = y := by
  rw [Function.iterate_succ_apply]
  rw [h.first_step_eq]
  exact iterate_step_pow_two_mul a y

/-- The same odd-to-odd relation takes exactly `a` iterations of `halfStep`.
This is why the natural denominator-compatible cyclic length is `A`, not
`A + L`. -/
theorem halfStep_reaches_target (h : OddToOddStep x y a) :
    (halfStep^[a]) x = y := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h.exponent_pos)
  rw [Function.iterate_succ_apply]
  have hfirst : halfStep x = 2 ^ b * y := by
    rw [halfStep_of_odd h.source_odd]
    have hfactor : 2 ^ (b + 1) * y = 2 * (2 ^ b * y) := by
      rw [pow_succ]
      ring
    rw [h.equation, hfactor]
    simp
  rw [hfirst]
  exact iterate_halfStep_pow_two_mul b y

/-- After the initial odd ordinary step and any `b ≤ a` halving steps, the
remaining state is exactly `2^(a-b) * y`. -/
theorem reaches_after_halvings (h : OddToOddStep x y a) {b : ℕ} (hb : b ≤ a) :
    (step^[b + 1]) x = 2 ^ (a - b) * y := by
  rw [Function.iterate_succ_apply]
  rw [h.first_step_eq]
  have hfactor : 2 ^ a * y = 2 ^ b * (2 ^ (a - b) * y) := by
    have hab : a = b + (a - b) := by omega
    calc
      2 ^ a * y = 2 ^ (b + (a - b)) * y := by
        exact congrArg (fun e : ℕ => 2 ^ e * y) hab
      _ = 2 ^ b * (2 ^ (a - b) * y) := by
        rw [pow_add]
        ring
  rw [hfactor]
  exact iterate_step_pow_two_mul b (2 ^ (a - b) * y)

/-- Before all `a` factors of two have been removed, the ordinary trajectory
is still at an even value. -/
theorem intermediate_even (h : OddToOddStep x y a) {b : ℕ} (hb : b < a) :
    Even ((step^[b + 1]) x) := by
  rw [h.reaches_after_halvings (Nat.le_of_lt hb)]
  have hpos : 0 < a - b := Nat.sub_pos_of_lt hb
  obtain ⟨d, hd⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
  rw [hd, pow_succ]
  refine ⟨2 ^ d * y, ?_⟩
  ring

/-- Operational exactness of the two-adic exponent for the ordinary map: every
earlier post-odd state is even, while the state after exactly `a` halvings is
the odd target. -/
theorem exact_removal (h : OddToOddStep x y a) :
    (∀ b : ℕ, b < a → Even ((step^[b + 1]) x)) ∧
      Odd ((step^[a + 1]) x) := by
  constructor
  · intro b hb
    exact h.intermediate_even hb
  · rw [h.reaches_target]
    exact h.target_odd

end OddToOddStep

/-- A positive odd Collatz cycle with `L` odd nodes, indexed cyclically.

The index type `ZMod L` makes the closing edge part of the same local equation
as every other edge. No combinatorial Radius-4 encoding is built into this
structure. -/
structure OddCycle (L : ℕ) [NeZero L] where
  node : ZMod L → ℕ
  exponent : ZMod L → ℕ
  node_pos : ∀ i, 0 < node i
  node_odd : ∀ i, Odd (node i)
  exponent_pos : ∀ i, 0 < exponent i
  step_eq : ∀ i, 3 * node i + 1 = 2 ^ exponent i * node (i + 1)

namespace OddCycle

variable {L : ℕ} [NeZero L]

/-- The local edge at cyclic position `i`, packaged as an exact odd-to-odd
Collatz transition. -/
theorem edge (c : OddCycle L) (i : ZMod L) :
    OddToOddStep (c.node i) (c.node (i + 1)) (c.exponent i) := by
  exact {
    source_pos := c.node_pos i
    target_pos := c.node_pos (i + 1)
    source_odd := c.node_odd i
    target_odd := c.node_odd (i + 1)
    exponent_pos := c.exponent_pos i
    equation := c.step_eq i
  }

/-- Every edge of an `OddCycle` is realised by ordinary Collatz iteration. -/
theorem edge_reaches_next (c : OddCycle L) (i : ZMod L) :
    (step^[c.exponent i + 1]) (c.node i) = c.node (i + 1) :=
  (c.edge i).reaches_target

/-- Every edge is also realised by exactly `exponent i` iterations of the
one-division map `halfStep`. -/
theorem edge_halfStep_reaches_next (c : OddCycle L) (i : ZMod L) :
    (halfStep^[c.exponent i]) (c.node i) = c.node (i + 1) :=
  (c.edge i).halfStep_reaches_target

/-- Every edge exponent in an `OddCycle` is exact in the operational ordinary
Collatz sense: all earlier post-odd states are even and the stated endpoint is
odd. -/
theorem edge_exact_removal (c : OddCycle L) (i : ZMod L) :
    (∀ b : ℕ, b < c.exponent i →
      Even ((step^[b + 1]) (c.node i))) ∧
      Odd ((step^[c.exponent i + 1]) (c.node i)) :=
  (c.edge i).exact_removal

/-- A cycle is non-trivial when at least one of its odd nodes is not `1`.
This is deliberately separate from the base cycle structure. -/
def IsNontrivial (c : OddCycle L) : Prop :=
  ∃ i : ZMod L, c.node i ≠ 1

/-- Rebase an odd cycle at another odd node. This changes only the chosen
cyclic origin; it does not alter any local Collatz equation. -/
def rebase (c : OddCycle L) (shift : ZMod L) : OddCycle L where
  node i := c.node (i + shift)
  exponent i := c.exponent (i + shift)
  node_pos i := c.node_pos (i + shift)
  node_odd i := c.node_odd (i + shift)
  exponent_pos i := c.exponent_pos (i + shift)
  step_eq i := by
    simpa [add_assoc, add_comm, add_left_comm] using c.step_eq (i + shift)

@[simp]
theorem rebase_node (c : OddCycle L) (shift i : ZMod L) :
    (c.rebase shift).node i = c.node (i + shift) := by
  rfl

@[simp]
theorem rebase_exponent (c : OddCycle L) (shift i : ZMod L) :
    (c.rebase shift).exponent i = c.exponent (i + shift) := by
  rfl

/-- The sum of exponents on the first `k` cyclic odd-to-odd edges, starting at
index zero. At `k = L` this traverses the cycle exactly once. -/
def prefixExponent (c : OddCycle L) (k : ℕ) : ℕ :=
  (Finset.range k).sum (fun j => c.exponent (j : ZMod L))

@[simp]
theorem prefixExponent_zero (c : OddCycle L) : c.prefixExponent 0 = 0 := by
  simp [prefixExponent]

@[simp]
theorem prefixExponent_succ (c : OddCycle L) (k : ℕ) :
    c.prefixExponent (k + 1) = c.prefixExponent k + c.exponent (k : ZMod L) := by
  unfold prefixExponent
  rw [Finset.sum_range_succ]

/-- Every odd-to-odd edge removes at least one factor of two, so the sum of the
first `k` exponents is at least `k`. -/
theorem prefixExponent_ge (c : OddCycle L) (k : ℕ) : k ≤ c.prefixExponent k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [c.prefixExponent_succ k]
      have hexp := c.exponent_pos (k : ZMod L)
      omega

/-- Total power of two removed during one traversal of the odd cycle. -/
def totalExponent (c : OddCycle L) : ℕ := c.prefixExponent L

/-- The total exponent is at least the number of odd nodes. -/
theorem length_le_totalExponent (c : OddCycle L) : L ≤ c.totalExponent := by
  exact c.prefixExponent_ge L

/-- The total exponent is positive. -/
theorem totalExponent_pos (c : OddCycle L) : 0 < c.totalExponent := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  exact lt_of_lt_of_le hL c.length_le_totalExponent

/-- Number of ordinary Collatz steps used by the first `k` odd-to-odd edges.
Each edge contributes its halving exponent plus the initial odd step. -/
def prefixStepCount (c : OddCycle L) (k : ℕ) : ℕ :=
  c.prefixExponent k + k

@[simp]
theorem prefixStepCount_zero (c : OddCycle L) : c.prefixStepCount 0 = 0 := by
  simp [prefixStepCount]

@[simp]
theorem prefixStepCount_succ (c : OddCycle L) (k : ℕ) :
    c.prefixStepCount (k + 1) =
      c.prefixStepCount k + (c.exponent (k : ZMod L) + 1) := by
  rw [prefixStepCount, prefixStepCount, c.prefixExponent_succ k]
  omega

/-- The inhomogeneous term generated by composing the first `k` odd-to-odd
relations. It is defined recursively in exactly the way composition creates it. -/
def prefixNumerator (c : OddCycle L) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 3 * prefixNumerator c k + 2 ^ c.prefixExponent k

@[simp]
theorem prefixNumerator_zero (c : OddCycle L) : c.prefixNumerator 0 = 0 := by
  rfl

@[simp]
theorem prefixNumerator_succ (c : OddCycle L) (k : ℕ) :
    c.prefixNumerator (k + 1) =
      3 * c.prefixNumerator k + 2 ^ c.prefixExponent k := by
  rfl

/-- The composed inhomogeneous numerator is positive after at least one edge. -/
theorem prefixNumerator_pos (c : OddCycle L) {k : ℕ} (hk : 0 < k) :
    0 < c.prefixNumerator k := by
  cases k with
  | zero => omega
  | succ k =>
      rw [c.prefixNumerator_succ k]
      positivity

/-- Composition of the first `k` odd-to-odd equations.

This is the first substantive arithmetic bridge: the formula is derived by
induction from `OddCycle.step_eq`, rather than postulated as cycle folklore. -/
theorem composed_identity (c : OddCycle L) (k : ℕ) :
    2 ^ c.prefixExponent k * c.node (k : ZMod L) =
      3 ^ k * c.node 0 + c.prefixNumerator k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have hstep :
          2 ^ c.exponent (k : ZMod L) * c.node ((k + 1 : ℕ) : ZMod L) =
            3 * c.node (k : ZMod L) + 1 := by
        symm
        simpa using c.step_eq (k : ZMod L)
      calc
        2 ^ c.prefixExponent (k + 1) * c.node ((k + 1 : ℕ) : ZMod L) =
            2 ^ c.prefixExponent k *
              (2 ^ c.exponent (k : ZMod L) * c.node ((k + 1 : ℕ) : ZMod L)) := by
                rw [c.prefixExponent_succ k, pow_add]
                ring
        _ = 2 ^ c.prefixExponent k * (3 * c.node (k : ZMod L) + 1) := by
              rw [hstep]
        _ = 3 * (2 ^ c.prefixExponent k * c.node (k : ZMod L)) +
              2 ^ c.prefixExponent k := by
                ring
        _ = 3 * (3 ^ k * c.node 0 + c.prefixNumerator k) +
              2 ^ c.prefixExponent k := by
                rw [ih]
        _ = 3 ^ (k + 1) * c.node 0 + c.prefixNumerator (k + 1) := by
              rw [c.prefixNumerator_succ k, pow_succ]
              ring

/-- The first `k` accelerated edges are exactly the first
`prefixStepCount k` ordinary Collatz steps. -/
theorem reaches_prefix_node (c : OddCycle L) (k : ℕ) :
    (step^[c.prefixStepCount k]) (c.node 0) = c.node (k : ZMod L) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [c.prefixStepCount_succ k]
      rw [Nat.add_comm]
      rw [Function.iterate_add_apply]
      rw [ih]
      simpa using c.edge_reaches_next (k : ZMod L)

/-- The first `k` odd-to-odd edges are exactly the first `prefixExponent k`
iterations of the one-division map. -/
theorem halfStep_reaches_prefix_node (c : OddCycle L) (k : ℕ) :
    (halfStep^[c.prefixExponent k]) (c.node 0) = c.node (k : ZMod L) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [c.prefixExponent_succ k]
      rw [Nat.add_comm]
      rw [Function.iterate_add_apply]
      rw [ih]
      simpa using c.edge_halfStep_reaches_next (k : ZMod L)

/-- The composed identity after one full traversal of the odd cycle. -/
theorem full_cycle_identity (c : OddCycle L) :
    2 ^ c.totalExponent * c.node 0 =
      3 ^ L * c.node 0 + c.prefixNumerator L := by
  simpa [totalExponent] using c.composed_identity L

/-- One full traversal of the odd-cycle data is a genuine period of the
ordinary Collatz map, of length `A + L`. -/
theorem node_zero_periodic (c : OddCycle L) :
    (step^[c.totalExponent + L]) (c.node 0) = c.node 0 := by
  simpa [prefixStepCount, totalExponent] using c.reaches_prefix_node L

/-- One full traversal is also a genuine period of `halfStep`, now of length
exactly `A`. This is the period compatible with `2^A - 3^L`. -/
theorem node_zero_halfStep_periodic (c : OddCycle L) :
    (halfStep^[c.totalExponent]) (c.node 0) = c.node 0 := by
  simpa [totalExponent] using c.halfStep_reaches_prefix_node L

/-- The base odd node of an `OddCycle` is a positive periodic point of the
ordinary, unaccelerated Collatz map. -/
theorem node_zero_isPositivePeriodicPoint (c : OddCycle L) :
    IsPositivePeriodicPoint (c.node 0) (c.totalExponent + L) := by
  refine ⟨c.node_pos 0, ?_, c.node_zero_periodic⟩
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  omega

/-- The base odd node is also a positive periodic point of the denominator-
compatible map `halfStep`, with period `A`. -/
theorem node_zero_isPositiveHalfPeriodicPoint (c : OddCycle L) :
    IsPositiveHalfPeriodicPoint (c.node 0) c.totalExponent := by
  exact ⟨c.node_pos 0, c.totalExponent_pos, c.node_zero_halfStep_periodic⟩

end OddCycle

end Collatz
