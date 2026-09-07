# Lean formalisation of the RL238 Radius-4 local theorem

This standalone repository reconstructs the established RL238 primitive
full-denominator transport-Radius-4 local impossibility theorem in Lean.
The final local theorem is **not yet proved here**.

The research derivation may be consulted as a read-only blueprint. It is not
a dependency: every formal step must follow from this repository's definitions,
proved Lean lemmas, and the pinned Mathlib. No research conclusion is an axiom.

## Cycle model and denominator

The ordinary Collatz map sends an even natural number to `n/2` and an odd
natural number to `3n+1`. Its familiar positive cycle is `1 → 4 → 2 → 1`.

The structure `OddCycle L` records positive odd nodes and exact transitions

`3*x_i + 1 = 2^a_i * x_(i+1)`.

Lean proves their operational meaning and ordinary periodicity. For the
denominator-compatible parity encoding it uses `halfStep`, which performs one
division by two on each transition. The encoded period has length
`A = sum a_i` and contains `L` odd source states.

The cycle equations imply, inside Lean,

`(2^A - 3^L) * x_0 = wordNumerator(parity word)`.

The full denominator `D = 2^A - 3^L` is positive and divides that exact
numerator. `OddCycle.positiveCycleDenominator_of_nontrivial` also proves
`D > 1` under the explicit nontriviality hypothesis. Shifted-origin versions
and the identification of rotation with the advanced parity origin are proved.

`OddCycle` does not assert a minimal represented period or primitivity.
Required `IsPrimitive` hypotheses must remain explicit.

## What transport Radius 4 means

Compare a cyclic binary word with one of its rotations. At a cyclic cut define

`G_k = target ones in the first k positions - source ones in those positions`.

The cut cost is `sum_{k=1}^{A-1} |G_k|`. The transport model defines exact
radius as the minimum of this cost over cyclic cuts for equal-weight words.
RL238 Radius 4 means that this minimum is exactly four.

The relevant predicates are `IsTransportRadiusFour` and
`OddCycle.IsCycleTransportRadiusFour`.

The older predicates `IsRadiusFour` and `OddCycle.IsCycleRadiusFour` mean
Hamming distance four. Their theorems remain support infrastructure and may
only be reused after their hypotheses have been formally established.
They do not state the RL238 transport theorem.

## Current formal boundary

R4-1 is complete: Lean proves the height-two `(1,2,1)` flow family and all five
unit-height component families `[4]`, `[3,1]`, `[2,2]`, `[2,1,1]`,
`[1,1,1,1]`, together with the required cut normalization and genuine advanced
parity origin. All intended transport modules are root-imported and checked by
ordinary full CI.

Work continues at the first established elimination, height-two and connected
`[4]`. No complete topology elimination or final impossibility theorem is yet
proved. Its LMN two-logarithm lower bound has no located formal counterpart in
pinned Mathlib; the exact obligation is documented in
[the analytic dependency audit](docs/RL238_ANALYTIC_DEPENDENCY.md).
It is not assumed by the Lean library.

See the [checkpoint](docs/CURRENT_CHECKPOINT.md),
[theorem index](docs/THEOREM_INDEX.md),
[roadmap](docs/FORMALISATION_ROADMAP.md),
[RL238 map](docs/RL238_TO_LEAN_MAP.md), and
[handover](docs/NEXT_SESSION_HANDOVER.md) for current verified scope.

## Endpoint

The target excludes the specified primitive full-denominator self-rotation
configuration at exact transport radius four. It does not by itself exclude
every nontrivial Collatz cycle or prove the Collatz conjecture.

This task ends when that local theorem is kernel-verified on main, all required
work is merged, full CI is green, and the completion audit passes.
Radius 5, Gate A, Gate B, global encounter work, and the unrelated reverse
ordinary-cycle draft PR #6 are outside this task.

## Building and proof hygiene

Lean and Mathlib are pinned by `lean-toolchain` and `lakefile.lean`.

```text
lake update
lake build
```

The package uses `autoImplicit = false` and `warningAsError = true`.
GitHub Actions resolves dependencies and runs the full library build.
Proof placeholders, research-conclusion axioms, and undocumented external
assumptions are not acceptable progress.

The [proof scope policy](docs/PROOF_SCOPE_POLICY.md) requires each substantial
theorem to state its meaning, assumptions, dependencies, and limitations.
