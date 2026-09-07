# Collatz cycles and a local transport obstruction in Lean

This repository develops a machine-checked local obstruction for possible
Collatz cycles. The intended final theorem is **not yet proved**. The verified
results currently supply cycle arithmetic, a classification of transport
configurations of cost four, and elementary ingredients for excluding them.

The ordinary Collatz map sends an even natural number `x` to `x/2` and an odd
one to `3*x+1`. For example, `1 → 4 → 2 → 1` is a positive cycle. The Collatz
conjecture says that every positive starting value eventually reaches this
cycle. The local theorem pursued here would not by itself prove that conjecture
or exclude every other cycle.

## The formal cycle model

`OddCycle L` records `L` positive odd nodes linked cyclically by exact equations

`3*x_i + 1 = 2^a_i * x_(i+1)`.

Each positive exponent `a_i` counts the divisions by two needed to reach the
next odd node. The auxiliary map `halfStep` divides by two at every step: it
sends an even `x` to `x/2` and an odd `x` to `(3*x+1)/2`. The encoded cycle has
`A = sum a_i` such steps and `L` odd source positions. A binary parity word
records those positions, with `1` for odd and `0` for even.

Composing these steps gives

`D * x_0 = Q(w)`, where `D = 2^A - 3^L`.

Here `Q` is the exact affine numerator `wordNumerator`; its definition and
composition law are explained in [Word arithmetic](docs/WORD_ARITHMETIC_SCOPE.md).
Lean proves this identity, positivity of `D`, divisibility by the entire `D`,
and corresponding identities at shifted origins. It also proves `D > 1` for
an `OddCycle` satisfying `c.IsNontrivial`, meaning that at least one odd
node is not `1`.

## The local target

For a cyclic binary word `w` of length `A`, let `L` be its number of ones and
read `Q(w)` from positions `0, …, A-1`. The intended theorem excludes a
self-rotation at exact transport radius four under these hypotheses:

- `0 < L < A`;
- the full integer denominator `D = 2^A - 3^L` satisfies `D > 1`;
- `D` divides `Q(w)` itself;
- `w` is primitive: no nonzero cyclic rotation fixes it;
- the compared rotation has a nonzero shift.

This is a statement about binary words meeting explicit arithmetic conditions.
The cycle model supplies an application of it; `OddCycle` does not automatically
assert primitivity or a minimal represented period.

To define transport radius, compare two equal-weight words from a chosen
cyclic cut. After `k` positions, let `G_k` be target-prefix ones minus
source-prefix ones. The cut cost is `sum_{k=1}^{A-1} |G_k|`. Exact transport
radius four means that the minimum cut cost is four. The Lean predicate is
`IsTransportRadiusFour`; see [Radius 4](docs/RADIUS4.md).

Hamming distance counts unequal positions instead. The separate predicates
`IsRadiusFour` and `OddCycle.IsCycleRadiusFour` use Hamming distance and cannot
be substituted for the transport hypothesis.

## What is verified and what remains

Lean classifies cost-four flow into a height-two profile `(1,2,1)` or four
unit-height edges grouped into consecutive runs of lengths `[4]`, `[3,1]`,
`[2,2]`, `[2,1,1]`, or `[1,1,1,1]`. It proves that the chosen cut can be moved
to zero by rotating the words. Signed local bits, exact replacement
coefficients, coprime cancellation, and elementary logarithmic bounds are
also verified.

No complete family exclusion or final impossibility theorem is verified.
The first exclusions still require representation and divisibility arguments,
a quantitative lower bound for a linear combination of `log 2` and `log 3`,
and finite arithmetic checks. The [analytic dependency](docs/ANALYTIC_DEPENDENCY.md)
states the missing proposition with its exact constants. It has no located
counterpart in the pinned Mathlib and is not assumed by this library.

The [checkpoint](docs/CURRENT_CHECKPOINT.md) records verified revisions and
build evidence. The [theorem index](docs/THEOREM_INDEX.md),
[proof map](docs/LOCAL_PROOF_MAP.md), and
[roadmap](docs/FORMALISATION_ROADMAP.md) separate proved ingredients from open
steps. [Project history](docs/PROJECT_HISTORY.md) records dated repository
milestones. Current working-branch source is not promoted merely by being present.

## Building

Install Lean's `elan` toolchain manager, then run from the repository root:

```text
lake update
lake build
```

`lean-toolchain` pins Lean `v4.34.0-rc2`; `lakefile.lean` pins Mathlib revision
`69fe4f49ffbc9580a2c3ae6d29591ef6d1d4131e`. These are the formal dependencies;
no additional project is required. The package enables `autoImplicit = false`
and `warningAsError = true`. GitHub Actions runs the full library build.

The [proof scope policy](docs/PROOF_SCOPE_POLICY.md) requires explicit
hypotheses and honest completion claims. Proof placeholders, new axioms for
mathematical conclusions, and `native_decide` are not permitted.
