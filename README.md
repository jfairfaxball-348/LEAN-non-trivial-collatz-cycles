# Lean formalisation of non-trivial Collatz-cycle obstructions

This repository is a **standalone formal mathematics project**. It is intended to be understandable and checkable without access to any other repository, private notes, prior calculations, or project history.

Its first substantial target is a local theorem about a structure called **Radius 4**. The repository defines the Collatz dynamics from first principles, derives the odd-cycle denominator inside Lean, and then builds the cyclic-word language needed to state the local Radius-4 question precisely.

## What is the Collatz problem?

For a positive integer `n`, define the ordinary Collatz map

- `T(n) = n / 2` if `n` is even;
- `T(n) = 3n + 1` if `n` is odd.

For example,

`5 -> 16 -> 8 -> 4 -> 2 -> 1 -> 4 -> 2 -> 1 -> ...`

The **Collatz conjecture** says that every positive starting integer eventually reaches `1`.

Under this version of the map, `1 -> 4 -> 2 -> 1` is the familiar trivial cycle. A **non-trivial cycle** would be any other finite periodic orbit of positive integers.

This repository does **not** assume the Collatz conjecture.

## Odd-to-odd cycle model

The substantive formalisation now includes an explicit positive odd-cycle structure. At each cyclic odd index `i`, Lean records

`3 * x_i + 1 = 2^(a_i) * x_(i+1)`,

with positive odd nodes and positive exponents.

The exponent is not merely labelled "exact": Lean proves operationally that all earlier ordinary post-odd states are even and that the stated endpoint is odd.

The repository also proves that these local equations are realised by the ordinary Collatz map. One full traversal returns the chosen base odd node after `A + L` ordinary Collatz steps, where

- `L` is the number of odd nodes;
- `A` is the sum of the exponents.

A reverse theorem extracting this odd-cycle structure from an arbitrary ordinary periodic orbit has not yet been formalised and remains an explicit bridge if the final theorem is to start from the most general ordinary-cycle formulation.

## Why a second map appears

For the Radius-4 encoding, the denominator itself fixes the natural cyclic length.

The repository defines the derived one-division map

- `S(n) = n / 2` if `n` is even;
- `S(n) = (3n + 1) / 2` if `n` is odd.

This is called `halfStep` in Lean. It does not replace the ordinary Collatz map; it is derived for the denominator-compatible encoding.

An odd-to-odd edge with exponent `a_i` takes exactly `a_i` `halfStep` transitions. Therefore one full odd cycle takes exactly `A` such transitions. This is why the final parity word has cyclic length `A`, not `A + L`.

## The derived denominator

Lean now derives, rather than assumes, the full composed cycle identity

`2^A * x_0 = 3^L * x_0 + N`,

where `N` is the recursively generated inhomogeneous numerator obtained from the local odd-to-odd equations.

Rearranging inside Lean gives

`(2^A - 3^L) * x_0 = N`.

So the characteristic denominator

`D = 2^A - 3^L`

is no longer only vocabulary: the repository proves that `D > 0` and that the complete integer `D` divides the exact generated numerator `N`, with quotient `x_0`.

The stronger scaffold predicate `PositiveCycleDenominator`, currently defined as `1 < D`, is **not** silently inferred from positivity. If `D > 1` is needed under a non-triviality hypothesis, that must be proved separately.

## What is Radius 4?

A finite cycle can be represented by a cyclic binary parity word. For the formal odd cycle above, the genuine Collatz-derived word has length `A`: at each cyclic `halfStep` position, its bit records whether the actual orbit state is odd.

If `w` is such a word and `s` is a cyclic shift, `rotate w s` is the same circular word read from a different starting point.

The **Hamming distance** between two binary words is the number of positions at which they differ.

A shift is at **exact Radius 4** when

`hammingDistance w (rotate w s) = 4`.

So Radius 4 is **not** four Collatz iterations and is **not** a bound on the size of an orbit. It is a local combinatorial property of the denominator-compatible parity word.

See [`docs/RADIUS4.md`](docs/RADIUS4.md) for the standalone scope explanation.

## Current Radius-4 boundary

The repository now has a genuine Collatz-specific Radius-4 predicate: exact Hamming distance four for the length-`A` parity word extracted from the proved periodic `halfStep` orbit.

It also defines an arithmetic marker word whose true positions are the cumulative exponent boundaries. Those positions are proved to be actual odd states. The theorem that the marker word equals the genuine parity word is still missing; formally, this requires showing that every non-boundary position inside each exponent block is even.

The next important bridge is then to prove that cyclic rotation of the parity word corresponds to advancing/rebasing the same periodic Collatz data, and to derive the exact full-denominator relation for the rotated numerator or numerator difference. Only after those bridges are available is it legitimate to state the final sparse Radius-4 contradiction.

## What would the Radius-4 local theorem prove?

The target remains:

> An eligible primitive positive Collatz-cycle encoding cannot satisfy the required full-denominator condition while also having a nonzero rotation at exact Hamming distance four.

That theorem is **not yet proved**.

## What would it *not* prove?

Even a completed Radius-4 local theorem would **not by itself**:

- prove the full Collatz conjecture;
- prove that every positive integer reaches `1`;
- prove that all Collatz trajectories are bounded;
- exclude every possible non-trivial cycle;
- prove anything automatically about other Hamming radii;
- prove that every hypothetical non-trivial cycle must exhibit a Radius-4 configuration.

The last step would require a separate **global bridge/encounter theorem** showing that every hypothetical non-trivial cycle necessarily generates an eligible Radius-4 configuration. The local Radius-4 theorem and such a global bridge are different results.

## Formalisation status

| Component | Status |
|---|---|
| Ordinary Collatz map | defined and checked in Lean |
| Exact odd-to-odd transition model | substantively formalised |
| Positive cyclic odd-cycle structure | substantively formalised |
| Exact removal of powers of two | proved operationally |
| Odd-cycle -> ordinary periodic orbit | proved for the chosen base odd node |
| Reverse arbitrary ordinary cycle -> odd-cycle extraction | not yet formalised |
| Derived one-division map `halfStep` | defined |
| Odd-cycle -> `halfStep` period `A` | proved |
| `L ≤ A` and `A > 0` | proved |
| Composed cycle identity | proved |
| Denominator identity `(2^A - 3^L) * x_0 = N` | proved |
| Positivity `2^A - 3^L > 0` | proved |
| Full denominator divides generated numerator | proved |
| Genuine length-`A` Collatz parity word | defined from the actual orbit |
| Exact Collatz-specific Radius-4 predicate | defined |
| Exponent-marker word equals genuine parity word | not yet proved |
| Rotation/rebasing arithmetic bridge | not yet proved |
| Radius-4 local impossibility theorem | not yet proved |
| Global Radius-4 encounter theorem | out of scope for the local proof |
| Full Collatz conjecture | not claimed |

## Repository rule: every proof states its scope

Every substantial formalised result added here is accompanied by plain-English documentation giving its assumptions, theorem name, source file, conclusion, limitations, and dependency boundary.

The current formal results are catalogued in [`docs/THEOREM_INDEX.md`](docs/THEOREM_INDEX.md). The documentation rule is defined in [`docs/PROOF_SCOPE_POLICY.md`](docs/PROOF_SCOPE_POLICY.md), and the dependency order for the Radius-4 proof is in [`docs/FORMALISATION_ROADMAP.md`](docs/FORMALISATION_ROADMAP.md).

## Proof hygiene

The project builds with `autoImplicit = false` and `warningAsError = true`. Admitted placeholders are not acceptable project progress.

## Building

The project uses Lean 4 and mathlib, pinned by the repository configuration.

```text
lake update
lake build
```

GitHub Actions performs dependency resolution and `lake build` on pushes and pull requests to `main`.
