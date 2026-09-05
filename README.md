# Lean formalisation of non-trivial Collatz-cycle obstructions

This repository is a **standalone formal mathematics project**. It is intended to be understandable and checkable without access to any other repository, private notes, prior calculations, or project history.

Its first substantial target is a local theorem about a structure called **Radius 4**. The repository begins by defining the Collatz problem itself, then builds the cyclic-word language needed to state Radius 4 precisely.

## What is the Collatz problem?

For a positive integer `n`, define the Collatz map

- `T(n) = n / 2` if `n` is even;
- `T(n) = 3n + 1` if `n` is odd.

For example,

`5 -> 16 -> 8 -> 4 -> 2 -> 1 -> 4 -> 2 -> 1 -> ...`

The **Collatz conjecture** says that every positive starting integer eventually reaches `1`.

Under this version of the map, `1 -> 4 -> 2 -> 1` is the familiar trivial cycle. A **non-trivial cycle** would be any other finite periodic orbit of positive integers.

This repository does **not** assume the Collatz conjecture. It formalises particular statements that may help exclude possible non-trivial cycles.

## What is Radius 4?

A hypothetical cycle can be encoded by finite cyclic combinatorial data. The first reusable layer in this repository is a **cyclic binary word**: a binary word whose positions are indexed around a circle.

If `w` is such a word and `s` is a cyclic shift, `rotate w s` is the same circular word read from a different starting point.

The **Hamming distance** between two binary words is the number of positions at which they differ.

A shift is at **exact Radius 4** when

`hammingDistance w (rotate w s) = 4`.

So Radius 4 is **not** four Collatz iterations and is **not** a bound on the size of an orbit. It is a local combinatorial property: a cyclic word differs from one of its nonzero rotations in exactly four positions.

See [`docs/RADIUS4.md`](docs/RADIUS4.md) for the full standalone explanation.

## How does Radius 4 relate to Collatz?

The Collatz-specific part of the formalisation must prove that the cyclic word under consideration genuinely represents an eligible hypothetical positive Collatz cycle.

For an odd-to-odd cycle description, if `L` is the number of odd nodes and `A` is the total number of powers of two removed, the cycle arithmetic naturally introduces

`D = 2^A - 3^L`.

The intended Radius-4 local theorem concerns primitive positive cycle encodings satisfying the exact arithmetic eligibility conditions, including a condition involving this full cycle denominator.

The repository deliberately keeps the pure cyclic-word definitions separate from those Collatz-specific eligibility proofs. Nothing is treated as a Collatz theorem until that connection has itself been formalised here.

## What would the Radius-4 local theorem prove?

The target has the following logical shape:

> An eligible primitive positive Collatz-cycle encoding cannot satisfy the required full-denominator condition while also having a nonzero rotation at exact Hamming distance four.

When Lean eventually accepts that full statement with all required definitions and lemmas, it will be a rigorous **local obstruction theorem**.

## What would it *not* prove?

Even a completed Radius-4 local theorem would **not by itself**:

- prove the full Collatz conjecture;
- prove that every positive integer reaches `1`;
- prove that all Collatz trajectories are bounded;
- exclude every possible non-trivial cycle;
- prove anything automatically about other Hamming radii;
- prove that every hypothetical non-trivial cycle must exhibit a Radius-4 configuration.

That final step would require a separate **global bridge/encounter theorem** showing that every hypothetical non-trivial cycle necessarily generates an eligible Radius-4 configuration. The local Radius-4 theorem and such a global bridge are different results and will never be conflated in this repository.

## Formalisation status

| Component | Status |
|---|---|
| Collatz map | scaffolded in Lean |
| Cyclic binary words | scaffolded in Lean |
| Cyclic rotation | scaffolded in Lean |
| Hamming distance | scaffolded in Lean |
| Rotational primitivity | scaffolded in Lean |
| Cycle denominator `2^A - 3^L` | scaffolded in Lean |
| Exact Radius-4 definition | scaffolded in Lean |
| Collatz-cycle-to-word eligibility theorem | not yet formalised |
| Exact full-denominator eligibility condition | not yet formalised |
| Radius-4 local impossibility theorem | not yet formalised |
| Global Radius-4 bridge theorem | out of scope for the local proof |
| Full Collatz conjecture | not claimed |

"Scaffolded" means source code has been written for the definition or elementary lemma; CI is being installed so that the repository itself will record whether the current tree is accepted by Lean.

## Repository rule: every proof states its scope

Every substantial formalised result added here should be accompanied by plain-English documentation giving:

1. the theorem statement;
2. all important assumptions;
3. the Lean theorem name and source file;
4. what the theorem establishes;
5. what it does **not** establish;
6. any additional theorem that would be required to turn it into a stronger Collatz conclusion.

See [`docs/PROOF_SCOPE_POLICY.md`](docs/PROOF_SCOPE_POLICY.md).

## Building

The project uses Lean 4 and mathlib, pinned by the repository configuration.

```text
lake update
lake build
```

GitHub Actions is used as an independent build check once CI is present on `main`.
