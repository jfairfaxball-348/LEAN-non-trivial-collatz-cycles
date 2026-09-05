# Formalisation roadmap

This roadmap describes the intended order of work inside this repository. Every mathematical dependency needed by a theorem must be defined or proved here; no unpublished or external argument is treated as an assumption.

## Stage 0 — Foundations

Status: **scaffolded and compiling**.

The project currently defines:

- the standard unaccelerated Collatz map on natural numbers;
- finite cyclic binary words;
- cyclic rotation;
- Hamming distance;
- rotational primitivity;
- the cycle denominator `2^A - 3^L`;
- exact Radius 4 as Hamming distance four from a nonzero cyclic rotation.

These definitions are only the vocabulary required for later theorems.

## Stage 1 — Odd-to-odd Collatz cycle arithmetic

Formalise the exact odd-to-odd step

`3x + 1 = 2^a y`

with `x` and `y` odd and `a >= 1` the exact two-adic exponent. Then define a finite hypothetical odd cycle and prove, inside Lean, the identities obtained by composing all odd-to-odd steps.

Required outcomes include:

- a precise cycle data structure;
- positivity and oddness conditions;
- exact two-adic exponents for each step;
- `L`, the number of odd nodes;
- `A`, the sum of the two-adic exponents;
- a proved derivation of the denominator `D = 2^A - 3^L`.

The existing `cycleDenominator` definition is notation only until this derivation is proved.

## Stage 2 — Collatz cycle encoding

Define the exact finite cyclic combinatorial object extracted from a hypothetical positive cycle and prove that the extraction preserves every property later used by Radius 4.

This stage must make explicit:

- what each bit means;
- the length of the cyclic word;
- how cyclic shifts correspond to changing the chosen starting point or comparing cycle data;
- why the relevant word is primitive in the cases where primitivity is assumed;
- which arithmetic quantities are invariant under rotation.

No theorem about an arbitrary `CyclicWord` should be advertised as a theorem about Collatz cycles until this encoding theorem exists.

## Stage 3 — Full-denominator eligibility

Derive the exact arithmetic quantity to which the complete denominator `D = 2^A - 3^L` applies.

The final predicate must be proved from the cycle equations rather than introduced as an unexplained hypothesis. In particular, this stage must distinguish divisibility by the full integer `D` from weaker congruence, factor, or residue conditions.

The current `FullDenominatorDivides` definition is only a generic divisibility relation and is not yet the Collatz-specific eligibility theorem.

## Stage 4 — Radius-4 local combinatorics

Develop the purely finite combinatorics of a primitive cyclic word and a nonzero shift whose Hamming distance is exactly four.

Any classification of the four changed positions, flow pattern, or topology must itself be formalised and shown exhaustive. Finite computation may be used only when its input domain and completeness are represented in Lean or otherwise checked by Lean's trusted kernel.

## Stage 5 — Radius-4 local impossibility theorem

Combine the Collatz eligibility results from Stages 1–3 with the Radius-4 combinatorics from Stage 4.

The intended theorem has the logical form:

> An eligible primitive positive Collatz-cycle encoding satisfying the exact full-denominator condition cannot possess a nonzero cyclic rotation at exact Hamming distance four.

The final Lean theorem must expose all mathematically meaningful assumptions in its type.

## Stage 6 — Scope and audit

For the completed local theorem:

- add a plain-English theorem statement;
- list every assumption;
- record the exact Lean theorem name and source file;
- explain what is proved;
- explain what is not proved;
- check that the proof contains no admitted gaps;
- keep CI green from a clean checkout.

## Separate future problem — global encounter theorem

A Radius-4 local impossibility theorem does **not** show that every hypothetical non-trivial Collatz cycle reaches an eligible Radius-4 configuration.

A separate global encounter or bridge theorem would be required for that conclusion. It is deliberately not folded into the local Radius-4 proof and should have its own statement, assumptions, documentation, and formalisation if attempted later.
