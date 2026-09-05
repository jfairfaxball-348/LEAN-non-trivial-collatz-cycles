# Formalisation roadmap

This roadmap describes the intended order of work inside this repository. Every mathematical dependency needed by a theorem must be defined or proved here; no unpublished or external argument is treated as an assumption.

## Stage 0 — Foundations

Status: **complete as infrastructure**.

The project defines:

- the standard unaccelerated Collatz map `step` on natural numbers;
- the derived one-division map `halfStep`;
- finite cyclic binary words;
- cyclic rotation;
- Hamming distance;
- rotational primitivity;
- the integer expression `2^A - 3^L`;
- exact Radius 4 as Hamming distance four from a nonzero cyclic rotation.

These definitions alone do not assert a Collatz obstruction.

## Stage 1 — Odd-to-odd Collatz cycle arithmetic

Status: **substantive forward direction proved; reverse extraction still open**.

The repository now formalises the exact odd-to-odd step

`3x + 1 = 2^a y`

with positive odd `x,y` and positive exponent `a`.

Lean proves:

- the local equation is realised by the ordinary Collatz map;
- every earlier ordinary post-odd state is even and the stated endpoint is odd;
- the same edge takes exactly `a` iterations of `halfStep`;
- a positive cyclic odd-cycle structure `OddCycle L`;
- `A`, the sum of its exponents, satisfies `L ≤ A` and `A > 0`;
- composition of the first `k` odd-to-odd equations;
- one full ordinary traversal returns the base odd node after `A+L` steps;
- one full `halfStep` traversal returns the base odd node after exactly `A` steps.

The remaining Stage-1 bridge, if the final theorem is stated from the most general ordinary-cycle hypothesis, is:

> **ordinary-cycle extraction lemma** — every hypothetical positive periodic orbit of the ordinary map can be rebased at an odd state and converted to an `OddCycle` with the exact exponent data above.

The current local development instead begins from explicit `OddCycle` data and proves that it genuinely gives an ordinary periodic orbit. That direction is fully explicit and not assumed.

## Stage 2 — Collatz cycle encoding

Status: **genuine parity word defined; rotation bridge incomplete**.

The denominator-compatible encoding uses `halfStep`, not the `A+L` ordinary-step traversal. This was a substantive representation correction: since each odd-to-odd exponent contributes exactly that many one-division transitions, the natural cyclic length is `A`, matching `2^A - 3^L`.

The repository now defines `OddCycle.parityWord`, a `CyclicWord A` whose bit at a cyclic position records whether the actual `halfStep` orbit state is odd.

It also defines cumulative exponent positions and an arithmetic marker word `oddStartWord`. Every marked exponent boundary is proved to be an actual odd state.

Next required encoding lemmas:

1. **marker/parity equality** — prove `oddStartWord = parityWord` by showing all non-boundary positions inside each exponent block are even;
2. **rotation/advance theorem** — prove that rotating `parityWord` by a cyclic shift corresponds to advancing the same periodic `halfStep` orbit by that shift;
3. **odd-node rebase theorem** — for shifts landing on odd positions, connect the rotated word to `OddCycle.rebase` and prove the relevant exponent/denominator invariants;
4. **primitivity bridge** — only if the final local theorem requires primitive words, prove exactly which cycle minimality/non-repetition hypothesis implies `IsPrimitive parityWord`.

No primitivity or rotation identity is to be inserted as an unexplained eligibility assumption.

## Stage 3 — Full-denominator arithmetic

Status: **base numerator divisibility proved; shift-specific relation still open**.

From the full composed cycle identity Lean now derives

`(2^A - 3^L) * x_0 = N`,

where `N = prefixNumerator L` is generated recursively from the local cycle equations.

Consequently Lean proves:

- `2^A - 3^L > 0`;
- the complete integer denominator `D = 2^A - 3^L` divides `N`;
- the quotient is the base odd node `x_0`.

This replaces the previous state in which `FullDenominatorDivides` was only generic vocabulary.

However, the final Radius-4 obstruction is expected to compare a parity word with a rotation. The next arithmetic theorem must therefore derive, not assume, the corresponding numerator for an advanced/rebased orbit and the exact full-`D` divisibility relation for the relevant difference or comparison expression.

Do not substitute a factor of `D`, a residue surrogate, or a hand-stated shifted numerator condition.

## Stage 4 — Radius-4 local combinatorics

Status: **pure definitions only; substantive attack waits on Stage-2/3 bridge**.

The generic cyclic-word layer already defines exact Radius 4. The Collatz encoding layer now defines `OddCycle.IsCycleRadiusFour` and `OddCycle.HasCycleRadiusFourRotation` for the genuine length-`A` parity word.

Before a sparse four-position contradiction can be attacked honestly, the rotation/advance and shift-specific denominator lemmas from Stages 2–3 must exist.

Then develop the finite combinatorics of a nonzero shift whose Hamming distance is exactly four. Any classification of the four changed positions must be formalised and exhaustive.

## Stage 5 — Radius-4 local impossibility theorem

Status: **not yet stated as a proved Collatz theorem**.

Only after Stages 2–4 are precise should the final theorem be stated. Its intended logical form remains:

> An eligible primitive positive Collatz-cycle encoding satisfying the exact full-denominator condition cannot possess a nonzero cyclic rotation at exact Hamming distance four.

The final Lean theorem must expose all mathematically meaningful assumptions in its type. In particular, it must not hide the cycle-to-word bridge, primitivity bridge, or shift-specific full-denominator relation inside definitions that merely assume the desired property.

## Stage 6 — Scope and audit

For any promoted substantive checkpoint:

- update `docs/THEOREM_INDEX.md`;
- explain all assumptions and limitations;
- check for `sorry`/`admit` or equivalent gaps;
- run the full Lean build with warnings as errors;
- keep `main` coherent and self-contained.

For a completed local theorem, additionally record the exact theorem name, source file, full assumptions, supporting chain, and the still-separate global encounter problem.

## Separate future problem — global encounter theorem

A Radius-4 local impossibility theorem does **not** show that every hypothetical non-trivial Collatz cycle reaches an eligible Radius-4 configuration.

A separate global encounter or bridge theorem would be required for that conclusion. It is deliberately not folded into the local Radius-4 proof and should have its own statement, assumptions, documentation, and formalisation if attempted later.
