# Word arithmetic bridge: scope and next dependency

This note records the exact role of `Collatz/WordArithmetic.lean` in the Radius-4 dependency chain.

## What is formalised

The file defines a finite binary affine word. Each bit encodes one equation of the form

- even bit: `2*y = x`;
- odd bit: `2*y = 3*x + 1`.

`Collatz.realizes_composed_identity` proves from those local equations that a realised word `bits` from `x` to `y` satisfies

`2^(bits.length) * y = 3^(listOnes bits) * x + wordNumerator bits`.

No Collatz assumption is used in that pure composition theorem.

The file then connects the actual one-division Collatz map `halfStep` to this affine language. `Collatz.orbitBits_realizes` proves that the chronological parity bits of a `halfStep` orbit realise the local equations. Consequently `Collatz.periodic_word_denominator_identity` proves that any closed `halfStep` orbit satisfies

`(2^k - 3^(number of odd states)) * x = wordNumerator`.

`Collatz.periodic_word_fullDenominatorDivides` records divisibility by that entire denominator.

## What this does not yet prove

For an `OddCycle L`, the separately derived denominator is `2^A - 3^L`, where `A = totalExponent`.

The word-level theorem currently yields `2^A - 3^(listOnes (orbitBits x A))`.

The next required bridge is therefore an equality of odd counts:

`listOnes (orbitBits (c.node 0) c.totalExponent) = L`.

Equivalently, one may prove that the actual `halfStep` parity word equals the exponent-boundary marker word and then count its marked positions.

A second required bridge concerns cyclic indexing: the finite chronological list and the `ZMod A` parity word in `Collatz/Encoding.lean` must be shown to represent the same period, and cyclic rotation must be identified with rebasing the periodic orbit.

Until those bridges are proved, the word arithmetic theorem is not advertised as the final Radius-4 full-denominator eligibility theorem.

## Radius-4 boundary

No contradiction from Hamming distance four is proved here. The Radius-4 local impossibility theorem remains open. This note does not assert that every non-trivial cycle encounters Radius 4, and it does not imply a global no-cycle theorem.
