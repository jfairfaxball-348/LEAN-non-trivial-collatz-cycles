# Word arithmetic bridge: proved scope and next dependency

This note records the exact role of `Collatz/WordArithmetic.lean` and `Collatz/CycleWordArithmetic.lean` in the Radius-4 dependency chain.

## Pure finite-word arithmetic

`Collatz.WordArithmetic` defines a finite binary affine word. Each bit encodes one equation of the form

- even bit: `2*y = x`;
- odd bit: `2*y = 3*x + 1`.

`Collatz.realizes_composed_identity` proves from those local equations that a realised word `bits` from `x` to `y` satisfies

`2^(bits.length) * y = 3^(listOnes bits) * x + wordNumerator bits`.

No Collatz-cycle hypothesis is used in that pure composition theorem.

The file then connects the actual one-division Collatz map `halfStep` to this affine language. `Collatz.orbitBits_realizes` proves that the chronological parity bits of a `halfStep` orbit realise the local equations. Consequently `Collatz.periodic_word_denominator_identity` proves that any closed `halfStep` orbit satisfies

`(2^k - 3^(number of odd source states)) * x = wordNumerator`.

`Collatz.periodic_word_fullDenominatorDivides` records divisibility by that entire word denominator.

## Collatz-specific parity-count bridge

`Collatz.OddToOddStep.orbitBits_ones` proves that one exact odd-to-odd block with exponent `a` contributes exactly one odd source bit among its `a` `halfStep` transitions.

`Collatz.OddCycle.orbitBits_prefix_ones` composes those block counts. In particular,

`Collatz.OddCycle.orbitBits_total_ones`

proves for an `OddCycle L` with total exponent `A` that

`listOnes (orbitBits (c.node 0) A) = L`.

This closes the earlier gap between the exponent count `L` and the actual chronological parity list.

## Full denominator on the genuine parity orbit

Using the proved odd-count equality, `Collatz.OddCycle.wordDenominator_eq_cycleDenominator` proves that the denominator computed directly from the actual `A`-step parity list is exactly

`2^A - 3^L`.

`Collatz.OddCycle.cycleDenominator_mul_base_eq_wordNumerator` then proves

`(2^A - 3^L) * x_0 = wordNumerator (orbitBits x_0 A)`.

`Collatz.OddCycle.fullDenominatorDivides_wordNumerator` records divisibility by the complete integer denominator, not by a proper factor or a residue surrogate.

Finally, `Collatz.OddCycle.wordNumerator_eq_prefixNumerator` proves that this parity-word numerator is exactly the same natural number as the independently derived numerator obtained by composing the odd-to-odd exponent blocks.

## What remains open

These theorems do not yet identify an arbitrary cyclic rotation of `OddCycle.parityWord` with the chronological parity list obtained by advancing the same periodic orbit. They therefore do not yet provide the shift-specific numerator comparison required by the Radius-4 contradiction.

The next local bridge is:

1. prove that advancing the `A`-periodic `halfStep` orbit by a cyclic shift gives the corresponding rotation of the parity word;
2. derive the complete `2^A - 3^L` identity for the numerator read from that advanced/rotated origin;
3. compare the base and shifted numerators under exact Hamming distance four.

The separate arithmetic marker word `OddCycle.oddStartWord` remains useful if a closed form in cumulative exponent positions is needed, but equality `oddStartWord = parityWord` is not required merely to establish the full denominator for the chronological parity list.

No Radius-4 contradiction is proved in these files. They do not assert that every hypothetical non-trivial cycle encounters Radius 4, and they imply no global no-cycle theorem.
