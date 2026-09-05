# Theorem index

This file is the human-readable scope register for formal results in the repository. A theorem is listed here only after its statement exists in Lean source. The repository itself and Lean kernel remain authoritative.

## Foundations and exact Collatz-cycle model

### Ordinary and one-division maps

Source: `Collatz/Basic.lean`

The repository defines the ordinary Collatz map `step` and the one-division map `halfStep`, with exact odd/even branch lemmas. `halfStep` is used because one exact odd-to-odd edge of exponent `a` takes exactly `a` such transitions.

### `Collatz.OddToOddStep`

Source: `Collatz/OddCycle.lean`

Represents one exact positive odd-to-odd Collatz transition

`3*x + 1 = 2^a * y`

with positive odd source and target and positive exponent. Lean proves that the ordinary map and `halfStep` realise this transition exactly and that intermediate ordinary post-odd states are even until the stated odd target is reached.

### `Collatz.OddCycle`

Source: `Collatz/OddCycle.lean`

A cyclic family of positive odd nodes and positive exponents satisfying the exact odd-to-odd equations. Radius-4 assumptions are not built into this structure.

Important proved consequences include:

- `edge_reaches_next`;
- `edge_halfStep_reaches_next`;
- `prefixExponent_ge`;
- `length_le_totalExponent`;
- `totalExponent_pos`;
- `composed_identity`;
- `full_cycle_identity`;
- `node_zero_periodic`;
- `node_zero_halfStep_periodic`.

The represented period is not asserted to be minimal.

## Exact denominator arithmetic

### `Collatz.cycleDenominator`

Source: `Collatz/Cycle.lean`

Definition:

`cycleDenominator A L = 2^A - 3^L`.

### `Collatz.OddCycle.denominator_mul_base_eq_numerator`

Source: `Collatz/Cycle.lean`

Derived from the composed cycle equations:

`(2^A - 3^L) * x₀ = prefixNumerator L`.

### `Collatz.OddCycle.cycleDenominator_pos`

Source: `Collatz/Cycle.lean`

Proves `2^A - 3^L > 0` for every positive odd cycle.

### `Collatz.OddCycle.positiveCycleDenominator_of_nontrivial`

Source: `Collatz/NontrivialDenominator.lean`

Uses the theorem that denominator one forces `A = 2`, `L = 1`, and the trivial odd node `1`. Consequently every `OddCycle.IsNontrivial` satisfies

`1 < 2^A - 3^L`.

This strict denominator fact is derived, not assumed.

## Genuine parity-word arithmetic

### `Collatz.wordNumerator`

Source: `Collatz/WordArithmetic.lean`

The exact inhomogeneous numerator produced by composing a finite parity word. Its recursive form retains powers of three determined by later odd bits.

### `Collatz.realizes_composed_identity`

Source: `Collatz/WordArithmetic.lean`

For any realised finite Boolean parity word:

`2^(length bits) * y = 3^(listOnes bits) * x + wordNumerator bits`.

### `Collatz.orbitBits_realizes`

Source: `Collatz/WordArithmetic.lean`

The actual `halfStep` orbit realises its chronological parity list.

### `Collatz.OddCycle.orbitBits_total_ones`

Source: `Collatz/CycleWordArithmetic.lean`

For one full denominator-compatible cycle period of length `A`, the genuine parity list contains exactly `L` odd bits.

### `Collatz.OddCycle.wordDenominator_eq_cycleDenominator`

Source: `Collatz/CycleWordArithmetic.lean`

The denominator computed from the genuine full-period parity word equals the independently derived cycle denominator `2^A - 3^L`.

### `Collatz.OddCycle.cycleDenominator_mul_base_eq_wordNumerator`

Source: `Collatz/CycleWordArithmetic.lean`

Proves

`(2^A - 3^L) * x₀ = wordNumerator (orbitBits x₀ A)`.

### `Collatz.OddCycle.fullDenominatorDivides_wordNumerator`

Source: `Collatz/CycleWordArithmetic.lean`

The complete denominator divides the genuine parity-word numerator.

### `Collatz.OddCycle.wordNumerator_eq_prefixNumerator`

Source: `Collatz/CycleWordArithmetic.lean`

The parity-word numerator equals the independently composed odd-to-odd numerator.

## Genuine Radius-4 encoding and rotation

### `Collatz.OddCycle.parityWord`

Source: `Collatz/Encoding.lean`

A cyclic word of length `A` defined directly from the actual periodic `halfStep` orbit.

### `Collatz.OddCycle.rotate_parityWord_eq_advancedParityWord`

Source: `Collatz/RotationWord.lean`

Proves that cyclic rotation of the genuine parity word is exactly the parity word obtained by advancing the same periodic `halfStep` orbit.

### Shifted-origin denominator theorems

Source: `Collatz/RotationArithmetic.lean`

The repository proves that every shifted full-period orbit has the same `L` odd bits and the same complete denominator `2^A - 3^L`, and derives the exact full-denominator identity for every advanced starting state.

## Exact shifted-minus-base numerator comparison

### `Collatz.OddCycle.cycleDenominator_mul_shiftedState_sub_base_eq_wordNumerator_difference`

Source: `Collatz/RotationNumeratorComparison.lean`

For a genuine cyclic shift:

`D * (advancedState - baseState) = shiftedNumerator - baseNumerator`.

The numerator difference is the actual difference of the two genuine full-period `wordNumerator`s.

### Radius-4 nonzero consequence

Source: `Collatz/Radius4CycleConsequences.lean`

Exact Hamming distance four implies that the rotated genuine parity word differs from the base word. Using the rotation/advance bridge, Lean proves that the advanced `halfStep` state differs from the base state. Therefore the exact numerator difference above is nonzero.

This conclusion does not require a primitivity or minimality assumption.

## Radius-4 directional and boundary structure

### Directional balance

Sources: `Collatz/Radius4Structure.lean`, `Collatz/Radius4BoundaryPositions.lean`

Exact Radius 4 between a word and its rotation gives exactly two `true -> false` and two `false -> true` mismatches.

### Genuine Collatz boundary extraction

Source: `Collatz/Radius4CycleBoundaries.lean`

For the actual `OddCycle.parityWord`, Lean extracts four genuine cyclic orbit positions: two down-boundaries and two up-boundaries, all distinct in the required cross-directions.

## Weighted numerator expansion

### Weighted true-bit form of `wordNumerator`

Source: `Collatz/WordNumeratorWeights.lean`

Lean expands the finite-word numerator as weighted contributions of true bits. Each contribution has the form

`2^position * 3^(number of later true bits)`.

This theorem is essential because changing four parity bits can change the powers of three attached to common odd bits between mismatch boundaries.

## Sparse local difference forcing

### `Collatz.affineDifferenceOffset`

Source: `Collatz/Radius4SparseDifference.lean`

The inhomogeneous term obtained by subtracting two one-step affine Collatz recurrences.

Lean proves:

- equal parity bits give zero forcing;
- `true -> false` gives `-(2*x+1)`;
- `false -> true` gives `+(2*x+1)`;
- the forcing is nonzero exactly when the parity bits differ.

### `Collatz.OddCycle.radiusFour_sparse_difference_offsets`

Source: `Collatz/Radius4SparseDifference.lean`

Under exact Radius 4, the actual shifted/base orbit difference forcing is nonzero at exactly four genuine cyclic positions. The two down-boundaries have exact negative odd forcing and the two up-boundaries exact positive odd forcing.

## Exact weighted forcing composition

### Difference-forcing composition

Source: `Collatz/DifferenceForcingComposition.lean`

The repository proves the finite-orbit composition of the local state-difference recurrence. Each local forcing receives the exact chronological power of two and the exact shifted suffix odd-count power of three.

Consequently the actual shifted-minus-base `wordNumerator` difference is exactly the weighted composition of local forcing terms. Common odd bits between Radius-4 boundaries are therefore retained correctly rather than treated as unchanged-weight cancellations.

## Exact weighted Radius-4 support

### `Collatz.OddCycle.radiusDifferenceWeight`

Source: `Collatz/Radius4WeightedBoundarySupport.lean`

The exact positive weight attached to a cyclic local forcing:

`2^position * 3^(shifted suffix odd-count)`.

### `Collatz.OddCycle.radiusWeightedDifferenceTerm_ne_zero_iff`

Source: `Collatz/Radius4WeightedBoundarySupport.lean`

Weighting neither creates nor removes support: the weighted local term is nonzero exactly when the underlying local forcing is nonzero.

### `Collatz.OddCycle.radiusFour_weighted_difference_support`

Source: `Collatz/Radius4WeightedBoundarySupport.lean`

Under exact Radius 4 there are exactly four nonzero weighted cyclic terms. Their values are the exact positional/suffix weights multiplied by the two negative and two positive genuine Collatz odd forcings.

## Four-boundary cyclic sum collapse

Source: `Collatz/Radius4FourTermSum.lean`

The promoted Radius-4 finite-support theorem sums the cyclic weighted local terms over the whole encoding period and collapses the sum exactly to the four genuine mismatch boundaries.

The resulting expression is an exact four-term signed arithmetic object: two positive weighted odd forcings and two negative weighted odd forcings. No convenient ordering, smallness, indivisibility, primitivity, or minimality assumption is inserted.

## Current unpromoted range-sum bridge

Experimental development: PR #21, `DifferenceForcingRangeSum.lean`.

It introduces a telescoping potential for the pair of genuine `halfStep` orbits and proves the local telescoping identity and finite-range telescoping lemma. It also identifies an in-range natural index with the corresponding cyclic weighted term.

Its CI failed only in the final endpoint normalization needed to derive the full-period range-sum identity. The experimental branch is not authoritative and must be freshly transplanted onto current `main` before any promotion.

## Radius-4 local impossibility theorem

Status: **not proved**.

The next exact bridge is to identify the complete chronological weighted forcing range sum with the promoted cyclic weighted-term sum. Once that is green, the genuine shifted-minus-base numerator difference can be rewritten in the promoted four-boundary form.

The remaining mathematical question is then whether this exact four-term identity, together with the already-proved nonzero state-difference quotient and `D > 1` for a nontrivial cycle, yields the desired contradiction.

If not, the precise missing condition or counterexample must be isolated rather than added as an assumption by convenience.

## Scope limitations

The reverse extraction from an arbitrary ordinary positive periodic Collatz point into canonical `OddCycle` data is still separate from this local theorem.

Even a completed local Radius-4 impossibility theorem would not by itself rule out every hypothetical nontrivial Collatz cycle. A separate global encounter theorem would be needed to prove that every such cycle necessarily has an eligible Radius-4 rotation.
