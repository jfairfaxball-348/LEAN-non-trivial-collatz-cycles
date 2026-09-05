# Theorem index

This file is the human-readable scope register for formal results in the repository. A theorem is listed here only after its statement exists in Lean source. The descriptions below distinguish elementary infrastructure from substantive Collatz results.

## Elementary Collatz-map checks

### `Collatz.step_one`

Source: `Collatz/Basic.lean`

Proves: one application of the defined Collatz map sends `1` to `4`.

Does not prove: termination, periodicity beyond this single step, or any part of the Collatz conjecture.

### `Collatz.step_two`

Source: `Collatz/Basic.lean`

Proves: one application of the defined Collatz map sends `2` to `1`.

Does not prove: termination for arbitrary inputs or absence of non-trivial cycles.

### `Collatz.step_four`

Source: `Collatz/Basic.lean`

Proves: one application of the defined Collatz map sends `4` to `2`.

Together with the two preceding checks, this verifies the familiar `1 -> 4 -> 2 -> 1` orbit for the map as defined. It does not classify any other orbit.

## Cyclic-word infrastructure

### `Collatz.rotate_zero`

Source: `Collatz/Basic.lean`

Proves: rotating a cyclic word by the zero shift leaves it unchanged.

Does not prove: anything specific to Collatz trajectories.

### `Collatz.hammingDistance_self`

Source: `Collatz/Basic.lean`

Proves: the Hamming distance from a finite cyclic binary word to itself is zero.

Does not prove: that a particular word encodes a Collatz cycle.

### `Collatz.primitive_nontrivial_rotation_ne`

Source: `Collatz/Basic.lean`

Assumptions: the word is rotationally primitive and the shift is nonzero.

Proves: the shifted word is not exactly equal to the original word.

Does not prove: a lower or upper bound on Hamming distance, Radius 4, or any Collatz-cycle obstruction.

## Radius-4 definitions and elementary consequences

### `Collatz.isRadiusFour_iff`

Source: `Collatz/Radius4.lean`

Proves: the predicate `IsRadiusFour w shift` is exactly the statement that `w` and `rotate w shift` have Hamming distance four.

This is a definitional theorem. It does not prove that Radius 4 is possible or impossible.

### `Collatz.hasRadiusFourRotation_iff`

Source: `Collatz/Radius4.lean`

Proves: `HasRadiusFourRotation w` is exactly the existence of a nonzero shift at Hamming distance four.

This is also definitional and contains no Collatz-specific eligibility claim.

### `Collatz.radiusFour_rotation_ne`

Source: `Collatz/Radius4.lean`

Assumption: the specified rotation is at exact Radius 4.

Proves: the rotated word is not exactly equal to the original word. The proof uses the fact that equal words have Hamming distance zero, contradicting exact distance four.

Primitivity and a separate nonzero-shift assumption are not needed for this elementary consequence.

This result does **not** prove the intended Radius-4 local impossibility theorem and does **not** exclude any Collatz cycle.

## Arithmetic definitions currently without substantive theorem claims

`Collatz.cycleDenominator`, `Collatz.PositiveCycleDenominator`, and `Collatz.FullDenominatorDivides` are definitions in `Collatz/Cycle.lean`. The file contains only small arithmetic examples checking those definitions.

The repository does not yet claim that an arbitrary pair `(A, L)` arises from a Collatz cycle, nor that `FullDenominatorDivides` is the final Collatz-specific full-denominator eligibility condition.

## Substantive target not yet proved

### Radius-4 local impossibility theorem

Status: **not yet formalised**.

Intended scope: eligible primitive positive Collatz-cycle encodings satisfying the exact full-denominator condition.

Intended conclusion: such an encoding cannot possess a nonzero rotation at exact Hamming distance four.

Even when completed, this will be a local obstruction theorem. It will not by itself prove the Collatz conjecture or exclude all non-trivial cycles, because a separate global encounter theorem would still be needed to show that every hypothetical non-trivial cycle necessarily produces an eligible Radius-4 configuration.
