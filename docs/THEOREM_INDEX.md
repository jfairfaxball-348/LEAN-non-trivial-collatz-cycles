# Theorem index

This file is the human-readable scope register for the current formalisation. The Lean source and kernel remain authoritative.

## Foundations and exact Collatz-cycle model

The repository contains the ordinary Collatz map, the one-division `halfStep` map, exact odd-to-odd transitions, `OddCycle`, the genuine denominator-compatible parity word, cyclic rotation, and the full denominator arithmetic needed by the Radius-4 development.

Important existing theorem families include:

- exact odd-to-odd and `halfStep` realisation in `Collatz/OddCycle.lean`;
- `cycleDenominator A L = 2^A - 3^L` and the positive denominator identities in `Collatz/Cycle.lean`;
- `OddCycle.positiveCycleDenominator_of_nontrivial` in `Collatz/NontrivialDenominator.lean`;
- genuine full-period parity-word arithmetic in `Collatz/CycleWordArithmetic.lean`;
- `OddCycle.rotate_parityWord_eq_advancedParityWord` in `Collatz/RotationWord.lean`;
- exact shifted-origin/full-denominator comparison in the rotation arithmetic files.

`OddCycle` does not assert a minimal represented period or primitivity.

## Earlier Hamming/four-boundary arithmetic infrastructure

The repository also kernel-verifies a substantial Radius-4 arithmetic chain under the older Hamming predicate `IsRadiusFour`, including directional mismatch balance, four genuine mismatch boundaries, weighted local difference forcing, chronological/cyclic weighted-sum identities, and an exact four-term representation of the genuine shifted-minus-base numerator difference.

Key theorem:

- `OddCycle.radiusFour_shifted_wordNumerator_difference_eq_four_terms`.

This mathematics remains valid but its Radius-4 hypothesis is Hamming distance. It is support infrastructure only and must not be identified with the RL238 adjacent-transposition transport theorem.

## RL238 transport-radius model

Source: `Collatz/Radius4Transport.lean`.

### Definitions

- `transportBitValue`
- `transportIncrement`
- `transportPrefixFlow`
- `transportCostAtCut`
- `IsExactTransportRadius`
- `IsTransportRadiusFour`
- `OddCycle.IsCycleTransportRadiusFour`

The cut flow is

`G_k = (# target ones in the first k positions) - (# source ones in the first k positions)`

and the charged cost is

`sum_{k=1}^{n-1} |G_k|`.

Exact transport radius is represented as the minimum of this cost over cyclic cuts for equal-weight words.

### Local increment and endpoint theorems

Promoted theorems include:

- `transportIncrement_eq_neg_one_or_zero_or_one`;
- `transportPrefixFlow_succ`;
- `transportPrefixFlow_step_natAbs_le_one`;
- `transportPrefixFlow_full_eq_ones_sub_ones`;
- `transportPrefixFlow_full_eq_zero_of_ones_eq`;
- `transportPrefixFlow_full_rotate_eq_zero`;
- `transportRadiusFour_exists_minimizing_cut`;
- `transportRadiusFour_cost_ge_four`.

Thus the formal prefix flow is one-Lipschitz and has the correct zero endpoint for equal-weight words and genuine self-rotations.

## Cost-four active-support decomposition

Source: `Collatz/Radius4TransportTopology.lean`.

Definitions and theorems:

- `transportFlowMagnitude`;
- `transportActiveEdgeOffsets`;
- `transportCostAtCut_eq_sum_magnitudes`;
- `transportCostAtCut_eq_sum_active_magnitudes`;
- `transportCostAtCut_eq_active_card_of_unit`;
- `transportActiveEdgeOffsets_card_eq_four_of_cost_four_of_unit`.

Consequences:

- zero-flow internal edges may be discarded without changing cost;
- in the unit-height branch of a cost-four cut, exactly four internal edges are active.

## Rigid height-two topology

Source: `Collatz/Radius4TransportHeightTwo.lean`.

Promoted theorems include:

- `transportFlowMagnitude_succ_le_add_one`;
- `transportFlowMagnitude_le_succ_add_one`;
- `transportFlowMagnitude_one_le_one`;
- `transportFlowMagnitude_last_le_one_of_ones_eq`;
- `transportMagnitudeSum_le_cost_of_subset`;
- `transportFlowMagnitude_le_two_of_cost_four`;
- `exists_transportFlowMagnitude_eq_two_of_cost_four_of_not_unit`;
- `transportHeightTwo_rigid_of_cost_four`;
- `exists_transportHeightTwo_pattern_of_cost_four_of_not_unit`.

The final theorem proves the complete non-unit equal-weight cost-four branch has exactly the RL238 height profile `(1,2,1)`.

## Unit-height connected-component topology

Source: `Collatz/Radius4TransportComponents.lean`.

Promoted definitions:

- `consecutiveOffsetRuns`;
- `consecutiveOffsetRunLengths`;
- `transportActiveEdgeOffsetList`;
- `transportActiveEdgeRuns`;
- `transportActiveEdgeRunLengths`.

The active offsets are placed in natural increasing order and decomposed into maximal consecutive runs. The concrete ordered component list is retained for later topology-specific use.

Key promoted theorem:

- `transportActiveEdgeRunLengths_family_of_cost_four_of_unit`.

At any cost-four unit-height cut, the four active internal edges have connected-run lengths, up to permutation of disconnected components, in exactly one of the five established RL238 families:

- `[4]`;
- `[3,1]`;
- `[2,2]`;
- `[2,1,1]`;
- `[1,1,1,1]`.

The use of `List.Perm` is only the family classification: orientations such as `[1,3]` are the same `[3,1]` topology family, while `transportActiveEdgeRuns` preserves the actual ordered components.

## Current R4-1 status

The finite exact-cost-four topology classification is **kernel-verified and green**:

- non-unit branch: `(1,2,1)`;
- unit-height branch: `[4]`, `[3,1]`, `[2,2]`, `[2,1,1]`, `[1,1,1,1]`.

Before topology-specific arithmetic elimination begins, consult the authoritative RL238 Radius-4 blueprint and formalise only any remaining bridge it actually requires between this prefix-flow/component representation and the inherited cyclic adjacent-transposition / rotation / genuine `OddCycle.parityWord` statement.

No such bridge should be invented merely for generality.

## Radius-4 local impossibility theorem

Status: **not yet kernel-verified in this repository**.

The mathematics is already established in the research repository. The remaining task here is faithful reconstruction and formal verification, not discovery.

After R4-1 is fully connected to the exact RL238 statement, translate the established elimination chain in this order:

1. `(1,2,1)` and connected `[4]`;
2. `[3,1]`;
3. `[2,2]`;
4. `[2,1,1]`;
5. `[1,1,1,1]` and the final quotient-cycle closure;
6. assemble the primitive full-denominator transport-Radius-4 local theorem.

## Scope limitation

Do not treat the local theorem as a global non-trivial-cycle exclusion theorem. No Radius 5, Gate A, Gate B, or global encounter work is part of the present repository objective unless explicitly requested later.
