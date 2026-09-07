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

R4-1 is complete. The authorized RL238 blueprint audit confirms that PR #33
provides the required cut normalization; no further general metric-equivalence
theorem is needed for the prefix-flow target.

Source: `Collatz/Radius4TransportCovariance.lean`.

- `transportIncrement_rotate_cut`;
- `transportPrefixFlow_rotate_cut`;
- `transportCostAtCut_rotate_cut`;
- `rotate_rotate_comm`;
- `transportCostAtCut_selfRotation_rotate_cut`;
- `transportRadiusFour_exists_rotated_zero_cut`;
- `OddCycle.cycleTransportRadiusFour_exists_advanced_zero_cut`.

PR #33 imports every intended transport module from the root and repairs the
Lean 4.34 elaboration failures that previous root builds had not exercised.
Its full local build and GitHub Actions Build passed before merge.

## R4-2 elementary prerequisites

These lemmas are prerequisites, not a completed height-two or connected `[4]`
elimination. All four modules are imported by `Collatz.lean`.
The full local root build passed with 8,912 jobs. All 27 new public lemmas were
also dependency-audited: only `propext`, `Classical.choice`, and `Quot.sound`
occur, with no research-conclusion or proof-placeholder axiom.

### Signed flow and height-two local bits

Source: `Collatz/Radius4TransportSigned.lean`.

- `transportIncrement_eq_one_iff`, `transportIncrement_eq_neg_one_iff`, and
  `transportIncrement_eq_zero_iff` identify the actual source/target bits.
- `transportPrefixFlow_succ_eq_of_magnitudes_eq_one` and
  `transportBits_eq_of_adjacent_magnitudes_eq_one` preserve the signed unit run
  and its unchanged interior bits.
- `transportHeightTwo_signed_of_magnitudes` refines magnitudes `(1,2,1)` to
  signed flows `(s,2*s,s)` for `s = 1` or `s = −1`.
- `transportHeightTwo_signed_of_cost_four`,
  `transportHeightTwo_flow_eq_zero_outside`, and
  `transportHeightTwo_local_bits_of_cost_four` derive the signed profile,
  zero flow off its three edges, and `0011 ↔ 1100` local bits from equal weight,
  exact cut cost four, and an internal magnitude-two edge.

### Exact local coefficients

Source: `Collatz/Radius4ConnectedCoefficients.lean`.

- `wordNumerator_localReplacement_difference` factors a replacement with equal
  local length and weight, in a common prefix/suffix, by `2^a * 3^b`.
- `transportConnectedFourCoefficient` and its `_mem` theorem give the eight
  coefficients `15,29,21,47,17,35,27,65` in Boolean lexicographic order.
- `wordNumerator_connectedFour_difference` proves
  `Q(0abc1) − Q(1abc0)` equals that coefficient.
- `wordNumerator_heightTwo_difference` proves `Q(1100) − Q(0011) = −15`.
- `wordNumerator_connectedFour_context_difference` and
  `wordNumerator_heightTwo_context_difference` retain the exact context factor.

### Coprime cancellation and finite denominators

Source: `Collatz/Radius4ConnectedDenominators.lean`.

- `cycleDenominator_isCoprime_six` assumes positive exponents `A,L`.
- `cycleDenominator_dvd_transport_context_iff` cancels `2^a * 3^b` from
  divisibility by the **full** integer denominator, with the same exponent hypotheses.
- `cycleDenominator_dvd_connectedFourCoefficient_of_context_difference` and
  `cycleDenominator_dvd_fifteen_of_heightTwo_context_difference` explicitly assume
  full-denominator divisibility of the common-context numerator difference.
- `transportConnected_denominator_mem` and
  `transportConnectedFour_denominator_mem` prove the natural divisor list
  `5,7,13,17,29,35,47,65`, assuming `d > 1`, `d.Coprime 6`, and the stated
  coefficient divisibility. The finite certificate is proved by kernel `decide`.
- `transportHeightTwo_denominator_eq_five` specializes the same strict and
  coprime hypotheses to `d ∣ 15`.

No lemma here silently identifies an arbitrary natural divisor with the full
cycle denominator; that application remains part of the geometry/arithmetic glue.

### Elementary logarithmic defect

Source: `Collatz/Radius4LogDefect.lean`.

- `cycleDenominator_log_defect_eq` identifies
  `A log 2 − L log 3 = log (1 + D/3^L)` with the exact full denominator.
- `cycleDenominator_log_defect_pos` and
  `cycleDenominator_log_defect_lt_ratio` assume `0 < D`.
- `cycleDenominator_log_defect_lt_sixty_five` assumes `0 < D ≤ 65`.
- `cycleDenominator_exponent_lt_twice_of_le_sixty_five` proves `A < 2L`
  under `D ≤ 65` and `4 ≤ L`.

None of these elementary lemmas asserts an LMN lower bound or the cutoff `L < 7000`.

## Analytic dependency for the first elimination

The height-two and connected `[4]` elimination already requires the explicit
LMN two-logarithm lower bound. No equivalent theorem was located in pinned
Mathlib. See `docs/RL238_ANALYTIC_DEPENDENCY.md` for the exact proposition and
the audited support. It is not an axiom or hypothesis in any Lean theorem.

## Radius-4 local impossibility theorem

Status: **not yet kernel-verified in this repository**.

The mathematics is already established in the research repository. The remaining task here is faithful reconstruction and formal verification, not discovery.

With R4-1 complete, translate the established elimination chain in this order:

1. `(1,2,1)` and connected `[4]`;
2. `[3,1]`;
3. `[2,2]`;
4. `[2,1,1]`;
5. `[1,1,1,1]` and the final quotient-cycle closure;
6. assemble the primitive full-denominator transport-Radius-4 local theorem.

## Scope limitation

Do not treat the local theorem as a global non-trivial-cycle exclusion theorem. No Radius 5, Gate A, Gate B, or global encounter work is part of the present repository objective unless explicitly requested later.
