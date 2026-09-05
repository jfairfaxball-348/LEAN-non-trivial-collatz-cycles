# RL238 to Lean working map

Date: 2026-09-05

This file maps the already-established RL238 mathematics into the standalone Lean development. It is not a theorem dependency. The Lean repository must prove every required proposition internally.

The research repository may be read only to recover the exact established theorem statements, conventions, and derivations. Do not import its code or artefacts and do not encode its conclusions as axioms.

## Existing Lean infrastructure

Already kernel-verified from genuine `OddCycle` / `halfStep` data:

- `OddCycle.parityWord`;
- full denominator arithmetic and genuine word numerator identities;
- `OddCycle.rotate_parityWord_eq_advancedParityWord`;
- exact shifted-minus-base denominator/numerator identities;
- `OddCycle.positiveCycleDenominator_of_nontrivial`;
- weighted forcing and exact four-boundary numerator formulas under the older Hamming Radius-4 hypothesis.

The Hamming results are valid support mathematics but are not RL238's transport-radius theorem.

## R4-1 transport geometry

RL238 uses cyclic adjacent-transposition transport distance. After a cyclic cut, define prefix flow

`G_k = (# target ones in first k positions) - (# source ones in first k positions)`

and cut cost

`sum_{k=1}^{A-1} |G_k|`.

For equal-weight words the endpoint is `G_A = 0`. Exact cyclic Radius 4 is the minimum cut cost being exactly four.

The six established exact-cost-four topology families are:

1. height-two `(1,2,1)`;
2. connected `[4]`;
3. `[3,1]`;
4. `[2,2]`;
5. `[2,1,1]`;
6. `[1,1,1,1]`.

## Promoted R4-1 Lean status

### Transport model — complete

`Collatz/Radius4Transport.lean` proves:

- `transportIncrement_eq_neg_one_or_zero_or_one`;
- `transportPrefixFlow_step_natAbs_le_one`;
- `transportPrefixFlow_full_eq_ones_sub_ones`;
- `transportPrefixFlow_full_eq_zero_of_ones_eq`;
- `transportPrefixFlow_full_rotate_eq_zero`;
- exact minimum-over-cuts definitions `IsExactTransportRadius`, `IsTransportRadiusFour`;
- genuine wrapper `OddCycle.IsCycleTransportRadiusFour`.

### Cost-four support — complete

`Collatz/Radius4TransportTopology.lean` proves:

- `transportCostAtCut_eq_sum_magnitudes`;
- `transportCostAtCut_eq_sum_active_magnitudes`;
- `transportCostAtCut_eq_active_card_of_unit`;
- `transportActiveEdgeOffsets_card_eq_four_of_cost_four_of_unit`.

Thus the unit-height cost-four branch has exactly four active internal edges.

### Height-two branch — complete

`Collatz/Radius4TransportHeightTwo.lean` proves:

- magnitude one-Lipschitz bounds in both directions;
- first/last internal height bounds;
- `transportFlowMagnitude_le_two_of_cost_four`;
- `exists_transportFlowMagnitude_eq_two_of_cost_four_of_not_unit`;
- `transportHeightTwo_rigid_of_cost_four`;
- `exists_transportHeightTwo_pattern_of_cost_four_of_not_unit`.

The complete non-unit cost-four branch is therefore exactly `(1,2,1)`.

## First missing RL238 proposition

Complete the unit-height half of the topology classification.

Starting from the already-proved fact that a unit-height cost-four minimizing cut has exactly four active internal edges, introduce a Lean representation of connected runs of consecutive active offsets and prove that the run lengths are exactly one of:

- `[4]`;
- `[3,1]`;
- `[2,2]`;
- `[2,1,1]`;
- `[1,1,1,1]`.

This should be a purely finite/combinatorial reconstruction of the established R4-1 classification. Do not search for a different classification or strengthen it.

The representation is free to be Lean-friendly so long as it faithfully records connected consecutive active-edge components and can feed the later RL238 topology eliminations.

## Remaining R4-1 bridge obligations

After the five unit-height families are classified, verify whether the blueprint needs any additional formal bridge for:

- equivalence between the prefix-flow minimum and the inherited cyclic adjacent-transposition metric;
- covariance of the chosen topology representation under cyclic cut/rotation;
- connection back to the genuine rotated `OddCycle.parityWord`.

Prove only the bridge actually required by the established RL238 proof.

## Exact hypothesis discipline

### Hamming versus transport

`IsRadiusFour` / `OddCycle.IsCycleRadiusFour` are Hamming notions. RL238 uses `IsTransportRadiusFour` / `OddCycle.IsCycleTransportRadiusFour`. Never substitute the Hamming theorem for transport radius without an explicit Lean proof.

### Primitivity

`OddCycle` and `OddCycle.IsNontrivial` do not imply primitive parity word. Preserve `IsPrimitive c.parityWord` explicitly if the final RL238 theorem requires it.

### Analytic inputs

Later RL238 eliminations use audited analytic reductions, including a two-logarithm lower bound. When reached, reproduce the exact established argument using formally available theorems. If a required external analytic theorem is not available in Mathlib, isolate that formalisation dependency precisely; do not introduce it as an axiom.

## Established proof order after R4-1

Translate only the already-proved RL238 route:

1. `(1,2,1)` and connected `[4]` eliminations;
2. `[3,1]`;
3. `[2,2]`;
4. `[2,1,1]`;
5. `[1,1,1,1]` quotient-cycle reduction and closure;
6. assemble the primitive full-denominator transport-Radius-4 local impossibility theorem.

When that theorem is kernel-verified, the repository task is complete.

No Radius 5, global encounter theorem, Gate A, Gate B, or new research objective belongs in this formalisation unless explicitly requested later.
