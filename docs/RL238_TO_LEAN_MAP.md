# RL238 to Lean working map

Date: 2026-09-05

This file is a working formalisation map, not a theorem dependency.  The Lean
repository remains self-contained and authoritative for every formal statement.
The completed RL238/RL239 material is used only to identify the mathematical
propositions that must be reconstructed and proved here.

## Already kernel-verified infrastructure

The standalone repository already proves the following ingredients from genuine
`OddCycle` / `halfStep` data.

- genuine denominator-compatible parity word: `OddCycle.parityWord`;
- exact full denominator and genuine word arithmetic, including
  `OddCycle.fullDenominatorDivides_wordNumerator` and
  `OddCycle.wordNumerator_eq_prefixNumerator`;
- rotation/advance semantics:
  `OddCycle.rotate_parityWord_eq_advancedParityWord`;
- exact shifted-minus-base denominator identity:
  `OddCycle.cycleDenominator_mul_shiftedState_sub_base_eq_wordNumerator_difference`;
- nontrivial denominator bound:
  `OddCycle.positiveCycleDenominator_of_nontrivial`;
- weighted forcing composition:
  `OddCycle.shifted_wordNumerator_difference_eq_radiusWeightedRangeSum`;
- chronological/cyclic sum bridge:
  `OddCycle.shifted_wordNumerator_difference_eq_radiusWeightedCyclicSum`;
- exact four-boundary numerator representation under the existing Hamming
  hypothesis:
  `OddCycle.radiusFour_shifted_wordNumerator_difference_eq_four_terms`.

The last item is valid formal mathematics but its hypothesis is the old
Hamming-distance `IsRadiusFour`.  It is therefore support infrastructure only;
it is not the RL238 local theorem.

## First missing RL238 proposition: R4-1 transport geometry

RL238 uses cyclic adjacent-transposition transport distance, represented after a
cyclic cut by prefix flow

`G_k = (# target ones in the first k positions)
       - (# source ones in the first k positions)`

and cut cost

`sum_{k=1}^{A-1} |G_k|`.

Exact cyclic Radius 4 means the minimum cut cost is exactly four for equal-weight
words.  The exhaustive flow topologies are:

1. height-two `(1,2,1)`;
2. connected `[4]`;
3. `[3,1]`;
4. `[2,2]`;
5. `[2,1,1]`;
6. `[1,1,1,1]`.

`Collatz/Radius4Transport.lean` reconstructs this layer with separate
transport-flow names.  No equivalence with Hamming distance is assumed.

## R4-1 bridge status

Already proved on `main` before the present transport layer:

- cyclic rotation preserves word weight: `ones_rotate`.

Proved by the transport reconstruction through PR #26:

- binary local increments are in `{-1,0,1}`:
  `transportIncrement_eq_neg_one_or_zero_or_one`;
- prefix flow is one-Lipschitz:
  `transportPrefixFlow_step_natAbs_le_one`;
- exact Radius 4 is represented as a minimum-over-cuts prefix-flow cost:
  `IsExactTransportRadius` and `IsTransportRadiusFour`;
- the genuine parity-word wrapper is
  `OddCycle.IsCycleTransportRadiusFour`.

The current endpoint bridge proves the next required transport fact:

- a full prefix has value `ones target - ones source`:
  `transportPrefixFlow_full_eq_ones_sub_ones`;
- therefore equal-weight words satisfy `G_n = 0` at every cut:
  `transportPrefixFlow_full_eq_zero_of_ones_eq`;
- in particular every self-rotation satisfies the endpoint condition:
  `transportPrefixFlow_full_rotate_eq_zero`.

After this endpoint bridge is promoted, the first missing R4-1 propositions are:

- formal equivalence between the minimum-over-cuts prefix-flow formulation and
  the cyclic adjacent-transposition metric used by RL238;
- exhaustive classification of an exact cost-four minimizing flow into the six
  certified topology families;
- connection of each topology representation back to the rotated genuine
  `OddCycle.parityWord`.

Only after those bridges are proved may the established RL238 covariance and
elimination lemmas be translated.

## Exact hypothesis mismatches to keep explicit

### Hamming versus transport radius

`IsRadiusFour` and `OddCycle.IsCycleRadiusFour` currently mean Hamming distance
four.  RL238 does not.  The transport development uses separate predicates and
must not rewrite one notion into the other without a proved theorem.

### Primitivity

`OddCycle` and `OddCycle.IsNontrivial` do not assert that `c.parityWord` is
primitive.  The faithful final local theorem must therefore carry
`IsPrimitive c.parityWord` explicitly unless a separate reduction is proved.
No such reduction is currently claimed.

### External analytic ingredient

Later RL238 eliminations use an audited two-logarithm lower bound.  When that
step is reached, the formalisation must derive the needed inequality from a
formally available Mathlib theorem or identify the precise missing formal
external theorem.  It must not be introduced as an axiom.

## Remaining established proof order

After R4-1 is fully formalised, continue only in the established order:

1. connected height-two and `[4]` eliminations;
2. `[3,1]`;
3. `[2,2]`;
4. `[2,1,1]`;
5. `[1,1,1,1]` quotient-cycle reduction and final closure;
6. assemble the primitive full-denominator transport-Radius-4 local
   impossibility theorem.

No global Radius-4 encounter theorem, Radius 5, Gate A, or Gate B work belongs
in this repository task.
