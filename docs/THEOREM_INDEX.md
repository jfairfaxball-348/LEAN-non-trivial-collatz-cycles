# Theorem index

This index records the meaning and scope of the verified library. The final
local impossibility theorem is unproved. Verified status refers to the main
revision and build evidence in [CURRENT_CHECKPOINT.md](CURRENT_CHECKPOINT.md).

## Model and notation

The ordinary Collatz map halves even `x` and sends odd `x` to `3*x+1`. Its
familiar positive cycle is `1 → 4 → 2 → 1`. The auxiliary `halfStep` map
also divides the odd result by two, giving a binary parity word of length
`A` with `L` odd source positions. Bits are written as zero and one.

An `OddCycle L` records positive odd nodes and positive exponents satisfying
`3*x_i+1 = 2^a_i*x_(i+1)`, with `A = sum a_i`. For a chronological list,
`Q = wordNumerator` satisfies `Q([])=0` and
`Q(b::bs)=3^(listOnes bs)*bitOffset b+2*Q(bs)`. `bitOffset` is the bit's
zero-or-one value, and `listOnes` counts ones. The full integer denominator
is `D = 2^A-3^L`.

The generic target retains `0 < L < A`, `D > 1`, `D ∣ Q(w)`, primitivity,
and a nonzero self-rotation shift. Primitivity means only the zero rotation
fixes the cyclic word. The target excludes exact transport radius four,
defined below. These explicit arithmetic and word hypotheses must not be
replaced by an unstated cycle assumption.

## Foundations and exact Collatz-cycle model

The repository contains the ordinary Collatz map, the one-division `halfStep` map, exact odd-to-odd transitions, `OddCycle`, the genuine denominator-compatible parity word, cyclic rotation, and the full denominator arithmetic needed by the Radius-4 development.

Important existing theorem families include:

- exact odd-to-odd and `halfStep` realisation in `Collatz/OddCycle.lean`;
- `cycleDenominator A L = 2^A - 3^L` and the positive denominator identities in `Collatz/Cycle.lean`;
- `OddCycle.positiveCycleDenominator_of_nontrivial` in
  `Collatz/NontrivialDenominator.lean`, proving `D > 1` from
  `c.IsNontrivial`, meaning at least one odd node is not `1`;
- genuine full-period parity-word arithmetic in `Collatz/CycleWordArithmetic.lean`;
- `OddCycle.rotate_parityWord_eq_advancedParityWord` in `Collatz/RotationWord.lean`;
- exact shifted-origin/full-denominator comparison in the rotation arithmetic files.

`OddCycle` does not assert a minimal represented period or primitivity.

## Earlier Hamming/four-boundary arithmetic infrastructure

The repository also kernel-verifies a substantial Radius-4 arithmetic chain under the older Hamming predicate `IsRadiusFour`, including directional mismatch balance, four genuine mismatch boundaries, weighted local difference forcing, chronological/cyclic weighted-sum identities, and an exact four-term representation of the genuine shifted-minus-base numerator difference.

Key theorem:

- `OddCycle.radiusFour_shifted_wordNumerator_difference_eq_four_terms`.

Hamming distance counts unequal word positions. These results remain valid
under their stated Hamming hypotheses, but do not establish the transport
hypothesis or the intended transport impossibility theorem.

## Transport-radius model

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

Thus the formal prefix flow changes by at most one per position and has
endpoint zero for equal-weight words and genuine self-rotations.

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

The final theorem in this module proves that an equal-weight cost-four cut
with some internal magnitude greater than one has exactly three consecutive
nonzero magnitudes `(1,2,1)`, exhausting the cost. This classifies the branch;
it does not exclude it arithmetically.

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

An active edge is an internal boundary with nonzero prefix flow. At a
cost-four unit-height cut, the four active edges have maximal consecutive-run
lengths, up to permutation of disconnected components, in one of five families:

- `[4]`;
- `[3,1]`;
- `[2,2]`;
- `[2,1,1]`;
- `[1,1,1,1]`.

The use of `List.Perm` is only the family classification: orientations such as `[1,3]` are the same `[3,1]` topology family, while `transportActiveEdgeRuns` preserves the actual ordered components.

## Verified classification and cut normalization

The finite exact-cost-four topology classification is **kernel-verified and green**:

- non-unit branch: `(1,2,1)`;
- unit-height branch: `[4]`, `[3,1]`, `[2,2]`, `[2,1,1]`, `[1,1,1,1]`.

The finite classification and cut normalization are complete for the
minimum-over-cuts prefix-flow definition used here.

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

## Elementary prerequisites for the first exclusions

These lemmas are prerequisites, not a completed height-two or connected `[4]`
elimination. All four modules are imported by `Collatz.lean`.
PR #34 promoted this layer with green PR and post-merge main Builds.
The full local root build passed with 8,912 jobs. All 27 new public lemmas were
also dependency-audited: only the standard core axioms `propext`,
`Classical.choice`, and `Quot.sound` occur, with no additional mathematical
axiom or proof placeholder.

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

- `wordNumerator_localReplacement_difference` assumes equal local lengths and
  equal local numbers of ones, in a common prefix `pre` and suffix `suffix`.
  It factors the target-minus-source integer numerator difference by exactly
  `2^(pre.length) * 3^(listOnes suffix)`.
- `transportConnectedFourCoefficient` and
  `transportConnectedFourCoefficient_mem` give the eight
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

None of these elementary lemmas asserts the required quantitative
logarithmic lower bound or the cutoff `L < 7000`.

## Unverified work and analytic dependency

New component helpers and a height-two outside-bit agreement lemma in
`Collatz/Radius4TransportSigned.lean`, together with
`Collatz/CyclicWordList.lean`, `Collatz/Radius4WordRotation.lean`,
`Collatz/Radius4FullDenominatorWord.lean`,
`Collatz/Radius4TransportConnectedBits.lean`,
`Collatz/Radius4TransportLocalWords.lean`, and
`Collatz/Radius4ConnectedBounds.lean`,
on branch `codex/r4-local-word-bridge`, pass a full local root build and an
audit of the bridge/application theorem dependencies. The audit finds only
`propext`, `Classical.choice`, and `Quot.sound`; no CI promotion is claimed
for this newer revision.

### Working-branch inventory — locally validated, not CI-promoted

The following are the 24 new public lemma statements in the current source.
Their descriptions specify the intended application boundary.

`Collatz/CyclicWordList.lean` defines `cyclicWordList`, the chronological list
of a cyclic word's bits starting at position zero, and contains eight lemmas:

- `length_cyclicWordList` and `getElem_cyclicWordList` identify its length
  and indexed entries.
- `cyclicWordList_rotate` identifies rotation of a nonempty cyclic word
  with rotation of its chronological list.
- `listOnes_eq_sum_map` expresses a list's weight as the sum of its bit values.
- `listOnes_cyclicWordList` identifies list weight with cyclic weight for a
  nonempty word.
- `take_drop_eq_of_getElem_eq_outside` gives equal prefixes and suffixes for
  equal-length lists agreeing outside a specified interval.
- `shared_prefix_suffix_of_getElem_eq_outside` gives the complete common-context
  decomposition when that interval lies within the lists.
- `cyclicWordList_take_drop_eq_of_eq_outside` carries pointwise cyclic
  agreement outside an interval into equal list prefixes and suffixes.

`Collatz/Radius4WordRotation.lean` contains three generic list-arithmetic lemmas:

- `wordNumerator_blockSwap_covariance` gives the exact integer numerator
  identity for exchanging two consecutive blocks.
- `cycleDenominator_dvd_wordNumerator_blockSwap` preserves source-numerator
  divisibility by the full denominator under that exchange, assuming
  positive total length and positive total weight.
- `cycleDenominator_dvd_wordNumerator_rotate` carries the same divisibility
  through any natural-number list rotation under the corresponding hypotheses.

`Collatz/Radius4FullDenominatorWord.lean` contains five application lemmas:

- `cycleDenominator_dvd_cyclicWordList_rotate` preserves full-denominator
  source-numerator divisibility under rotation of an arbitrary nonempty
  positive-weight cyclic word.
- `cycleDenominator_dvd_cyclicWordList_rotate_sub` derives divisibility of
  the rotated-minus-source numerator difference from that source hypothesis.
- `cycleDenominator_natAbs_mem_of_dvd_connectedFourCoefficient` applies the
  finite divisor list to the absolute value of the actual full denominator,
  assuming positive length and weight, `D > 1`, and connected-coefficient
  divisibility.
- `cycleDenominator_le_sixty_five_of_dvd_connectedFourCoefficient` concludes
  `D ≤ 65` under those same hypotheses.
- `cycleDenominator_eq_five_of_dvd_fifteen` concludes `D = 5` from positive
  length and weight, `D > 1`, and `D ∣ 15`.

The existing component and signed-flow modules gain three lemmas:

- `consecutiveOffsetRunLengths_four_connected_iff`, in
  `Collatz/Radius4TransportComponents.lean`, characterizes when four offsets
  have the single-run family label `[4]` by successive offset equalities.
- `transportActiveEdgeOffsetList_eq_four_consecutive_of_connected`, in the
  same file, extracts the actual ordered list `[p,p+1,p+2,p+3]` from cost-four,
  unit-height, connected-family hypotheses, with `p+4 < n`.
- `transportHeightTwo_bits_eq_outside_of_cost_four`, in
  `Collatz/Radius4TransportSigned.lean`, gives source/target bit agreement
  outside the four-position height-two window, assuming equal weight,
  cut cost four, and an internal magnitude-two edge.

`Collatz/Radius4TransportConnectedBits.lean` contains
`transportConnectedFour_local_bits_of_cost_four`. Under equal weight, cut
cost four, unit height, and family label `[4]`, its statement extracts the
endpoint exchange `1abc0 ↔ 0abc1`, with all three interior bits and every
bit outside the five-position window unchanged. It retains the actual cut
and the bounded chronological window.

`Collatz/Radius4TransportLocalWords.lean` contains two common-context statements:

- `transportConnectedFour_exists_word_context_of_cost_four` writes the
  complete chronological source and target lists with the same prefix and
  suffix around `1abc0 ↔ 0abc1`, under equal weight and the connected
  unit-height cost-four hypotheses at cut zero.
- `transportHeightTwo_exists_word_context_of_cost_four` gives the corresponding
  common-context lists around `0011 ↔ 1100`, under equal weight, cut-zero
  cost four, and an internal magnitude-two edge.

`Collatz/Radius4ConnectedBounds.lean` contains the two branch-bound applications:

- `transportConnectedFour_fullDenominator_le_sixty_five` concludes `D ≤ 65`
  for a nonempty positive-weight generic word whose full denominator satisfies
  `D > 1` and divides its source numerator, assuming its self-rotation has
  cost four at cut zero, unit height, and connected family label `[4]`.
- `transportHeightTwo_fullDenominator_eq_five` concludes `D = 5` under the
  same word and source-divisibility assumptions, with cut-zero cost four and
  an internal magnitude-two edge instead of the unit-height family hypotheses.

These last two statements derive the local replacements and their difference
divisibility from the source hypothesis and geometry; they do not assume those
intermediate conclusions separately. They do not require primitivity, do not
exclude a complete family, and do not establish the intended final theorem.

`Collatz/Radius4SmallCases.lean` closes the first fully finite height-two
subrange without any analytic input:

- `cycleDenominator_eq_five_of_ones_le_three` proves that the positive
  solutions of `2^A - 3^L = 5` with `L ≤ 3` are exactly `(A,L) = (3,1)` and
  `(5,3)`.
- `cycleDenominator_small_list_of_ones_le_five` proves the first segment of
  the later finite-list certificate: for `L ≤ 5`, the list
  `{5,7,13,17,29,35,47,65}` gives exactly its seven displayed exponent and
  denominator triples.
- `transportHeightTwo_no_small_ones` rules out a radius-four transport in
  both resulting finite word spaces, retaining full source-numerator
  divisibility.
- `transportHeightTwo_no_small_ones_of_cost_four` connects that finite result
  to the existing height-two `D = 5` application theorem.

This is a verified small-weight closure only.  It leaves the unbounded
height-two branch, and every other radius-four family, open.

The same module also contains
`transportRadiusFour_no_generic_length_four` and
`transportRadiusFour_no_generic_length_five`, and
`transportRadiusFour_no_generic_length_six`, complete finite exclusions at
periods four through six under the intended generic local hypotheses: positive
proper weight, strict positive full denominator, source-numerator divisibility,
primitivity, and nonzero shift.  They are exhaustive kernel computations over
the respective word spaces, not assumed finite certificates.

### Required analytic lower bound — unproved

The height-two and connected `[4]` exclusions require a quantitative lower
bound for `log |A log 2-L log 3|`. No equivalent theorem was located in pinned
Mathlib. [ANALYTIC_DEPENDENCY.md](ANALYTIC_DEPENDENCY.md) states the exact
proposition, constants, hypotheses, and useful library support. It is not an
axiom or hypothesis in any current Lean theorem. The cutoff and the subsequent
finite exponent certificate remain unproved.

## Radius-4 local impossibility theorem

Status: **not yet kernel-verified in this repository**.

The generic target assumes `0 < L < A`, `D > 1`, `D ∣ Q(w)`, primitivity,
and a nonzero rotation shift, and excludes `IsTransportRadiusFour w shift`.
The remaining family exclusions and assembly are:

1. `(1,2,1)` and connected `[4]`;
2. `[3,1]`;
3. `[2,2]`;
4. `[2,1,1]`;
5. `[1,1,1,1]`, including the required reduction to a smaller cyclic object
   and a proof closing that reduction;
6. assemble the primitive full-denominator transport-Radius-4 local theorem.

## Scope limitation

Even a completed local theorem would not show that every other Collatz cycle
contains the excluded rotation configuration. It would therefore not by itself
exclude all other cycles or prove the Collatz conjecture.
