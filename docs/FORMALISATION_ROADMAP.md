# Formalisation roadmap

The objective is to prove a local impossibility theorem for cyclic binary
words arising in Collatz-cycle arithmetic. The ordinary Collatz map sends
even `x` to `x/2` and odd `x` to `3*x+1`; the parity encoding uses `halfStep`,
which also divides the odd result by two.

For a word of length `A` with `L` ones, let `D = 2^A-3^L` and let `Q(w)` be
its exact chronological affine numerator. The target retains `0 < L < A`,
`D > 1`, `D ∣ Q(w)`, primitivity, and a nonzero rotation shift. Primitivity
means no nonzero rotation fixes the word. Transport radius is the minimum
over cyclic cuts of the sum of absolute differences between target and
source prefix weights. The target excludes exact radius four under these
hypotheses; it remains unproved.

## Cycle model and arithmetic — verified

The library defines ordinary Collatz steps, `halfStep`, exact odd-to-odd
transitions, and `OddCycle`. It proves the genuine parity encoding, the full
denominator identity, denominator positivity, the strict denominator bound
for a nontrivial cycle, and shifted-origin identities. `OddCycle` does not
assert a minimal represented period or primitivity.

## Transport classification and cut normalization — verified

The prefix-flow model has increments in `{-1,0,1}` and endpoint zero for
equal-weight words. At cost four, the possible nonzero magnitude patterns are
the height-two profile `(1,2,1)` or four unit-height edges. Maximal consecutive
runs of those four edges have lengths `[4]`, `[3,1]`, `[2,2]`, `[2,1,1]`, or
`[1,1,1,1]`, up to component permutation. Actual component order is retained.

A minimizing cut can be normalized to zero by rotating the words. For cycle
parity words, `OddCycle.cycleTransportRadiusFour_exists_advanced_zero_cut`
identifies the actual advanced orbit origin. All required classification
modules are imported by the root library and included in the recorded builds.

## Height-two and connected four-edge exclusions — in progress

The verified prerequisites include signed height-two bits `0011 ↔ 1100`,
exact local coefficients, coprime context cancellation, a finite divisor list,
and elementary logarithmic upper bounds. PR #34 promoted these prerequisites;
see the [checkpoint](CURRENT_CHECKPOINT.md) for build evidence.

The first three steps are proved; the unbounded analytic step remains:

1. Extract `0abc1 ↔ 1abc0` from the connected four-edge geometry.
2. Express each comparison using common prefix and suffix lists, and prove
   that full-denominator source divisibility passes through generic rotation.
3. Apply the local coefficient and divisor lemmas to the actual word pair.
4. Prove a justified quantitative logarithmic lower bound and its cutoff.
   The exact finite exponent list and word exclusions below weight 7000
   are now verified in `Radius4FiniteCertificate.lean`, with the range
   hypothesis explicit. `Radius4ConnectedFinite.lean` applies the list to
   connected geometry and removes height two and connected `[4]` from the
   normalized classification in that range.

New component, cyclic-list, word-rotation, full-denominator-word, local-bit,
and common-context work on `codex/r4-local-word-bridge`, including the
application statements in `Collatz/Radius4ConnectedBounds.lean`, passes the
local root build and bridge axiom audit; no CI promotion is claimed for this
newer revision. The application statements target `D = 5` for height-two and
`D ≤ 65` for connected four-edge flow, not complete exclusions.

The proposed logarithmic proposition and a newly identified gap in its
source specialization are documented in
[ANALYTIC_DEPENDENCY.md](ANALYTIC_DEPENDENCY.md). No equivalent formal theorem
was located in the pinned Mathlib. It must receive a kernel proof and cannot
be added as an axiom or an extra hypothesis of the intended final theorem.

## Remaining component families — unproved

The planned order after the first exclusions is:

1. `[3,1]`: one run of three active edges and one isolated active edge.  The
   ordered active-edge list is refined into its two possible placements
   (triple first or triple last).  The triple run now yields a local
   `0ab1 ↔ 1ab0` bit word, and the isolated edge yields `01 ↔ 10`.
   Relating these two local exchanges and proving the required arithmetic
   exclusion are still unproved.
2. `[2,2]`: two runs of two active edges.
3. `[2,1,1]`: one run of two and two isolated active edges.
4. `[1,1,1,1]`: four isolated active edges, including the required reduction
   to a smaller cyclic object and its closure argument.

Each family needs its full arithmetic exclusion. The classification alone
does not supply these conclusions. The [local proof map](LOCAL_PROOF_MAP.md)
locates existing ingredients and their application gaps.

## Assemble and audit the local theorem — unproved

Combine all families into the generic primitive-word statement. Retain the
full `D ∣ Q(w)` hypothesis and exact transport radius. The separate Hamming
distance predicates count mismatches and do not state this result. Cycle
applications must establish any required primitivity explicitly.

Completion requires the final theorem and dependencies on main, every needed
module in the root build, successful local and GitHub Actions builds, an axiom
audit, no proof placeholders or `native_decide`, and consistent documentation.
Even a completed local theorem would require an additional result showing
that every other cycle contains the excluded configuration before it could
imply a general no-cycle conclusion.
