# Current verified checkpoint

Date: 2026-09-07

The final primitive full-denominator transport-radius-four impossibility
theorem is **unproved**. This document distinguishes the verified main-branch
results from source currently under development.

## Objective and definitions

The Collatz map sends an even natural number to half its value and an odd one
to three times its value plus one. An `OddCycle L` records positive odd nodes
with transitions `3*x_i+1 = 2^a_i*x_(i+1)`. The auxiliary `halfStep` map divides
by two on every transition. Its binary parity word has length `A = sum a_i`
and weight `L`, the number of ones.

For any cyclic binary word `w`, write `Q(w)` for `wordNumerator` applied to the
chronological list from position zero and `D = 2^A-3^L` for the full integer
denominator. The target excludes a nonzero self-rotation at exact transport
radius four when `0 < L < A`, `D > 1`, `D ∣ Q(w)`, and `IsPrimitive w`.
Primitivity means that no nonzero rotation fixes the word. It is an explicit
hypothesis, not a field supplied by `OddCycle`.

Transport radius is the minimum, over cyclic cuts, of
`sum_{k=1}^{A-1} |G_k|`, where `G_k` is target-prefix ones minus source-prefix
ones. It differs from Hamming distance, which counts unequal positions.

## Verified main branch

PR #34 merged at `d7d1f372635c4d749da2172e16f247ba68b3d750`.
Its verified head was `98c0147b420a1112830d54d8fb537e7218ea1245`.
The full local `lake build` passed with 8,912 jobs. GitHub Actions PR run
`34115337625` passed the actual Build step, including the four new modules
and root library. Post-merge main run `34115689962` also passed its actual
Build step.

An explicit dependency audit of the 27 new public lemmas found only the
standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`, where
used. No additional mathematical axiom or proof placeholder was used.

The earlier transport classification and cut normalization were promoted by
PR #33 at `174e0914a1a039234f15e078c56d545f247dc747`. Its full local build
passed with 8,908 jobs; PR run `34039991808` and post-merge main run
`34040305206` passed their actual Build steps. That change added all intended
transport modules to the root build and repaired the elaboration issues this
coverage exposed.

## Proved transport classification

At an equal-weight cut of cost four, Lean proves:

1. Each prefix-flow increment lies in `{-1,0,1}`, and the full prefix has flow zero.
2. Removing zero-flow edges does not change the cost.
3. Every internal magnitude is at most two.
4. A magnitude-two edge forces consecutive magnitudes `(1,2,1)`, which exhaust the cost.
5. Otherwise exactly four edges have unit magnitude. Their maximal consecutive
   run lengths are, up to permutation, `[4]`, `[3,1]`, `[2,2]`, `[2,1,1]`, or `[1,1,1,1]`.
6. Rotating both words moves a minimizing cut to zero while retaining the
   self-rotation shift. For cycle parity words, this is the actual advanced orbit origin.

Key theorems are `exists_transportHeightTwo_pattern_of_cost_four_of_not_unit`,
`transportActiveEdgeRunLengths_family_of_cost_four_of_unit`,
`transportRadiusFour_exists_rotated_zero_cut`, and
`OddCycle.cycleTransportRadiusFour_exists_advanced_zero_cut`.
The concrete `transportActiveEdgeRuns` list retains component order;
`List.Perm` is used only to label families.

## Proved arithmetic ingredients

PR #34 supplies the following prerequisites to the height-two and connected
four-edge exclusions:

- signed unit flow and height-two local bits `0011 ↔ 1100`;
- local numerator replacement identities, all eight connected coefficients,
  and the signed height-two coefficient `−15`;
- cancellation of powers of two and three from full-denominator divisibility;
- the possible natural divisors `5,7,13,17,29,35,47,65`, under explicit strict,
  coprime, and coefficient-divisibility hypotheses;
- the logarithmic defect identity and upper bound under `0 < D ≤ 65`, and
  `A < 2L` under `D ≤ 65` and `L ≥ 4`.

The [theorem index](THEOREM_INDEX.md) gives names and exact scope. These
ingredients do not yet exclude an entire transport family.

## Current unverified work and remaining obligations

Branch `codex/r4-local-word-bridge` contains new helpers in
`Collatz/Radius4TransportComponents.lean` and a height-two outside-bit agreement
lemma in `Collatz/Radius4TransportSigned.lean`, plus the new modules
`Collatz/CyclicWordList.lean`, `Collatz/Radius4WordRotation.lean`,
`Collatz/Radius4FullDenominatorWord.lean`,
`Collatz/Radius4TransportConnectedBits.lean`,
`Collatz/Radius4TransportLocalWords.lean`, and
`Collatz/Radius4ConnectedBounds.lean`. These additions have **not completed
full validation and have not been promoted**. Individual module builds passed
for `CyclicWordList.lean`, `Radius4WordRotation.lean`, and
`Radius4FullDenominatorWord.lean`, as did the updated transport definition,
topology, height-two, and component modules. The validation sequence was
stopped during the signed-flow module check to save the current work as a
closeout snapshot. The remaining module checks, full root build, and audit of
the 24 new public lemmas are incomplete. No CI result is claimed for this
snapshot. Individual checks do not establish whole-branch coverage. The green
CI builds above certify their recorded revisions, not these later edits.

The new application statements aim to derive `D = 5` for the height-two
configuration and `D ≤ 65` for the connected four-edge configuration from
the actual generic word, its source-numerator divisibility, and the stated
zero-cut geometry. They are not complete family exclusions. The
[theorem index](THEOREM_INDEX.md) inventories all 24 new public lemma
statements under validation.

The first exclusions require extracting the connected local word, proving
common-prefix/suffix decompositions, carrying the original `D ∣ Q(w)` through
generic word rotation, and identifying the positive full denominator with the
natural divisor used in the finite list. Existing shifted-origin cycle
identities do not replace this generic word argument.

The quantitative logarithmic lower bound in
[ANALYTIC_DEPENDENCY.md](ANALYTIC_DEPENDENCY.md) is also unproved. Its exact
constants are required for the intended cutoff `L < 7000`; neither that
cutoff nor the remaining finite and structural exclusions may be assumed.

After height-two and connected `[4]`, the remaining families are `[3,1]`,
`[2,2]`, `[2,1,1]`, and `[1,1,1,1]`, followed by assembly of the generic local
theorem. Completion requires that theorem and its dependencies to be checked
on main with a successful full build and synchronized documentation. It would
remain a local obstruction, not a proof of the Collatz conjecture.
