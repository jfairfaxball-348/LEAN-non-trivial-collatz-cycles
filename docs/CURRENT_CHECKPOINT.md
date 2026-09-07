# Current authoritative checkpoint

Date: 2026-09-07

The repository, Lean kernel, and actual GitHub Actions results remain authoritative.
Recover live main, recent commits, open PRs, CI, and all five checkpoint documents before continuing.

## Sole objective

Faithfully reconstruct the established RL238 primitive full-denominator transport-Radius-4
local impossibility theorem in standalone Lean. The research repository is a read-only
blueprint, never a dependency or an axiom source. The final theorem is **not yet proved**.

The scope ends at that local theorem. Preserve explicit primitivity; do not substitute
Hamming radius for transport radius. The unrelated draft PR #6 remains untouched.

## Promoted R4-1 checkpoint

PR #33, `Formalize Radius-4 transport cut covariance`, was merged at
`174e0914a1a039234f15e078c56d545f247dc747`.

Its verified repair head was `71637765c062ca0b8a04b93fdc708648f6ef487e`.
Full local `lake build` passed (8,908 jobs). GitHub Actions run
`34039991808` also passed its actual Build step; logs explicitly show every
transport module and the root library building successfully. The post-merge
main run `34040305206` also passed its actual Build step.

The root now imports Transport, Topology, HeightTwo, Components, and Covariance.
This corrects the earlier coverage gap: previous green root builds did not
exercise every promoted transport file. Lean 4.34 elaboration repairs preserve
the theorem statements and actual ordered components.

## R4-1 is complete

The checksum-verified RL238 blueprint uses the minimum-over-cuts prefix-flow
formulation already defined in Lean. PR #33 supplies its required normalization
to a rotated word and the genuine advanced OddCycle parity origin. No additional
general adjacent-swap equivalence theorem is required for this target.

The promoted layer proves:

1. binary increments and one-Lipschitz prefix flow;
2. equal-weight endpoint `G_n = 0`;
3. zero-flow edge removal without cost change;
4. internal magnitude at most two at cost four;
5. the unique non-unit magnitude profile `(1,2,1)`, exhausting the cost;
6. exactly four active edges in the unit branch;
7. increasing active offsets and actual maximal consecutive components;
8. all five unit families, up to component-order permutation:
   `[4]`, `[3,1]`, `[2,2]`, `[2,1,1]`, `[1,1,1,1]`;
9. cut normalization with the same self-rotation shift and the advanced parity origin.

Key theorems:

- `exists_transportHeightTwo_pattern_of_cost_four_of_not_unit`;
- `transportActiveEdgeRunLengths_family_of_cost_four_of_unit`;
- `transportRadiusFour_exists_rotated_zero_cut`;
- `OddCycle.cycleTransportRadiusFour_exists_advanced_zero_cut`.

`transportActiveEdgeRuns` retains actual component order. `List.Perm` labels
families only.

## Current elimination target and analytic dependency

The current R4-2 increment formalizes elementary prerequisites to the first
elimination, height-two and connected `[4]`:

- signed unit runs and the actual height-two local bits `0011 ↔ 1100`;
- local replacement identities, all eight connected coefficients, and height-two coefficient `−15`;
- coprime context cancellation and the finite denominator list under `D > 1`;
- the exact logarithmic defect, its upper bound under `0 < D ≤ 65`, and
  `L ≥ 4 → A < 2L` under `D ≤ 65`.

These are independent Lean lemmas, not a complete topology elimination.
The generic local replacement and divisor lemmas retain explicit context and
divisibility hypotheses. The remaining geometry-to-arithmetic glue must prove
those hypotheses for the actual normalized self-rotation: extract the `[4]`
word, produce common prefix/suffix decompositions, and propagate the original
full-denominator divisibility `D ∣ Q(w)` through rotation. The generic primitive
word theorem is the endpoint; the existing genuine OddCycle identities supply
its cycle application, not a narrower replacement. The theorem index records
exact names and scope.

The elementary increment passed the full local root build (8,912 jobs).
An explicit audit of all 27 new public lemmas found only the standard Lean
axioms `propext`, `Classical.choice`, and `Quot.sound`, where used. Every
promotion still requires its own successful GitHub Actions Build; PR #33's
earlier CI result is not evidence for later source changes.

R4-2 already requires the explicit Laurent–Mignotte–Nesterenko two-logarithm
lower bound. The pinned Mathlib audit found no corresponding formal theorem.
See [the exact dependency audit](RL238_ANALYTIC_DEPENDENCY.md), including the
precise proposition, source locations, available support, and why nearby
Mathlib theorems do not fill the gap. No lower-bound assumption is added to Lean.

## Remaining established order

1. Finish height-two `(1,2,1)` and connected `[4]`.
2. Eliminate `[3,1]`.
3. Eliminate `[2,2]`.
4. Eliminate `[2,1,1]`.
5. Prove the `[1,1,1,1]` quotient-cycle reduction and closure.
6. Assemble and audit the exact primitive full-denominator transport-Radius-4 theorem.

Only after that theorem is on main with full green CI may the project be marked
complete. No automatic successor task is authorized.
