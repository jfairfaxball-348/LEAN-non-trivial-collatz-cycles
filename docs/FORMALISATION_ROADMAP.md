# Formalisation roadmap

The sole objective is the standalone kernel verification of the established
RL238 primitive full-denominator transport-Radius-4 local impossibility theorem.
The research repository is a read-only blueprint. The final theorem is not yet proved.

## Stages 0–1 — foundations and genuine cycle arithmetic

Complete as infrastructure for the local theorem: ordinary Collatz and halfStep,
exact OddCycle data, genuine parity-word encoding, full denominator arithmetic,
positive nontrivial denominator, and shifted-origin numerator identities.
Reverse extraction from ordinary periodic points is separate; draft PR #6 is out of scope.

## Stage 2 — earlier Hamming support

The four-boundary arithmetic chain remains valid support infrastructure under
its stated Hamming hypotheses. It cannot stand in for transport radius.
Reuse requires an explicit formal derivation of its hypotheses.

## Stages 3–4 — transport model and R4-1

Complete, including the cut-normalisation bridge promoted in PR #33.

The prefix flow has binary increments, one-Lipschitz steps, equal-weight zero
endpoint, and exact minimum-over-cuts cost. The cost-four families are the
height-two `(1,2,1)` profile and the five ordered-component families, labeled
up to permutation as `[4]`, `[3,1]`, `[2,2]`, `[2,1,1]`, and `[1,1,1,1]`.

The chosen cut is normalized to zero in a rotated genuine parity word using
`OddCycle.cycleTransportRadiusFour_exists_advanced_zero_cut`.
The authorized RL238 blueprint requires no additional general metric equivalence.

All intended transport modules are root-imported. PR #33 repaired the earlier
coverage gap and passed full local build and GitHub Build before merge.

## Stage 5 — established eliminations

In progress at the elementary prerequisites to the **first** elimination.
No complete topology elimination is yet proved.

The present elementary layer includes signed height-two local bits, exact
replacement coefficients, coprime cancellation, the strict natural divisor
list, and the logarithmic defect with `A < 2L` for `L ≥ 4` and `D ≤ 65`.
The remaining first-branch glue is the `[4]` local word, common-context list
decompositions, and full-denominator divisibility under generic word rotation. These
applications are not implicit in the generic prerequisite lemmas.

Preserve the established order:

1. Signed height-two and connected `[4]` words, exact local coefficients,
   coprime context cancellation, LMN cutoff and finite tail.
2. `[3,1]`.
3. `[2,2]`.
4. `[2,1,1]`.
5. `[1,1,1,1]` quotient cycle and final closure.

The LMN two-logarithm lower bound is already needed in item 1. No corresponding
theorem was located in pinned Mathlib. The exact obligation and available
support are recorded in [RL238_ANALYTIC_DEPENDENCY.md](RL238_ANALYTIC_DEPENDENCY.md).
It must be proved internally, not added as an axiom or a new final hypothesis.

## Stage 6 — assemble the local theorem

Not yet proved. Preserve all exact RL238 hypotheses, including explicit
primitivity where required. OddCycle does not silently supply primitivity
or a minimal period. The endpoint must concern `IsTransportRadiusFour` and
retain the generic primitive full-denominator word scope of RL238;
`OddCycle.IsCycleTransportRadiusFour` belongs to its genuine-cycle application,
not a narrower replacement for that endpoint. In particular,
retain `D ∣ Q(w)`, not merely divisibility of a numerator difference.

## Stage 7 — audit and completion

Before declaring completion, verify the exact final theorem on main, actual
full green CI, root coverage, no proof placeholders, no research-conclusion
axioms or external research dependency, explicit hypotheses, all topology
families, no required unmerged PR, and synchronized documentation.

The endpoint is the local Radius-4 theorem. Radius 5, Gate A, Gate B, global
encounter work, alternative proof strategies, and other research are not successor tasks.
