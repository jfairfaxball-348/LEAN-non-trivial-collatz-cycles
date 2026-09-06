# Next session handover

Date: 2026-09-06

Repository: `jfairfaxball-348/LEAN-non-trivial-collatz-cycles`

## Objective

Continue the standalone Lean formalisation of the already-proved RL238 Radius-4 local theorem.

This is a translation/reconstruction/formal-verification task, not mathematical research. The research repository may be consulted only as a read-only blueprint for the established Radius-4 proof. The Lean repository must remain completely self-contained.

Do not search for new proof strategies, improve the mathematics, move to Radius 5, or start Gate/global work.

## Authoritative promoted checkpoint

At this handover, the latest promoted mathematical `main` is:

`98922c2d125bdc24e6094fb879f7dc447c764ca9`

This is the green merge of PR #31, `Formalize Radius-4 unit-height component families`.

PR #31 final head:

`a7f609ef9e3bcac8b4b338e81b943531e9fb616f`

GitHub Actions run `33994980788` completed the full Lean CI `Build` step successfully before merge.

Do not assume this SHA is still current in the next session. First inspect live `main`, recent commits, open PRs, CI, and the current authoritative documentation.

## What was completed this session

The remaining unit-height half of the finite R4-1 exact-cost-four topology classification is now kernel-verified.

New source:

`Collatz/Radius4TransportComponents.lean`

Promoted definitions retain the actual connected components of active internal edges:

- `consecutiveOffsetRuns`;
- `consecutiveOffsetRunLengths`;
- `transportActiveEdgeOffsetList`;
- `transportActiveEdgeRuns`;
- `transportActiveEdgeRunLengths`.

The active offsets are listed in increasing order and decomposed into maximal consecutive runs. The concrete run ordering is retained for later topology-specific arguments.

Key promoted theorem:

`transportActiveEdgeRunLengths_family_of_cost_four_of_unit`

At every unit-height cost-four cut, the four active internal edges have run lengths, up to permutation of disconnected components, in exactly one of the established RL238 families:

- `[4]`;
- `[3,1]`;
- `[2,2]`;
- `[2,1,1]`;
- `[1,1,1,1]`.

`List.Perm` is used only for the family label, so orientations such as `[1,3]` are not treated as new topology families; the actual ordered components remain available through `transportActiveEdgeRuns`.

Together with the previously promoted non-unit rigidity theorem, Lean now kernel-verifies all six finite exact-cost-four topology families:

1. `(1,2,1)`;
2. `[4]`;
3. `[3,1]`;
4. `[2,2]`;
5. `[2,1,1]`;
6. `[1,1,1,1]`.

## Unique next target

Do not begin topology-specific arithmetic elimination yet.

First recover from the authoritative RL238 Radius-4 blueprint the exact remaining R4-1 bridge, if any, between the promoted Lean prefix-flow/component classification and the statement actually used by RL238.

The bridge may involve only what the blueprint genuinely requires, for example:

- equivalence with the inherited cyclic adjacent-transposition formulation;
- covariance under cyclic cut/rotation;
- connection of the component representation to the genuine rotated `OddCycle.parityWord`.

Do not invent a bridge merely for generality. If the promoted Lean definitions already supply the required connection, record that precisely and move directly to the first established elimination. Otherwise formalise only the missing established bridge on a fresh branch and run full Lean CI.

## Required source policy

Formal authority:

- this Lean repository for definitions, existing Lean theorems, branches, PRs, CI, and checkpoint documentation.

Mathematical blueprint:

- only the authoritative RL238 Radius-4 material in `jfairfaxball-348/Proof-that-non-trivial-cycles-cannot-exist-in-Collatz`, read only as needed to recover exact established conventions/statements and proof order.

Forbidden:

- importing research code or artefacts as Lean dependencies;
- asserting research conclusions as axioms;
- unrelated historical RL archives;
- external Collatz formalisation projects;
- new Radius-4 mathematical exploration.

## Important distinctions

- RL238 Radius 4 is cyclic adjacent-transposition transport distance, not Hamming distance.
- `IsTransportRadiusFour` and `OddCycle.IsCycleTransportRadiusFour` are the relevant current predicates.
- Older Hamming/four-boundary theorems remain valid support infrastructure only where their hypotheses genuinely match.
- `OddCycle` does not imply primitivity/minimality; preserve the exact RL238 hypotheses.

## Established order after R4-1 is fully connected

Translate only the already-proved RL238 elimination chain, in this order:

1. `(1,2,1)` and connected `[4]`;
2. `[3,1]`;
3. `[2,2]`;
4. `[2,1,1]`;
5. `[1,1,1,1]` quotient-cycle reduction and final closure;
6. assemble the primitive full-denominator transport-Radius-4 local impossibility theorem.

Do not strengthen, replace, reorder, or generalise these arguments unless a small prerequisite lemma is required to faithfully encode the established proof.

Once the final local theorem is Lean-verified and full CI is green, stop: the repository objective is complete unless the user explicitly supplies a new objective.

## Repository hygiene

The old draft PR #6 is a separate reverse ordinary-cycle line and is not part of the current target. Do not revive it during Radius-4 formalisation.

After every substantive promotion, update:

- `docs/CURRENT_CHECKPOINT.md`;
- `docs/THEOREM_INDEX.md`;
- `docs/FORMALISATION_ROADMAP.md`;
- `docs/RL238_TO_LEAN_MAP.md`;
- this handover when the session closes.
