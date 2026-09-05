# Next session handover

Date: 2026-09-05

Repository: `jfairfaxball-348/LEAN-non-trivial-collatz-cycles`

## Objective

Continue the standalone Lean formalisation of the already-proved RL238 Radius-4 local theorem.

This is a translation/reconstruction/formal-verification task, not mathematical research. The research repository may be consulted only as a read-only blueprint for the established Radius-4 proof. The Lean repository must remain completely self-contained.

Do not search for new proof strategies, improve the mathematics, move to Radius 5, or start Gate/global work.

## Authoritative promoted checkpoint

At this handover, `main` is:

`7dbce6e3015cbd58cd3f4ad997122e115fcded7d`

This is the green merge of PR #29.

Do not assume this SHA is still current in the next session. First inspect live `main`, recent commits, open PRs, CI, and the current documentation.

## What was completed this session

PR #27 — merged green:

- full-prefix identity `G_n = ones(target)-ones(source)`;
- zero full-prefix flow for equal-weight pairs and self-rotations.

PR #28 — merged green:

- absolute internal flow magnitudes;
- active-edge support;
- zero-edge removal preserves cost;
- unit-height cost-four branch has exactly four active internal edges.

PR #29 — merged green:

- magnitude one-Lipschitz bounds in both directions;
- first/last internal-edge height bounds;
- no cost-four internal height exceeds two;
- every non-unit cost-four cut contains a height-two edge;
- complete non-unit branch is rigidly `(1,2,1)` and these three heights exhaust the cost.

Key final theorem:

`exists_transportHeightTwo_pattern_of_cost_four_of_not_unit`

in `Collatz/Radius4TransportHeightTwo.lean`.

## Unique next target

Finish R4-1 by classifying the unit-height cost-four branch.

Already available:

`transportActiveEdgeOffsets_card_eq_four_of_cost_four_of_unit`

So at a unit-height minimizing cut there are exactly four active internal height-one edges.

Introduce a Lean-friendly but faithful notion of connected runs/components of consecutive active offsets and prove the exhaustive run-length classification:

- `[4]`;
- `[3,1]`;
- `[2,2]`;
- `[2,1,1]`;
- `[1,1,1,1]`.

Do not begin the topology-specific arithmetic eliminations until this five-family classification is kernel-verified.

## Required source policy

Formal authority:

- this Lean repository for definitions, theorem statements already present, branches, PRs, and CI.

Mathematical blueprint:

- the authoritative RL238 Radius-4 material in `jfairfaxball-348/Proof-that-non-trivial-cycles-cannot-exist-in-Collatz`, read only as needed to recover exact established conventions/statements.

Forbidden:

- importing research code/artefacts as dependencies;
- asserting research conclusions as axioms;
- unrelated historical RL archives;
- external Collatz formalisation projects;
- new Radius-4 proof invention.

## Important distinctions

- RL238 Radius 4 is cyclic adjacent-transposition transport distance, not Hamming distance.
- `IsTransportRadiusFour` and `OddCycle.IsCycleTransportRadiusFour` are the relevant current predicates.
- Older Hamming/four-boundary theorems remain valid support infrastructure only where hypotheses match.
- `OddCycle` does not imply primitivity/minimality; preserve exact RL238 hypotheses.

## After the unit-height classification

Complete only any R4-1 bridge actually required by the established blueprint, such as connecting the chosen component representation to cyclic cut/rotation semantics or the inherited adjacent-transposition formulation.

Then translate the established eliminations in order:

1. `(1,2,1)` and connected `[4]`;
2. `[3,1]`;
3. `[2,2]`;
4. `[2,1,1]`;
5. `[1,1,1,1]` and final quotient-cycle closure;
6. final primitive full-denominator transport-Radius-4 local impossibility theorem.

Once that final local theorem is Lean-verified, stop: the repository objective is complete unless the user explicitly supplies a new objective.

## Repository hygiene

The old draft PR #6 is a separate reverse ordinary-cycle line and is not part of the current target. Do not revive it during R4 formalisation.

After every substantive promotion, update:

- `docs/CURRENT_CHECKPOINT.md`;
- `docs/THEOREM_INDEX.md`;
- `docs/FORMALISATION_ROADMAP.md`;
- `docs/RL238_TO_LEAN_MAP.md`;
- this handover if the session closes.
