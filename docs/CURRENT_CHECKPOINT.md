# Current authoritative checkpoint

Date: 2026-09-05

The repository itself remains authoritative. Every future session must inspect live `main`, recent commits, open PRs, CI, this file, `docs/THEOREM_INDEX.md`, `docs/FORMALISATION_ROADMAP.md`, `docs/RL238_TO_LEAN_MAP.md`, and `docs/NEXT_SESSION_HANDOVER.md` before continuing.

## Absolute objective

This repository is a standalone Lean formalisation project for the already-established RL238 Radius-4 local theorem. It is not a mathematical research programme.

The corresponding research repository may be consulted only as a read-only mathematical blueprint for the established Radius-4 derivation. Nothing from that repository is a formal dependency: do not import its code or artefacts, do not add its conclusions as axioms, and prove every required proposition inside this repository from Lean definitions and previously proved lemmas.

Do not search for new proof strategies, extend to Radius 5, work on Gate A/Gate B/global encounter questions, or revive unrelated historical derivations unless explicitly instructed by the user.

## Latest promoted mathematical checkpoint

Current promoted `main` at this closeout:

`98922c2d125bdc24e6094fb879f7dc447c764ca9`

This is the green merge of PR #31, `Formalize Radius-4 unit-height component families`.

PR #31 final head:

`a7f609ef9e3bcac8b4b338e81b943531e9fb616f`

GitHub Actions run `33994980788` completed the full Lean CI `Build` step successfully before merge.

The preceding documentation-only closeout was PR #30 at merge `3838f2c5a4a5debbfe4f3388960741d1023feaf6`; the preceding mathematical promotion was PR #29, the height-two transport rigidity theorem.

## Kernel-verified RL238 transport layer now promoted

The faithful transport-distance development is separate from the older Hamming predicate `IsRadiusFour`.

Promoted Lean proves:

1. binary transport increments are exactly in `{-1,0,1}`;
2. prefix flow is one-Lipschitz;
3. `transportCostAtCut` is the sum of absolute internal prefix-flow heights;
4. `IsExactTransportRadius`, `IsTransportRadiusFour`, and `OddCycle.IsCycleTransportRadiusFour` model the exact minimum-over-cuts transport notion used by RL238;
5. the full prefix satisfies `G_n = ones(target) - ones(source)`, hence equal-weight pairs and self-rotations have `G_n = 0`;
6. zero-flow internal edges may be removed without changing transport cost;
7. in the unit-height cost-four branch exactly four internal edges are active;
8. every equal-weight cost-four internal height is at most two;
9. every non-unit cost-four flow contains a height-two edge;
10. the complete non-unit branch is rigidly `(1,2,1)` and those three heights exhaust the cost;
11. the four active unit-height edges are represented in increasing offset order and decomposed into maximal consecutive connected runs;
12. their connected-run lengths are exhaustively, up to permutation of disconnected components, exactly the five RL238 families `[4]`, `[3,1]`, `[2,2]`, `[2,1,1]`, or `[1,1,1,1]`.

Key files:

- `Collatz/Radius4Transport.lean`
- `Collatz/Radius4TransportTopology.lean`
- `Collatz/Radius4TransportHeightTwo.lean`
- `Collatz/Radius4TransportComponents.lean`

Key new theorem:

`transportActiveEdgeRunLengths_family_of_cost_four_of_unit`

The concrete component ordering is retained by `transportActiveEdgeRuns`; `List.Perm` is used only for the five-family label so orientations such as `[1,3]` are not misclassified as new topology families.

## R4-1 status

The finite exact-cost-four topology classification itself is now kernel-verified:

- non-unit family: `(1,2,1)`;
- unit-height families: `[4]`, `[3,1]`, `[2,2]`, `[2,1,1]`, `[1,1,1,1]`.

Do not begin topology-specific arithmetic elimination merely from this checkpoint. First consult only the authoritative RL238 Radius-4 blueprint and determine whether R4-1 still requires a precise bridge from the formal prefix-flow/component representation to the inherited cyclic adjacent-transposition formulation, cyclic cut/rotation covariance, or the genuine rotated `OddCycle.parityWord` statement.

Prove only the bridge that the established blueprint actually uses. Do not invent or generalise bridge obligations.

## Established proof order after R4-1

Once the required R4-1 bridge, if any, is kernel-verified, translate the already-established RL238 eliminations in this order:

1. height-two `(1,2,1)` and connected `[4]`;
2. `[3,1]`;
3. `[2,2]`;
4. `[2,1,1]`;
5. `[1,1,1,1]` quotient-cycle reduction and final closure;
6. assemble the primitive full-denominator transport-Radius-4 local impossibility theorem.

Preserve the exact RL238 hypotheses. `OddCycle` does not silently imply primitivity or minimality.

## Scope discipline

- RL238 Radius 4 is cyclic adjacent-transposition transport distance, not Hamming distance.
- The older Hamming/four-boundary arithmetic chain remains support infrastructure only where its hypotheses genuinely match.
- The research proof is a blueprint, not an axiom source.
- A completed local Radius-4 theorem is the endpoint of this repository task unless the user explicitly changes the objective.
- The old reverse ordinary-cycle PR #6 is separate and is not the current blocker.

## Next-session start

1. Recover live `main`, recent commits, open PRs, CI, and the authoritative docs.
2. Confirm PR #31 remains promoted and green.
3. Read `Collatz/Radius4TransportComponents.lean` together with the earlier transport files.
4. Consult only the authoritative RL238 Radius-4 material needed to identify the exact remaining R4-1 bridge, if any.
5. Formalise only that established bridge on a fresh branch and run full Lean CI.
6. Do not start the topology eliminations until R4-1 is formally connected to the exact statement used by RL238.
7. After any substantive promotion, update the authoritative documentation again.
