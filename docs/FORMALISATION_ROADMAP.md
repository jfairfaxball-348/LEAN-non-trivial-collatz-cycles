# Formalisation roadmap

This repository has one objective: faithfully reconstruct and kernel-verify the already-proved RL238 Radius-4 local theorem in Lean.

The research repository is a read-only mathematical blueprint, never a formal dependency. Do not invent new mathematics, move to Radius 5, or start global Gate work unless the user explicitly changes the objective.

## Stage 0 — Foundations

Status: **complete as infrastructure**.

The repository defines the ordinary Collatz map, `halfStep`, cyclic words, rotation, exact odd-to-odd cycle data, denominator arithmetic, and genuine parity-word encoding.

## Stage 1 — Genuine cycle and denominator arithmetic

Status: **complete for the local Radius-4 formalisation**.

Lean proves the exact `OddCycle` equations, full `halfStep` periodicity, the denominator `D = 2^A - 3^L`, positivity, the nontrivial bound `D > 1`, full-denominator word arithmetic, and shifted-origin identities.

Reverse extraction from an arbitrary ordinary periodic point remains separate and is not part of the present target.

## Stage 2 — Earlier Hamming/four-boundary support arithmetic

Status: **kernel-verified support infrastructure; not the RL238 Radius-4 metric**.

The repository proves exact Hamming-distance four mismatch structure and weighted four-boundary numerator formulas. These results may be reused only where their hypotheses match later transport-derived statements.

Never identify Hamming Radius 4 with RL238 transport Radius 4 without a theorem.

## Stage 3 — RL238 transport-radius model

Status: **complete through endpoint and cost definitions**.

`Collatz/Radius4Transport.lean` provides:

- signed binary transport increments;
- prefix flow `G_k`;
- one-Lipschitz flow steps;
- cut cost `sum |G_k|` over internal edges;
- exact minimum-over-cuts transport radius;
- `OddCycle.IsCycleTransportRadiusFour` for the genuine parity word;
- the full-prefix identity `G_n = ones(target)-ones(source)`;
- zero full-prefix flow for equal-weight pairs and self-rotations.

## Stage 4 — R4-1 exact cost-four topology classification

Status: **finite topology classification complete; exact bridge audit next**.

Promoted results in `Collatz/Radius4TransportTopology.lean`, `Collatz/Radius4TransportHeightTwo.lean`, and `Collatz/Radius4TransportComponents.lean` prove:

- zero-flow edges can be removed without changing cost;
- the unit-height cost-four branch has exactly four active internal edges;
- every cost-four internal height is at most two;
- any non-unit cost-four flow has a height-two edge;
- the complete non-unit branch is rigidly `(1,2,1)` and those three heights exhaust the cost;
- active unit-height offsets can be decomposed into maximal consecutive connected runs;
- the resulting four-edge run lengths are exhaustively, up to component-order permutation, `[4]`, `[3,1]`, `[2,2]`, `[2,1,1]`, or `[1,1,1,1]`.

Key theorem:

`transportActiveEdgeRunLengths_family_of_cost_four_of_unit`.

### Next exact target

Consult only the authoritative RL238 Radius-4 blueprint and determine whether R4-1 requires any further formal bridge between the current prefix-flow/component representation and:

- the inherited cyclic adjacent-transposition metric;
- cyclic cut/rotation covariance;
- the genuine rotated `OddCycle.parityWord` statement.

Prove only the bridge actually used by RL238. Do not add a general equivalence or covariance theory merely because it could be useful.

Do not begin topology elimination until that exact R4-1 bridge obligation, if any, has been identified and kernel-verified.

## Stage 5 — Established RL238 topology eliminations

Status: **not yet translated**.

Once R4-1 is complete, translate the already-established proof in its certified order:

1. height-two `(1,2,1)` and connected `[4]`;
2. `[3,1]`;
3. `[2,2]`;
4. `[2,1,1]`;
5. `[1,1,1,1]` quotient-cycle reduction and final closure.

Do not improve, replace, or broaden these arguments. Reconstruct them faithfully and break them into Lean-sized lemmas as needed.

## Stage 6 — Assemble the local theorem

Status: **not yet kernel-verified**.

Assemble the exact primitive full-denominator transport-Radius-4 local impossibility theorem from the promoted topology classification and translated eliminations.

Preserve the exact established hypotheses. In particular, `OddCycle` does not imply primitivity or minimality; if RL238 requires `IsPrimitive c.parityWord`, retain it explicitly unless a separate formal reduction has actually been proved.

When this local theorem is proved and full Lean CI is green, the present repository objective is complete.

## Stage 7 — Audit and closeout

At completion:

- run full Lean CI;
- verify no `sorry`, axiom, imported research artefact, or silent Hamming/transport substitution entered the proof;
- update `docs/CURRENT_CHECKPOINT.md`, `docs/THEOREM_INDEX.md`, and `docs/RL238_TO_LEAN_MAP.md`;
- state the exact final theorem and hypotheses;
- stop. There is no automatic Radius-5 or global-research successor.

## Explicitly out of scope

Unless the user later asks for them separately:

- Radius 5;
- Gate A;
- Gate B;
- global Radius-4 encounter/bridge research;
- unrelated Collatz formalisation projects;
- historical RL archives outside the authoritative RL238 blueprint;
- redesigning the already-proved mathematics.
