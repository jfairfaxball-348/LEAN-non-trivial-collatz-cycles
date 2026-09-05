# Current authoritative checkpoint

Date: 2026-09-05

The repository itself remains authoritative. Every future session must inspect live `main`, recent commits, open PRs, CI, this file, `docs/THEOREM_INDEX.md`, `docs/FORMALISATION_ROADMAP.md`, and `docs/RL238_TO_LEAN_MAP.md` before continuing.

## Absolute objective

This repository is a standalone Lean formalisation project for the already-established RL238 Radius-4 local theorem. It is not a mathematical research programme.

The corresponding research repository may be consulted only as a read-only mathematical blueprint for the established Radius-4 derivation. Nothing from that repository is a formal dependency: do not import its code or artefacts, do not add its conclusions as axioms, and prove every required proposition inside this repository from Lean definitions and previously proved lemmas.

Do not search for new proof strategies, extend to Radius 5, work on Gate A/Gate B/global encounter questions, or revive unrelated historical derivations unless explicitly instructed by the user.

## Latest promoted mathematical checkpoint

Current `main`:

`7dbce6e3015cbd58cd3f4ad997122e115fcded7d`

This is the green merge of PR #29, `Formalize height-two transport rigidity`.

PR #29's final head `0545fbce4524ae11f8a1ede8207238d518999e90` passed the full Lean CI `Build` step before merge.

Immediately preceding transport promotions:

- `64552275d0955f955929ad8d5d1dc60cb778e520` — PR #28, exact cost-four active-support decomposition and four-active-edge theorem for the unit-height branch;
- `479780cccfee64e1c7768b026f5c27c9af4e7559` — PR #27, full-prefix endpoint identity `G_n = ones(target)-ones(source)` and zero endpoint for equal-weight/self-rotation pairs;
- `aea4a2d87a64f3c1bd6d56752502f4752e07c566` — PR #26, faithful RL238 prefix-flow transport model, exact minimum-over-cuts Radius-4 predicate, one-Lipschitz local increments, and genuine parity-word wrapper;
- `7d2afc2fb4c4061097d79c0c20ea5799763aedc3` — PR #25, earlier exact Hamming/four-boundary numerator support infrastructure. This remains valid Lean mathematics but is not the RL238 transport-radius theorem.

## Kernel-verified RL238 transport layer now promoted

The faithful transport-distance development is separate from the older Hamming predicate `IsRadiusFour`.

Promoted Lean now proves:

1. Binary transport increments are exactly in `{-1,0,1}`.
2. Prefix flow is one-Lipschitz.
3. `transportCostAtCut` is the sum of absolute internal prefix-flow heights `|G_1| + ... + |G_(n-1)|`.
4. `IsExactTransportRadius` and `IsTransportRadiusFour` express exact minimum-over-cuts transport radius; `OddCycle.IsCycleTransportRadiusFour` applies this to the genuine Collatz parity word.
5. The full prefix satisfies

   `G_n = ones(target) - ones(source)`.

   Equal-weight pairs, and therefore every word/self-rotation pair, have `G_n = 0` at every cut.
6. Active internal edges are precisely the nonzero flow heights; removing zero edges preserves transport cost.
7. In the unit-height cost-four branch, exactly four internal edges are active.
8. Absolute flow magnitude is one-Lipschitz in both directions; the first and last charged internal edges have height at most one for equal-weight words.
9. At an equal-weight cost-four cut every internal height is at most two.
10. If the cost-four cut is not unit-height, a height-two edge exists.
11. The complete non-unit branch is rigid: a height-two edge is strictly internal, its two neighbours have height one, and those three heights exhaust the entire cost. Thus the non-unit topology is exactly the RL238 `(1,2,1)` family.

Key files:

- `Collatz/Radius4Transport.lean`
- `Collatz/Radius4TransportTopology.lean`
- `Collatz/Radius4TransportHeightTwo.lean`

## Exact remaining R4-1 gap

R4-1 is not yet complete.

The next target is only the remaining unit-height classification. At a minimizing cost-four cut, Lean already proves there are exactly four active internal edges and each has height one. Formalise their connected-run decomposition and prove that the run lengths are exactly one of the five partitions of four used by RL238:

- `[4]`;
- `[3,1]`;
- `[2,2]`;
- `[2,1,1]`;
- `[1,1,1,1]`.

The representation may be chosen for Lean convenience, but it must faithfully encode connected runs of consecutive active internal edges. Do not alter the established mathematics.

After that classification is kernel-verified, complete any remaining R4-1 bridge needed to connect the topology representation to the genuine rotated `OddCycle.parityWord` and the inherited cyclic adjacent-transposition formulation. Then translate the already-established RL238 topology eliminations in their existing order.

## Established proof order after R4-1

Use the research repository only to recover the exact already-proved statements and derivations. Continue in this order unless the blueprint itself requires a smaller prerequisite lemma:

1. connected height-two `(1,2,1)` and connected `[4]` eliminations;
2. `[3,1]`;
3. `[2,2]`;
4. `[2,1,1]`;
5. `[1,1,1,1]` quotient-cycle reduction and final closure;
6. assemble the primitive full-denominator transport-Radius-4 local impossibility theorem.

The final local theorem must preserve the exact RL238 hypotheses, including primitivity if it is genuinely required. `OddCycle` does not silently provide minimality or primitivity.

## Important scope discipline

- Hamming Radius 4 is not RL238 transport Radius 4. Never substitute one for the other without a proved equivalence theorem.
- The older Hamming/four-boundary arithmetic chain remains support infrastructure only where its hypotheses actually match.
- The research proof is a blueprint, not an axiom source.
- A completed local Radius-4 theorem is the endpoint of this repository task unless the user explicitly asks for something further.
- The old reverse ordinary-cycle PR #6 is separate and is not the current blocker.

## Open PR state at closeout

- PR #29: merged green; current mathematical checkpoint.
- PR #28: merged green.
- PR #27: merged green.
- PR #26: merged green.
- PR #6: older draft reverse-bridge line; leave untouched unless separately requested.

## Next-session start

1. Re-read live repository state; do not assume this SHA is still current.
2. Confirm no newer R4 transport PR has appeared.
3. Read `Collatz/Radius4TransportTopology.lean` and `Collatz/Radius4TransportHeightTwo.lean`.
4. Consult only the authoritative RL238 research material needed to recover the exact unit-height run classification conventions.
5. Formalise the connected-run representation and prove the five exhaustive unit-height partitions of four.
6. Run full Lean CI and merge only when green.
7. Update the theorem index, roadmap, RL238 map, and this checkpoint after promotion.
