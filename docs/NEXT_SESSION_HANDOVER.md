# Next session handover

Date: 2026-09-07

## Objective and authority

Finish the standalone Lean verification of the established RL238 primitive
full-denominator transport-Radius-4 local impossibility theorem.
The final theorem remains **unproved** in this repository.

Use this repository for formal authority. Consult only the authorized RL238
blueprint in the sibling research checkout, read-only. Preserve primitivity
and the transport metric. Do not import research artifacts or assume research
conclusions. Draft PR #6 is unrelated and remains untouched.

## Promoted work

PR #33 was repaired and merged at `174e0914a1a039234f15e078c56d545f247dc747`.
Its head `71637765c062ca0b8a04b93fdc708648f6ef487e` passed the full local
build and GitHub Actions run `34039991808`, including the actual Build step.
Main's post-merge run `34040305206` also passed its actual Build step.

All transport modules are now root-imported. The earlier finite family and
height-two files needed Lean 4.34 repairs that their previous root builds had
not exercised. Those proofs now compile while retaining their statements.

R4-1 is complete: the six finite topology families, cut normalization, and the
genuine advanced OddCycle parity origin are connected in Lean. The authorized
blueprint does not require another general metric-equivalence theorem.

## First remaining target

R4-2: height-two `(1,2,1)` and connected `[4]`.

The current increment supplies signed unit-flow and actual height-two bits,
local numerator coefficients, coprime context cancellation, the finite natural
divisor list, and elementary logarithmic bounds with the `A < 2L` reduction.
See the theorem index for exact names and hypotheses. All four new modules
are root-imported; none proves a whole branch elimination.

Next, extract the `[4]` local word from the actual ordered components; convert
both local geometries to common-prefix/suffix lists; propagate the original
full-denominator source divisibility through generic word rotation; and connect the natural
divisor list to the strict positive full denominator. Then complete the
established LMN parameter enlargement, lower bound, cutoff, finite certificate,
and structural exclusions. Do not substitute another argument.
The endpoint is the generic primitive full-denominator word theorem. An
OddCycle-only theorem would undershoot the authorized RL238 statement; keep
the original hypothesis `D ∣ Q(w)`, which the finite structural tails use.

The source bundle and exact missing two-logarithm bound are recorded in
[RL238_ANALYTIC_DEPENDENCY.md](RL238_ANALYTIC_DEPENDENCY.md).
The audit found the exact logarithm and Legendre support in pinned Mathlib,
but no LMN/Baker/Matveev or equivalent quantitative two-logarithm theorem.
The formal lower bound must be supplied by a kernel proof; an assumption-wrapped
final statement is not completion.

## Required continuation checks

1. Recover live main, recent commits, all relevant PRs, CI and the five authority docs.
2. Check `THEOREM_INDEX.md` for which new R4-2 lemmas have actually been promoted.
3. Follow R4-2, then `[3,1]`, `[2,2]`, `[2,1,1]`, and `[1,1,1,1]`.
4. Keep every required module root-imported and run full local and GitHub builds.
5. Merge only green work; synchronize the checkpoint, index, roadmap and map.
6. Audit the final exact theorem and all dependencies before declaring completion.

The installed local toolchain is available at
`/Users/johnfairfax-ball/.elan/bin/lake`. The repository pins Lean
`v4.34.0-rc2` and Mathlib `69fe4f49ffbc9580a2c3ae6d29591ef6d1d4131e`.
Shell Git authentication was unavailable during this session; the connected
GitHub app was used to publish and merge, with local Git objects verified
against the exact remote SHAs.

Stop only at the stated endpoint or report the exact unresolved formal
dependency. Do not start Radius 5, Gate A, Gate B, or global encounter work.
