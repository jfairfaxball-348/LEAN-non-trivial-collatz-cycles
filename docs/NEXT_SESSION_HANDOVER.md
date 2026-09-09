# Development handover

Date: 2026-09-09

## Objective and model

Finish the local impossibility theorem for primitive binary words whose full
denominator divides their numerator. The final theorem remains **unproved**.

The Collatz map halves even inputs and sends odd `x` to `3*x+1`. Its
denominator-compatible parity encoding uses `halfStep`, which divides by two
on every transition. A word has length `A`, number of ones `L`, exact
chronological numerator `Q(w) = wordNumerator(w)`, and full integer denominator
`D = 2^A-3^L`.

The intended generic statement excludes a nonzero self-rotation at exact
transport radius four under `0 < L < A`, `D > 1`, `D ∣ Q(w)`, and
`IsPrimitive w`. A primitive word is fixed only by the zero rotation.
Transport radius minimizes the sum of absolute prefix-weight differences
over cyclic cuts. It is distinct from Hamming distance. `OddCycle` supplies
cycle arithmetic but does not supply primitivity or minimal period.

## Verified baseline

The current local `main` checkpoint is `c7c8161` plus the repository
infrastructure commits `e29396c`, `c369b10`, `bd4b655`, and `1cdb765`. The
proof checkpoint passed a full local build of 8,925 jobs before promotion.
The infrastructure locks dependencies, adds a fast CI sanity gate, a pull
request template, and the repository working agreements in `AGENTS.md`.

The verified library contains the six cost-four flow families, normalization
to a zero cut, the genuine advanced parity origin, signed height-two local
bits, exact local numerator coefficients, coprime cancellation, a finite
natural divisor list, and elementary logarithmic bounds. All corresponding
modules are root-imported. No full transport-family exclusion is proved.
Consult the [theorem index](THEOREM_INDEX.md) for exact statements and scope.

## Current branch and next work

The former local-word bridge is now promoted. It includes the height-two and
connected local-word bridges, their elementary denominator bounds, and the
ordered `[3,1]` topology. `Radius4TransportThreeOneBits.lean` now proves the
two component-level local exchanges: a triple run gives `0ab1 ↔ 1ab0`, while
the isolated run gives `01 ↔ 10`. These are reductions only: their joint
arithmetic exclusion remains unproved.

The height-two and connected applications conclude respectively `D = 5` and
`D ≤ 65` under their stated hypotheses; these bounds are not full family
exclusions. The [theorem index](THEOREM_INDEX.md) records exact statements.

The existing cycle-specific shifted-origin identities are available for
applications, but they do not replace the generic word result.

The next arithmetic obligation is the precise lower bound for
`A log 2 - L log 3` in [ANALYTIC_DEPENDENCY.md](ANALYTIC_DEPENDENCY.md).
That note gives all constants and hypotheses. Pinned Mathlib supplies
elementary logarithm and continued-fraction support, but no corresponding
quantitative two-logarithm theorem was located. The intended cutoff
`L < 7000`, finite exponent certificate, and structural exclusions each need
their own formal proof. A final statement conditional on the missing bound
would not complete the target.

After the height-two and connected `[4]` families, continue with `[3,1]`,
`[2,2]`, `[2,1,1]`, and `[1,1,1,1]`; bracket entries are lengths of maximal
consecutive active-edge runs. Assemble the generic theorem only after every
family is excluded.

## Validation and documentation

Read `AGENTS.md` first. Work in a small, isolated theorem-family branch. While
iterating, build only the module being edited; do not routinely run the full
library build. Before opening a PR, run the required disallowed-placeholder
grep, update the theorem index, and use a full `lake build` only as the final
integration check. Do not run `lake update`: dependencies are locked by the
committed manifest.

The repository pins Lean `v4.34.0-rc2` and Mathlib
`69fe4f49ffbc9580a2c3ae6d29591ef6d1d4131e`. Install `elan`, then use
`lake update` and `lake build` from the repository root. Proof placeholders,
new mathematical axioms, and `native_decide` are not allowed.

The endpoint is the verified local theorem on main with full green builds.
It would not establish that every nontrivial Collatz cycle contains this
configuration, or prove the Collatz conjecture.
