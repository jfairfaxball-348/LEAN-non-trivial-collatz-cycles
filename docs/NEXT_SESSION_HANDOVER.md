# Development handover

Date: 2026-09-10

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

The current baseline is `6888142` ("Formalize Radius-4 finite and LMN
scaffolding"). New work described below is uncommitted. No new full build,
commit, or PR has been made. Historical root-build evidence is preserved in
the checkpoint; it must not be presented as validation of the current tree.

The verified library contains the six cost-four flow families, normalization
to a zero cut, the genuine advanced parity origin, signed height-two local
bits, exact local numerator coefficients, coprime cancellation, a finite
natural divisor list, and elementary logarithmic bounds. All corresponding
modules are root-imported. No full transport-family exclusion is proved.
Consult the [theorem index](THEOREM_INDEX.md) for exact statements and scope.

## Newly verified finite work

`Collatz/Radius4FiniteCertificate.lean` proves the complete seven-triple
certificate for `0 < L < A`, `L < 7000`, and the eight-element denominator
list. Modular order reduces to `A < 16`. It then applies the existing
small-weight certificate and finite word exclusions. Its height-two and
generic small-denominator word theorems retain `L < 7000` explicitly.

`Collatz/Radius4ConnectedFinite.lean` derives the full denominator list from
connected geometry, excludes that family below weight 7000, and removes
height two and connected `[4]` from the normalized generic classification in
that range. The four disconnected families remain open.

Both files passed their targeted builds and are imported by the root source.
The finite build completed with exit status 0 (177 seconds), and the connected
build completed with exit status 0 (170 seconds). No full build was run.
The axiom audit of all eight new public theorems passed and listed only
`propext`, `Classical.choice`, and `Quot.sound`.
The inherited `Radius4LMNInterpolation.lean`, zero-power proof repair, and
their earlier documentation remain uncommitted and preserved. The monomial
auxiliary is not the actual quantitative LMN construction.

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
`L < 7000` and unbounded structural exclusions still need proofs. The finite
exponent certificate and its word exclusions are now proved under that
explicit range hypothesis. A final statement conditional on the missing
bound would not complete the target. The additional source-specialization
gap is recorded in `ANALYTIC_DEPENDENCY.md` and must also be resolved.

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
`69fe4f49ffbc9580a2c3ae6d29591ef6d1d4131e`. Use the committed locked
manifest; do not run `lake update` or change the pin during proof work. Proof placeholders,
new mathematical axioms, and `native_decide` are not allowed.

The endpoint is the verified local theorem on main with full green builds.
It would not establish that every nontrivial Collatz cycle contains this
configuration, or prove the Collatz conjecture.
