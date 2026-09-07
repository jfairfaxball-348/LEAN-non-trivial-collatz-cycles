# Development handover

Date: 2026-09-07

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

PR #34 merged at `d7d1f372635c4d749da2172e16f247ba68b3d750`; its verified
head was `98c0147b420a1112830d54d8fb537e7218ea1245`.
The full local build passed with 8,912 jobs. GitHub Actions run `34115337625`
passed its actual Build step, as did post-merge main run `34115689962`.
The audit of 27 new public lemmas found only `propext`, `Classical.choice`,
and `Quot.sound`, where used.

The verified library contains the six cost-four flow families, normalization
to a zero cut, the genuine advanced parity origin, signed height-two local
bits, exact local numerator coefficients, coprime cancellation, a finite
natural divisor list, and elementary logarithmic bounds. All corresponding
modules are root-imported. No full transport-family exclusion is proved.
Consult the [theorem index](THEOREM_INDEX.md) for exact statements and scope.

## Current branch and next work

`codex/r4-local-word-bridge` adds component helpers and a height-two
outside-bit agreement lemma in `Radius4TransportSigned.lean`, plus
`Collatz/CyclicWordList.lean`, `Collatz/Radius4WordRotation.lean`,
`Collatz/Radius4FullDenominatorWord.lean`,
`Collatz/Radius4TransportConnectedBits.lean`,
`Collatz/Radius4TransportLocalWords.lean`, and
`Collatz/Radius4ConnectedBounds.lean`. These changes have **not completed
full validation and have not been promoted** at this checkpoint.
Individual module builds passed for `CyclicWordList.lean`,
`Radius4WordRotation.lean`, and `Radius4FullDenominatorWord.lean`, plus the
updated transport definition, topology, height-two, and component modules.
Validation was stopped during the signed-flow module check for closeout.
The remaining module checks, full root build, and 24-new-lemma axiom audit
are incomplete; no CI result is claimed for this snapshot. Development is
paused here, without promotion or additional formalisation.

The last module applies the proposed bridges to the actual strict positive
full denominator: its statements conclude `D = 5` for height-two and
`D ≤ 65` for connected four-edge flow. These bounds are not family
exclusions. The [theorem index](THEOREM_INDEX.md) lists all 24 new public
lemma statements awaiting full-branch validation.

If development resumes, first finish validation of the existing component,
signed-flow, connected-bit, common-context, and denominator-application proofs.
Do not duplicate their current source or treat it as verified before checking
it. The existing cycle-specific shifted-origin identities are available for
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

Check current main, the working branch, relevant pull requests, and actual CI
Build results. Keep each required module in `Collatz.lean` and run the full
`lake build`; an earlier green revision does not validate later edits. Before
promotion, audit theorem dependencies and synchronize the checkpoint, index,
roadmap, and proof map.

The repository pins Lean `v4.34.0-rc2` and Mathlib
`69fe4f49ffbc9580a2c3ae6d29591ef6d1d4131e`. Install `elan`, then use
`lake update` and `lake build` from the repository root. Proof placeholders,
new mathematical axioms, and `native_decide` are not allowed.

The endpoint is the verified local theorem on main with full green builds.
It would not establish that every nontrivial Collatz cycle contains this
configuration, or prove the Collatz conjecture.
