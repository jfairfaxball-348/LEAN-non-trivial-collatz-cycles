# Current authoritative checkpoint

Date: 2026-09-05

This file records the authoritative stopping point of the first substantive Radius-4 formalisation attack. The repository itself remains authoritative: a future session must still inspect `main`, recent commits, open pull requests, CI, and this file before continuing.

## Promoted code checkpoint

The last mathematical promotion before this handover is:

`f6c40cabd3f62f372a64eef0c6ecfe8657b2ac2e`

It passed Lean CI and includes the promoted strict-denominator theorem for nontrivial odd cycles.

This handover file is a documentation-only commit after that mathematical checkpoint.

## Kernel-verified mathematical state

The following chain is now promoted on `main`.

1. A genuine length-`A` `halfStep` parity-word encoding for an `OddCycle`.
2. The exact cycle denominator `D = 2^A - 3^L`, derived from the odd-to-odd cycle equations.
3. The full-period parity count `#odd bits = L`.
4. Equality between the genuine parity-word denominator and `2^A - 3^L`.
5. Full-`D` divisibility of the genuine parity-word numerator.
6. Equality of the parity-word numerator with the independently composed odd-to-odd numerator.
7. Exact Radius-4 directional balance: two `true -> false` and two `false -> true` mismatches.
8. Exact rotation/advance semantics for the Collatz-derived parity word: rotating by a cyclic shift agrees with reading the same periodic `halfStep` orbit from the advanced state.
9. Full-denominator arithmetic at arbitrary shifted origins.
10. Finite-word append and block-swap numerator identities.
11. Exact base-versus-advanced numerator comparison:
   `D * (advancedState - baseState) = shiftedNumerator - baseNumerator`.
12. The corresponding full-`D` divisibility of the actual shifted-minus-base numerator difference, derived from the cycle rather than inserted as an eligibility assumption.
13. Extraction of the four actual Collatz orbit boundary positions from Radius 4: two odd-to-nonodd and two nonodd-to-odd positions.
14. At a Radius-4 shift the advanced `halfStep` state is not the base state, and therefore the exact full-`D` numerator difference is nonzero. No global primitivity hypothesis is needed for this particular conclusion.
15. Denominator one forces `A = 2`, `L = 1`, and the trivial odd node `1`; consequently every `OddCycle.IsNontrivial` satisfies the strict eligibility predicate `1 < 2^A - 3^L`.

Important promoted commits in this chain include:

- `fd7dafcbcda583ffd1de140e508c869396f5e8a6` — genuine parity-word/full-denominator bridge.
- `acc1bc66d4d4060d48a1630cf8302f6928c4199c` — rotation/advance and shifted-denominator semantics.
- `36722d8f23d895875cda4339ee8dd11fcbbced7d` — finite block arithmetic, exact rotated numerator comparison, four-boundary extraction, and nonzero Radius-4 numerator consequence.
- `f6c40cabd3f62f372a64eef0c6ecfe8657b2ac2e` — strict denominator positivity for nontrivial cycles.

## The Radius-4 theorem is not proved

Do not state or imply that the Radius-4 local impossibility theorem is complete.

The representation and full-denominator bridges that were previously open are now closed. The first genuinely unresolved local step is the sparse arithmetic forced by the four mismatch boundaries.

The exact challenge is not merely to say that four bits changed. `wordNumerator` weights a true bit by a positional power of two and by a power of three depending on the number of later true bits. Therefore a Radius-4 comparison may also change the weights of common true bits lying between mismatch boundaries. A correct proof must account for that structure, probably by decomposing the cyclic word into the intervals determined by the four boundaries or by proving an equivalent weighted-prefix/suffix identity.

The desired contradiction must be derived from the actual Collatz parity words and the already-proved exact relation

`D * (advancedState - baseState) = shiftedNumerator - baseNumerator`,

with the right-hand side nonzero under Radius 4 and `D > 1` available for nontrivial cycles.

Do not replace this missing arithmetic with an assumption saying that the numerator difference has the desired sparse form, is too small, or cannot be divisible by `D`.

## Experimental branch deliberately not promoted

PR #15, branch

`formalize/word-numerator-weighted-terms-20260905`

at repaired head

`aa3aae42db7732a8111eeedf100ae30ccc35c8cc`

is an isolated experiment exposing the weighted true-bit form of `wordNumerator`.

It defines a list of contributions of the form

`2^(offset+j) * 3^(number of true bits after j)`

and proves on that branch that their sum equals the exact recursive `wordNumerator`.

The first CI run failed only on the elementary commutativity goal `listOnes bs + 1 = 1 + listOnes bs`. That proof was repaired, and the repaired CI run completed successfully.

However, PR #15 was tested against the earlier base `36722d8f...`; `main` subsequently advanced through the strict-denominator promotion and this documentation handover. Therefore **none of PR #15 is authoritative or promoted at this freeze**. A future session should freshly transplant or rebase the small weighted-numerator delta onto current `main`, rerun full Lean CI, and promote only if that fresh integration is green.

## Period/minimality discipline

`OddCycle` records a positive cyclic representation but does not assert that its listed period is minimal. `IsNontrivial` is already defined separately.

Do not silently assume rotational primitivity or minimality. The proved Radius-4 nonzero-state/numerator step does not need primitivity because exact Hamming distance four already implies the rotated parity word differs from the base word.

If a later sparse arithmetic theorem genuinely requires a primitive/minimal representation, state the exact condition and prove that the intended nontrivial cycle representation satisfies it, or keep it as an explicit local-theorem hypothesis with the scope documented. Do not conflate nontriviality, primitivity, and minimality.

## Separate work that is not the current local blocker

The reverse extraction from an arbitrary ordinary positive periodic Collatz point into canonical `OddCycle` data is not complete. PR #6 is an older development line for that Stage-1 direction.

That reverse bridge is not required to continue the present local Radius-4 theorem from explicit `OddCycle` data. Do not divert into it unless the local obstruction has been completed or the repository's current roadmap explicitly reprioritises it.

Likewise, even a completed local Radius-4 obstruction would not by itself exclude all nontrivial Collatz cycles. A separate global encounter theorem would still be required to show that every hypothetical nontrivial cycle necessarily produces an eligible Radius-4 configuration.

## Recommended next attack

1. Inspect current `main`, this checkpoint, recent commits, open PRs, and CI before doing any work.
2. Resolve PR #15 first. Its repaired head is green against the older base, so freshly transplant/rebase the small weighted-numerator delta onto current `main`, rerun full Lean CI, and promote only if the new integration is green.
3. Use the weighted-numerator representation only as a tool, not as the conclusion. Formalise how an exact Radius-4 rotation partitions the chronological parity period into intervals on which suffix odd counts differ by fixed small offsets.
4. Derive an exact closed formula for `shiftedNumerator - baseNumerator` from those four boundaries. Be alert that common true bits between boundaries can acquire different powers of three.
5. Combine that exact formula with the promoted full-`D` identity, nonzero quotient, and `D > 1` for `IsNontrivial`.
6. Attempt the actual arithmetic impossibility. If the intended contradiction is false or needs an additional hypothesis, stop and record the precise counterexample or missing condition rather than strengthening assumptions ad hoc.
7. Only after a kernel-verified local theorem exists, update `THEOREM_INDEX.md`, `FORMALISATION_ROADMAP.md`, and the Radius-4 scope documentation.

## Repository hygiene at freeze

- PR #14 was fully green and merged; its merge commit is `f6c40cabd3f62f372a64eef0c6ecfe8657b2ac2e`.
- Stale PR #10 was closed as superseded by PR #14.
- PRs #11 and #13 were already closed as superseded by the promoted PR #12 line.
- PR #15 is green on its repaired old-base head but remains experimental and unpromoted; fresh current-main integration is required.
- PR #6 remains an unrelated/open reverse-bridge development line.

The next session should treat repository state, not this prose alone, as final authority.