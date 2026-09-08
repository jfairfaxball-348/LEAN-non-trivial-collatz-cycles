# Local proof map

Date: 2026-09-07

This document connects the mathematical steps of the intended local theorem
to this repository's definitions, verified lemmas, and open obligations.
The final theorem and all complete transport-family exclusions remain unproved.

## Objects and exact target

The ordinary Collatz map halves even `x` and sends odd `x` to `3*x+1`.
The auxiliary `halfStep` map divides by two at every transition. Its parity
encoding is a binary word; one denotes an odd source state. `OddCycle L`
records `L` positive odd nodes with exact transitions
`3*x_i+1 = 2^a_i*x_(i+1)`, giving parity length `A = sum a_i`.

For a generic cyclic binary word `w` of length `A` and weight `L`, define its
chronological numerator by `Q([])=0` and
`Q(b::bs)=3^(number of ones in bs)*b+2*Q(bs)`, interpreting bits as zero or
one. This is Lean's `wordNumerator`. The full denominator is the integer
`D = 2^A-3^L`.

The target excludes exact transport radius four for a nonzero self-rotation
under `0 < L < A`, `D > 1`, `D ∣ Q(w)`, and `IsPrimitive w`. Primitivity
means that only the zero rotation fixes the word. `OddCycle` does not imply
it. The source-numerator divisibility itself must remain available; a
numerator-difference divisibility statement alone does not supply it.

For equal-weight source and target words, a cyclic cut defines prefix flow
`G_k = target-prefix ones - source-prefix ones`. The cut cost is
`sum_{k=1}^{A-1} |G_k|`. Exact transport radius four means every cut costs at
least four and some cut costs four. The formal predicate is
`IsTransportRadiusFour`. The separate `IsRadiusFour` predicate counts four
unequal positions in Hamming distance.

## Flow classification and normalization — verified

| Mathematical ingredient | Lean source |
| --- | --- |
| Binary increments, zero endpoint, exact transport radius | `Collatz/Radius4Transport.lean` |
| Remove zero-flow edges and count four unit-height active edges | `Collatz/Radius4TransportTopology.lean` |
| Magnitude bound two and unique height-two profile `(1,2,1)` | `Collatz/Radius4TransportHeightTwo.lean` |
| Ordered active components and all five unit-height families | `Collatz/Radius4TransportComponents.lean` |
| Move the cut to zero and identify the advanced cycle origin | `Collatz/Radius4TransportCovariance.lean` |

An active edge is an internal boundary with nonzero prefix flow. Unit-height
means every active edge has absolute flow one. Their maximal consecutive run
lengths are `[4]`, `[3,1]`, `[2,2]`, `[2,1,1]`, or `[1,1,1,1]`, up to
permutation. The actual ordered components are retained in
`transportActiveEdgeRuns`; `List.Perm` labels only the family.

These modules are included in the verified root build. The
[checkpoint](CURRENT_CHECKPOINT.md) records the exact promotion evidence.

## First exclusions: height-two and connected four-edge flow

The intended chain is:

1. Derive the actual local words from signed flow: height-two
   `0011 ↔ 1100` and connected four-edge `0abc1 ↔ 1abc0`.
2. Prove common prefix/suffix decompositions and rotation preservation of
   full-denominator source divisibility.
3. Evaluate connected coefficients `15,17,21,27,29,35,47,65` and the
   height-two coefficient of absolute value `15`.
4. Cancel the coprime context factor, a product of powers of two and three,
   to restrict the strict positive full denominator to
   `5,7,13,17,29,35,47,65`.
5. Establish `0 < A log 2-L log 3 < 65/3^L`.
6. Prove and apply the exact quantitative lower bound to obtain `L < 7000`.
7. Prove the seven-triple finite exponent certificate and exclude the
   remaining word configurations using primitivity and full divisibility.

The current verified arithmetic coverage is narrower than this full chain:

| Verified ingredient | Lean source and application boundary |
| --- | --- |
| Signed unit flow and actual height-two bits | `Collatz/Radius4TransportSigned.lean`; connected word extraction remains |
| Common-context replacement and exact coefficients | `Collatz/Radius4ConnectedCoefficients.lean`; complete word decompositions must be supplied |
| Coprime cancellation and finite natural divisor list | `Collatz/Radius4ConnectedDenominators.lean`; the stated divisibility hypotheses remain explicit |
| Logarithmic defect, upper bound, and `A < 2L` reduction | `Collatz/Radius4LogDefect.lean`; no quantitative lower bound or cutoff is asserted |

PR #34 promoted these four modules at
`d7d1f372635c4d749da2172e16f247ba68b3d750`. The local build passed with
8,912 jobs; PR run `34115337625` and main run `34115689962` passed their
actual Build steps. The 27-public-lemma audit found only standard core axioms.

New component helpers and a height-two outside-bit agreement lemma in
`Collatz/Radius4TransportSigned.lean`, plus `Collatz/CyclicWordList.lean`,
`Collatz/Radius4WordRotation.lean`, `Collatz/Radius4FullDenominatorWord.lean`,
`Collatz/Radius4TransportConnectedBits.lean`,
`Collatz/Radius4TransportLocalWords.lean`, and
`Collatz/Radius4ConnectedBounds.lean` on `codex/r4-local-word-bridge`,
pass the local root build and the bridge/application theorem audit; no CI
promotion is claimed for this newer revision.
The last module's application statements target `D = 5` for height-two and
`D ≤ 65` for connected four-edge flow, retaining source-numerator
divisibility and deriving the local replacements from the zero-cut geometry.
Existing cycle-specific shifted-origin identities remain available, but the
endpoint requires generic word scope. The exact missing lower-bound proposition and
finite certificate target appear in
[ANALYTIC_DEPENDENCY.md](ANALYTIC_DEPENDENCY.md).

## Remaining family exclusions and assembly — unproved

After the first exclusions, handle `[3,1]`, `[2,2]`, `[2,1,1]`, and
`[1,1,1,1]`. Their bracket entries specify lengths of consecutive active-edge
runs. Each family requires its own complete arithmetic argument. The final
isolated-edge family also requires the planned reduction to a smaller cyclic
object and a proof that closes that reduction. No such full exclusion is
currently claimed.

Combine all families to prove the generic primitive full-denominator local
theorem. Genuine `OddCycle` numerator and rotation identities then supply
cycle applications subject to the explicit hypotheses. A statement only
about `OddCycle` would not establish the generic target.

The theorem would remain local: it would not show that every other Collatz
cycle has an exact-radius-four self-rotation, and would not prove the Collatz
conjecture.
