# RL238 to Lean working map

Date: 2026-09-07

This is a map of the established proof, not a formal dependency.
Use only the authorized RL238 Radius-4 bundle as a read-only blueprint.
The Lean repository must prove every required proposition internally.

## Conventions and final scope

RL238 uses exact cyclic adjacent-transposition transport radius, represented
here by the minimum over cyclic cuts of `sum |G_k|`, where prefix flow is
target weight minus source weight. The complete endpoint is zero for equal weights.

The target is primitive full-denominator self-rotation impossibility at exact
transport radius four. The blueprint's numerator Q has the same bit order and
recursion as Lean's `wordNumerator`. The full denominator is `2^A - 3^L`,
with strict region `D > 1`; a factor or modular surrogate may not replace it.
`OddCycle` supplies genuine cycle arithmetic but does not imply primitivity.
The final endpoint is generic in eligible binary words, not restricted to
`OddCycle`: the connected verifier retains `0 < L < A`, `D > 1`, nonzero
self-rotation shift, primitivity, and `D ∣ Q(w)`. Exact transport radius four
already excludes the zero shift. Structural exclusions use the source-numerator
divisibility itself; divisibility of the rotation difference alone is insufficient.

## R4-1 — complete

| Established ingredient | Lean source |
| --- | --- |
| Binary increments, one-Lipschitz flow, zero endpoint, exact radius | `Radius4Transport.lean` |
| Remove zero edges, exactly four unit-height active edges | `Radius4TransportTopology.lean` |
| Magnitude bound two and unique `(1,2,1)` branch | `Radius4TransportHeightTwo.lean` |
| Ordered active components and all five unit families | `Radius4TransportComponents.lean` |
| Cut normalization and genuine advanced parity origin | `Radius4TransportCovariance.lean` |

PR #33 root-imports all these modules and repairs their Lean 4.34 elaboration.
Full local and GitHub builds passed. Its merge is
`174e0914a1a039234f15e078c56d545f247dc747`.

The six families are height-two plus `[4]`, `[3,1]`, `[2,2]`, `[2,1,1]`,
`[1,1,1,1]`. The component lists remain ordered; only the family label uses
`List.Perm`. The blueprint audit requires no extra general metric-equivalence theorem.

## R4-2 — first elimination, in progress

The established connected proof is in the authorized bundle's nested
`verify_rl238_connected_radius4_closure.py`. Its order is:

1. Obtain the signed local words from the flow geometry.
2. Use rotation covariance of full-denominator divisibility and local replacement.
3. Evaluate connected coefficients `15,17,21,27,29,35,47,65` and height-two coefficient `15`.
4. Cancel the coprime context monomial; restrict full denominators to
   `5,7,13,17,29,35,47,65`.
5. Establish `0 < A log 2 - L log 3 < 65/3^L`.
6. Apply the exact LMN lower bound to prove `L < 7000`.
7. Prove the seven-triple finite denominator certificate and exclude the structural tails.

Current elementary Lean coverage:

| Established ingredient | Lean source and boundary |
| --- | --- |
| Signed unit runs; signed height-two profile and actual `0011 ↔ 1100` bits | `Radius4TransportSigned.lean`; `[4]` local extraction remains |
| Common-context replacement, eight connected coefficients, signed height-two coefficient | `Radius4ConnectedCoefficients.lean`; application requires complete list decompositions |
| Coprime context cancellation and eight possible natural denominators | `Radius4ConnectedDenominators.lean`; divisibility and strict-denominator hypotheses remain explicit |
| Exact logarithmic defect, exponential upper bound, `A < 2L` reduction | `Radius4LogDefect.lean`; no LMN lower bound or cutoff is asserted |

No complete connected-branch elimination is yet proved in Lean. The actual
normalized geometry must still supply the local lists, propagate generic source
numerator divisibility through rotation, and identify the natural divisor with
the positive full denominator. The existing OddCycle identities provide the
genuine-cycle application but do not replace that generic word scope.
The precise missing analytic theorem is documented in
[RL238_ANALYTIC_DEPENDENCY.md](RL238_ANALYTIC_DEPENDENCY.md).
Existing logarithm bounds and Legendre's theorem support elementary and finite
parts, but do not supply the quantitative two-logarithm lower bound.

## Remaining established chain

After R4-2, preserve the certified order:

- R4-3: `[3,1]`, with reduced convergents and every admissible multiple.
- R4-4: `[2,2]`, retaining both zero and nonzero skew.
- R4-5: every `[2,1,1]` skew sector.
- R4-6–7: `[1,1,1,1]` quotient cycle and minimum-growth closure.
- Assemble the primitive full-denominator transport-Radius-4 local theorem.

These eliminations and the final theorem remain unproved here.
No external certificate execution, source-file presence, axiom, or extra
hypothesis may be described as kernel verification.

## Existing support and scope

Genuine OddCycle denominator and shifted-origin identities are available.
Older `IsRadiusFour` / `OddCycle.IsCycleRadiusFour` theorems use Hamming distance;
only reuse them after their hypotheses have been formally established.
The final statement must retain transport radius and exact primitivity hypotheses.

The local theorem is the endpoint. No Radius 5, Gate A, Gate B, or global
encounter theorem belongs to this task.
