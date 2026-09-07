# Radius 4: meaning and formal boundary

## Genuine cycle encoding

The ordinary Collatz map is `n/2` on even inputs and `3n+1` on odd inputs.
An `OddCycle L` records positive odd nodes with exact equations

`3*x_i + 1 = 2^a_i * x_(i+1)`.

Lean derives their operational interpretation, ordinary periodicity, and the
denominator-compatible `halfStep` period of length `A = sum a_i`.
The genuine `parityWord : ZMod A → Bool` records the parity of the actual
`halfStep` orbit at each cyclic position. It has `L` ones.

The integer `D = 2^A - 3^L` is derived from the composed cycle equations.
Lean proves full-denominator numerator identities at the base and advanced
origins, positivity, and `D > 1` for a nontrivial OddCycle.

## Transport radius

For equal-length, equal-weight binary words, a cyclic cut defines prefix flow

`G_k = target prefix weight - source prefix weight`.

The endpoints are `G_0 = G_A = 0`, each increment lies in `{-1,0,1}`, and
the charged cut cost is

`sum_{k=1}^{A-1} |G_k|`.

`IsExactTransportRadius` specifies the exact minimum of these costs over
cyclic cuts. `IsTransportRadiusFour w shift` applies radius four to the
self-rotation pair `w, rotate w shift`.
`OddCycle.IsCycleTransportRadiusFour` applies it to the genuine parity word.

This is RL238's adjacent-transposition transport notion. It is different from
Hamming distance, which counts unequal positions. The earlier
`IsRadiusFour` and `OddCycle.IsCycleRadiusFour` definitions use Hamming
distance and remain separate support definitions.

## Completed R4-1 geometry

At a cost-four minimizing cut, the six established families are:

- height-two magnitudes `(1,2,1)` on consecutive edges;
- four unit-height edges whose maximal consecutive-run lengths, up to
  component-order permutation, are `[4]`, `[3,1]`, `[2,2]`,
  `[2,1,1]`, or `[1,1,1,1]`.

The concrete ordered components remain in `transportActiveEdgeRuns`.
Only the family label forgets their order.

PR #33 proves the cut normalization and the genuine advanced parity origin via
the existing rotation/parity-word theorem. It also root-imports all intended
transport modules and repairs the proof elaboration exposed by full CI.
R4-1 is complete for the prefix-flow target used in the blueprint.

## Primitivity and the full denominator

A word is primitive if only the zero rotation fixes it. `OddCycle` does not
supply that property or minimality. Preserve `IsPrimitive` explicitly in the
final theorem unless a separate Lean theorem proves its removal is justified.

The complete denominator must be retained. A factor, residue surrogate, or
informal eligibility statement cannot replace full-`D` divisibility.
Generic local replacement lemmas state their actual divisibility hypotheses;
their application to genuine transport geometry also requires a formal proof.

## Remaining local theorem

The established elimination order is height-two/connected `[4]`, then
`[3,1]`, `[2,2]`, `[2,1,1]`, and `[1,1,1,1]` quotient-cycle closure.

No complete elimination or final impossibility theorem is yet proved in this
repository. The first elimination already requires the explicit LMN
two-logarithm lower bound. The precise missing formal dependency and available
Mathlib support are recorded in [the analytic audit](RL238_ANALYTIC_DEPENDENCY.md).

The endpoint is the primitive full-denominator transport-Radius-4 local
impossibility theorem. It is not a global encounter theorem or a proof that all
nontrivial Collatz cycles are absent. No broader research target follows
automatically from this repository's completion.
