# Radius 4: definitions, target, and verified boundary

The ordinary Collatz map sends even `x` to `x/2` and odd `x` to `3*x+1`.
Its familiar positive cycle is `1 → 4 → 2 → 1`. This project studies a
specific obstruction to possible additional cycles, using binary parity
words and a distance between a word and a rotation of itself.

## Cycle encoding and arithmetic

An `OddCycle L` records positive odd nodes and exact equations

`3*x_i+1 = 2^a_i*x_(i+1)`.

The positive exponent `a_i` counts divisions by two before the next odd node.
The auxiliary map `halfStep` divides by two on every transition, including
its odd transition `(3*x+1)/2`. The resulting parity word has length
`A = sum a_i` and exactly `L` ones, with a one marking an odd source state.
`parityWord : ZMod A → Bool` indexes this actual orbit cyclically.

Composition gives `D*x_0 = Q(w)`, with full integer denominator
`D = 2^A-3^L` and exact chronological numerator `Q = wordNumerator`.
The numerator satisfies `Q([])=0` and
`Q(b::bs)=3^(listOnes bs)*bitOffset b+2*Q(bs)`, where `bitOffset` is zero
for a zero bit and one for a one bit. Lean proves the full identity and
its shifted-origin versions, denominator positivity, and `D > 1` under
`c.IsNontrivial`, meaning at least one odd node is not `1`.

## Transport radius

Compare a cyclic source word and target word with the same length and number
of ones. Choose a cut and read positions in cyclic order. Let

`G_k = target ones in the first k positions - source ones in those positions`.

Then `G_0 = G_A = 0`, and each increment is `−1`, `0`, or `1`. Charge the
internal boundary after each of the first `A-1` positions:

`cost at the cut = sum_{k=1}^{A-1} |G_k|`.

An active edge is an internal boundary with nonzero flow. Its height is
`|G_k|`. Exact transport radius is the minimum of the cut costs over every
cyclic cut. `IsExactTransportRadius` defines this minimum by a universal lower
bound and a cut achieving equality. `IsTransportRadiusFour w shift` applies
it to `w` and `rotate w shift`; `OddCycle.IsCycleTransportRadiusFour` applies
it to an actual cycle parity word.

Hamming distance instead counts unequal positions. The separate predicates
`IsRadiusFour` and `OddCycle.IsCycleRadiusFour` have Hamming hypotheses.
Their results require a proof of those hypotheses before reuse in this
transport development.

## Verified cost-four classification

At a cost-four equal-weight cut, there are six families:

- Height two: three consecutive active edges have magnitudes `(1,2,1)`.
- Unit height: four active edges form maximal consecutive runs with lengths
  `[4]`, `[3,1]`, `[2,2]`, `[2,1,1]`, or `[1,1,1,1]`, up to permutation.

For example, `[3,1]` means one block of three consecutive active boundaries
and one isolated active boundary. `transportActiveEdgeRuns` preserves their
actual order; only the family label forgets the order.

The classification and cut normalization are verified. A minimizing cut can
be moved to zero by rotating both words, retaining the same relative shift.
For cycle words, `OddCycle.cycleTransportRadiusFour_exists_advanced_zero_cut`
identifies the genuine advanced orbit origin. See the
[theorem index](THEOREM_INDEX.md) for the component theorems.

## Exact target and open exclusions

The intended theorem concerns a generic cyclic word of length `A` with
`L` ones, under `0 < L < A`, `D > 1`, `D ∣ Q(w)`, explicit primitivity, and
a nonzero rotation shift. Primitivity means that no nonzero shift fixes the
word. `OddCycle` does not supply this property or a minimal represented period.
The conclusion excludes exact transport radius four.

No complete family exclusion or final local theorem has yet been proved.
Verified prerequisites include signed height-two bits `0011 ↔ 1100`, local
numerator coefficients, coprime context cancellation, and elementary
logarithmic upper bounds.  The finite module
`Collatz/Radius4SmallCases.lean` additionally excludes the height-two branch
when `D = 5` and the word has at most three odd positions; it is not a
complete height-two exclusion. The new generic word and local-bit work on
`codex/r4-local-word-bridge` passes the local root build and bridge axiom
audit; no CI promotion is claimed for this newer revision.

The first exclusions, height-two and connected `[4]`, still need the
quantitative lower bound stated in
[ANALYTIC_DEPENDENCY.md](ANALYTIC_DEPENDENCY.md), followed by a proved finite
arithmetic reduction. The remaining families are `[3,1]`, `[2,2]`, `[2,1,1]`,
and `[1,1,1,1]`. Full source-numerator divisibility must be retained throughout.

The target is a local obstruction. It does not assert that every other cycle
has such a rotation, exclude all other Collatz cycles, or prove the Collatz
conjecture.
