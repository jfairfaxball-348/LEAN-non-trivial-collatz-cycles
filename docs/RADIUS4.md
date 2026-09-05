# Radius 4: meaning, scope, and current formalisation boundary

This document is self-contained. It assumes no prior knowledge of the Collatz problem or of this repository.

## 1. The ordinary Collatz map

For a positive integer `n`, define

- `T(n) = n / 2` when `n` is even;
- `T(n) = 3n + 1` when `n` is odd.

The Collatz conjecture says that every positive starting value eventually reaches `1`. Under this unaccelerated map, reaching `1` enters the familiar cycle

`1 -> 4 -> 2 -> 1`.

A **non-trivial Collatz cycle** would be a different finite periodic orbit of positive integers.

This repository is concerned only with statements checked by Lean. A local theorem about one structural feature of a hypothetical cycle is not the Collatz conjecture and is not automatically a proof that non-trivial cycles do not exist.

## 2. Exact odd-to-odd cycle data

For two positive odd integers `x` and `y`, an odd-to-odd Collatz transition has the arithmetic form

`3x + 1 = 2^a y`,

where `a >= 1` is the number of factors of two removed before the next odd value is reached.

The Lean structure `OddToOddStep` stores the positivity, oddness, positive exponent, and this exact equation. Lean then proves that the ordinary map really reaches `y` after one odd step and `a` halving steps.

Exactness is operationally proved: before all `a` factors have been removed, the post-odd states are even, and after exactly `a` halvings the state is the odd target.

A formal `OddCycle L` is a cyclic family

`x_0, ..., x_(L-1)`

with exponents

`a_0, ..., a_(L-1)`

satisfying the odd-to-odd equation at every cyclic index.

Let

`A = a_0 + ... + a_(L-1)`.

Lean proves that one full traversal of this odd-cycle data is a genuine period of the ordinary map, using `A + L` ordinary Collatz steps.

## 3. Why the Radius-4 word has length A, not A + L

The characteristic cycle denominator is

`D = 2^A - 3^L`.

That denominator points to a denominator-compatible dynamical encoding in which one division by two occurs at every transition.

The repository therefore defines the derived map `halfStep`:

- `S(n) = n / 2` when `n` is even;
- `S(n) = (3n + 1) / 2` when `n` is odd.

This map does **not** replace the ordinary Collatz map. It is derived from it for the cyclic encoding.

An odd-to-odd edge with exponent `a_i` takes exactly `a_i` iterations of `S`. Consequently a full odd cycle takes exactly

`A = a_0 + ... + a_(L-1)`

iterations of `S`.

Lean proves this closure. Therefore the denominator-compatible cyclic parity word has length `A`.

An earlier development attempt considered an `A + L` word based directly on ordinary-map step positions. That representation was rejected before promotion because it did not align with the exponent `A` occurring in `2^A - 3^L`. The current formalisation keeps the ordinary-map bridge but uses the length-`A` `halfStep` orbit for Radius 4.

## 4. The genuine Collatz parity word

A binary cyclic word of length `n` is represented in Lean as

`ZMod n -> Bool`.

For an `OddCycle`, Lean now defines a genuine Collatz-derived word of length `A`.

At cyclic position `t : ZMod A`, `parityWord t` is true exactly when the actual `halfStep` orbit state reached after the canonical representative `t.val` is odd.

Thus this is not an arbitrary binary word with a later eligibility assumption attached. Its bits are defined directly from a proved periodic Collatz-derived orbit.

The repository also defines an arithmetic marker word `oddStartWord`. Its true positions are the cumulative exponent boundaries

`0, a_0, a_0+a_1, ...`.

Lean proves that every such boundary is an actual odd state of the `halfStep` orbit.

However, the converse theorem

`oddStartWord = parityWord`

is not yet proved. Its missing content is finite but real: every non-boundary position inside each exponent block must be shown to be even. The two words remain separate definitions until that bridge is formally established.

## 5. Cyclic rotation and Hamming distance

A finite cycle has no distinguished starting point. For a cyclic word `w` and a shift `s`, `rotate w s` reads the same circular word from the shifted index.

The **Hamming distance** between two words of equal length is the number of positions at which they differ.

A shift is at **exact Radius 4** when

`hammingDistance w (rotate w s) = 4`.

The Collatz-specific predicate now applies this definition to `OddCycle.parityWord`.

So Radius 4 is **not** four Collatz iterations and is **not** a numerical bound on a trajectory. It is an exact four-position difference between the denominator-compatible parity word and one of its cyclic rotations.

What is still missing is the formal semantic theorem for an arbitrary shift: Lean must connect `rotate parityWord s` with advancing the same periodic `halfStep` orbit by `s`. For shifts that land on an odd position, a further theorem should connect that advance with rebasing the `OddCycle` at the corresponding odd node.

## 6. The denominator is now derived inside Lean

The local odd-cycle equations are composed inductively. Lean proves

`2^A * x_0 = 3^L * x_0 + N`,

where `N` is the recursively generated inhomogeneous numerator produced by the composition.

It then proves the rearranged identity

`(2^A - 3^L) * x_0 = N`.

Therefore the complete integer denominator

`D = 2^A - 3^L`

satisfies

`D | N`,

with quotient `x_0`.

Lean also proves `D > 0` from positivity of the cycle data.

This is stronger than the original scaffold, where `D` and generic divisibility were merely definitions. It is still not the complete shift-specific Radius-4 arithmetic condition: the final local argument must derive the corresponding numerator or numerator-difference expression for a rotated/advanced encoding and prove exactly how the full `D` applies to that expression.

No proper factor of `D`, residue surrogate, or unexplained divisibility hypothesis is accepted as a replacement.

## 7. Primitivity

A cyclic word is **primitive** when no nonzero rotation fixes it exactly.

The generic definition already exists. The Collatz-specific primitivity bridge is not yet proved.

If the final local theorem requires primitivity, the repository must prove exactly which mathematical cycle hypothesis implies that `parityWord` is primitive. Minimality, non-repetition, or distinctness must not be silently conflated.

## 8. The Radius-4 local theorem target

The intended local theorem has the logical shape:

> An eligible primitive positive Collatz-cycle encoding cannot simultaneously satisfy the required full cycle-denominator arithmetic condition and possess a nonzero rotation at exact Hamming distance four.

That sentence remains a **formalisation target**, not yet a Lean theorem.

The important word is **eligible**. The repository has now formalised much of that eligibility chain, but it will not state the final impossibility theorem as proved until the rotation/rebasing and shift-specific denominator bridges are explicit.

## 9. Exact current blocker

The strongest chain currently reaches:

1. exact positive odd-to-odd Collatz equations;
2. a cyclic positive odd-cycle structure;
3. real ordinary Collatz periodicity;
4. exact exponent removal;
5. a denominator-compatible `halfStep` period of length `A`;
6. an inductively derived composed cycle identity;
7. the full denominator identity `D*x_0 = N`;
8. full-`D` divisibility of `N`;
9. a genuine length-`A` parity word defined from the actual orbit;
10. an exact Collatz-specific Radius-4 predicate on that word.

The immediate local blocker is a package of representation/arithmetic bridge lemmas:

- prove the exponent-boundary marker word equals the genuine parity word;
- prove rotation equals advancing the periodic `halfStep` orbit;
- connect odd-position advances to rebased odd-cycle data;
- derive the rotated/rebased numerator and exact full-denominator comparison relation;
- prove any primitivity hypothesis required by the final local theorem.

Only then should the four changed positions be classified and the final sparse contradiction attacked.

## 10. What a completed Radius-4 local proof would establish

Once all eligibility lemmas and the final contradiction are accepted by Lean, the result would rigorously exclude one specific local configuration: an eligible primitive positive cycle candidate carrying an exact Radius-4 rotation under the stated full-denominator arithmetic conditions.

That would be a genuine theorem about a constrained class of hypothetical Collatz cycles.

## 11. What it would not establish

A completed Radius-4 local proof would **not**, by itself:

- prove the full Collatz conjecture;
- prove that every positive integer reaches `1`;
- prove that Collatz trajectories are bounded;
- exclude every possible non-trivial cycle;
- exclude analogous configurations at every other Hamming radius;
- prove that every hypothetical non-trivial cycle must contain a Radius-4 configuration.

The last item requires a separate **global encounter/bridge theorem** showing that every hypothetical non-trivial cycle necessarily produces an eligible Radius-4 configuration. That global theorem is not part of the local Radius-4 obstruction.
