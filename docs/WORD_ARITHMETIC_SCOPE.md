# Word arithmetic: definitions, proved identities, and open applications

The ordinary Collatz map sends an even natural number `x` to `x/2` and an
odd one to `3*x+1`. Its familiar cycle is `1 → 4 → 2 → 1`. To describe
cycles arithmetically, this repository uses the auxiliary map `halfStep`,
which sends even `x` to `x/2` and odd `x` to `(3*x+1)/2`.

A binary parity word records whether the source of each `halfStep` transition
is odd. A zero bit denotes an even source, and a one bit denotes an odd
source. This note explains the exact numerator of such a word and what the
verified arithmetic does and does not establish.

## Pure finite-word arithmetic

`Collatz/WordArithmetic.lean` defines `Realizes bits x y`: a chronological
binary list `bits` is realized from `x` to `y` when its successive states
satisfy the following equations:

- zero bit: `2*y = x`;
- one bit: `2*y = 3*x+1`.

`listOnes` counts the ones in a list. `bitOffset` is zero or one according to
the bit. The exact natural numerator is defined recursively by

`wordNumerator [] = 0`

and

`wordNumerator (b::bs) = 3^(listOnes bs)*bitOffset b + 2*wordNumerator bs`.

`realizes_composed_identity` assumes `Realizes bits x y` and proves

`2^(bits.length)*y = 3^(listOnes bits)*x + wordNumerator bits`.

This is pure affine composition and uses no cycle assumption.
`orbitBits x k` records the actual first `k` parity bits of the `halfStep`
orbit from `x`. `orbitBits_realizes` proves that these bits realize the local
equations. If `(halfStep^[k]) x = x`, then
`periodic_word_denominator_identity` proves

`(2^k-3^(listOnes (orbitBits x k)))*x = wordNumerator (orbitBits x k)`

as an integer identity. `periodic_word_fullDenominatorDivides` gives
divisibility by this entire integer denominator.

## Exact cycle parity count and denominator

An `OddCycle L` contains `L > 0` positive odd nodes, positive exponents,
and cyclic transitions `3*x_i+1 = 2^a_i*x_(i+1)`. Let `A = sum a_i`.
The file `Collatz/CycleWordArithmetic.lean` proves the count connecting the
odd-node model to its genuine `A`-step parity word:

- `OddToOddStep.orbitBits_ones`: an exact block of `a` `halfStep` transitions
  from one odd node to the next contributes exactly one odd source bit.
- `OddCycle.orbitBits_prefix_ones`: concatenating these exact blocks adds
  their counts.
- `OddCycle.orbitBits_total_ones`:
  `listOnes (orbitBits (c.node 0) A) = L`.

Consequently `OddCycle.wordDenominator_eq_cycleDenominator` identifies the
actual parity-list denominator with `D = 2^A-3^L`.
`OddCycle.cycleDenominator_mul_base_eq_wordNumerator` proves

`D*x_0 = wordNumerator (orbitBits x_0 A)`.

`OddCycle.fullDenominatorDivides_wordNumerator` records full divisibility.
`OddCycle.wordNumerator_eq_prefixNumerator` identifies this numerator with
the one independently obtained by composing odd-to-odd exponent blocks.
The denominator is not replaced by a factor or a residue.

## Shifted origins — verified

`Collatz/RotationArithmetic.lean` proves identities for a natural shift
satisfying `shift ≤ A`:

- `OddCycle.orbitBits_shift_total_ones` preserves the number of ones;
- `OddCycle.shifted_wordDenominator_eq_cycleDenominator` preserves the full
  denominator;
- `OddCycle.cycleDenominator_mul_shiftedState_eq_wordNumerator` gives the
  exact numerator identity at the advanced orbit state;
- `OddCycle.fullDenominatorDivides_shifted_wordNumerator` gives divisibility
  by that same full denominator.

`Collatz/RotationWord.lean` defines `advancedParityWord` from the advanced
actual orbit. `OddCycle.rotate_parityWord_eq_advancedParityWord` proves that
it is the corresponding cyclic rotation. These are proved cycle-specific
facts, not open items in the current roadmap.

## Generic words and the remaining local theorem

The target is broader than the cycle-specific identities: for a cyclic word
of length `A` and weight `L`, it retains `0 < L < A`, `D > 1`, `D ∣ Q(w)`,
primitivity, and a nonzero self-rotation shift. Here `Q(w)` is read
chronologically from position zero; primitive means only the zero rotation
fixes the word. `OddCycle` does not assert that property or a minimal period.

Transport radius minimizes, over cyclic cuts, the sum of absolute differences
between target and source prefix weights. The intended theorem excludes
exact radius four under the generic hypotheses. Hamming distance instead
counts unequal positions; its separate four-mismatch theorems do not establish
this transport conclusion.

The current branch's `Collatz/CyclicWordList.lean`,
`Collatz/Radius4WordRotation.lean`, `Collatz/Radius4FullDenominatorWord.lean`,
`Collatz/Radius4TransportLocalWords.lean`, and
`Collatz/Radius4ConnectedBounds.lean` pass the local root build and the
bridge/application axiom audit at the [checkpoint](CURRENT_CHECKPOINT.md); no
CI promotion is claimed for this newer revision. They connect arbitrary cyclic
words to chronological lists, preserve generic full-denominator divisibility
through rotation, and produce the required common-context decompositions.
The application statements in the last module target the full-denominator
bounds `D = 5` for height-two and `D ≤ 65` for connected four-edge flow;
neither statement is itself an impossibility result.

No complete transport-family exclusion or final local impossibility theorem
is proved. The exact remaining quantitative logarithmic dependency is stated
in [ANALYTIC_DEPENDENCY.md](ANALYTIC_DEPENDENCY.md). These arithmetic identities
also do not show that every other Collatz cycle contains a radius-four
configuration, or imply the Collatz conjecture.
