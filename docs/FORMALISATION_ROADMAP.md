# Formalisation roadmap

This roadmap describes the intended order of work inside this standalone repository. Every mathematical dependency needed by a theorem must be defined or proved here; no unpublished or external argument is treated as an assumption.

## Stage 0 — Foundations

Status: **complete as infrastructure**.

The repository defines the ordinary Collatz map `step`, the one-division map `halfStep`, cyclic Boolean words, rotation, Hamming distance, exact Radius 4, and the denominator expression `2^A - 3^L`.

## Stage 1 — Odd-to-odd Collatz cycle arithmetic

Status: **forward direction complete for the present local theorem; reverse extraction separate**.

The repository proves exact odd-to-odd Collatz transitions, builds `OddCycle`, composes the cycle equations, derives the genuine ordinary and `halfStep` periods, and proves the exact denominator identity.

The reverse theorem extracting canonical `OddCycle` data from an arbitrary ordinary positive periodic point remains a separate future bridge and is not the current Radius-4 local blocker.

## Stage 2 — Genuine denominator-compatible parity encoding

Status: **substantially complete for the present local attack**.

The repository defines the genuine length-`A` parity word directly from the actual `halfStep` orbit. It proves that one full parity period has exactly `L` odd bits, and that cyclic rotation agrees exactly with advancing the same periodic `halfStep` orbit.

No primitivity or minimal-period property is assumed.

## Stage 3 — Full-denominator and shifted-origin arithmetic

Status: **complete through the exact shifted-minus-base numerator identity**.

Lean proves:

- `D = 2^A - 3^L` from the cycle equations;
- `D > 0` for every positive odd cycle;
- `D > 1` for every `OddCycle.IsNontrivial`;
- the genuine parity-word denominator equals `D`;
- full-`D` divisibility of the genuine parity-word numerator;
- full-denominator identities at every shifted orbit origin;
- the exact comparison

  `D * (advancedState - baseState) = shiftedNumerator - baseNumerator`;

- under exact Radius 4, the state difference and hence this numerator difference are nonzero.

## Stage 4 — Radius-4 sparse weighted arithmetic

Status: **four-boundary support and cyclic four-term collapse promoted; chronological range bridge still open**.

The repository now proves the following chain.

1. Exact Radius 4 gives two `true -> false` and two `false -> true` genuine parity mismatches.
2. Subtracting the actual `halfStep` affine recurrences gives an exact local state-difference forcing.
3. That forcing is nonzero at exactly the four Radius-4 boundary positions, with values `-(2*x+1)` at the two down-boundaries and `+(2*x+1)` at the two up-boundaries.
4. The complete numerator difference is a weighted composition of these local forcings. The weights contain the exact chronological power of two and the shifted suffix odd-count power of three, so common odd bits between mismatch boundaries are accounted for rather than discarded.
5. Each cyclic local term is given its exact positive positional/suffix weight. Weighting preserves support.
6. The cyclic weighted sum over the full encoding period collapses exactly to four genuine boundary terms: two positive and two negative weighted odd forcings.

The remaining bridge is to identify the complete chronological/range weighted forcing sum with the cyclic weighted-term sum on current `main`.

Experimental PR #21 developed a telescoping-potential proof of this bridge, but its CI failed in the final endpoint simplification. The underlying telescoping lemmas compiled. Since `main` advanced afterward, the useful delta must be freshly transplanted and reverified rather than merged from the stale base.

## Stage 5 — Radius-4 local impossibility theorem

Status: **not proved**.

After the range/cyclic bridge is promoted, combine it with the four-boundary collapse to obtain an exact four-term formula for the genuine shifted-minus-base numerator difference.

Then attempt the actual arithmetic contradiction using only already-derived Collatz data, including the nonzero state-difference quotient and `D > 1` for nontrivial cycles.

Do not insert assumptions that:

- the four-term expression is smaller than `D`;
- `D` cannot divide it;
- the four boundary positions have a convenient ordering;
- the parity word is primitive or minimal.

If the intended contradiction is false under the current hypotheses, isolate the precise counterexample or missing condition and document it rather than strengthening the theorem ad hoc.

## Stage 6 — Scope and audit

For every substantive promotion:

- run full Lean CI with warnings as errors;
- keep `main` self-contained;
- update `docs/CURRENT_CHECKPOINT.md`;
- update `docs/THEOREM_INDEX.md` and this roadmap when the theorem surface materially changes;
- distinguish promoted mathematics from experimental branches.

For a completed local theorem, record its exact assumptions and keep the still-separate global encounter problem explicit.

## Separate future problem — global encounter theorem

A Radius-4 local impossibility theorem would not by itself exclude all hypothetical nontrivial Collatz cycles.

A separate theorem would still be required to prove that every hypothetical nontrivial cycle necessarily encounters an eligible Radius-4 rotation. That global problem remains deliberately outside the present local formalisation attack.
