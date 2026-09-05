# Current authoritative checkpoint

Date: 2026-09-05

The repository itself remains authoritative. A future session must still inspect live `main`, recent commits, open pull requests, CI, this file, and the theorem/roadmap documentation before continuing.

## Promoted mathematical checkpoint

The latest promoted mathematical `main` at this closeout is:

`24463e599f05098ad8e7584610334a1218cad4fa`

This includes the green merge of PR #22, `Collapse weighted Radius-4 cyclic sum to four terms`.

Important immediately preceding promoted commits are:

- `afac4e21b6f86ab0c124fbf4c275561382d5767d` — exact weighted Radius-4 boundary support;
- `ad10df5b0d749b3571512a63f13f41918e98b821` — exact weighted composition of the genuine shifted-minus-base numerator difference;
- `1539ab7d6b97704ccd62ba60c88ba1044baf6c41` — exact sparse local difference forcing at the four Radius-4 mismatch positions;
- `c6ed7b9d50880dcae950aa030905acd4b2a878e3` — freshly integrated weighted true-bit form of `wordNumerator`;
- `f6c40cabd3f62f372a64eef0c6ecfe8657b2ac2e` — denominator one forces the trivial cycle, so every nontrivial odd cycle has `1 < 2^A - 3^L`.

## Kernel-verified Radius-4 chain now promoted

The promoted development proves all of the following from genuine `OddCycle` / `halfStep` orbit data.

1. The length-`A` genuine parity word and exact denominator `D = 2^A - 3^L`.
2. Exactly `L` odd bits in one full `A`-step parity period.
3. Equality of the parity-word denominator with `D` and full-`D` divisibility of the genuine parity-word numerator.
4. Equality of that parity-word numerator with the independently composed odd-to-odd numerator.
5. Exact Radius-4 directional balance: two `true -> false` and two `false -> true` mismatches.
6. Exact rotation/advance semantics and full-denominator identities at shifted orbit origins.
7. Exact relation

   `D * (advancedState - baseState) = shiftedNumerator - baseNumerator`.

8. The Radius-4 shifted state is genuinely different from the base state, hence this numerator difference is nonzero.
9. Every nontrivial `OddCycle` satisfies `D > 1`.
10. `wordNumerator` is exposed as a sum of terms with exact powers `2^position * 3^(later odd-count)`.
11. Subtracting the two actual `halfStep` recurrences gives an exact local forcing term. Under Radius 4 it is nonzero at exactly four genuine orbit positions: two negative odd forcings `-(2*x+1)` and two positive odd forcings `+(2*x+1)`.
12. Those local forcings compose with the correct shifted suffix powers of three. Thus common odd bits between mismatch boundaries are retained correctly rather than ignored.
13. The actual shifted-minus-base numerator difference is identified with the weighted finite-orbit forcing composition.
14. Each cyclic local forcing has an exact positive positional/suffix weight. Weighting preserves support, so exact Radius 4 gives exactly four nonzero weighted terms.
15. The sum of the cyclic weighted local terms over the whole encoding period collapses exactly to those four genuine boundary contributions, with two positive and two negative weighted odd forcings.

The Radius-4 local impossibility theorem is still **not proved**.

## Exact remaining local gap

The two promoted sides are now very close:

- the complete genuine numerator difference has an exact weighted forcing composition;
- the cyclic weighted forcing sum has an exact four-boundary closed form.

What is still missing on `main` is the clean bridge identifying the complete chronological/range weighted sum with the cyclic weighted-term sum in the form needed to combine those two facts without assumptions.

Once that bridge is promoted, the numerator difference can be rewritten as an explicit four-boundary arithmetic expression. The next mathematical question is then whether the resulting exact identity, together with the already-proved nonzero quotient and `D > 1`, yields an actual contradiction for a nontrivial cycle or exposes a further genuine condition that must be proved.

Do not replace this with assumptions that the four-term expression is small, indivisible by `D`, conveniently ordered, primitive, or minimal.

## Experimental PR #21 — useful but unpromoted

PR #21, `Identify the weighted forcing range sum`, was created from the earlier promoted base

`afac4e21b6f86ab0c124fbf4c275561382d5767d`

with head

`267cbb739261e9749bd582a7f703e9e518995548`.

Its substantive Lean development introduces a telescoping potential for the pair of genuine `halfStep` orbits and proves:

- each natural-indexed weighted local forcing is one adjacent potential difference;
- the full chronological range telescopes;
- an in-range natural representative agrees with the corresponding cyclic `radiusWeightedDifferenceTerm`;
- intended full-period range-sum identities connecting the denominator/state difference and shifted-minus-base numerator difference to the weighted range sum.

The first CI run reached the final endpoint-normalisation theorem and failed there for proof-engineering reasons:

- one `orbitDifferencePotential ... 0` occurrence remained folded, so the attempted rewrite of the shifted full-period odd count did not match;
- two `simp` arguments were flagged as unused.

The local telescoping mathematics compiled before that point. This is **not** evidence of a mathematical counterexample, but PR #21 is not green and is not authoritative.

Because `main` has since advanced through PR #22, a future session must not merge PR #21 directly. Freshly transplant only the useful `DifferenceForcingRangeSum` delta onto current `main`, repair the endpoint proof by establishing the endpoint potentials explicitly, rerun full Lean CI, and promote only if green.

## Interpretation of the earlier `nonzero multiple of D` sanity check

The observation that a nonzero multiple of `D` is not automatically contradictory remains only a warning against a shortcut. It does not weaken the promoted proof state.

The repository already has the stronger exact quotient identity with the literal state difference. The final Radius-4 contradiction must come from the exact four-boundary arithmetic, not from the bare facts `D > 1`, divisibility, and nonzeroness alone.

## Minimality / primitivity discipline

`OddCycle` does not assert a minimal represented period. `IsNontrivial`, primitivity, and minimality remain distinct notions.

No promoted theorem in the current Radius-4 chain requires primitivity to show that the Radius-4 shifted state differs from the base state: exact Hamming distance four already implies the rotation differs.

If later arithmetic genuinely needs minimality or primitivity, identify the exact required property and prove it from the intended cycle representation if possible. Otherwise keep it as an explicit hypothesis of a deliberately weaker theorem. Do not introduce it silently.

## Separate problems that remain out of scope for this local attack

The reverse extraction of an arbitrary ordinary positive periodic Collatz point into canonical `OddCycle` data remains separate and is not the present blocker.

Likewise, even a completed local Radius-4 impossibility theorem would not exclude all hypothetical nontrivial Collatz cycles. A separate global encounter theorem would still be needed to show that every such cycle necessarily produces an eligible Radius-4 rotation.

## Recommended next session

1. Verify live `main`, open PRs, CI, and this checkpoint.
2. Inspect closed/experimental PR #21 and its CI failure, but do not merge its stale-base history.
3. Freshly transplant `DifferenceForcingRangeSum.lean` onto current `main`.
4. Repair the endpoint potential proof explicitly. A robust route is to prove separate lemmas for `orbitDifferencePotential ... total` and `orbitDifferencePotential ... 0`, then derive the full range-sum identity from those lemmas rather than relying on fragile unfolding/rewrite order.
5. Run full Lean CI and promote only if green.
6. Combine the promoted range-sum bridge with the already-promoted four-boundary cyclic-sum theorem to derive an exact four-term formula for the genuine shifted-minus-base numerator difference.
7. Then attack the actual four-term arithmetic contradiction. If it fails, isolate the precise counterexample or missing condition rather than adding convenient assumptions.
8. Update `THEOREM_INDEX.md`, `FORMALISATION_ROADMAP.md`, and this checkpoint after the next promoted mathematical result.

## Repository hygiene at closeout

- PR #17: green and merged; clean current-main weighted numerator integration.
- PR #18: green and merged; clean current-main sparse local forcing integration.
- PR #19: green and merged; exact weighted difference-forcing composition.
- PR #20: green and merged; exact four-position weighted boundary support.
- PR #22: green and merged; full cyclic weighted sum collapses to the four Radius-4 boundaries.
- PR #21: experimental range-sum bridge; CI failed only at endpoint proof normalisation and remains unpromoted/stale-base.
- PR #6: older reverse-bridge development line; not the current local blocker.
