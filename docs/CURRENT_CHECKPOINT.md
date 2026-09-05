# Current authoritative checkpoint

Date: 2026-09-05

The repository itself remains authoritative. A future session must still inspect live `main`, recent commits, open pull requests, CI, this file, and the theorem/roadmap documentation before continuing.

## Promoted mathematical checkpoint

The latest promoted mathematical checkpoint at this closeout is:

`24463e599f05098ad8e7584610334a1218cad4fa`

This is the green merge of PR #22, `Collapse weighted Radius-4 cyclic sum to four terms`.

Documentation-only closeout commits follow that mathematical checkpoint on `main`.

Important immediately preceding promoted mathematical commits are:

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

## Closed experimental PR #21 — useful but unpromoted

PR #21, `Identify the weighted forcing range sum`, was created from the earlier promoted base

`afac4e21b6f86ab0c124fbf4c275561382d5767d`.

Its branch eventually reached head

`7e505608d3945f50bc5ed001e3b2fcb65236d945`

but remained CI-failing and has been closed unmerged because `main` advanced through PR #22.

Its substantive Lean development introduces a telescoping potential for the pair of genuine `halfStep` orbits and proves:

- each natural-indexed weighted local forcing is one adjacent potential difference;
- the full chronological range telescopes;
- an in-range natural representative agrees with the corresponding cyclic `radiusWeightedDifferenceTerm`.

The first CI run failed in the full-period endpoint simplification because one `orbitDifferencePotential ... 0` occurrence remained folded and two `simp` arguments were unused.

A subsequent repair attempted to isolate the two endpoint potentials explicitly. That second run also reached only those endpoint lemmas and failed because `change` was used to replace the folded `orbitDifferencePotential` targets by expanded formulas that were not definitionally equal. The exact failures were at the intended `j = total` and `j = 0` endpoint lemmas.

This remains a proof-engineering issue, not evidence of a mathematical counterexample: the local telescoping and indexing mathematics compiled before those endpoint goals.

Because the branch is stale relative to current `main`, do not reopen or merge PR #21 directly. Freshly transplant only the useful `DifferenceForcingRangeSum.lean` mathematics onto current `main` and repair the endpoint lemmas by explicitly unfolding `orbitDifferencePotential` (or using `simp [orbitDifferencePotential, ...]`) before rewriting periodicity and full-period odd counts. Do not rely on `change` to unfold the potential.

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
2. Inspect closed experimental PR #21 and its final head `7e505608d3945f50bc5ed001e3b2fcb65236d945`, but do not merge its stale-base history.
3. Freshly transplant the useful `DifferenceForcingRangeSum.lean` delta onto current `main`.
4. Repair the endpoint potential lemmas by unfolding `orbitDifferencePotential` explicitly. At `j = total`, reduce the suffix to the empty orbit and use periodicity of both base and shifted states. At `j = 0`, reduce the power of two and use the already-proved shifted full-period odd count `L`.
5. Derive the full chronological weighted range-sum identity from those two endpoint lemmas and the already-working telescoping theorem.
6. Run full Lean CI and promote only if green.
7. Combine the promoted range-sum bridge with the already-promoted four-boundary cyclic-sum theorem to derive an exact four-term formula for the genuine shifted-minus-base numerator difference.
8. Then attack the actual four-term arithmetic contradiction. If it fails, isolate the precise counterexample or missing condition rather than adding convenient assumptions.
9. Update `THEOREM_INDEX.md`, `FORMALISATION_ROADMAP.md`, and this checkpoint after the next promoted mathematical result.

## Repository hygiene at closeout

- PR #17: green and merged; clean current-main weighted numerator integration.
- PR #18: green and merged; clean current-main sparse local forcing integration.
- PR #19: green and merged; exact weighted difference-forcing composition.
- PR #20: green and merged; exact four-position weighted boundary support.
- PR #22: green and merged; full cyclic weighted sum collapses to the four Radius-4 boundaries.
- PR #21: closed unmerged; useful telescoping/range-sum experiment, but both endpoint-proof attempts failed CI and the branch is stale-base.
- PR #6: older reverse-bridge development line; not the current local blocker.
