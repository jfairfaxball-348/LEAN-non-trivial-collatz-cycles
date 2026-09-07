# RL238 analytic dependency audit

Date: 2026-09-06

The final Radius-4 impossibility theorem is **not proved in this repository**.
The first established elimination, R4-2 (height-two and connected `[4]`),
requires a quantitative two-logarithm lower bound that has not been located in
the pinned Mathlib. No such bound is assumed by the Lean source.

## Exact authorized blueprint

The read-only RL238 bundle is stored in the research checkout under
`sessions/RL239/RL238_RADIUS4_LOCAL_THEOREM_TRANSPORT/`.
The directory contains the completed RL238 bundle, despite the parent
session directory being named RL239.

All nine base64 transport parts match `PART_SHA256SUMS.txt`. The decoded ZIP
SHA256 is
`52c46b7c1249f597ca52d210f50d78f9900edfb4412270eed38482ebaec6ee51`,
matching its authoritative sidecar. All fifteen nested Python verifier files
match the packed-verifier checksums. These checks establish source identity;
they are not Lean proof certificates or formal dependencies.

Load-bearing locations inside that bundle:

- `RL238_CERTIFIED_FACTS_AND_PROOF_LEDGER.md`, R4-2;
- `RL238_EXTERNAL_DEPENDENCY_AUDIT.md`, LMN;
- `verifiers/packed_parts/` → `rl238_verifier_pack/verify_rl238_connected_radius4_closure.py`,
  lines 96–115 (connected cutoff) and 118–134 (finite denominator list);
- the same nested pack's `verify_rl238_1111_multiunit_closure.py`,
  lines 48–53 (the exact inherited LMN specialization).

The external audit cites Laurent, Mignotte, and Nesterenko,
*Formes linéaires en deux logarithmes et déterminants d'interpolation*,
Journal of Number Theory 55 (1995), 285–321. The bundle records its use, but
does not include a proof of that external theorem.

## Narrow missing formal theorem

For positive natural exponents `A` and `L`, write

`Λ = A * log 2 - L * log 3`

and

`M = max (log (A / log 3 + L / log 2) + 3/50) 21`.

RL238 uses

`-22 * M^2 * log 2 * log 3 ≤ log |Λ|`, when `Λ ≠ 0`.

The formal obligation, displayed only as a proposition (not a declaration or
an assumption in the library), is:

```lean
∀ A L : ℕ, 0 < A → 0 < L →
  (A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3 ≠ 0 →
  let M := max
    (Real.log ((A : ℝ) / Real.log 3 + (L : ℝ) / Real.log 2) + (3 / 50 : ℝ))
    21
  -(22 : ℝ) * M ^ 2 * Real.log 2 * Real.log 3 ≤
    Real.log |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3|
```

The exact constants and hypotheses must be justified by an internal proof of
the established external theorem and its specialization. Merely adding this
proposition as an axiom or as a final-theorem hypothesis does not complete the
standalone project.

## Where it is first needed

The connected local coefficients are
`15, 17, 21, 27, 29, 35, 47, 65`; the height-two coefficient is `15`.
After the established local replacement and coprime-monomial cancellation,
under the strict full-denominator hypothesis `D > 1`, the possible full denominators are
`5, 7, 13, 17, 29, 35, 47, 65`.

For `D = 2^A - 3^L` with `0 < D ≤ 65`, elementary logarithm identities give

`0 < Λ = log (1 + D/3^L) < D/3^L ≤ 65/3^L`.

The blueprint then proves `L ≥ 4 → A < 2L`, enlarges the LMN parameter to
`max (log (4L) + 3/50) 21`, and obtains `L < 7000`. Its exact finite search
below that cutoff leaves the seven triples

`(3,1,5), (4,1,13), (5,1,29), (4,2,7), (5,3,5), (7,4,47), (8,5,13)`.

The infinite cutoff and this finite certificate must each be proved in Lean.
Running the Python verifier or assuming `L < 7000` cannot replace either proof.
The remaining topology eliminations must retain their established order.

## Pinned Mathlib audit and available support

Audited revision: `69fe4f49ffbc9580a2c3ae6d29591ef6d1d4131e`, with Lean
`v4.34.0-rc2`. Searches covered Mathlib, MathlibTest, pinned Lean source, and
the transcendence, Diophantine approximation, and height developments.
No LMN, Baker, Matveev, or equivalent quantitative two-logarithm theorem was
located. The unrelated polynomial-coefficient bound named after Mignotte does
not supply this logarithmic estimate.

Available ingredients include:

- `Real.log_pow`, `Real.log_div`, `Real.log_injOn_pos`, and
  `Real.log_lt_sub_one_of_pos` in
  `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`;
- rigorous logarithm series bounds `Real.sum_range_sub_log_div_le`,
  `Real.sum_range_le_log_div`, and `Real.log_div_le_sum_range_add` in
  `Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean`;
- Legendre's criterion `Real.exists_rat_eq_convergent` in
  `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean` and
  `Real.exists_convs_eq_rat` in `ContinuedFractions.lean`.

The nearby Liouville estimate
`exists_pos_real_of_irrational_root` requires a specified nonzero integer
polynomial vanishing at its argument; those hypotheses are not available for
the logarithm ratio. Lindemann's `exp_polynomial_approx` has an unspecified
constant and does not state the required explicit two-logarithm bound.
Neither can be substituted for LMN in the established argument.

These checks isolate a missing formal dependency; they do not challenge or
replace the research theorem. Completing its formal proof remains necessary
before the standalone Radius-4 theorem can be claimed.
