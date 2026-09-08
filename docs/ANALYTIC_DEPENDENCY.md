# Quantitative logarithmic dependency

Audit date: 2026-09-06. Status updated: 2026-09-07.

The final local transport-radius-four impossibility theorem is **unproved**.
The first family exclusions require the quantitative logarithmic proposition
below. No equivalent theorem was located in the pinned Mathlib, and no such
bound is an axiom or hypothesis of the current Lean library.

## Why logarithms enter the problem

The Collatz map sends even `x` to `x/2` and odd `x` to `3*x+1`. Recording a
cycle using the auxiliary map that divides by two at every step produces a
binary word of length `A` with `L` odd source positions. Composing its local
equations gives a full integer denominator `D = 2^A-3^L` and an exact
numerator `Q(w) = wordNumerator(w)`.

The intended generic local theorem assumes `0 < L < A`, `D > 1`,
`D ∣ Q(w)`, primitivity, and a nonzero self-rotation shift. Primitivity means
no nonzero rotation fixes the word. Exact transport radius four means that
the minimum, over cyclic cuts, of the sum of absolute target-minus-source
prefix-weight differences is four.

For the height-two and connected four-edge flow families, local numerator
identities lead to small coefficients. After the required application and
coprime cancellation, these constrain `D` to a small positive list. A bound
on `2^A-3^L` makes the positive difference `A log 2-L log 3` extremely small
when `L` is large. A quantitative lower bound for the same expression is
needed to turn that observation into a finite range of exponents.

## Exact missing proposition

Here `log` is the real natural logarithm. For positive natural numbers `A,L`,
write

`Λ = A * log 2 - L * log 3`

and

`M = max (log (A / log 3 + L / log 2) + 3/50) 21`.

The required lower bound is

`-22 * M^2 * log 2 * log 3 ≤ log |Λ|`, provided `Λ ≠ 0`.

The complete formal obligation is displayed as a proposition only. It is not
a theorem declaration, an axiom, or an assumption added to the library:

```lean
∀ A L : ℕ, 0 < A → 0 < L →
  (A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3 ≠ 0 →
  let M := max
    (Real.log ((A : ℝ) / Real.log 3 + (L : ℝ) / Real.log 2) + (3 / 50 : ℝ))
    21
  -(22 : ℝ) * M ^ 2 * Real.log 2 * Real.log 3 ≤
    Real.log |(A : ℝ) * Real.log 2 - (L : ℝ) * Real.log 3|
```

The nonvanishing side condition itself is now discharged internally for this
specialization: `two_pow_ne_three_pow` and
`log_two_three_defect_ne_zero` in `Collatz/Radius4LogDefect.lean` prove it
from positivity of `A`, using parity of powers.  The quantitative inequality
remains the missing part.

`Collatz/Radius4LMNDeterminants.lean` now records the analytic upper-bound
primitive for an interpolation determinant: a complex square matrix whose
entries have norm at most `x` has determinant norm at most
`card(ι)! * x^card(ι)`.  The remaining task is to construct the LMN matrix,
prove its determinant nonzero by the relevant zero lemma, and establish its
explicit arithmetic lower bound.

This is the required specialization of a quantitative two-logarithm bound
associated with Laurent, Mignotte, and Nesterenko. Every hypothesis and the
constants `22`, `3/50`, and `21` require formal justification. Naming a
classical theorem does not supply its Lean proof. Making this proposition
an extra final-theorem hypothesis would leave the intended target incomplete.

## Verified elementary ingredients

The connected local coefficient set is `15,17,21,27,29,35,47,65`; the
height-two coefficient has absolute value `15`. The generic coefficient and
cancellation lemmas are verified. For a natural divisor `d > 1` coprime to
six, they give the possible values `5,7,13,17,29,35,47,65` when the stated
coefficient divisibility holds. Their application to the actual full
denominator and transport geometry remains a separate obligation.

For `D = 2^A-3^L` with `0 < D ≤ 65`,
`Collatz/Radius4LogDefect.lean` proves

`0 < Λ = log (1 + D/3^L) < D/3^L ≤ 65/3^L`.

It also proves `L ≥ 4 → A < 2L` under `D ≤ 65`. The corresponding theorem
names are `cycleDenominator_log_defect_eq`,
`cycleDenominator_log_defect_pos`, `cycleDenominator_log_defect_lt_ratio`,
`cycleDenominator_log_defect_lt_sixty_five`, and
`cycleDenominator_exponent_lt_twice_of_le_sixty_five`.

## Remaining cutoff and finite certificate

The intended next steps enlarge the logarithmic parameter to
`max (log (4L) + 3/50) 21`, combine the lower and upper bounds to prove
`L < 7000`, and check the finite denominator equation in that range.
Neither the cutoff nor that finite certificate is currently proved here.

The exact certificate target is: if `0 < L < A`, `L < 7000`,
`D = 2^A-3^L`, and `D ∈ {5,7,13,17,29,35,47,65}`, then `(A,L,D)` is one of

`(3,1,5), (4,1,13), (5,1,29), (4,2,7), (5,3,5), (7,4,47), (8,5,13)`.

Even after proving this finite statement, the remaining word configurations
must be excluded using the actual target hypotheses, including primitivity
and `D ∣ Q(w)`. A computation performed outside the Lean kernel or an
assumed cutoff does not establish these obligations.

## Pinned Mathlib audit and useful support

The audit used Mathlib `69fe4f49ffbc9580a2c3ae6d29591ef6d1d4131e` and Lean
`v4.34.0-rc2`. It searched the library, tests, pinned Lean source, and the
transcendence, Diophantine approximation, and height developments. No
Laurent–Mignotte–Nesterenko, Baker, Matveev, or equivalent quantitative
linear-form-in-two-logarithms theorem was located. This is an audit result,
not a claim that no possible formal proof exists.

Available support includes:

- `Real.log_pow`, `Real.log_div`, `Real.log_injOn_pos`, and
  `Real.log_lt_sub_one_of_pos` in
  `Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`;
- rigorous logarithm series bounds `Real.sum_range_sub_log_div_le`,
  `Real.sum_range_le_log_div`, and `Real.log_div_le_sum_range_add` in
  `Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean`;
- Legendre's rational-approximation criterion
  `Real.exists_rat_eq_convergent` in
  `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean` and
  `Real.exists_convs_eq_rat` in `ContinuedFractions.lean`.

These facts support elementary estimates and finite approximation arguments.
They do not provide the displayed lower bound. The nearby theorem
`exists_pos_real_of_irrational_root` requires a specified nonzero integer
polynomial vanishing at its argument, which has not been provided for the
logarithm ratio. `exp_polynomial_approx` contains an unspecified constant.
The polynomial-coefficient bound named after Mignotte concerns another object.
None supplies the exact constants needed here.

The missing quantitative proof remains part of the local theorem's formal
dependency chain. The final local result, even when completed, would not prove
the Collatz conjecture or exclude all nontrivial cycles by itself.
