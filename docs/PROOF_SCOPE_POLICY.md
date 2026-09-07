# Proof scope and documentation policy

This repository studies a local obstruction to possible Collatz cycles. The
Collatz map halves an even natural number and sends an odd `x` to `3*x+1`.
The familiar positive cycle is `1 → 4 → 2 → 1`. A local obstruction excludes
one specified configuration; it does not show that every other hypothetical
cycle contains that configuration.

Every document must explain its mathematical objects and proof status within
this repository. Readers should be able to follow it without personal notes,
project history, or additional unpublished material.

## What substantial theorems must document

For each substantial theorem, provide:

1. A plain-English statement introducing its terminology and notation.
2. The exact Lean theorem name and source file.
3. All meaningful hypotheses: positivity, primitivity, cycle encoding,
   full-denominator divisibility, exact or bounded radius, and any local
   geometric assumptions.
4. The conclusion actually proved, together with nearby stronger claims
   that do not follow.
5. Its formal dependencies and any unresolved application steps.

For this project, a primitive cyclic word is one fixed only by the zero
rotation. The full denominator is the entire integer `D = 2^A-3^L`, where
`A` is the parity-word length and `L` its number of ones. `Q(w)` is its exact
chronological numerator `wordNumerator`. Retain `D ∣ Q(w)` when required;
divisibility of a difference alone is a weaker hypothesis.

Transport radius minimizes the sum of absolute target-minus-source prefix
weights over cyclic cuts. Hamming distance counts unequal positions. The
predicates for these two notions must not be interchanged. `OddCycle` records
exact positive odd-node transitions but does not assert primitivity or a
minimal represented period.

## Status language and evidence

Use these descriptions consistently:

- **Defined:** the stated definition has been checked by Lean.
- **Proved:** Lean has checked the theorem with no proof placeholder or new
  mathematical axiom.
- **Verified on main:** the exact revision is merged and the required root
  build has passed.
- **Unverified work:** source has been edited but has not yet passed its
  required checks.
- **Target:** a proposition intended for proof, with no claim of completion.
- **Out of scope:** a result not included in the stated objective.

Record the revision and actual CI Build result supporting a promotion. An
older green build does not validate later edits, and a module omitted from
root imports is not covered by the root build. A Markdown statement or a
file's presence is never evidence of a theorem proof.

Required proofs must use this repository's checked results or declared Lean
and Mathlib dependencies. Do not introduce `sorry`, `admit`, new mathematical
axioms, or `native_decide`. Standard kernel-checked finite `decide` proofs are
acceptable. Report axiom-audit results accurately; the accepted standard core
may include `propext`, `Classical.choice`, and `Quot.sound`.

## Unresolved dependencies and the endpoint

The intended final theorem excludes exact transport radius four for generic
cyclic words with `0 < L < A`, `D > 1`, `D ∣ Q(w)`, primitivity, and a nonzero
self-rotation shift. It is currently unproved. Its quantitative logarithmic
obligation is stated explicitly in
[ANALYTIC_DEPENDENCY.md](ANALYTIC_DEPENDENCY.md). Removing background material
must never remove that mathematical dependency or turn it into an assumption.

A theorem conditional on an unproved lower bound is not completion of the
intended unconditional local result. Every component family and every
required arithmetic check must be handled before claiming that result.

Even the completed local obstruction would require a separate theorem saying
that every other hypothetical cycle contains the excluded configuration to
support a general no-cycle conclusion. Excluding cycles alone would also not
prove that every positive Collatz trajectory reaches the familiar cycle.
