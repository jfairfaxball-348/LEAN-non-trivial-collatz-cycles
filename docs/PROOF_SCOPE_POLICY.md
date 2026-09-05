# Proof scope policy

This repository is intended to be readable as a self-contained mathematical object. A reader should not need unpublished notes, another repository, or historical context to understand what a theorem means.

## Required documentation for substantial theorems

Every substantial theorem should document all of the following.

### 1. Plain-English statement

Explain the result before presenting technical notation. Introduce any Collatz-specific terminology from first principles.

### 2. Formal statement

Give the Lean theorem name and identify the source file in which it is proved.

### 3. Assumptions

List every mathematically meaningful hypothesis. In particular, distinguish assumptions about:

- positivity;
- primitivity;
- cycle encoding;
- arithmetic divisibility or denominator conditions;
- exact versus bounded Hamming distance;
- local versus global structure.

### 4. What the theorem proves

State the strongest conclusion that follows from the Lean theorem itself.

### 5. What the theorem does not prove

Explicitly list nearby stronger claims that are not consequences of the theorem. For local Collatz obstructions, this normally includes whether the theorem does or does not exclude all non-trivial cycles and whether a separate global bridge is still needed.

### 6. Dependency boundary

All mathematical dependencies needed for the theorem must appear in this repository or in its declared Lean/mathlib dependencies. Informal external results must either be formalised here, replaced by a formally imported theorem, or clearly identified as an unformalised blocker. No theorem should be presented as complete while relying on an unstated external argument.

## Status language

Use status descriptions conservatively:

- **defined**: Lean accepts a definition;
- **proved**: Lean accepts the theorem without `sorry` or an equivalent placeholder;
- **scaffolded**: the relevant source structure exists but the intended substantial theorem is not yet complete;
- **target**: a statement intended for future formalisation and not yet claimed as proved;
- **out of scope**: intentionally not part of the theorem under discussion.

A Markdown description of a target is never evidence that the target has been proved.

## Local theorem versus global bridge

A recurring distinction in this project is between a **local obstruction** and a **global bridge**.

A local obstruction says that a particular configuration cannot occur in an eligible hypothetical Collatz cycle.

A global bridge would say that every hypothetical non-trivial cycle must contain such a configuration.

Only the conjunction of those two kinds of results can exclude all hypothetical cycles through that route. The repository must never describe a local obstruction as a global no-cycle theorem unless the required bridge has also been formalised.
