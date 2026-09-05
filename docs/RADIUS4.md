# Radius 4: meaning, scope, and formalisation target

This document is self-contained. It assumes no prior knowledge of the Collatz problem or of this repository.

## 1. The Collatz map

For a positive integer `n`, define

- `T(n) = n / 2` when `n` is even;
- `T(n) = 3n + 1` when `n` is odd.

The Collatz conjecture says that every positive starting value eventually reaches `1`. Under the unaccelerated map above, reaching `1` enters the familiar cycle

`1 -> 4 -> 2 -> 1`.

A **non-trivial Collatz cycle** would be a different finite periodic orbit of positive integers.

This repository is concerned only with rigorous statements that can be checked by Lean. A local theorem about one structural feature of a hypothetical cycle is not the Collatz conjecture and is not automatically a proof that non-trivial cycles do not exist.

## 2. Cyclic binary words

A finite cycle has no distinguished starting point. This naturally leads to cyclic data: a finite word considered around a circle rather than from a fixed left endpoint.

The formalisation uses binary cyclic words as a combinatorial layer. A word of length `n` is represented as a function

`ZMod n -> Bool`.

The type `ZMod n` supplies the cyclic indexing. Rotating the word by a shift `s` means reading the same circular word from a different index.

The Collatz-specific encoding of a hypothetical cycle into such a word is a separate mathematical step. It will be defined and proved inside this repository before any theorem is advertised as a Collatz theorem.

## 3. Hamming distance and radius

Given two binary words of the same length, their **Hamming distance** is the number of positions at which they differ.

For a cyclic word `w` and a nonzero cyclic shift `s`, compare

`w`

with

`rotate w s`.

The shift is an **exact Radius-4 rotation** when those two words differ in exactly four positions.

So "Radius 4" does **not** mean a numerical bound on a Collatz orbit and does **not** mean four Collatz iterations. It is a local combinatorial statement about the Hamming distance between a cyclic word and one of its rotations.

## 4. Primitive words

A cyclic word is **primitive** when no nonzero rotation fixes it exactly. Equivalently, the word is not obtained by repeating a shorter cyclic pattern.

Primitivity matters because repetitions can create artificial rotational coincidences that belong to a smaller underlying object.

## 5. The Collatz cycle denominator

A common odd-to-odd description of a Collatz trajectory writes

`3x + 1 = 2^a y`,

where `x` and `y` are odd and `a >= 1` is the exact number of factors of two removed.

For a hypothetical odd cycle with `L` odd nodes, let the corresponding exponents be

`a_0, ..., a_(L-1)`

and let

`A = a_0 + ... + a_(L-1)`.

Composing the cycle equations produces the characteristic denominator

`D = 2^A - 3^L`.

The Lean project defines this integer directly. The stronger arithmetic condition informally described as a **full-denominator** condition must use the entire integer `D`, not merely a chosen factor or residue class. The exact quantity required to be divisible by `D` will be introduced only when its derivation has also been formalised here.

## 6. The Radius-4 local theorem target

The intended local theorem has the following logical shape:

> An eligible primitive positive Collatz cycle encoding cannot simultaneously satisfy the full cycle-denominator condition and possess a nonzero rotation at exact Hamming distance four.

That sentence is a **formalisation target**, not yet a theorem merely because it appears in this document. The repository status table records which pieces Lean currently checks.

The important word is **eligible**. Before the final Radius-4 theorem can be claimed, this repository must itself formalise every condition connecting the pure cyclic word to a genuine positive Collatz-cycle candidate.

## 7. What a completed Radius-4 local proof would establish

Once all definitions, eligibility lemmas, and the final contradiction are accepted by Lean, the result would rigorously exclude one specific local configuration: an eligible primitive positive cycle candidate carrying an exact Radius-4 rotation under the stated full-denominator hypotheses.

That would be a genuine theorem about a constrained class of hypothetical Collatz cycles.

## 8. What it would not establish

A completed Radius-4 local proof would **not**, by itself:

- prove the full Collatz conjecture;
- prove that every positive integer reaches `1`;
- prove that Collatz trajectories are bounded;
- exclude every possible non-trivial cycle;
- exclude analogous configurations at every other Hamming radius;
- prove that every hypothetical non-trivial cycle must contain a Radius-4 configuration.

The last item is especially important. To turn a local Radius-4 obstruction into a global no-cycle theorem, one would additionally need a separate **global encounter/bridge theorem** showing that every hypothetical non-trivial cycle necessarily produces an eligible Radius-4 configuration. That bridge is a different theorem and is not part of the Radius-4 local result.

## 9. Current formalisation boundary

At scaffold stage, Lean checks the basic Collatz map, cyclic words, rotation, Hamming distance, primitivity, the cycle denominator, and the definition of exact Radius 4.

The Collatz-to-word eligibility machinery, exact full-denominator condition, and final Radius-4 local impossibility theorem are deliberately not claimed until they are formalised in this repository.
