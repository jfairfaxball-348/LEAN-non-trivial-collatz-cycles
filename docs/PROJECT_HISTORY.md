# Repository proof history

This history records development milestones and their verification evidence
within this repository.
For the current proof boundary, use the [checkpoint](CURRENT_CHECKPOINT.md).

The project studies binary parity words associated with the Collatz map,
which halves even natural numbers and sends odd `x` to `3*x+1`. A word of
length `A` with `L` ones has full denominator `D = 2^A-3^L`. The local target
excludes an exact transport-radius-four self-rotation for primitive words
satisfying `0 < L < A`, `D > 1`, and `D ∣ Q(w)`, where `Q` is the exact
chronological numerator. Primitive means no nonzero rotation fixes the word.
Transport cost sums the absolute target-minus-source prefix-weight differences
at internal boundaries and is minimized over cyclic cuts.

## 2026-09-05: height-two classification source checkpoint

Revision `7dbce6e3015cbd58cd3f4ad997122e115fcded7d` recorded source for the
rigid height-two transport classification. This is a source-history checkpoint;
it does not claim that its root build exercised all transport modules. The
remaining classification step was
to group the four unit-height active edges into maximal consecutive runs.
The possible run-length families were `[4]`, `[3,1]`, `[2,2]`, `[2,1,1]`,
and `[1,1,1,1]`. Later build-coverage work, recorded below, checked all the
required transport modules through the root library.

## Classification and normalization promoted by 2026-09-07

PR #33 merged at `174e0914a1a039234f15e078c56d545f247dc747`. It completed
the cut-normalization link, included all intended transport modules in the
root build, and repaired the elaboration problems exposed by that coverage.
The full local build passed with 8,908 jobs. GitHub Actions PR run
`34039991808` and main run `34040305206` passed their actual Build steps.

This established the height-two `(1,2,1)` family, all five unit-height
run-length families, and normalization to the genuine advanced parity origin.
It did not exclude any complete transport family arithmetically.

## 2026-09-07: elementary arithmetic prerequisites promoted

PR #34 merged at `d7d1f372635c4d749da2172e16f247ba68b3d750`, from verified
head `98c0147b420a1112830d54d8fb537e7218ea1245`. The full local build passed
with 8,912 jobs. PR run `34115337625` and post-merge main run `34115689962`
passed their actual Build steps. The audit of 27 new public lemmas found only
`propext`, `Classical.choice`, and `Quot.sound`, where used.

The additions prove signed local flow, height-two bits, local numerator
coefficients, coprime cancellation, a finite divisor list, and elementary
logarithmic bounds. Representation and rotation work on
`codex/r4-local-word-bridge` is subsequent work that has not completed full
validation or promotion at this checkpoint.

The subsequent closeout snapshot retains six new modules and the standalone
documentation rewrite on `codex/r4-local-word-bridge`. Individual cyclic-list,
word-rotation, full-denominator-word, and transport/component checks passed.
The validation sequence was stopped during the signed-flow check; the full
root build and new 24-lemma axiom audit were not completed. This snapshot is
not a promoted theorem or a claim of green CI.

The quantitative logarithmic lower bound described in
[ANALYTIC_DEPENDENCY.md](ANALYTIC_DEPENDENCY.md), complete family exclusions,
and the final local theorem remain unproved. No general exclusion of other
Collatz cycles or proof of the Collatz conjecture is recorded here.
