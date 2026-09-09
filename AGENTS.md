# Working agreements for this repo

- Work in small, isolated PRs: one file or one theorem family per PR. Do not bundle unrelated changes.
- While iterating, build only the specific file you're working on (e.g. lake build Collatz.SomeFile), not the whole project. Only run a full lake build as a final check before opening a PR.
- Never introduce sorry, admit, or a custom axiom declaration. native_decide is not allowed either — use decide only for small finite checks.
- Never change the Mathlib version pin in lakefile.lean except in a PR whose sole purpose is that version bump, opened separately from any proof work.
- Do not run lake update as part of routine work — dependencies are locked via the committed lake-manifest.json. Only run it deliberately, in its own PR, when a bump is intended.
- When a new theorem is proved, add or update its entry in docs/THEOREM_INDEX.md in the same PR.
- Before opening a PR, confirm: grep -rn "sorry\\|native_decide" Collatz/ returns nothing.
