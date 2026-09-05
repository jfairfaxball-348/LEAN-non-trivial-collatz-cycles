import Lake

open Lake DSL

package «collatz-formal» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "69fe4f49ffbc9580a2c3ae6d29591ef6d1d4131e"

@[default_target]
lean_lib Collatz where
