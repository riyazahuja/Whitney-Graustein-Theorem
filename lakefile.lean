import Lake
open Lake DSL

package «Whitney-Graustein» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩]

@[default_target]
lean_lib «WhitneyGraustein» where

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"
