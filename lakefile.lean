import Lake
open Lake DSL

package «complexity-barriers» where


require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Pseudorandomness» where
  globs := #[.submodules `Pseudorandomness]
