import Lake
open Lake DSL

package «nondeterminism» where
  -- add package configuration options here

lean_lib «Nondeterminism» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_exe «nondeterminism» where
  root := `Main
