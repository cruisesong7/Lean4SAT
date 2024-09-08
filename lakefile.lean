import Lake
open Lake DSL

package "leansat" where
  -- add package configuration options here

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"v4.11.0"

lean_lib «Leansat» where
  -- add library configuration options here

@[default_target]
lean_exe "leansat" where
  root := `Main
