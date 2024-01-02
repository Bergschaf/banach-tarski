import Lake
open Lake DSL

package «banach-tarski» where
  -- add any package configuration options here

require mathlib4 from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib «BanachTarski» where
  -- add any library configuration options here
