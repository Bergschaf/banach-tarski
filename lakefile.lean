import Lake
open Lake DSL

package banach_tarski where
  leanOptions := #[
    ⟨`relaxedAutoImplicit, true⟩, -- prevents typos to be interpreted as new free variables
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib banach_tarski where
  -- add any library configuration options here
