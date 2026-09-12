import Lake

open Lake DSL

package tuza where
  description := "The 165/59 bound for Tuza's conjecture."
  license := "MIT"
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`warningAsError, true⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.0"

@[default_target]
lean_lib Tuza
