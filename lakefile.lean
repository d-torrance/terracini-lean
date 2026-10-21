import Lake
open Lake DSL

package «terraciniLean»

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"

require Macaulean from git
  "https://github.com/Macaulean/Macaulean" @ "6cdeddef93be60b5d26e1f39562476fba4620822"

@[default_target]
lean_lib «TerraciniLemma»

/-- Computes the rank certificates of the base cases with Macaulay2 (via Macaulean) and
writes them to `TerraciniLemma/CubicCertificates/`. Run from the repository root:
`lake exe certificates`. -/
lean_lib Generator

lean_exe certificates where
  root := `Generator.Main

