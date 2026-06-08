import Lake
open Lake DSL

package «terraciniLean» where
  name := "TerraciniLean"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.30.0-rc2"

lean_lib «TerraciniLemma» where
  globs := #[.path `TerraciniLemma]
