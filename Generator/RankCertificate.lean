import Macaulean.Macaulay2
import MRDI.Basic

/-!
# Rank certificates from Macaulay2

The client side of `m2/terracini.m2`, this repository's extension of the Macaulean
server: MRDI serialization of integer matrices, and a call to the `rankCertificate`
JSON-RPC method. The certificates are written out as Lean source (`Cert.toLean`) and
checked in the kernel by `RankCertificate.check` (`TerraciniLemma/RankCertificate.lean`).
-/

open Lean

namespace Generator

/-- An integer matrix, given by its rows, as exchanged with Macaulay2. -/
structure IntMatrix where
  rows : List (List Int)

/-- Matrices are stored in the Lean namespace as the list of their rows, with integer
entries stored as strings (the MRDI convention; see `m2/terracini.m2`). -/
instance : MrdiType IntMatrix where
  mrdiType := .parameterized "Matrix" (.str "Int")
  decode? json := pure do
    let rows : List (List String) ← fromJson? json
    let rows ← rows.mapM fun r => r.mapM fun x =>
      match x.toInt? with
      | some z => .ok z
      | none => .error s!"expected an integer, got {x}"
    pure ⟨rows⟩
  encode A := pure <| toJson (A.rows.map (·.map toString))

/-- The reply of the `rankCertificate` method. -/
structure RankCertificateReply where
  rows : List Nat
  cols : List Nat
  modulus : Nat
  inverse : Mrdi

instance : FromJson RankCertificateReply where
  fromJson? json := do
    pure {
      rows := ← json.getObjValAs? (List Nat) "rows"
      cols := ← json.getObjValAs? (List Nat) "cols"
      modulus := ← json.getObjValAs? Nat "modulus"
      inverse := ← json.getObjValAs? Mrdi "inverse" }

/-- A rank certificate, as written to Lean source (`RankCertificate.Cert`). -/
structure Cert where
  rows : List Nat
  cols : List Nat
  inv : List (List Nat)
  modulus : Nat

/-- Load this repository's extension into the running Macaulean server. -/
def loadExtension (m2 : Macaulay2) : IO Unit := do
  let path ← IO.FS.realPath "m2/terracini.m2"
  discard <| m2.eval s!"load \"{path}\""

/-- Ask Macaulay2 for a rank certificate of `A`. -/
def rankCertificate (m2 : Macaulay2) (A : IntMatrix) : IO Cert := do
  let reply : Json ← runMrdiIO do
    let mrdi ← toMrdi A
    m2.sendRequest "rankCertificate" [toJson mrdi]
  let .ok reply := fromJson? (α := RankCertificateReply) reply
    | throw <| .userError s!"unexpected reply from Macaulay2: {reply}"
  let .ok inv ← runMrdiIO (fromMrdi? (α := IntMatrix) reply.inverse)
    | throw <| .userError "could not decode the inverse"
  pure ⟨reply.rows, reply.cols, inv.rows.map (·.map Int.toNat), reply.modulus⟩

/-- The number of multiply-adds the kernel performs per declaration when checking a
certificate. The kernel caches every intermediate term of a declaration, so this bounds its
memory use (about 15 KB per multiply-add). -/
def chunkBudget : Nat := 150000

/-- Lean source for a certificate `<name>Cert` for the matrix `A` (a Lean term of type
`ℕ → ℕ → ℤ`) with `m` rows and `n` columns, checked by the theorem `<name>Check`. The rows of
the inverse are split into chunks `<name>Inv<k>`, each checked in its own declaration
`<name>Check<k>` (see `chunkBudget`). -/
def Cert.toLean (c : Cert) (name A m n : String) : String := Id.run do
  let showList {α} [ToString α] (l : List α) := "[" ++ ", ".intercalate (l.map toString) ++ "]"
  let k := c.rows.length
  let size := max 1 (chunkBudget / max 1 (k * k))
  let chunks := (List.range ((k + size - 1) / size)).map fun q => (q * size, (c.inv.drop (q * size)).take size)
  let chunks := if chunks.isEmpty then [(0, [])] else chunks
  let mut src := ""
  for (q, (start, rows)) in chunks.zipIdx.map (fun (x, q) => (q, x)) do
    src := src ++ s!"/-- Rows {start} to {start + rows.length - 1} of the inverse in `{name}Cert`. -/
def {name}Inv{q} : List (List Nat) :=
  {showList (rows.map showList)}

"
  -- `Inv0 ++ (Inv1 ++ (⋯))`, nested to the right like the chain of `checkRows_append`s below
  -- (`++` associates to the left, and a mismatch makes the elaborator evaluate the appends)
  let invTerm := (List.range chunks.length).foldr (init := "") fun q acc =>
    if q + 1 = chunks.length then s!"{name}Inv{q}" else s!"{name}Inv{q} ++ ({acc})"
  src := src ++ s!"/-- The rank certificate `{name}Cert` (rank {k}). -/
def {name}Cert : RankCertificate.Cert where
  rows := {showList c.rows}
  cols := {showList c.cols}
  inv := {invTerm}
  modulus := {c.modulus}
"
  for (q, (start, _)) in chunks.zipIdx.map (fun (x, q) => (q, x)) do
    src := src ++ s!"
/-- The kernel checks the rows of `{name}Inv{q}`. -/
theorem {name}Check{q} : RankCertificate.checkRows {name}Cert.modulus
    (RankCertificate.minorCols ({A}) {name}Cert.modulus
      {name}Cert.rows {name}Cert.cols)
    {start} {name}Inv{q} = true := by
  decide +kernel
"
  -- `checkRows_append (Check0) (checkRows_append (Check1) (⋯) rfl) rfl`
  let combined := (List.range chunks.length).foldr (init := "") fun q acc =>
    if q + 1 = chunks.length then s!"{name}Check{q}"
    else s!"(RankCertificate.checkRows_append {name}Check{q}\n      {acc} rfl)"
  src := src ++ s!"
/-- The kernel checks the certificate. -/
theorem {name}Check : RankCertificate.check ({A}) ({m})
    ({n}) {name}Cert = true :=
  RankCertificate.check_of_checkRows (by decide +kernel)
    {combined}
"
  return src

end Generator
