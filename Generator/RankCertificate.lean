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
  denominator : Nat
  inverse : Mrdi

instance : FromJson RankCertificateReply where
  fromJson? json := do
    pure {
      rows := ← json.getObjValAs? (List Nat) "rows"
      cols := ← json.getObjValAs? (List Nat) "cols"
      denominator := ← json.getObjValAs? Nat "denominator"
      inverse := ← json.getObjValAs? Mrdi "inverse" }

/-- A rank certificate, as written to Lean source (`RankCertificate.Cert`). -/
structure Cert where
  rows : List Nat
  cols : List Nat
  inv : List (List Int)
  den : Nat

/-- Zigzag encoding, inverse to `RankCertificate.unzigzag`. -/
def zigzag (z : Int) : Nat := if 0 ≤ z then 2 * z.toNat else 2 * (-z).toNat - 1

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
  pure ⟨reply.rows, reply.cols, inv.rows, reply.denominator⟩

/-- Lean source for a certificate named `name`. -/
def Cert.toLean (c : Cert) (name : String) : String :=
  let showList {α} [ToString α] (l : List α) := "[" ++ ", ".intercalate (l.map toString) ++ "]"
  s!"def {name} : RankCertificate.Cert where
  rows := {showList c.rows}
  cols := {showList c.cols}
  inv := {showList (c.inv.map fun r => showList (r.map zigzag))}
  den := {c.den}
"

end Generator
