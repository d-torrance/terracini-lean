import Generator.RankCertificate

open Generator

def main : IO Unit := do
  let (_, m2) ← startM2Server
  loadExtension m2
  -- smoke test
  let A : IntMatrix := ⟨[[1, 2, 3], [2, 4, 6], [0, 1, 1], [1, -1, 5]]⟩
  let c ← rankCertificate m2 A
  IO.println (c.toLean "toy")
