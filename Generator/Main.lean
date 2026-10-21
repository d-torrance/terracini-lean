import Generator.Degree

open Generator

/-- `lake exe certificates [name …]`: run the named jobs (all jobs if none are given). -/
def main (args : List String) : IO Unit := do
  let (_, m2) ← startM2Server
  loadExtension m2
  -- each certificate file imports the previous one (see `CubicJob.run`)
  let imports := "TerraciniLemma.CubicBaseCases" ::
    cubicJobs.map (s!"TerraciniLemma.CubicCertificates.{·.name}")
  for (job, imp) in cubicJobs.zip imports do
    if args.isEmpty || args.contains job.name then
      job.run m2 imp
  for job in degJobs do
    if args.isEmpty || args.contains job.name then
      job.run m2
