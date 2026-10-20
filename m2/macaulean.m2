-- Macaulean's Lean client starts its server as `M2 --script ./macaulean.m2` in the
-- directory `./m2/` relative to the working directory, so running the certificate
-- generator from the root of this repository starts this file. Hand off to
-- Macaulean's server script; this repository's extension (`terracini.m2`) is then
-- loaded into the running server by the generator.
load(currentFileDirectory | "../.lake/packages/Macaulean/m2/macaulean.m2")
