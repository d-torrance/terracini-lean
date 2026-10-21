-- terracini-lean's extension of the Macaulean server: MRDI serialization of matrices
-- and a JSON-RPC method computing rank certificates. It is loaded into the running
-- server (see `Generator/RankCertificate.lean`), so it may use the globals of
-- Macaulean's `macaulean.m2`: `server`, `leanRings`, and `M2Rings`.

-------------------------------------
-- MRDI serialization of matrices --
-------------------------------------

-- A matrix over ZZ or QQ is stored in the Lean namespace as the list of its rows.
-- Following the MRDI convention, integers are stored as strings and rationals as
-- pairs of strings (numerator, denominator).

toLeanEntry = method()
toLeanEntry ZZ := toString
toLeanEntry QQ := x -> {toString numerator x, toString denominator x}

addSaveMethod(Matrix,
    A -> leanRings#(ring A),
    A -> apply(entries A, row -> apply(row, toLeanEntry)),
    Name => "Matrix",
    Namespace => "Lean")

fromLeanEntry = kk -> x -> (
    if kk === ZZ then value x else value x#0 / value x#1)

addLoadMethod("Matrix",
    (params, data) -> (
	kk := M2Rings#params;
	if #data == 0 then map(kk^0, kk^0, 0)
	else matrix(kk, apply(data, row -> apply(row, fromLeanEntry kk)))),
    Namespace => "Lean")

---------------------
-- rank certificates --
---------------------

-- The certificates work modulo a prime p: if B * A' = id over ZZ/p for a square
-- submatrix A' of an integer matrix A, then det A' is nonzero mod p, hence nonzero, so
-- A has rank >= #rows over every field of characteristic zero.
certificateModulus = 2147483647

-- input:
--   Amrdi: MRDI-serialized matrix over ZZ
-- output: a hash table
--   "rows", "cols" => indices of a maximal minor A' of A, invertible mod p
--   "modulus"      => the prime p
--   "inverse"      => MRDI-serialized integer matrix B, entries in [0, p), with
--                     B * A' = id mod p
-- so that #rows = rank of A mod p.

registerMethod(server, "rankCertificate", Amrdi -> (
	p := certificateModulus;
	A := sub(loadMRDI Amrdi, ZZ/p);
	cols := columnRankProfile mutableMatrix A;
	rows := rowRankProfile mutableMatrix A_cols;
	Ainv := inverse A^rows_cols;
	hashTable {
	    "rows" => rows,
	    "cols" => cols,
	    "modulus" => p,
	    "inverse" => saveMRDI(matrix applyTable(entries lift(Ainv, ZZ), x -> x % p),
		Namespace => "Lean",
		ToString => false)}))
