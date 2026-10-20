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

-- input:
--   Amrdi: MRDI-serialized matrix over ZZ or QQ
-- output: a hash table
--   "rows", "cols" => indices of an invertible maximal minor A' of A
--   "denominator"  => a positive integer D
--   "inverse"      => MRDI-serialized integer matrix B with B * A' = D * id
-- so that #rows = rank A.

registerMethod(server, "rankCertificate", Amrdi -> (
	A := sub(loadMRDI Amrdi, QQ);
	cols := columnRankProfile mutableMatrix A;
	rows := rowRankProfile mutableMatrix A_cols;
	A' := A^rows_cols;
	Ainv := inverse A';
	D := lcm prepend(1, apply(flatten entries Ainv, denominator));
	hashTable {
	    "rows" => rows,
	    "cols" => cols,
	    "denominator" => D,
	    "inverse" => saveMRDI(lift(D * Ainv, ZZ),
		Namespace => "Lean",
		ToString => false)}))
