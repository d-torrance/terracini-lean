module

public import TerraciniLemma.Semicontinuity

/-!
# Rank certificates

A *rank certificate* for an integer matrix `A` (stored as a list of rows) consists of row
indices `rows`, column indices `cols` (both of length `k`), an integer `k × k` matrix `B`, and a
nonzero integer `D` with `B · A[rows, cols] = D · 1`. It proves that the `k × k` minor
`A[rows, cols]` is invertible over any field of characteristic zero, hence that `A` has rank
`≥ k` there (`le_rank_of_check`).

Certificates are computed by Macaulay2 (see `m2/terracini.m2` and the generator in
`Generator/`), stored in Lean source files, and checked by the kernel: `check` is a plain
computable function, so `check A c = true` is proved by `decide +kernel`. To keep the stored
data cheap to elaborate, the entries of `B` are stored as natural numbers in *zigzag*
encoding (`0, -1, 1, -2, 2, … ↦ 0, 1, 2, 3, 4, …`).
-/

@[expose] public section

namespace RankCertificate

/-- Zigzag decoding: `2k ↦ k` and `2k + 1 ↦ -(k + 1)`. -/
def unzigzag (z : Nat) : Int :=
  if z % 2 = 0 then ((z / 2 : Nat) : Int) else -(((z / 2 : Nat) : Int) + 1)

/-- A rank certificate, as produced by Macaulay2. -/
structure Cert where
  /-- Row indices of the invertible minor. -/
  rows : List Nat
  /-- Column indices of the invertible minor. -/
  cols : List Nat
  /-- The rows of `B`, zigzag-encoded. -/
  inv : List (List Nat)
  /-- The scalar `D` with `B · A[rows, cols] = D · 1`. -/
  den : Nat

/-- The `(i, j)` entry of a matrix stored as a list of rows (`0` out of range). -/
def entry (A : List (List Int)) (i j : Nat) : Int := (A.getD i []).getD j 0

/-- Dot product of two lists (truncating to the shorter one). -/
def dot : List Int → List Int → Int
  | a :: as, b :: bs => a * b + dot as bs
  | _, _ => 0

/-- Check one row `r` of `B` against all the columns `cs` of the minor, starting at column
index `j`: the products must be `D` on the diagonal (`i = j`) and `0` elsewhere. -/
def checkRow (D : Int) (r : List Int) (i : Nat) : List (List Int) → Nat → Bool
  | c :: cs, j => (dot r c == if i == j then D else 0) && checkRow D r i cs (j + 1)
  | [], _ => true

/-- Check all rows of `B` (starting at row index `i`) against the columns `cols` of the
minor. -/
def checkRows (D : Int) (cols : List (List Int)) : Nat → List (List Int) → Bool
  | i, r :: rs => checkRow D r i cols 0 && checkRows D cols (i + 1) rs
  | _, [] => true

/-- The columns of the minor `A[rows, cols]`. -/
def minorCols (A : List (List Int)) (rows cols : List Nat) : List (List Int) :=
  cols.map fun j => rows.map fun i => entry A i j

/-- Check a certificate for an `m × n` integer matrix `A`. -/
def check (A : List (List Int)) (m n : Nat) (c : Cert) : Bool :=
  c.den != 0 &&
  c.cols.length == c.rows.length &&
  c.inv.length == c.rows.length &&
  c.inv.all (fun r => r.length == c.rows.length) &&
  c.rows.all (· < m) && c.cols.all (· < n) &&
  checkRows (c.den : Int) (minorCols A c.rows c.cols) 0 (c.inv.map (·.map unzigzag))

/-! ### Soundness -/

/-- The matrix with entries `entry A i j`. -/
def toMatrix (A : List (List Int)) (m n : Nat) : Matrix (Fin m) (Fin n) ℤ :=
  Matrix.of fun i j => entry A i j

theorem dot_eq_sum {k : Nat} (u v : List Int) (hu : u.length = k) (hv : v.length = k) :
    dot u v = ∑ t : Fin k, u.getD t 0 * v.getD t 0 := by
  induction k generalizing u v with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.mp hu
    simp [dot]
  | succ k ih =>
    obtain ⟨a, as, rfl⟩ := List.exists_cons_of_length_eq_add_one hu
    obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_length_eq_add_one hv
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hu hv
    rw [dot, ih as bs hu hv, Fin.sum_univ_succ]
    simp

theorem checkRow_spec {D : Int} {r : List Int} {i : Nat} :
    ∀ (cs : List (List Int)) (j : Nat), checkRow D r i cs j = true →
      ∀ t : Fin cs.length, dot r cs[t] = if i = j + t then D else 0
  | [], _, _, t => t.elim0
  | c :: cs, j, h, t => by
    simp only [checkRow, Bool.and_eq_true, beq_iff_eq] at h
    refine Fin.cases ?_ (fun t => ?_) t
    · simpa using h.1
    · have := checkRow_spec cs (j + 1) h.2 t
      simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem checkRows_spec {D : Int} {cols : List (List Int)} :
    ∀ (B : List (List Int)) (i : Nat), checkRows D cols i B = true →
      ∀ (s : Fin B.length) (t : Fin cols.length),
        dot B[s] cols[t] = if i + s = t then D else 0
  | [], _, _, s => s.elim0
  | r :: rs, i, h, s => by
    simp only [checkRows, Bool.and_eq_true] at h
    refine Fin.cases (fun t => ?_) (fun s t => ?_) s
    · simpa using checkRow_spec cols 0 h.1 t
    · have := checkRows_spec rs (i + 1) h.2 s t
      simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-- **Soundness of rank certificates.** If `check A m n c` holds, the `k × k` minor of `A`
selected by the certificate is invertible over any field of characteristic zero, so `A` has
rank `≥ k` there, where `k` is the number of rows in the certificate. -/
theorem le_rank_of_check {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {A : List (List Int)} {m n : Nat}
    {c : Cert} (h : check A m n c = true) :
    c.rows.length ≤ ((toMatrix A m n).map (Int.cast : ℤ → 𝕜)).rank := by
  simp only [check, Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hD, hcols⟩, hinv⟩, hinvRows⟩, hrows⟩, hcolsLt⟩, hcheck⟩ := h
  set k := c.rows.length
  -- the row and column selections of the minor
  let f : Fin k → Fin m := fun s => ⟨c.rows[s], hrows _ (List.getElem_mem _)⟩
  let g : Fin k → Fin n := fun t =>
    ⟨c.cols[t.cast hcols.symm], hcolsLt _ (List.getElem_mem _)⟩
  -- the certificate matrix `B`
  let B : Matrix (Fin k) (Fin k) ℤ := Matrix.of fun s t =>
    unzigzag ((c.inv.getD s []).getD t 0)
  -- `B · A[rows, cols] = D · 1` over `ℤ`
  have hBA : B * (toMatrix A m n).submatrix f g = (c.den : ℤ) • 1 := by
    ext s t
    have hs : (s : Nat) < (c.inv.map (·.map unzigzag)).length := by simp [hinv]
    have ht : (t : Nat) < (minorCols A c.rows c.cols).length := by simp [minorCols, hcols]
    have := checkRows_spec _ 0 hcheck ⟨s, hs⟩ ⟨t, ht⟩
    rw [dot_eq_sum (k := k) _ _ (by simp [hinvRows _ (List.getElem_mem _)])
      (by simp [minorCols, k])] at this
    simp only [Matrix.mul_apply, Matrix.submatrix_apply, toMatrix, Matrix.of_apply,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, B, f, g]
    rw [show (∑ u : Fin k, unzigzag ((c.inv.getD s []).getD u 0) *
          entry A c.rows[u] c.cols[Fin.cast hcols.symm t])
        = ∑ u : Fin k, ((c.inv.map (fun r : List Nat => r.map unzigzag))[s]'hs).getD u 0 *
          ((minorCols A c.rows c.cols)[t]'ht).getD u 0 from
      Finset.sum_congr rfl fun u _ => by
        have hu : (u : Nat) < c.rows.length := u.isLt
        simp [minorCols, List.getD_eq_getElem?_getD, List.getElem?_map, hinvRows _
          (List.getElem_mem _), hinv, List.getElem?_eq_getElem hu]]
    refine Eq.trans ?_ (this.trans ?_)
    · rfl
    · simp [Fin.ext_iff]
  -- hence `det B · det A[rows, cols] = D ^ k ≠ 0` in `𝕜`
  have hdet : (((toMatrix A m n).map (Int.cast : ℤ → 𝕜)).submatrix f g).det ≠ 0 := by
    have h1 := congrArg (fun M : Matrix (Fin k) (Fin k) ℤ => ((Int.castRingHom 𝕜) M.det)) hBA
    simp only [Matrix.det_mul, map_mul, Matrix.det_smul, Matrix.det_one, mul_one,
      Fintype.card_fin, map_pow, eq_intCast, Int.cast_natCast] at h1
    have hD' : ((c.den : 𝕜)) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hD)
    rw [← h1] at hD'
    rw [show ((toMatrix A m n).map (Int.cast : ℤ → 𝕜)).submatrix f g
        = (Int.castRingHom 𝕜).mapMatrix ((toMatrix A m n).submatrix f g) from rfl,
      ← RingHom.map_det]
    simpa using right_ne_zero_of_mul hD'
  exact Matrix.le_rank_of_submatrix_det_ne_zero f g hdet

end RankCertificate
