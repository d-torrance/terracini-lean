module

public import TerraciniLemma.Semicontinuity
public import Mathlib.Data.ZMod.Basic

/-!
# Rank certificates

A *rank certificate* for an integer matrix `A` (given by its entry function) consists of row
indices `rows`, column indices `cols` (both of length `k`), a modulus `p ≥ 2`, and a `k × k`
matrix `B` of natural numbers with `B · A[rows, cols] ≡ 1 (mod p)`. Then `det A[rows, cols]` is
a unit mod `p`, so it is a nonzero integer, and `A` has rank `≥ k` over any field of
characteristic zero (`le_rank_of_check`).

Certificates are computed by Macaulay2 (see `m2/terracini.m2` and the generator in
`Generator/`), stored in Lean source files, and checked by the kernel: `check` is a plain
computable function, so `check A m n c = true` is proved by `decide +kernel`. Working mod `p`
keeps the entries of `B` small and the check in natural-number arithmetic, which the kernel
performs with GMP.

The kernel caches every intermediate term while checking a declaration, so its memory grows
with the size of the computation. Large certificates are therefore checked in chunks of rows
of `B`, one declaration per chunk (`checkRows_append`, `check_of_checkRows`).
-/

@[expose] public section

namespace RankCertificate

/-- A rank certificate, as produced by Macaulay2. -/
structure Cert where
  /-- Row indices of the minor. -/
  rows : List Nat
  /-- Column indices of the minor. -/
  cols : List Nat
  /-- The rows of `B`, with entries in `[0, p)`. -/
  inv : List (List Nat)
  /-- The modulus `p`. -/
  modulus : Nat

/-- Dot product of two lists (truncating to the shorter one). -/
def dot : List Nat → List Nat → Nat
  | a :: as, b :: bs => a * b + dot as bs
  | _, _ => 0

/-- Check one row `r` of `B` against all the columns `cs` of the minor (reduced mod `p`),
starting at column index `j`: the products must be `1` on the diagonal (`i = j`) and `0`
elsewhere, mod `p`. -/
def checkRow (p : Nat) (r : List Nat) (i : Nat) : List (List Nat) → Nat → Bool
  | c :: cs, j => (dot r c % p == if i == j then 1 else 0) && checkRow p r i cs (j + 1)
  | [], _ => true

/-- Check all rows of `B` (starting at row index `i`) against the columns `cols` of the
minor. -/
def checkRows (p : Nat) (cols : List (List Nat)) : Nat → List (List Nat) → Bool
  | i, r :: rs => checkRow p r i cols 0 && checkRows p cols (i + 1) rs
  | _, [] => true

/-- The columns of the minor `A[rows, cols]`, reduced mod `p`. -/
def minorCols (A : Nat → Nat → Int) (p : Nat) (rows cols : List Nat) : List (List Nat) :=
  cols.map fun j => rows.map fun i => (A i j % p).toNat

/-- The shape conditions of a certificate for an `m × n` matrix. -/
def checkShape (m n : Nat) (c : Cert) : Bool :=
  2 ≤ c.modulus &&
  c.cols.length == c.rows.length &&
  c.inv.length == c.rows.length &&
  c.inv.all (fun r => r.length == c.rows.length) &&
  c.rows.all (· < m) && c.cols.all (· < n)

/-- Check a certificate for an `m × n` integer matrix `A`. -/
def check (A : Nat → Nat → Int) (m n : Nat) (c : Cert) : Bool :=
  checkShape m n c && checkRows c.modulus (minorCols A c.modulus c.rows c.cols) 0 c.inv

theorem checkRows_append {p : Nat} {cols : List (List Nat)} {i j : Nat}
    {B₁ B₂ : List (List Nat)} (h₁ : checkRows p cols i B₁ = true)
    (h₂ : checkRows p cols j B₂ = true) (hj : i + B₁.length = j) :
    checkRows p cols i (B₁ ++ B₂) = true := by
  induction B₁ generalizing i with
  | nil => simpa [← hj] using h₂
  | cons r rs ih =>
    simp only [List.cons_append, checkRows, Bool.and_eq_true] at h₁ ⊢
    exact ⟨h₁.1, ih h₁.2 (by simp at hj; omega)⟩

theorem check_of_checkRows {A : Nat → Nat → Int} {m n : Nat} {c : Cert}
    (h₁ : checkShape m n c = true)
    (h₂ : checkRows c.modulus (minorCols A c.modulus c.rows c.cols) 0 c.inv = true) :
    check A m n c = true := by
  simp [check, h₁, h₂]

/-! ### Soundness -/

/-- The `m × n` matrix with entries `A i j`. -/
def toMatrix (A : Nat → Nat → Int) (m n : Nat) : Matrix (Fin m) (Fin n) ℤ :=
  Matrix.of fun i j => A i j

theorem dot_eq_sum {k : Nat} (u v : List Nat) (hu : u.length = k) (hv : v.length = k) :
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

theorem checkRow_spec {p : Nat} {r : List Nat} {i : Nat} :
    ∀ (cs : List (List Nat)) (j : Nat), checkRow p r i cs j = true →
      ∀ t : Fin cs.length, dot r cs[t] % p = if i = j + t then 1 else 0
  | [], _, _, t => t.elim0
  | c :: cs, j, h, t => by
    simp only [checkRow, Bool.and_eq_true, beq_iff_eq] at h
    refine Fin.cases ?_ (fun t => ?_) t
    · simpa using h.1
    · have := checkRow_spec cs (j + 1) h.2 t
      simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem checkRows_spec {p : Nat} {cols : List (List Nat)} :
    ∀ (B : List (List Nat)) (i : Nat), checkRows p cols i B = true →
      ∀ (s : Fin B.length) (t : Fin cols.length),
        dot B[s] cols[t] % p = if i + s = t then 1 else 0
  | [], _, _, s => s.elim0
  | r :: rs, i, h, s => by
    simp only [checkRows, Bool.and_eq_true] at h
    refine Fin.cases (fun t => ?_) (fun s t => ?_) s
    · simpa using checkRow_spec cols 0 h.1 t
    · have := checkRows_spec rs (i + 1) h.2 s t
      simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-- Reducing mod `p` commutes with the cast to `ZMod p`. -/
theorem cast_toNat_emod {p : Nat} (hp : p ≠ 0) (a : Int) :
    (((a % p).toNat : Nat) : ZMod p) = (a : ZMod p) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp)),
    ZMod.intCast_mod]

/-- **Soundness of rank certificates.** If `check A m n c` holds, the `k × k` minor of `A`
selected by the certificate has nonzero determinant, so `A` has rank `≥ k` over any field of
characteristic zero, where `k` is the number of rows in the certificate. -/
theorem le_rank_of_check {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {A : Nat → Nat → Int} {m n : Nat}
    {c : Cert} (h : check A m n c = true) :
    c.rows.length ≤ ((toMatrix A m n).map (Int.cast : ℤ → 𝕜)).rank := by
  simp only [check, checkShape, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hp, hcols⟩, hinv⟩, hinvRows⟩, hrows⟩, hcolsLt⟩, hcheck⟩ := h
  set p := c.modulus
  have : Fact (1 < p) := ⟨hp⟩
  set k := c.rows.length
  -- the row and column selections of the minor
  let f : Fin k → Fin m := fun s => ⟨c.rows[s], hrows _ (List.getElem_mem _)⟩
  let g : Fin k → Fin n := fun t =>
    ⟨c.cols[t.cast hcols.symm], hcolsLt _ (List.getElem_mem _)⟩
  let M : Matrix (Fin k) (Fin k) ℤ := (toMatrix A m n).submatrix f g
  -- the certificate matrix `B`, over `ZMod p`
  let B : Matrix (Fin k) (Fin k) (ZMod p) := Matrix.of fun s t => ((c.inv.getD s []).getD t 0 : ℕ)
  -- `B · M = 1` over `ZMod p`
  have hBM : B * (Int.castRingHom (ZMod p)).mapMatrix M = 1 := by
    ext s t
    have hs : (s : Nat) < c.inv.length := by simp [hinv, k]
    have ht : (t : Nat) < (minorCols A p c.rows c.cols).length := by simp [minorCols, hcols, k]
    have h1 := checkRows_spec _ 0 hcheck ⟨s, hs⟩ ⟨t, ht⟩
    rw [dot_eq_sum (k := k) _ _ (by simp [hinvRows _ (List.getElem_mem _)])
      (by simp [minorCols, k])] at h1
    have h2 := congrArg (Nat.cast : ℕ → ZMod p) h1
    rw [ZMod.natCast_mod] at h2
    push_cast at h2
    simp only [Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
      Matrix.submatrix_apply, toMatrix, Matrix.of_apply, Matrix.one_apply, B, M, f, g]
    refine Eq.trans (Finset.sum_congr rfl fun u _ => ?_) (h2.trans ?_)
    · have hu : (u : Nat) < c.rows.length := u.isLt
      simp [minorCols, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hs,
        List.getElem?_eq_getElem hu, cast_toNat_emod (show p ≠ 0 by omega)]
    · simp [Fin.ext_iff]
  -- hence `det M` is a unit mod `p`, so it is nonzero
  have hdetM : M.det ≠ 0 := by
    intro h0
    have h3 := congrArg Matrix.det hBM
    rw [Matrix.det_mul, ← RingHom.map_det, h0, map_zero, mul_zero, Matrix.det_one] at h3
    exact zero_ne_one h3
  have hdet : (((toMatrix A m n).map (Int.cast : ℤ → 𝕜)).submatrix f g).det ≠ 0 := by
    rw [show ((toMatrix A m n).map (Int.cast : ℤ → 𝕜)).submatrix f g
        = (Int.castRingHom 𝕜).mapMatrix M from rfl, ← RingHom.map_det]
    simpa using hdetM
  exact Matrix.le_rank_of_submatrix_det_ne_zero f g hdet

end RankCertificate
