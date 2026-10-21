module

public import TerraciniLemma.RankCertificate
public import TerraciniLemma.CubicLattice

/-!
# Rank certificates for tangent spaces of `v_e(ℙⁿ)`, in any degree

Integer points of `𝕜^{n+1}` (lists of coordinates) and monomials of degree `e` (lists of variable
indices) give an integer matrix `degMatrix`: column `j + (n+1) k` is the tangent vector at the
`k`-th point in the direction `eⱼ`, at the row monomials, `∂ x^s / ∂ xⱼ = count_j(s) x^{s - j}`.
A rank certificate for it (`RankCertificate`) bounds the dimension of the span of the tangent
spaces at the points from below (`le_finrank_of_check`).
-/

@[expose] public section

namespace DegreeCertificate

/-! ### §A — The computable side -/

/-- `∂ x^s / ∂ xⱼ` at the integer point `p`, for a monomial `s` given by its variable indices. -/
def monoEntry (p : List ℤ) (j : ℕ) (s : List ℕ) : ℤ :=
  (s.count j : ℤ) * ((s.erase j).map fun a => p.getD a 0).prod

/-- The matrix of tangent vectors at the points `pts` of `𝕜^N` (column `j + N k`: the `k`-th
point, direction `eⱼ`), at the monomials `rows`. -/
def degMatrix (N : ℕ) (rows : List (List ℕ)) (pts : List (List ℤ)) (r col : ℕ) : ℤ :=
  monoEntry (pts.getD (col / N) []) (col % N) (rows.getD r [])

/-- The nondecreasing lists of length `e` with entries `< N`, each starting at `≥ a`. -/
def monosFrom (N : ℕ) : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | e + 1, a => ((List.range N).filter (a ≤ ·)).flatMap fun b => (monosFrom N e b).map (b :: ·)

/-- All monomials of degree `e` in `N` variables. -/
def allMonos (N e : ℕ) : List (List ℕ) := monosFrom N e 0

/-- The rows are monomials of degree `e` in `N` variables. -/
def validRows (N e : ℕ) (rows : List (List ℕ)) : Bool :=
  rows.all fun s => s.length == e && s.all (· < N)

/-! ### §B — Soundness -/

section Soundness

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] {n e : ℕ}

/-- The monomial of a valid row. -/
def rowSym {rows : List (List ℕ)} (hv : validRows (n + 1) e rows = true) (r : Fin rows.length) :
    Sym (Fin (n + 1)) e :=
  have h : ∀ s ∈ rows, s.length = e ∧ ∀ a ∈ s, a < n + 1 := by
    simpa [validRows] using hv
  Sym.mk ((rows[r]).pmap Fin.mk (h _ (List.getElem_mem r.2)).2 : Multiset (Fin (n + 1))) (by
    simp [(h _ (List.getElem_mem r.2)).1])

omit [CharZero 𝕜] in
/-- The integer entries are the coordinates of the tangent vectors. -/
theorem cast_monoEntry (p : List ℤ) (j : Fin (n + 1)) (s : List ℕ) (hs : ∀ a ∈ s, a < n + 1)
    (hse : s.length = e) :
    ((monoEntry p j s : ℤ) : 𝕜) = veroneseDegDeriv n e (fun x => ((p.getD x 0 : ℤ) : 𝕜))
      (Pi.single j 1) (Sym.mk ((s.pmap Fin.mk hs : List (Fin (n + 1))) : Multiset (Fin (n + 1)))
        (by simp [hse])) := by
  classical
  set s' := s.pmap Fin.mk hs
  have hs' : s = s'.map Fin.val := by simp [s', List.map_pmap]
  rw [veroneseDegDeriv_apply, Finset.sum_eq_single j (fun b _ hb => by simp [hb])
    (by simp), Pi.single_eq_same, mul_one]
  simp only [Multiset.coe_count, Multiset.coe_erase, Multiset.map_coe, Multiset.prod_coe]
  rw [monoEntry]
  conv_lhs => rw [hs']
  rw [List.count_map_of_injective _ _ Fin.val_injective, ← List.map_erase Fin.val_injective,
    List.map_map]
  push_cast
  simp [s', Function.comp_def]

/-- Selecting the row monomials. -/
def rowSelect {rows : List (List ℕ)} (hv : validRows (n + 1) e rows = true) :
    (Sym (Fin (n + 1)) e → 𝕜) →ₗ[𝕜] (Fin rows.length → 𝕜) :=
  LinearMap.funLeft 𝕜 𝕜 (rowSym hv)

/-- **Soundness.** A rank certificate for `degMatrix` bounds the dimension of the span of the
tangent spaces at the points. -/
theorem le_finrank_of_check {rows : List (List ℕ)} (hv : validRows (n + 1) e rows = true)
    {pts : List (List ℤ)} {c : RankCertificate.Cert}
    (hc : RankCertificate.check (degMatrix (n + 1) rows pts) rows.length
      (pts.length * (n + 1)) c = true) :
    c.rows.length ≤ Module.finrank 𝕜 (⨆ k : Fin pts.length,
      (veroneseDegParam n e (fun x => ((pts[k].getD x 0 : ℤ) : 𝕜))).tangentSpace :
        Submodule 𝕜 _) := by
  have h : ∀ s ∈ rows, s.length = e ∧ ∀ a ∈ s, a < n + 1 := by simpa [validRows] using hv
  refine (RankCertificate.le_rank_of_check (𝕜 := 𝕜) hc).trans (le_trans ?_
    (Submodule.finrank_map_le (rowSelect (𝕜 := 𝕜) hv) _))
  rw [Matrix.rank_eq_finrank_span_cols]
  refine Submodule.finrank_mono (Submodule.span_le.mpr ?_)
  rintro _ ⟨col, rfl⟩
  obtain ⟨⟨k, j⟩, rfl⟩ := finProdFinEquiv.surjective col
  refine ⟨veroneseDegDeriv n e (fun x => ((pts[k].getD x 0 : ℤ) : 𝕜)) (Pi.single j 1),
    Submodule.mem_iSup_of_mem k ⟨_, rfl⟩, ?_⟩
  funext r
  simp only [rowSelect, LinearMap.funLeft_apply, Matrix.col_apply, Matrix.map_apply,
    RankCertificate.toMatrix, Matrix.of_apply, finProdFinEquiv_apply_val, degMatrix]
  have hN : 0 < n + 1 := Nat.succ_pos n
  rw [show (j + (n + 1) * k) / (n + 1) = k by
      rw [Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt j.2, zero_add],
    show (j + (n + 1) * k) % (n + 1) = j by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.2],
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem k.2, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem r.2, Option.getD_some]
  exact (cast_monoEntry _ j _ (h _ (List.getElem_mem r.2)).2 (h _ (List.getElem_mem r.2)).1).symm

end Soundness

end DegreeCertificate
