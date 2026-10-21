module

public import TerraciniLemma.CubicInduction
public import TerraciniLemma.RankCertificate

/-!
# Base cases of the cubic induction, from rank certificates

A base case `Good 𝕜 s t K i m` is proved at one explicit configuration of integer points (then
semicontinuity, `Good.of_point`, gives general points). We list points with their locations
(`LocatedPoints`), build the integer matrix of their tangent vectors restricted to the monomials
outside `P̂₀ + ⋯ + P̂_{i-1}` (`baseMatrix`), and check a rank certificate for it computed by
Macaulay2.

* §A — monomials `{a, b, c}` and the closed form of the tangent vectors of `v₃`;
* §B — the computable side: rows (`baseRows`), the matrix (`baseMatrix`), and the validity
  check of the located points (`validPoints`);
* §C — soundness: a certificate of full row rank gives `A_{i,K}(t) = everything`
  (`good_top_of_check`), and one of rank `r` gives `dim A_{0,K}(t) ≥ r`
  (`good_zero_of_check`).
-/

@[expose] public section

noncomputable section CubicBaseCases

open MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-! ### §A — Monomials and tangent vectors -/

section Monomials

variable {n : ℕ}

/-- The monomial `x_a x_b x_c`. -/
def sym3 (a b c : Fin (n + 1)) : Sym (Fin (n + 1)) 3 := ⟨{a, b, c}, rfl⟩

omit [CharZero 𝕜] in
/-- The tangent vector of `v₃` at `p` in the coordinate direction `j`, at the monomial
`x_a x_b x_c`: `∂(x_a x_b x_c)/∂x_j (p)`. -/
theorem veroneseDegDeriv_sym3 (p : Fin (n + 1) → 𝕜) (j a b c : Fin (n + 1)) :
    veroneseDegDeriv n 3 p (Pi.single j 1) (sym3 a b c)
      = (if a = j then p b * p c else 0) + (if b = j then p a * p c else 0)
        + (if c = j then p a * p b else 0) := by
  classical
  rw [veroneseDegDeriv_single]
  have hpoly : veroneseDegPoly (𝕜 := 𝕜) n 3 (sym3 a b c) = X a * (X b * X c) := by
    simp [veroneseDegPoly, sym3]
  rw [hpoly]
  simp only [pderiv_mul, pderiv_X, Pi.single_apply, map_add, map_mul, eval_X]
  split_ifs <;> simp only [map_one, map_zero] <;> ring

theorem sym3_swap12 (a b c : Fin (n + 1)) : sym3 a b c = sym3 b a c :=
  Subtype.ext (Multiset.cons_swap a b {c})

theorem sym3_swap23 (a b c : Fin (n + 1)) : sym3 a b c = sym3 a c b :=
  Subtype.ext (congrArg (a ::ₘ ·) (Multiset.pair_comm b c))

/-- Every cubic monomial is `x_a x_b x_c` with `a ≤ b ≤ c`. -/
theorem exists_sym3 (m : Sym (Fin (n + 1)) 3) :
    ∃ a b c : Fin (n + 1), a ≤ b ∧ b ≤ c ∧ m = sym3 a b c := by
  obtain ⟨l, hl⟩ := Quot.exists_rep (m : Multiset (Fin (n + 1)))
  have hlen : l.length = 3 := by
    have h : Multiset.card (Quot.mk _ l : Multiset (Fin (n + 1))) = 3 := hl ▸ m.2
    simpa using h
  obtain ⟨x, y, z, rfl⟩ := List.length_eq_three.mp hlen
  have hm : m = sym3 x y z := Subtype.ext hl.symm
  rw [hm]
  rcases le_total x y with hxy | hyx <;> rcases le_total y z with hyz | hzy <;>
    rcases le_total x z with hxz | hzx
  · exact ⟨x, y, z, hxy, hyz, rfl⟩
  · exact ⟨x, y, z, hxy, hyz, rfl⟩
  · exact ⟨x, z, y, hxz, hzy, sym3_swap23 _ _ _⟩
  · exact ⟨z, x, y, hzx, hxy, (sym3_swap23 _ _ _).trans (sym3_swap12 _ _ _)⟩
  · exact ⟨y, x, z, hyx, hxz, sym3_swap12 _ _ _⟩
  · exact ⟨y, z, x, hyz, hzx, (sym3_swap12 _ _ _).trans (sym3_swap23 _ _ _)⟩
  · exact ⟨z, y, x, hzy, hyx, (sym3_swap23 _ _ _).trans ((sym3_swap12 _ _ _).trans
      (sym3_swap23 _ _ _))⟩
  · exact ⟨z, y, x, hzy, hyx, (sym3_swap23 _ _ _).trans ((sym3_swap12 _ _ _).trans
      (sym3_swap23 _ _ _))⟩

end Monomials

/-! ### §B — The computable side -/

section Computable

/-- Coordinate `a` lies in block `β`. -/
def inBlockN (β a : ℕ) : Bool := 3 * β ≤ a && a < 3 * β + 3

/-- The monomial `x_a x_b x_c` meets every block `β < i`, i.e. lies outside
`P̂₀ + ⋯ + P̂_{i-1}`. -/
def meetsBlocks (i a b c : ℕ) : Bool :=
  (List.range i).all fun β => inBlockN β a || inBlockN β b || inBlockN β c

/-- The rows: the monomials `x_a x_b x_c`, `a ≤ b ≤ c < N`, meeting every block `β < i`. -/
def baseRows (N i : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range N).flatMap fun a => (List.range N).flatMap fun b => (List.range N).filterMap
    fun c => if a ≤ b ∧ b ≤ c ∧ meetsBlocks i a b c then some (a, b, c) else none

/-- `∂(x_a x_b x_c)/∂x_j` at the integer point `p`. -/
def tangentEntry (p : List ℤ) (j a b c : ℕ) : ℤ :=
  (if a = j then p.getD b 0 * p.getD c 0 else 0) + (if b = j then p.getD a 0 * p.getD c 0 else 0)
    + (if c = j then p.getD a 0 * p.getD b 0 else 0)

/-- Points listed by location: each entry is a location (a list of lattice indices) and the
points placed there. -/
abbrev LocatedPoints := List (List ℕ × List (List ℤ))

/-- All the listed points. -/
def allPoints (data : LocatedPoints) : List (List ℤ) := data.flatMap (·.2)

/-- The matrix of the tangent vectors at the listed points (columns, one per point and
coordinate direction: column `j + N k` is the `k`-th point in direction `j`), restricted to the
rows `baseRows N i`. It is given by its entries, which the kernel computes directly from the
monomial and the point (this is much cheaper than indexing into a computed list of rows). -/
def baseMatrix (N i : ℕ) (data : LocatedPoints) (r col : ℕ) : ℤ :=
  tangentEntry ((allPoints data).getD (col / N) []) (col % N) ((baseRows N i).getD r (0, 0, 0)).1
    ((baseRows N i).getD r (0, 0, 0)).2.1 ((baseRows N i).getD r (0, 0, 0)).2.2

/-- The listed points form part of a configuration on `K` lattice spaces at level `t`: the
locations are distinct (and listed in increasing order), lie in `{0, …, K-1}`, each location
holds at most `countAt` points, and each point has `t + 5` coordinates vanishing on the blocks
of its location. -/
def validPoints (s : ℕ → ℕ) (t K : ℕ) (data : LocatedPoints) : Bool :=
  (data.map (·.1)).Nodup && data.all fun (loc, pts) =>
    loc.Pairwise (· < ·) && loc.all (· < K) && decide (pts.length ≤ countAt s t K loc.toFinset) &&
    pts.all fun p => p.length == t + 5 &&
      (List.range (t + 5)).all fun a => !(loc.any fun β => inBlockN β a) || p.getD a 0 == 0

end Computable

/-! ### §C — Soundness -/

section Soundness

variable {s : ℕ → ℕ} {t K : ℕ}

omit [CharZero 𝕜] in
/-- **Realization.** Valid listed points are points of a configuration: there are parameters
placing each listed point in its own slot. -/
theorem exists_param_of_valid {data : LocatedPoints} (h : validPoints s t K data = true) :
    ∃ x₀ : Param s t K → 𝕜, ∀ p ∈ allPoints data, ∃ σ : Slot s t K,
      configPoint x₀ σ = fun j : Fin (t + 4 + 1) => ((p.getD j 0 : ℤ) : 𝕜) := by
  classical
  simp only [validPoints, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨hnodup, hall⟩ := h
  have hsorted : ∀ e : Fin data.length, data[e].1.Pairwise (· < ·) := fun e =>
    (hall _ (List.getElem_mem e.2)).1.1.1
  have hloc : ∀ e : Fin data.length, data[e].1.toFinset ∈ (Finset.range K).powerset :=
    fun e => by
      have := (hall _ (List.getElem_mem e.2)).1.1.2
      simpa [Finset.subset_iff] using this
  have hcount : ∀ e : Fin data.length,
      data[e].2.length ≤ countAt s t K data[e].1.toFinset :=
    fun e => (hall _ (List.getElem_mem e.2)).1.2
  have hzero : ∀ e : Fin data.length, ∀ q ∈ data[e].2, ∀ a < t + 5,
      (data[e].1.any fun β => inBlockN β a) = true → q.getD a 0 = 0 := fun e q hq a ha hb => by
    have := ((hall _ (List.getElem_mem e.2)).2 q hq).2 a (List.mem_range.mpr ha)
    simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq] at this
    rcases this with h' | h'
    · exact absurd (h'.symm.trans hb) (by decide)
    · exact h'
  -- the slot of the `c`-th point at the `e`-th location
  let slot : (Σ e : Fin data.length, Fin data[e].2.length) → Slot s t K := fun ec =>
    ⟨⟨data[ec.1].1.toFinset, hloc ec.1⟩, ⟨ec.2, lt_of_lt_of_le ec.2.2 (hcount ec.1)⟩⟩
  have hslot : Function.Injective slot := by
    rintro ⟨e, c⟩ ⟨e', c'⟩ hee'
    simp only [slot, Sigma.mk.inj_iff] at hee'
    obtain ⟨h1, h2⟩ := hee'
    have hfs : data[e].1.toFinset = data[e'].1.toFinset := congrArg Subtype.val h1
    have hlists : data[e].1 = data[e'].1 :=
      List.Perm.eq_of_pairwise' ((hsorted e).imp le_of_lt) ((hsorted e').imp le_of_lt)
        (List.perm_of_nodup_nodup_toFinset_eq ((hsorted e).imp ne_of_lt)
          ((hsorted e').imp ne_of_lt) hfs)
    have hee : e = e' := by
      have hinj := List.nodup_iff_injective_get.mp hnodup
      have := @hinj ⟨e, by simp⟩ ⟨e', by simp⟩ (by simpa using hlists)
      exact Fin.ext (by simpa using congrArg Fin.val this)
    subst hee
    have hcc : c = c' := Fin.ext (by simpa using (Fin.heq_ext_iff rfl).mp h2)
    rw [hcc]
  let pt : (Σ e : Fin data.length, Fin data[e].2.length) → Fin (t + 4 + 1) → 𝕜 := fun ec j =>
    ((data[ec.1].2[ec.2].getD j 0 : ℤ) : 𝕜)
  refine ⟨fun xj => if h : ∃ ec, slot ec = xj.1 then pt h.choose xj.2 else 0, ?_⟩
  intro p hp
  obtain ⟨q, hq, hpq⟩ := List.mem_flatMap.mp hp
  obtain ⟨e, he, rfl⟩ := List.getElem_of_mem hq
  obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hpq
  let ec : Σ e : Fin data.length, Fin data[e].2.length := ⟨⟨e, he⟩, ⟨c, hc⟩⟩
  refine ⟨slot ec, ?_⟩
  have hex : ∃ ec', slot ec' = (slot ec) := ⟨ec, rfl⟩
  have hchoose : hex.choose = ec := hslot hex.choose_spec
  funext j
  simp only [configPoint, zeroBlocks, dite_eq_left hex, hchoose]
  split_ifs with hj
  · obtain ⟨β, hβ, hin⟩ := hj
    rw [hzero ⟨e, he⟩ _ (List.getElem_mem hc) j j.2 ?_, Int.cast_zero]
    simp only [List.any_eq_true]
    refine ⟨β, by simpa [slot] using hβ, ?_⟩
    simpa [inBlockN, InBlock] using hin
  · rfl

theorem mem_baseRows {N i a b c : ℕ} :
    (a, b, c) ∈ baseRows N i ↔ a < N ∧ b < N ∧ c < N ∧ a ≤ b ∧ b ≤ c ∧ meetsBlocks i a b c := by
  simp only [baseRows, List.mem_flatMap, List.mem_range, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨a', ha', b', hb', c', hc', ⟨hab, hbc, hm⟩, rfl, rfl, rfl⟩
    exact ⟨ha', hb', hc', hab, hbc, hm⟩
  · rintro ⟨ha, hb, hc, hab, hbc, hm⟩
    exact ⟨a, ha, b, hb, c, hc, ⟨hab, hbc, hm⟩, rfl, rfl, rfl⟩

/-- The monomial of a row. -/
def rowSym {n i : ℕ} (r : Fin (baseRows (n + 1) i).length) : Sym (Fin (n + 1)) 3 :=
  have h := mem_baseRows.mp (List.getElem_mem r.2)
  sym3 ⟨_, h.1⟩ ⟨_, h.2.1⟩ ⟨_, h.2.2.1⟩

theorem inBlockN_iff {n : ℕ} (β : ℕ) (a : Fin (n + 1)) : inBlockN β a = true ↔ InBlock β a := by
  simp [inBlockN, InBlock]

theorem mem_sym3 {n : ℕ} {a b c x : Fin (n + 1)} : x ∈ sym3 a b c ↔ x = a ∨ x = b ∨ x = c := by
  simp [sym3, Sym.mem_mk]

theorem meetsBlocks_iff {n i : ℕ} (a b c : Fin (n + 1)) :
    meetsBlocks i a b c = true ↔ sym3 a b c ∉ {m : Sym (Fin (n + 1)) 3 | ∃ β < i, AvoidsBlock β m} := by
  constructor
  · rintro h ⟨β, hβ, hav⟩
    have := List.all_eq_true.mp h β (List.mem_range.mpr hβ)
    simp only [Bool.or_eq_true, inBlockN_iff] at this
    rcases this with (h1 | h1) | h1
    · exact hav a (mem_sym3.mpr (Or.inl rfl)) h1
    · exact hav b (mem_sym3.mpr (Or.inr (Or.inl rfl))) h1
    · exact hav c (mem_sym3.mpr (Or.inr (Or.inr rfl))) h1
  · intro h
    refine List.all_eq_true.mpr fun β hβ => ?_
    by_contra hne
    simp only [Bool.or_eq_true, inBlockN_iff, not_or] at hne
    refine h ⟨β, List.mem_range.mp hβ, fun x hx => ?_⟩
    rcases mem_sym3.mp hx with rfl | rfl | rfl
    · exact hne.1.1
    · exact hne.1.2
    · exact hne.2

/-- The rows enumerate all the monomials outside `P̂₀ + ⋯ + P̂_{i-1}`. -/
theorem exists_rowSym {n i : ℕ} {m : Sym (Fin (n + 1)) 3}
    (hm : m ∉ {m : Sym (Fin (n + 1)) 3 | ∃ β < i, AvoidsBlock β m}) :
    ∃ r, rowSym (n := n) (i := i) r = m := by
  obtain ⟨a, b, c, hab, hbc, rfl⟩ := exists_sym3 m
  have hmem : ((a : ℕ), (b : ℕ), (c : ℕ)) ∈ baseRows (n + 1) i :=
    mem_baseRows.mpr ⟨a.2, b.2, c.2, hab, hbc, (meetsBlocks_iff a b c).mpr hm⟩
  obtain ⟨r, hr, hreq⟩ := List.getElem_of_mem hmem
  refine ⟨⟨r, hr⟩, ?_⟩
  unfold rowSym
  ext
  simp [hreq]

/-- Selecting the row monomials. -/
def rowSelect (n i : ℕ) :
    (Sym (Fin (n + 1)) 3 → 𝕜) →ₗ[𝕜] (Fin (baseRows (n + 1) i).length → 𝕜) :=
  LinearMap.funLeft 𝕜 𝕜 rowSym

omit [CharZero 𝕜] in
theorem entry_baseMatrix (N i : ℕ) (data : LocatedPoints) (r : ℕ) (hr : r < (baseRows N i).length)
    (k : ℕ) (hk : k < (allPoints data).length) (j : ℕ) (hj : j < N) :
    baseMatrix N i data r (j + N * k)
      = tangentEntry (allPoints data)[k] j ((baseRows N i)[r]).1 ((baseRows N i)[r]).2.1
          ((baseRows N i)[r]).2.2 := by
  have hN : 0 < N := by omega
  have hdiv : (j + N * k) / N = k := by
    rw [Nat.add_mul_div_left _ _ hN, Nat.div_eq_of_lt hj, zero_add]
  have hmod : (j + N * k) % N = j := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
  simp only [baseMatrix, hdiv, hmod, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr,
    List.getElem?_eq_getElem hk, Option.getD_some]

omit [CharZero 𝕜] in
/-- The integer tangent entries are the tangent vectors of `v₃`. -/
theorem cast_tangentEntry {n : ℕ} (p : List ℤ) (j a b c : Fin (n + 1)) :
    ((tangentEntry p j a b c : ℤ) : 𝕜) = veroneseDegDeriv n 3 (fun x => ((p.getD x 0 : ℤ) : 𝕜))
      (Pi.single j 1) (sym3 a b c) := by
  rw [veroneseDegDeriv_sym3, tangentEntry]
  simp only [Fin.ext_iff]
  push_cast
  split_ifs <;> simp

variable {s : ℕ → ℕ} {t K : ℕ}

omit [CharZero 𝕜] in
/-- The rank of the certified matrix is at most the dimension of the span of the tangent
spaces at the listed points, restricted to the row monomials. -/
theorem rank_le_finrank_map {n i : ℕ} (data : LocatedPoints) :
    ((RankCertificate.toMatrix (baseMatrix (n + 1) i data) (baseRows (n + 1) i).length
        ((allPoints data).length * (n + 1))).map (Int.cast : ℤ → 𝕜)).rank
      ≤ Module.finrank 𝕜 ((⨆ k : Fin (allPoints data).length, (veroneseDegParam n 3
          (fun x => (((allPoints data)[k].getD x 0 : ℤ) : 𝕜))).tangentSpace).map
        (rowSelect n i)) := by
  rw [Matrix.rank_eq_finrank_span_cols]
  refine Submodule.finrank_mono (Submodule.span_le.mpr ?_)
  rintro _ ⟨col, rfl⟩
  -- the column `j + (n + 1) k` is the tangent vector at the `k`-th point in direction `j`
  obtain ⟨⟨k, j⟩, rfl⟩ := finProdFinEquiv.surjective col
  refine ⟨veroneseDegDeriv n 3 (fun x => (((allPoints data)[k].getD x 0 : ℤ) : 𝕜))
    (Pi.single j 1), Submodule.mem_iSup_of_mem k ⟨_, rfl⟩, ?_⟩
  funext r
  simp only [rowSelect, LinearMap.funLeft_apply, Matrix.col_apply, Matrix.map_apply,
    RankCertificate.toMatrix, Matrix.of_apply]
  rw [finProdFinEquiv_apply_val, entry_baseMatrix _ _ _ _ r.2 _ k.2 _ j.2, rowSym]
  exact (cast_tangentEntry (n := n) _ _ _ _ _).symm

/-- The span of the tangent spaces at the listed points. -/
def listedSpan (n : ℕ) (data : LocatedPoints) : Submodule 𝕜 (Sym (Fin (n + 1)) 3 → 𝕜) :=
  ⨆ k : Fin (allPoints data).length, (veroneseDegParam n 3
    (fun x => (((allPoints data)[k].getD x 0 : ℤ) : 𝕜))).tangentSpace

/-- **Full row rank.** If a certificate shows that the tangent vectors at the listed points,
restricted to the monomials outside `P̂₀ + ⋯ + P̂_{i-1}`, have full row rank, then their span
restricted to those monomials is everything. -/
theorem map_restrict_eq_top_of_check {i : ℕ} {data : LocatedPoints} {c : RankCertificate.Cert}
    (hc : RankCertificate.check (baseMatrix (t + 4 + 1) i data) (baseRows (t + 4 + 1) i).length
      ((allPoints data).length * (t + 4 + 1)) c = true)
    (hR : c.rows.length = (baseRows (t + 4 + 1) i).length) :
    (listedSpan (𝕜 := 𝕜) (t + 4) data).map (coordRestrict (t + 4) 3 (latticeSet t i)ᶜ) = ⊤ := by
  classical
  have hrank := (RankCertificate.le_rank_of_check (𝕜 := 𝕜) hc).trans (rank_le_finrank_map data)
  rw [hR] at hrank
  have htop : (listedSpan (𝕜 := 𝕜) (t + 4) data).map (rowSelect (t + 4) i) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _)
      (by rw [Module.finrank_fin_fun]; exact hrank))
  rw [eq_top_iff]
  rintro g -
  let v : Fin (baseRows (t + 4 + 1) i).length → 𝕜 := fun r =>
    if h : rowSym r ∈ (latticeSet t i)ᶜ then g ⟨_, h⟩ else 0
  obtain ⟨w, hw, hwv⟩ :=
    (htop ▸ Submodule.mem_top : v ∈ (listedSpan (t + 4) data).map (rowSelect (t + 4) i))
  refine ⟨w, hw, funext fun ⟨m, hm⟩ => ?_⟩
  obtain ⟨r, rfl⟩ := exists_rowSym (n := t + 4) (i := i) hm
  have := congrFun hwv r
  simp only [rowSelect, LinearMap.funLeft_apply] at this
  show w (rowSym r) = _
  rw [this]
  exact dite_eq_left hm

omit [CharZero 𝕜] in
/-- Valid listed points span a subspace of the configuration space at suitable parameters. -/
theorem exists_param_listedSpan_le {data : LocatedPoints}
    (hv : validPoints s t K data = true) :
    ∃ x₀ : Param s t K → 𝕜, listedSpan (t + 4) data
      ≤ ⨆ σ, (veroneseDegParam (t + 4) 3 (configPoint x₀ σ)).tangentSpace := by
  obtain ⟨x₀, hx₀⟩ := exists_param_of_valid (𝕜 := 𝕜) hv
  refine ⟨x₀, iSup_le fun k => ?_⟩
  obtain ⟨σ, hσ⟩ := hx₀ _ (List.getElem_mem k.2)
  exact le_iSup_of_le σ (le_of_eq (congrArg (fun v =>
    (veroneseDegParam (𝕜 := 𝕜) (t + 4) 3 v).tangentSpace) hσ.symm))

/-- **Base case, superabundant form.** If the listed points are valid and a certificate shows
that their tangent vectors, restricted to the monomials outside `P̂₀ + ⋯ + P̂_{i-1}`, have full
row rank, then `A_{i,K}(t)` is everything for general points. -/
theorem good_top_of_check {i : ℕ} {data : LocatedPoints} (hv : validPoints s t K data = true)
    {c : RankCertificate.Cert}
    (hc : RankCertificate.check (baseMatrix (t + 4 + 1) i data) (baseRows (t + 4 + 1) i).length
      ((allPoints data).length * (t + 4 + 1)) c = true)
    (hR : c.rows.length = (baseRows (t + 4 + 1) i).length) :
    Good 𝕜 s t K i ((t + 7).choose 3) := by
  obtain ⟨x₀, hx₀⟩ := exists_param_listedSpan_le (𝕜 := 𝕜) hv
  refine Good.of_point x₀ ?_
  have hconfig : configSpace s t K i x₀ = ⊤ := by
    rw [eq_top_iff, ← (monoSpan_sup_eq_top_iff _ _).mpr (map_restrict_eq_top_of_check hc hR)]
    exact sup_le_sup_left hx₀ _
  rw [hconfig, finrank_top, finrank_ambient_veroneseDeg]

/-- **Base case, independence form for `i = 0`.** A certificate of rank `r` for the tangent
vectors at valid listed points gives `dim A_{0,K}(t) ≥ r` for general points. -/
theorem good_zero_of_check {data : LocatedPoints} (hv : validPoints s t K data = true)
    {c : RankCertificate.Cert}
    (hc : RankCertificate.check (baseMatrix (t + 4 + 1) 0 data) (baseRows (t + 4 + 1) 0).length
      ((allPoints data).length * (t + 4 + 1)) c = true) :
    Good 𝕜 s t K 0 c.rows.length := by
  obtain ⟨x₀, hx₀⟩ := exists_param_listedSpan_le (𝕜 := 𝕜) hv
  refine Good.of_point x₀ ?_
  calc c.rows.length ≤ _ := RankCertificate.le_rank_of_check (𝕜 := 𝕜) hc
    _ ≤ _ := rank_le_finrank_map data
    _ ≤ Module.finrank 𝕜 (listedSpan (𝕜 := 𝕜) (t + 4) data) := Submodule.finrank_map_le _ _
    _ ≤ _ := Submodule.finrank_mono (le_sup_of_le_right hx₀)

/-- **Small cases.** A certificate of rank `r` for the tangent vectors at listed points of
`𝕜^{n+1}` gives `r ≤ dim ∑ T_p`. -/
theorem le_finrank_listedSpan_of_check {n : ℕ} {data : LocatedPoints} {c : RankCertificate.Cert}
    (hc : RankCertificate.check (baseMatrix (n + 1) 0 data) (baseRows (n + 1) 0).length
      ((allPoints data).length * (n + 1)) c = true) :
    c.rows.length ≤ Module.finrank 𝕜 (listedSpan (𝕜 := 𝕜) n data) :=
  (RankCertificate.le_rank_of_check hc).trans
    ((rank_le_finrank_map data).trans (Submodule.finrank_map_le _ _))

/-- The monomial of a row lies outside `P̂₀ + ⋯ + P̂_{i-1}`. -/
theorem rowSym_not_mem {n i : ℕ} (r : Fin (baseRows (n + 1) i).length) :
    rowSym r ∉ {m : Sym (Fin (n + 1)) 3 | ∃ β < i, AvoidsBlock β m} := by
  unfold rowSym
  exact (meetsBlocks_iff _ _ _).mp (mem_baseRows.mp (List.getElem_mem r.2)).2.2.2.2.2

omit [CharZero 𝕜] in
/-- Selecting the row monomials factors through the restriction to the monomials outside
`P̂₀ + ⋯ + P̂_{i-1}`, so it can only lose dimension. -/
theorem finrank_map_rowSelect_le {i : ℕ} (W : Submodule 𝕜 (Sym (Fin (t + 4 + 1)) 3 → 𝕜)) :
    Module.finrank 𝕜 (W.map (rowSelect (t + 4) i))
      ≤ Module.finrank 𝕜 (W.map (coordRestrict (t + 4) 3 (latticeSet t i)ᶜ)) := by
  let g : (↥(latticeSet t i)ᶜ → 𝕜) →ₗ[𝕜] (Fin (baseRows (t + 4 + 1) i).length → 𝕜) :=
    LinearMap.funLeft 𝕜 𝕜 fun r => ⟨rowSym r, rowSym_not_mem r⟩
  have : rowSelect (t + 4) i = g ∘ₗ coordRestrict (t + 4) 3 (latticeSet t i)ᶜ :=
    LinearMap.ext fun _ => rfl
  rw [this, Submodule.map_comp]
  exact Submodule.finrank_map_le _ _

omit [CharZero 𝕜] in
/-- `P̂₀ + ⋯ + P̂_{i-1}` has codimension at most the number of rows. -/
theorem finrank_monoSpan_latticeSet (i : ℕ) :
    (t + 7).choose 3 - (baseRows (t + 4 + 1) i).length
      ≤ Module.finrank 𝕜 (monoSpan (𝕜 := 𝕜) (t + 4) 3 (latticeSet t i)) := by
  classical
  have h := finrank_monoSpan_sup (𝕜 := 𝕜) (latticeSet t i) ⊤
  rw [sup_top_eq, finrank_top, finrank_ambient_veroneseDeg, Submodule.map_top,
    (LinearMap.range_eq_top (f := coordRestrict (𝕜 := 𝕜) (t + 4) 3 (latticeSet t i)ᶜ)).mpr
      (LinearMap.funLeft_surjective_of_injective _ _ _
      Subtype.val_injective), finrank_top, Module.finrank_fintype_fun_eq_card] at h
  have hcard : Fintype.card ↥(latticeSet t i)ᶜ ≤ (baseRows (t + 4 + 1) i).length := by
    have := Fintype.card_le_of_surjective
      (fun r : Fin (baseRows (t + 4 + 1) i).length => (⟨rowSym r, rowSym_not_mem r⟩ :
        ↥(latticeSet t i)ᶜ))
      fun ⟨m, hm⟩ => (exists_rowSym hm).imp fun _ hr => Subtype.ext hr
    rw [Fintype.card_fin] at this
    convert this
  have h7 : t + 4 + 3 = t + 7 := rfl
  rw [h7] at h
  omega

/-- **Base case, general form.** If the listed points are valid and a certificate shows that
their tangent vectors, restricted to the monomials outside `P̂₀ + ⋯ + P̂_{i-1}`, have rank
`≥ r`, then `dim A_{i,K}(t) ≥ N - #rows + r` for general points. -/
theorem good_of_check {i : ℕ} {data : LocatedPoints} (hv : validPoints s t K data = true)
    {c : RankCertificate.Cert}
    (hc : RankCertificate.check (baseMatrix (t + 4 + 1) i data) (baseRows (t + 4 + 1) i).length
      ((allPoints data).length * (t + 4 + 1)) c = true) :
    Good 𝕜 s t K i ((t + 7).choose 3 - (baseRows (t + 4 + 1) i).length + c.rows.length) := by
  obtain ⟨x₀, hx₀⟩ := exists_param_listedSpan_le (𝕜 := 𝕜) hv
  refine Good.of_point x₀ ?_
  have hrank := (RankCertificate.le_rank_of_check (𝕜 := 𝕜) hc).trans
    ((rank_le_finrank_map data).trans (finrank_map_rowSelect_le _))
  calc _ ≤ Module.finrank 𝕜 (monoSpan (𝕜 := 𝕜) (t + 4) 3 (latticeSet t i))
        + Module.finrank 𝕜 ((listedSpan (𝕜 := 𝕜) (t + 4) data).map
          (coordRestrict (t + 4) 3 (latticeSet t i)ᶜ)) :=
        Nat.add_le_add (finrank_monoSpan_latticeSet i) hrank
    _ = Module.finrank 𝕜 ((monoSpan (𝕜 := 𝕜) (t + 4) 3 (latticeSet t i)
          ⊔ listedSpan (t + 4) data : Submodule 𝕜 _)) := (finrank_monoSpan_sup _ _).symm
    _ ≤ _ := Submodule.finrank_mono (sup_le_sup_left hx₀ _)

end Soundness

/-! ### §D — The uniform case `K = 3` -/

section Uniform

/-- A monomial meeting all three blocks has its coordinates among the first nine. -/
theorem lt_nine_of_meets {n : ℕ} {m : Sym (Fin (n + 1)) 3}
    (hm : m ∉ {m : Sym (Fin (n + 1)) 3 | ∃ β < 3, AvoidsBlock β m}) : ∀ a ∈ m, (a : ℕ) < 9 := by
  obtain ⟨a, b, c, -, -, rfl⟩ := exists_sym3 m
  have h := List.all_eq_true.mp ((meetsBlocks_iff a b c).mpr hm)
  have h0 := h 0 (by simp)
  have h1 := h 1 (by simp)
  have h2 := h 2 (by simp)
  simp only [inBlockN, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h0 h1 h2
  intro x hx
  rcases mem_sym3.mp hx with rfl | rfl | rfl <;> omega

/-- The block-meeting condition only sees the values of the coordinates. -/
theorem map_castLE_mem_compl {m n : ℕ} (h : m ≤ n) {i : ℕ} {m' : Sym (Fin (m + 1)) 3}
    (hm' : m' ∈ {m' : Sym (Fin (m + 1)) 3 | ∃ β < i, AvoidsBlock β m'}ᶜ) :
    Sym.map (Fin.castLE (Nat.succ_le_succ h)) m'
      ∈ {m : Sym (Fin (n + 1)) 3 | ∃ β < i, AvoidsBlock β m}ᶜ := by
  rintro ⟨β, hβ, hav⟩
  refine hm' ⟨β, hβ, fun a ha hin => hav _ (Sym.mem_map.mpr ⟨a, ha, rfl⟩) ?_⟩
  simpa [InBlock] using hin

variable {s : ℕ → ℕ} {t : ℕ}

omit [CharZero 𝕜] in
/-- **Realization for a family.** Points with an injective assignment of slots, vanishing on
the blocks of their locations, are configuration points. -/
theorem exists_param_of_family {ι : Type*} (q : ι → Fin (t + 4 + 1) → 𝕜) (τ : ι → Slot s t K)
    (hτ : Function.Injective τ)
    (hq : ∀ k a, (∃ β ∈ ((τ k).1 : Finset ℕ), InBlock β a) → q k a = 0) :
    ∃ x₀ : Param s t K → 𝕜, ∀ k, configPoint x₀ (τ k) = q k := by
  classical
  refine ⟨fun σa => if h : ∃ k, τ k = σa.1 then q h.choose σa.2 else 0, fun k => ?_⟩
  have hex : ∃ k', τ k' = τ k := ⟨k, rfl⟩
  have hk : hex.choose = k := hτ hex.choose_spec
  funext a
  simp only [configPoint, zeroBlocks, dite_eq_left hex, hk]
  split_ifs with ha
  · exact (hq k a ha).symm
  · rfl

/-- The nine points of the uniform case, as located points: three on each `U_j`. -/
def uniformData (ps : Fin 3 → Fin 3 → List ℤ) : LocatedPoints :=
  (List.finRange 3).map fun j : Fin 3 => ([(j : ℕ)], (List.finRange 3).map (ps j))

/-- **The uniform case `K = 3`.** Let nine points of `𝕜⁹` (three on each `U_j`) have tangent
vectors filling the `27` monomials meeting all three blocks, as shown by a certificate at level
`t = 4`. Then for every `t ≥ 4`, the same points (padded by zeros) make `A_{3,3}(t)` everything:
the monomials meeting all three blocks only involve the first nine coordinates. -/
theorem good_three (ps : Fin 3 → Fin 3 → List ℤ)
    (hv : validPoints (fun _ => 0) 4 3 (uniformData ps) = true) {c : RankCertificate.Cert}
    (hc : RankCertificate.check (baseMatrix (4 + 4 + 1) 3 (uniformData ps))
      (baseRows (4 + 4 + 1) 3).length ((allPoints (uniformData ps)).length * (4 + 4 + 1)) c = true)
    (hR : c.rows.length = (baseRows (4 + 4 + 1) 3).length) (ht : 4 ≤ t) :
    Good 𝕜 s t 3 3 ((t + 7).choose 3) := by
  classical
  have hle : 4 + 4 + 1 ≤ t + 4 + 1 := by omega
  let ι : Fin (4 + 4 + 1) → Fin (t + 4 + 1) := Fin.castLE hle
  have hι : Function.Injective ι := Fin.castLE_injective hle
  -- the small points, and their slots at level `t`
  let P : Fin 3 × Fin 3 → Fin (4 + 4 + 1) → 𝕜 := fun jc a => (((ps jc.1 jc.2).getD a 0 : ℤ) : 𝕜)
  have hloc : ∀ j : Fin 3, ({(j : ℕ)} : Finset ℕ) ∈ (Finset.range 3).powerset := fun j => by
    simp
  have hcount : ∀ j : Fin 3, countAt s t 3 {(j : ℕ)} = 3 := fun j => by
    simp [countAt, countFor]
  let τ : Fin 3 × Fin 3 → Slot s t 3 := fun jc =>
    ⟨⟨{(jc.1 : ℕ)}, hloc jc.1⟩, ⟨jc.2, by rw [hcount]; exact jc.2.2⟩⟩
  have hτ : Function.Injective τ := by
    rintro ⟨j, c⟩ ⟨j', c'⟩ h
    simp only [τ, Sigma.mk.inj_iff] at h
    obtain ⟨h1, h2⟩ := h
    have hj : j = j' := Fin.ext (by simpa using congrArg Subtype.val h1)
    subst hj
    have hc : c = c' := Fin.ext (by simpa using (Fin.heq_ext_iff rfl).mp h2)
    rw [hc]
  -- the small points vanish on the blocks of their locations
  have hmemData : ∀ j : Fin 3, ([(j : ℕ)], (List.finRange 3).map (ps j)) ∈ uniformData ps :=
    fun j => List.mem_map.mpr ⟨j, List.mem_finRange j, rfl⟩
  have hzero : ∀ (jc : Fin 3 × Fin 3) (a : Fin (4 + 4 + 1)), InBlock jc.1 a → P jc a = 0 := by
    rintro ⟨j, c⟩ a hin
    simp only [validPoints, Bool.and_eq_true, List.all_eq_true] at hv
    have h := (hv.2 _ (hmemData j)).2 (ps j c) (List.mem_map.mpr ⟨c, List.mem_finRange c, rfl⟩)
    have h' := h.2 a (List.mem_range.mpr a.2)
    have hb : ([(j : ℕ)].any fun β => inBlockN β a) = true := by
      simpa [inBlockN, InBlock] using hin
    simp only [hb, Bool.not_true, Bool.false_or, beq_iff_eq] at h'
    simp only [P]
    rw [h', Int.cast_zero]
  obtain ⟨x₀, hx₀⟩ := exists_param_of_family (fun jc => extAlong ι (P jc)) τ hτ (by
    rintro jc a ⟨β, hβ, hin⟩
    simp only [τ, Finset.mem_singleton] at hβ
    subst hβ
    by_cases ha : a ∈ Set.range ι
    · obtain ⟨a', rfl⟩ := ha
      rw [extAlong_apply hι]
      exact hzero jc a' (by simpa [ι, InBlock] using hin)
    · exact extAlong_of_not_mem _ ha)
  refine Good.of_point x₀ ?_
  -- the listed points at level `4` fill the 27 monomials meeting all three blocks
  set W := listedSpan (𝕜 := 𝕜) (4 + 4) (uniformData ps)
  have hfill := map_restrict_eq_top_of_check (𝕜 := 𝕜) hc hR
  -- they are the points `P jc`
  have hW : W ≤ ⨆ jc, (veroneseDegParam (4 + 4) 3 (P jc)).tangentSpace := iSup_le fun k => by
    obtain ⟨e, he, hq⟩ := List.mem_flatMap.mp (List.getElem_mem k.2 :
      (allPoints (uniformData ps))[k] ∈ allPoints (uniformData ps))
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp he
    obtain ⟨c, -, hc'⟩ := List.mem_map.mp hq
    refine le_iSup_of_le (j, c) (le_of_eq (congrArg (fun v =>
      (veroneseDegParam (𝕜 := 𝕜) (4 + 4) 3 v).tangentSpace) ?_))
    funext x
    simp only [P, hc']
    rfl
  -- pushed to level `t`, they are configuration points
  have hpush : W.map (pushAlong (𝕜 := 𝕜) (d := 3) ι).toLinearMap
      ≤ ⨆ σ, (veroneseDegParam (t + 4) 3 (configPoint x₀ σ)).tangentSpace := by
    refine (Submodule.map_mono hW).trans ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun jc => (map_tangentSpace_pushAlong_le hι (P jc)).trans ?_
    exact le_iSup_of_le (τ jc) (le_of_eq (congrArg (fun v =>
      (veroneseDegParam (𝕜 := 𝕜) (t + 4) 3 v).tangentSpace) (hx₀ jc).symm))
  -- the monomials meeting all three blocks come from level `4`
  have hcompl : ∀ m' : Sym (Fin (4 + 4 + 1)) 3, m' ∈ (latticeSet 4 3)ᶜ →
      Sym.map ι m' ∈ (latticeSet t 3)ᶜ := fun m' hm' =>
    map_castLE_mem_compl (m := 4 + 4) (n := t + 4) (by omega) hm'
  have htransfer : (W.map (pushAlong (𝕜 := 𝕜) (d := 3) ι).toLinearMap).map
      (coordRestrict (t + 4) 3 (latticeSet t 3)ᶜ) = ⊤ := by
    rw [eq_top_iff]
    rintro g -
    let g' : ↥(latticeSet 4 3)ᶜ → 𝕜 := fun m' => g ⟨Sym.map ι m', hcompl m' m'.2⟩
    obtain ⟨w, hw, hwg⟩ := (hfill ▸ Submodule.mem_top :
      g' ∈ W.map (coordRestrict (4 + 4) 3 (latticeSet 4 3)ᶜ))
    refine ⟨pushAlong ι w, ⟨w, hw, rfl⟩, funext fun ⟨m, hm⟩ => ?_⟩
    have hall : ∀ a ∈ m, a ∈ Set.range ι := fun a ha =>
      ⟨⟨a, by have := lt_nine_of_meets hm a ha; omega⟩, Fin.ext rfl⟩
    obtain ⟨m', rfl⟩ := sym_mem_range_map hall
    have hm' : m' ∈ (latticeSet 4 3)ᶜ := by
      rintro ⟨β, hβ, hav⟩
      refine hm ⟨β, hβ, fun a ha hin => ?_⟩
      obtain ⟨a', ha', rfl⟩ := Sym.mem_map.mp ha
      exact hav a' ha' (by simpa [ι, InBlock] using hin)
    simp only [coordRestrict, LinearMap.funLeft_apply]
    rw [pushAlong_map hι]
    exact congrFun hwg ⟨m', hm'⟩
  have hconfig : configSpace s t 3 3 x₀ = ⊤ := by
    rw [eq_top_iff, ← (monoSpan_sup_eq_top_iff _ _).mpr htransfer]
    exact sup_le_sup_left hpush _
  rw [hconfig, finrank_top, finrank_ambient_veroneseDeg]

end Uniform

end CubicBaseCases
