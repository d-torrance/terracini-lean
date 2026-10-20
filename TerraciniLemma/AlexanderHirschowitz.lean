module

public import TerraciniLemma.AlexanderHirschowitzCubic
public import TerraciniLemma.VeroneseGeneral

/-!
# The Alexander–Hirschowitz exceptional cases, at general points

The Alexander–Hirschowitz theorem says that `σ_r(v_d(ℙⁿ))` has the expected dimension
`min(N, r(n+1)) - 1` except in the following cases, where it is **defective**:

* `d = 2`, `2 ≤ r ≤ n` (quadrics);
* `(n, d, r) = (2, 4, 5), (3, 4, 9), (4, 4, 14)` (quartics);
* `(n, d, r) = (4, 3, 7)` (cubics).

This file proves the defectivity of every exceptional case **for general points**
(`ForGeneralPoints`), following Brambilla–Ottaviani, *On the Alexander–Hirschowitz theorem*,
J. Pure Appl. Algebra **212** (2008), §2. (The hard direction of the theorem, that every other
case is non-defective, is not formalized.) By Terracini's Lemma, defectivity of `σ_r` at general
points is defectivity of the span of the tangent spaces at `r` general points of the cone, which
is what `IsDefective` measures.

* **Quartics** (§1). Since `r < binom(n+2, 2)`, some nonzero quadric `Q` passes through the `r`
  points; then `Q²` is a nonzero quartic singular at all of them, so the tangent spaces lie in a
  hyperplane (`finrank_iSup_tangentSpace_le_of_singular`). Here no genericity is needed beyond
  the points being nonzero.
* **Quadrics** (§2). Transferred from `isDefective_veroneseGeneral_of_linearIndependent` (the
  `Sym2` model of `v₂(ℙⁿ)`) to the `Sym _ 2` model used here, along the identification
  `Sym2 α ≃ Sym α 2`. General points are linearly independent.
* **Cubics** (in `TerraciniLemma.AlexanderHirschowitzCubic`). Seven general points of `ℙ⁴`
  lie on a rational normal quartic, and the cubic hypersurface `σ₂` of that curve is singular
  along it (`ah437_isDefective_general`).

§3 collects everything into `alexanderHirschowitz_exceptions_isDefective`.
-/

@[expose] public section

noncomputable section AlexanderHirschowitz

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-! ### §1 — Quartics: `(2,4,5)`, `(3,4,9)`, `(4,4,14)` -/

omit [CharZero 𝕜] in
/-- Through any `r < binom(n+2,2)` points of `𝕜^{n+1}` passes a nonzero quadric: the `r`
evaluation conditions on the `binom(n+2,2)`-dimensional space of quadrics have a common
nonzero solution. -/
theorem exists_quadric_through {n r : ℕ} (p : Fin r → Fin (n + 1) → 𝕜)
    (hr : r < (n + 2).choose 2) :
    ∃ χ : Module.Dual 𝕜 (Sym (Fin (n + 1)) 2 → 𝕜), χ ≠ 0 ∧
      ∀ k, χ (veroneseDeg n 2 (p k)) = 0 := by
  let ev : Module.Dual 𝕜 (Sym (Fin (n + 1)) 2 → 𝕜) →ₗ[𝕜] (Fin r → 𝕜) :=
    { toFun := fun χ k => χ (veroneseDeg n 2 (p k))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : LinearMap.ker ev ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rwa [Subspace.dual_finrank_eq, finrank_ambient_veroneseDeg, Module.finrank_fin_fun])
  obtain ⟨χ, hχ, hχ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨χ, hχ0, fun k => congrFun hχ k⟩

/-- **The quartic bound.** For *any* `r < binom(n+2,2)` points, the tangent spaces to the cone
over `v₄(ℙⁿ)` at their images span at most `binom(n+4,4) - 1` dimensions: they all lie in the
hyperplane dual to `Q²`, where `Q` is a quadric through the points. -/
theorem finrank_iSup_tangentSpace_quartic_le {n r : ℕ} (p : Fin r → Fin (n + 1) → 𝕜)
    (hr : r < (n + 2).choose 2) :
    Module.finrank 𝕜 (⨆ k, (veroneseDegParam n 4 (p k)).tangentSpace : Submodule 𝕜 _)
      ≤ (n + 4).choose 4 - 1 := by
  obtain ⟨χ, hχ0, hχp⟩ := exists_quadric_through p hr
  set Q := veroneseFormOf n 2 χ with hQ
  refine finrank_iSup_tangentSpace_le_of_singular p (F := Q * Q)
    (mul_mem_veroneseForms rfl ⟨χ, rfl⟩ ⟨χ, rfl⟩) ?_ fun k => ?_
  · obtain ⟨x, hx⟩ := exists_apply_veroneseDeg_ne_zero hχ0
    intro h
    exact hx (mul_self_eq_zero.mp (congrFun h x))
  · -- `d(Q²) = 2 Q dQ` vanishes where `Q` does.
    have h := (hasFDerivAt_veroneseFormOf n 2 χ (p k)).mul
      (hasFDerivAt_veroneseFormOf n 2 χ (p k))
    have hq : Q (p k) = 0 := hχp k
    rw [← hQ, hq] at h
    refine h.congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
    simp

/-- **Quartic defectivity.** If `r < binom(n+2,2)` but `binom(n+4,4) ≤ r(n+1)`, then
`σ_r(v₄(ℙⁿ))` is defective at every `r`-tuple of nonzero points. The two inequalities hold
exactly for `(n, r) = (2, 5), (3, 9), (4, 14)`. -/
theorem isDefective_quartic {n r : ℕ} (p : Fin r → Fin (n + 1) → 𝕜) (hp : ∀ k, p k ≠ 0)
    (hr : r < (n + 2).choose 2) (hN : (n + 4).choose 4 ≤ r * (n + 1)) :
    IsDefective (fun k => (veroneseDegParam n 4 (p k)).tangentSpace) :=
  isDefective_of_finrank_le (by norm_num) p hp hN (finrank_iSup_tangentSpace_quartic_le p hr)

/-- `σ₅(v₄(ℙ²))` is defective at general points (the `(2,4,5)` case). -/
theorem ah245_isDefective_general :
    ForGeneralPoints (𝕜 := 𝕜) 5 3
      (fun p => IsDefective (fun k => (veroneseDegParam 2 4 (p k)).tangentSpace)) :=
  ForGeneralPoints.ne_zero.mono fun p hp => isDefective_quartic p hp (by decide) (by decide)

/-- `σ₉(v₄(ℙ³))` is defective at general points (the `(3,4,9)` case). -/
theorem ah349_isDefective_general :
    ForGeneralPoints (𝕜 := 𝕜) 9 4
      (fun p => IsDefective (fun k => (veroneseDegParam 3 4 (p k)).tangentSpace)) :=
  ForGeneralPoints.ne_zero.mono fun p hp => isDefective_quartic p hp (by decide) (by decide)

/-- `σ₁₄(v₄(ℙ⁴))` is defective at general points (the `(4,4,14)` case). -/
theorem ah4414_isDefective_general :
    ForGeneralPoints (𝕜 := 𝕜) 14 5
      (fun p => IsDefective (fun k => (veroneseDegParam 4 4 (p k)).tangentSpace)) :=
  ForGeneralPoints.ne_zero.mono fun p hp => isDefective_quartic p hp (by decide) (by decide)

/-! ### §2 — Quadrics: `d = 2`, `2 ≤ r ≤ n` -/

omit [CharZero 𝕜] in
/-- The two models of the ambient space of `v₂(ℙⁿ)` — `Sym2 (Fin (n+1)) → 𝕜`
(`TerraciniLemma.VeroneseGeneral`) and `Sym (Fin (n+1)) 2 → 𝕜` (`TerraciniLemma.VeroneseDegree`)
— identified along `Sym2.equivSym`. -/
def sym2AmbientEquiv (n : ℕ) : (Sym2 (Fin (n + 1)) → 𝕜) ≃ₗ[𝕜] (Sym (Fin (n + 1)) 2 → 𝕜) :=
  LinearEquiv.funCongrLeft 𝕜 𝕜 (Sym2.equivSym (Fin (n + 1))).symm

omit [CharZero 𝕜] in
/-- `sym2AmbientEquiv` as a continuous linear map (a reindexing of coordinates). -/
def sym2AmbientCLM (n : ℕ) : (Sym2 (Fin (n + 1)) → 𝕜) →L[𝕜] (Sym (Fin (n + 1)) 2 → 𝕜) :=
  ContinuousLinearMap.pi fun s => ContinuousLinearMap.proj ((Sym2.equivSym (Fin (n + 1))).symm s)

omit [CharZero 𝕜] in
/-- The two cone parametrizations of `v₂(ℙⁿ)` agree under `sym2AmbientEquiv`. -/
theorem veroneseDeg_two_eq (n : ℕ) (v : Fin (n + 1) → 𝕜) :
    veroneseDeg n 2 v = sym2AmbientCLM n (veroneseGeneral n v) := by
  funext s
  obtain ⟨z, rfl⟩ := (Sym2.equivSym (Fin (n + 1))).surjective s
  induction z using Sym2.ind with
  | _ i j =>
    have hval : ((Sym2.equivSym (Fin (n + 1)) s(i, j) : Sym (Fin (n + 1)) 2) :
        Multiset (Fin (n + 1))) = {i, j} := rfl
    simp [sym2AmbientCLM, veroneseDeg, veroneseDegPoly, hval, veroneseGeneral,
      veroneseGeneralPoly]

omit [CharZero 𝕜] in
theorem veroneseDegDeriv_two_eq (n : ℕ) (v : Fin (n + 1) → 𝕜) :
    veroneseDegDeriv n 2 v = (sym2AmbientCLM n).comp (veroneseGeneralDeriv n v) := by
  have h := (sym2AmbientCLM (𝕜 := 𝕜) n).hasFDerivAt.comp v (hasFDerivAt_veroneseGeneral n v)
  rw [show ⇑(sym2AmbientCLM (𝕜 := 𝕜) n) ∘ veroneseGeneral n = veroneseDeg n 2 from
    funext fun v => (veroneseDeg_two_eq n v).symm] at h
  exact (hasFDerivAt_veroneseDeg n 2 v).unique h

omit [CharZero 𝕜] in
/-- The tangent spaces of the two models correspond under `sym2AmbientEquiv`. -/
theorem tangentSpace_veroneseDegParam_two (n : ℕ) (v : Fin (n + 1) → 𝕜) :
    (veroneseDegParam n 2 v).tangentSpace
      = (veroneseGeneralParam n v).tangentSpace.map (sym2AmbientEquiv (𝕜 := 𝕜) n).toLinearMap := by
  show LinearMap.range (veroneseDegDeriv (𝕜 := 𝕜) n 2 v).toLinearMap = _
  rw [veroneseDegDeriv_two_eq]
  show LinearMap.range ((sym2AmbientCLM (𝕜 := 𝕜) n).toLinearMap.comp
    (veroneseGeneralDeriv (𝕜 := 𝕜) n v).toLinearMap) = _
  rw [LinearMap.range_comp]
  rfl

/-- **Quadric defectivity.** For `2 ≤ r ≤ n` and any linearly independent `p₀, …, p_{r-1}`,
`σ_r(v₂(ℙⁿ))` is defective, transported from
`isDefective_veroneseGeneral_of_linearIndependent`. -/
theorem isDefective_quadric_of_linearIndependent {n r : ℕ} (hrn : r ≤ n) (h2r : 2 ≤ r) (p : Fin r → Fin (n + 1) → 𝕜)
    (hp : LinearIndependent 𝕜 p) :
    IsDefective (fun k => (veroneseDegParam n 2 (p k)).tangentSpace) := by
  have h := isDefective_veroneseGeneral_of_linearIndependent hrn p hp h2r
  have hsup : (⨆ k, (veroneseDegParam n 2 (p k)).tangentSpace : Submodule 𝕜 _)
      = (⨆ k, (veroneseGeneralParam n (p k)).tangentSpace).map
        (sym2AmbientEquiv (𝕜 := 𝕜) n).toLinearMap := by
    simp_rw [tangentSpace_veroneseDegParam_two, Submodule.map_iSup]
  have hdim : ∀ k, Module.finrank 𝕜 (veroneseDegParam n 2 (p k)).tangentSpace
      = Module.finrank 𝕜 (veroneseGeneralParam n (p k)).tangentSpace := fun k => by
    rw [tangentSpace_veroneseDegParam_two, LinearEquiv.finrank_map_eq]
  unfold IsDefective expectedDim at h ⊢
  rw [hsup, LinearEquiv.finrank_map_eq, Finset.sum_congr rfl fun k _ => hdim k,
    finrank_ambient_veroneseDeg]
  rwa [finrank_ambient_veroneseGeneral] at h

omit [CharZero 𝕜] in
/-- `r ≤ n + 1` general points of `𝕜^{n+1}` are linearly independent: the polynomial is the
leading `r × r` minor of the coordinate matrix. -/
theorem ForGeneralPoints.linearIndependent {n r : ℕ} (hr : r ≤ n + 1) :
    ForGeneralPoints (𝕜 := 𝕜) r (n + 1) (fun p => LinearIndependent 𝕜 p) := by
  classical
  let A : Matrix (Fin r) (Fin r) (MvPolynomial (Fin r × Fin (n + 1)) 𝕜) :=
    fun k i => MvPolynomial.X (k, Fin.castLE hr i)
  refine ⟨A.det, fun h => ?_, fun p hp => ?_⟩
  · -- At the coordinate points `e₀, …, e_{r-1}` the minor is `det 1 = 1`.
    have h1 := congrArg (MvPolynomial.eval fun ki : Fin r × Fin (n + 1) =>
      (Pi.single (Fin.castLE hr ki.1) 1 : Fin (n + 1) → 𝕜) ki.2) h
    rw [RingHom.map_det, map_zero] at h1
    have hone : (MvPolynomial.eval fun ki : Fin r × Fin (n + 1) =>
        (Pi.single (Fin.castLE hr ki.1) 1 : Fin (n + 1) → 𝕜) ki.2).mapMatrix A = 1 := by
      ext k i
      show MvPolynomial.eval _ (MvPolynomial.X _) = _
      rw [MvPolynomial.eval_X]
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [hone, Matrix.det_one] at h1
    exact one_ne_zero h1
  · rw [RingHom.map_det] at hp
    have hrows := Matrix.linearIndependent_rows_of_det_ne_zero hp
    refine LinearIndependent.of_comp (LinearMap.funLeft 𝕜 𝕜 (Fin.castLE hr)) ?_
    convert hrows using 1
    funext k i
    exact (MvPolynomial.eval_X (f := fun ki : Fin r × Fin (n + 1) => p ki.1 ki.2) (k, Fin.castLE hr i)).symm

/-- `σ_r(v₂(ℙⁿ))` is defective at general points for `2 ≤ r ≤ n`. -/
theorem quadric_isDefective_general {n r : ℕ} (hrn : r ≤ n) (h2r : 2 ≤ r) :
    ForGeneralPoints (𝕜 := 𝕜) r (n + 1)
      (fun p => IsDefective (fun k => (veroneseDegParam n 2 (p k)).tangentSpace)) :=
  (ForGeneralPoints.linearIndependent (by omega)).mono fun p hp =>
    isDefective_quadric_of_linearIndependent hrn h2r p hp

/-- **Quadric defectivity at every configuration** of `r` nonzero points, `2 ≤ r ≤ n`
(including linearly dependent ones), by semicontinuity from general points. -/
theorem isDefective_quadric {n r : ℕ} (hrn : r ≤ n) (h2r : 2 ≤ r) (p : Fin r → Fin (n + 1) → 𝕜)
    (hp : ∀ k, p k ≠ 0) :
    IsDefective (fun k => (veroneseDegParam n 2 (p k)).tangentSpace) :=
  isDefective_of_forGeneralPoints (by norm_num) (quadric_isDefective_general hrn h2r) p hp

/-- The tangent spaces at the `n + 1` coordinate points span the ambient space of `v₂(ℙⁿ)`
(transported from `veroneseGeneral_sup_eq_top`). -/
theorem iSup_tangentSpace_two_single_eq_top (n : ℕ) :
    ⨆ j : Fin (n + 1), (veroneseDegParam n 2 (Pi.single j (1 : 𝕜))).tangentSpace = ⊤ := by
  have h := veroneseGeneral_sup_eq_top (𝕜 := 𝕜) n
  have hfam : ∀ j, (veroneseGeneralFamily (𝕜 := 𝕜) n (n + 1) le_rfl j).tangentSpace
      = (veroneseGeneralParam n (Pi.single j (1 : 𝕜))).tangentSpace := fun j => by
    simp [veroneseGeneralFamily, veroneseGeneralPt]
  simp_rw [hfam] at h
  simp_rw [tangentSpace_veroneseDegParam_two, ← Submodule.map_iSup, h, Submodule.map_top,
    LinearEquiv.range]

/-- **Quadric non-defectivity for `r ≥ n + 1` at general points**: at a configuration
containing the `n + 1` coordinate points the tangent spaces already fill the ambient space, and
semicontinuity spreads this to general points. -/
theorem quadric_not_isDefective_general {n r : ℕ} (hr : n + 1 ≤ r) :
    ForGeneralPoints (𝕜 := 𝕜) r (n + 1)
      (fun p => ¬ IsDefective (fun k => (veroneseDegParam n 2 (p k)).tangentSpace)) := by
  -- the coordinate points `e₀, …, eₙ`, repeated cyclically
  let p₀ : Fin r → Fin (n + 1) → 𝕜 := fun k =>
    Pi.single (⟨k % (n + 1), Nat.mod_lt _ n.succ_pos⟩ : Fin (n + 1)) 1
  refine forGeneralPoints_not_isDefective (by norm_num) p₀ (fun k => by simp [p₀]) ?_
  have hp₀ : ∀ j : Fin (n + 1), p₀ ⟨j, lt_of_lt_of_le j.2 hr⟩ = Pi.single j 1 := fun j => by
    show Pi.single _ 1 = _
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt j.2)
  have htop : ⨆ k, (veroneseDegParam n 2 (p₀ k)).tangentSpace = ⊤ :=
    eq_top_iff.mpr ((iSup_tangentSpace_two_single_eq_top n).symm.le.trans
      (iSup_le fun j => le_iSup_of_le ⟨j, lt_of_lt_of_le j.2 hr⟩ (by rw [hp₀])))
  unfold IsDefective
  rw [htop, finrank_top, finrank_ambient_veroneseDeg, not_lt]
  exact (expectedDim_veroneseDegParam_le p₀).trans (min_le_left _ _)

/-- **The Alexander–Hirschowitz theorem for quadrics**: for `r ≥ 1` general points,
`σ_r(v₂(ℙⁿ))` is defective if and only if `2 ≤ r ≤ n`. -/
theorem alexanderHirschowitz_quadric {n r : ℕ} (hr : 1 ≤ r) :
    ForGeneralPoints (𝕜 := 𝕜) r (n + 1) (fun p =>
      IsDefective (fun k => (veroneseDegParam n 2 (p k)).tangentSpace) ↔ 2 ≤ r ∧ r ≤ n) := by
  by_cases h : 2 ≤ r ∧ r ≤ n
  · exact (quadric_isDefective_general h.2 h.1).mono fun p hp => iff_of_true hp h
  rcases (by omega : r = 1 ∨ n + 1 ≤ r) with rfl | hr'
  · exact ForGeneralPoints.ne_zero.mono fun p hp =>
      iff_of_false (not_isDefective_one (by norm_num) p hp) h
  · exact (quadric_not_isDefective_general hr').mono fun p hp => iff_of_false hp h

/-! ### §3 — All the exceptional cases -/

/-- The exceptional cases of the Alexander–Hirschowitz theorem: `σ_r(v_d(ℙⁿ))` with
`d = 2, 2 ≤ r ≤ n`, or `(n, d, r) ∈ {(2,4,5), (3,4,9), (4,4,14), (4,3,7)}`. -/
def IsAHException (n d r : ℕ) : Prop :=
  (d = 2 ∧ 2 ≤ r ∧ r ≤ n) ∨ (n, d, r) = (2, 4, 5) ∨ (n, d, r) = (3, 4, 9) ∨
    (n, d, r) = (4, 4, 14) ∨ (n, d, r) = (4, 3, 7)

/-- **The Alexander–Hirschowitz exceptions are defective.** In every exceptional case, the
tangent spaces to the cone over `v_d(ℙⁿ)` at `r` general points are defective, i.e. (by
Terracini's Lemma) `σ_r(v_d(ℙⁿ))` has less than the expected dimension. -/
theorem alexanderHirschowitz_exceptions_isDefective_general {n d r : ℕ}
    (h : IsAHException n d r) :
    ForGeneralPoints (𝕜 := 𝕜) r (n + 1)
      (fun p => IsDefective (fun k => (veroneseDegParam n d (p k)).tangentSpace)) := by
  rcases h with ⟨rfl, h2r, hrn⟩ | h | h | h | h
  · exact quadric_isDefective_general hrn h2r
  all_goals
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
  · exact ah245_isDefective_general
  · exact ah349_isDefective_general
  · exact ah4414_isDefective_general
  · exact ah437_isDefective_general

theorem IsAHException.one_le_d {n d r : ℕ} (h : IsAHException n d r) : 1 ≤ d := by
  rcases h with ⟨rfl, -⟩ | h | h | h | h <;> simp_all

/-- **The Alexander–Hirschowitz exceptions are defective at every configuration of nonzero
points**, not just general ones: the generic defect propagates by semicontinuity. -/
theorem alexanderHirschowitz_exceptions_isDefective {n d r : ℕ} (h : IsAHException n d r)
    (p : Fin r → Fin (n + 1) → 𝕜) (hp : ∀ k, p k ≠ 0) :
    IsDefective (fun k => (veroneseDegParam n d (p k)).tangentSpace) :=
  isDefective_of_forGeneralPoints h.one_le_d (alexanderHirschowitz_exceptions_isDefective_general h)
    p hp

end AlexanderHirschowitz
