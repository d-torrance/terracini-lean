module

public import TerraciniLemma.VeroneseForms

/-!
# Linear changes of coordinates on the Veronese cone

A linear map `L : 𝕜^{n+1} → 𝕜^{n+1}` acts on the ambient space of `v_d(ℙⁿ)` by a linear map
`symPow L` with `symPow L (v_d(p)) = v_d(L p)` (`symPow_veroneseDeg`): each coordinate
`p ↦ v_d(L p)(s)` is a product of linear forms, hence a form of degree `d`. It maps tangent
vectors to tangent vectors, `symPow L (dv_d(p) w) = dv_d(L p)(L w)`
(`symPow_veroneseDegDeriv`).

Consequently a linear map with a left inverse does not lower the dimension of a span of tangent
spaces (`finrank_iSup_tangentSpace_le_comp`), and any `ε < n + 1` points can be moved into the
hyperplane `{x₀ = 0}` without lowering it (`exists_finrank_iSup_tangentSpace_le_of_zero`).
-/

@[expose] public section

noncomputable section VeroneseLinear

open MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] {n d : ℕ}

/-! ### §A — The induced map on the ambient space -/

omit [CharZero 𝕜] in
/-- A linear map of `𝕜^{n+1}` as a continuous linear map. -/
def toCLM (L : (Fin (n + 1) → 𝕜) →ₗ[𝕜] (Fin (n + 1) → 𝕜)) :
    (Fin (n + 1) → 𝕜) →L[𝕜] (Fin (n + 1) → 𝕜) :=
  ContinuousLinearMap.pi fun a => ∑ b, L (Pi.single b 1) a • ContinuousLinearMap.proj b

omit [CharZero 𝕜] in
theorem toCLM_apply (L : (Fin (n + 1) → 𝕜) →ₗ[𝕜] (Fin (n + 1) → 𝕜)) (x : Fin (n + 1) → 𝕜) :
    toCLM L x = L x := by
  classical
  funext a
  rw [LinearMap.pi_apply_eq_sum_univ L x]
  have hs : ∀ k : Fin (n + 1), (fun j : Fin (n + 1) => if k = j then (1 : 𝕜) else 0)
      = Pi.single k 1 := fun k => by
    funext j; simp only [Pi.single_apply]; split_ifs <;> simp_all [eq_comm]
  simp only [hs]
  simp [toCLM, Finset.sum_apply, mul_comm]

omit [CharZero 𝕜] in
/-- Each coordinate of `v_d ∘ L` is a form of degree `d`. -/
theorem veroneseDeg_comp_mem_veroneseForms (L : (Fin (n + 1) → 𝕜) →ₗ[𝕜] (Fin (n + 1) → 𝕜)) :
    ∀ (d : ℕ) (s : Sym (Fin (n + 1)) d),
      (fun p => veroneseDeg n d (L p) s) ∈ veroneseForms (𝕜 := 𝕜) n d
  | 0, s => by
    refine ⟨LinearMap.proj (R := 𝕜) (φ := fun _ : Sym (Fin (n + 1)) 0 => 𝕜) s, ?_⟩
    funext p
    simp [veroneseFormOf_apply, veroneseDeg, veroneseDegPoly, Sym.eq_nil_of_card_zero s]
  | d + 1, s => by
    classical
    obtain ⟨a, ha⟩ := Sym.exists_mem s
    have h1 : (fun p => (L p) a) ∈ veroneseForms (𝕜 := 𝕜) n 1 :=
      linearMap_mem_veroneseForms n ((LinearMap.proj a).comp L)
    have h := mul_mem_veroneseForms (by omega : 1 + d = d + 1) h1
      (veroneseDeg_comp_mem_veroneseForms L d (s.erase a ha))
    convert h using 1
    funext p
    simp only [veroneseDeg, veroneseDegPoly, Pi.mul_apply]
    rw [← Multiset.prod_map_erase (f := X) ha, map_mul, eval_X]
    rfl

omit [CharZero 𝕜] in
/-- The map induced by `L` on the ambient space of `v_d`. -/
def symPow (L : (Fin (n + 1) → 𝕜) →ₗ[𝕜] (Fin (n + 1) → 𝕜)) (d : ℕ) :
    (Sym (Fin (n + 1)) d → 𝕜) →ₗ[𝕜] (Sym (Fin (n + 1)) d → 𝕜) :=
  LinearMap.pi fun s => (veroneseDeg_comp_mem_veroneseForms L d s).choose

omit [CharZero 𝕜] in
theorem symPow_veroneseDeg (L : (Fin (n + 1) → 𝕜) →ₗ[𝕜] (Fin (n + 1) → 𝕜))
    (p : Fin (n + 1) → 𝕜) : symPow L d (veroneseDeg n d p) = veroneseDeg n d (L p) := by
  funext s
  exact congrFun (veroneseDeg_comp_mem_veroneseForms L d s).choose_spec p

omit [CharZero 𝕜] in
/-- `symPow L` as a continuous linear map. -/
def symPowCLM (L : (Fin (n + 1) → 𝕜) →ₗ[𝕜] (Fin (n + 1) → 𝕜)) (d : ℕ) :
    (Sym (Fin (n + 1)) d → 𝕜) →L[𝕜] (Sym (Fin (n + 1)) d → 𝕜) :=
  ∑ s, (ContinuousLinearMap.proj s).smulRight (symPow L d (Pi.single s 1))

omit [CharZero 𝕜] in
theorem symPowCLM_apply (L : (Fin (n + 1) → 𝕜) →ₗ[𝕜] (Fin (n + 1) → 𝕜))
    (f : Sym (Fin (n + 1)) d → 𝕜) : symPowCLM L d f = symPow L d f := by
  classical
  rw [LinearMap.pi_apply_eq_sum_univ (symPow L d) f]
  simp only [symPowCLM, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 2
  funext t
  simp [Pi.single_apply, eq_comm]

omit [CharZero 𝕜] in
/-- `symPow L` maps tangent vectors to tangent vectors. -/
theorem symPow_veroneseDegDeriv (L : (Fin (n + 1) → 𝕜) →ₗ[𝕜] (Fin (n + 1) → 𝕜))
    (p w : Fin (n + 1) → 𝕜) :
    symPow L d (veroneseDegDeriv n d p w) = veroneseDegDeriv n d (L p) (L w) := by
  have h1 := (symPowCLM L d).hasFDerivAt.comp p (hasFDerivAt_veroneseDeg (𝕜 := 𝕜) n d p)
  have h2 := (hasFDerivAt_veroneseDeg (𝕜 := 𝕜) n d (toCLM L p)).comp p (toCLM L).hasFDerivAt
  rw [show ⇑(symPowCLM L d) ∘ veroneseDeg n d = veroneseDeg n d ∘ ⇑(toCLM L) from
    funext fun q => by simp [symPowCLM_apply, symPow_veroneseDeg, toCLM_apply]] at h1
  rw [toCLM_apply] at h2
  have := congrArg (fun F : (Fin (n + 1) → 𝕜) →L[𝕜] _ => F w) (h1.unique h2)
  simpa [symPowCLM_apply, toCLM_apply] using this

/-! ### §B — Spans of tangent spaces -/

omit [CharZero 𝕜] in
/-- A linear map with a left inverse does not lower the dimension of a span of tangent
spaces. -/
theorem finrank_iSup_tangentSpace_le_comp {ι : Type*} [Finite ι]
    {L L' : (Fin (n + 1) → 𝕜) →ₗ[𝕜] (Fin (n + 1) → 𝕜)} (hL : L' ∘ₗ L = LinearMap.id)
    (q : ι → Fin (n + 1) → 𝕜) :
    Module.finrank 𝕜 ((⨆ i, (veroneseDegParam n d (q i)).tangentSpace : Submodule 𝕜 _))
      ≤ Module.finrank 𝕜 ((⨆ i, (veroneseDegParam n d (L (q i))).tangentSpace :
          Submodule 𝕜 _)) := by
  have hLL : ∀ x, L' (L x) = x := fun x => congrArg (fun F => F x) hL
  refine (Submodule.finrank_mono ?_).trans (Submodule.finrank_map_le (symPow L' d) _)
  refine iSup_le fun i => ?_
  rintro _ ⟨w, rfl⟩
  refine ⟨veroneseDegDeriv n d (L (q i)) (L w),
    Submodule.mem_iSup_of_mem i ⟨L w, rfl⟩, ?_⟩
  show symPow L' d (veroneseDegDeriv n d (L (q i)) (L w)) = veroneseDegDeriv n d (q i) w
  rw [symPow_veroneseDegDeriv, hLL, hLL]

omit [CharZero 𝕜] in
/-- **Moving points into a hyperplane.** Any `ε < n + 1` of the points can be moved into
`{x₀ = 0}` by a linear map that does not lower the dimension of the span of the tangent
spaces. -/
theorem exists_linear_zero_of_lt {ε : ℕ} (hε : ε < n + 1) (q : Fin ε → Fin (n + 1) → 𝕜) :
    ∃ L L' : (Fin (n + 1) → 𝕜) →ₗ[𝕜] (Fin (n + 1) → 𝕜),
      L' ∘ₗ L = LinearMap.id ∧ ∀ i, L (q i) 0 = 0 := by
  classical
  -- a nonzero functional `φ` vanishing on the points
  have hlt : Submodule.span 𝕜 (Set.range q) < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => ?_
    have := finrank_range_le_card (R := 𝕜) q
    unfold Set.finrank at this
    rw [h, finrank_top, Module.finrank_fin_fun, Fintype.card_fin] at this
    omega
  obtain ⟨φ, hφ, hφq⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  have hφi : ∀ i, φ (q i) = 0 := fun i => by
    have : φ (q i) ∈ (Submodule.span 𝕜 (Set.range q)).map φ :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨i, rfl⟩)
    rwa [hφq, Submodule.mem_bot] at this
  -- some coordinate vector `e_l` has `φ(e_l) ≠ 0`
  obtain ⟨l, hl⟩ : ∃ l, φ (Pi.single l 1) ≠ 0 := by
    by_contra! h
    exact hφ (LinearMap.pi_ext' fun l => LinearMap.ext_ring (h l))
  -- `L x` puts `φ x` in coordinate `0` and `x₀` in coordinate `l`
  let L : (Fin (n + 1) → 𝕜) →ₗ[𝕜] (Fin (n + 1) → 𝕜) :=
    { toFun := fun x a => if a = 0 then φ x else if a = l then x 0 else x a
      map_add' := fun x y => by
        funext a
        rcases eq_or_ne a 0 with rfl | h0
        · simp
        rcases eq_or_ne a l with rfl | hal <;> simp [*]
      map_smul' := fun c x => by
        funext a
        rcases eq_or_ne a 0 with rfl | h0
        · simp
        rcases eq_or_ne a l with rfl | hal <;> simp [*] }
  have hinj : LinearMap.ker L = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hcoord : ∀ a, a ≠ l → x a = 0 := by
      intro a hal
      by_cases ha0 : a = 0
      · subst ha0
        have := congrFun hx l
        simpa [L, hal.symm, Ne.symm hal] using this
      · have := congrFun hx a
        simpa [L, ha0, hal] using this
    have hx' : x = x l • Pi.single l 1 := by
      funext a
      by_cases hal : a = l
      · subst hal; simp
      · simp [hal, hcoord a hal]
    have h0 : φ x = 0 := by simpa [L] using congrFun hx 0
    rw [hx', map_smul, smul_eq_mul, mul_eq_zero] at h0
    rw [hx', h0.resolve_right hl, zero_smul]
  obtain ⟨L', hL'⟩ := LinearMap.exists_leftInverse_of_injective L hinj
  exact ⟨L, L', hL', fun i => by simp [L, hφi]⟩

end VeroneseLinear
