module

public import TerraciniLemma.CubicLattice
public import TerraciniLemma.DifferentialHorace
public import TerraciniLemma.VeroneseLinear

/-!
# The inductive step of the Alexander–Hirschowitz theorem

Brambilla–Ottaviani, *On the Alexander–Hirschowitz theorem*, Theorem 6.4, in the language of
spans of tangent spaces. The ambient space is `𝕜^{n+2}`, with the hyperplane `H = {x₀ = 0}`
identified with `𝕜^{n+1}` (`extAlong Fin.succ`).

* The **residual map** `resid n d : V_{d+1} → V_d`, `(resid φ)(s) = φ(x₀ · s)`. Its kernel is the
  trace part: the vectors supported on monomials without `x₀`, the image of
  `pushAlong Fin.succ` (`ker_resid`). For a tangent vector,
  `resid (dv_{d+1}(p) v) = v₀ v_d(p) + p₀ dv_d(p) v` (`resid_veroneseDegDeriv`).
* **The Horace step** (`horace_step`). Let `W` be a subspace and move `ε` points `γᵢ ∈ H` off
  `H` along `γᵢ + t e₀`. For general `t`,
  `dim (W + ∑ T_{γᵢ + t e₀}) + dim r(W) ≥ dim (W + span v(γᵢ)) + dim (r(W) + ∑ T^H_{γᵢ})`:
  the trace keeps the points `γᵢ` and the residual gets the tangent spaces `T^H_{γᵢ}` along `H`
  in degree `d`. This is the differential Horace lemma (`differentialHorace`) followed by the
  splitting along `resid`.
* **The step** (`AHHolds.step`): `AH_{n,d+2}(u)`, `AH_{n+1,d+1}(k-u)` and `AH_{n+1,d}(k-u-ε)`
  give `AH_{n+1,d+2}(k)`, for `(n+1)u + ε + N_{d+1} = k(n+2)` with `ε ≤ n`.
-/

@[expose] public section

noncomputable section AHStep

open MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-! ### §A — Euler's identity and the residual map -/

omit [CharZero 𝕜] in
/-- **Euler's identity**: the derivative of `v_d` at `p` in the direction `p` is `d • v_d(p)`. -/
theorem veroneseDegDeriv_self (n d : ℕ) (p : Fin (n + 1) → 𝕜) :
    veroneseDegDeriv n d p p = (d : 𝕜) • veroneseDeg n d p := by
  classical
  funext s
  rw [veroneseDegDeriv_apply]
  have hterm : ∀ k, (s.val.count k : 𝕜) * (Multiset.map p (s.val.erase k)).prod * p k
      = (s.val.count k : 𝕜) * (Multiset.map p s.val).prod := by
    intro k
    by_cases hk : k ∈ s.val
    · rw [mul_assoc, mul_comm _ (p k), Multiset.prod_map_erase hk]
    · rw [Multiset.count_eq_zero.mpr hk, Nat.cast_zero, zero_mul, zero_mul, zero_mul]
  have hcount : ∑ k, (s.val.count k : 𝕜) = d := by
    rw [← Nat.cast_sum, Multiset.sum_count_eq_card (fun a _ => Finset.mem_univ a)]
    simp
  simp only [hterm, ← Finset.sum_mul, hcount, Pi.smul_apply, smul_eq_mul, veroneseDeg,
    veroneseDegPoly, map_multiset_prod, Multiset.map_map, Function.comp_def, eval_X]

/-- The point `v_d(p)` lies in the tangent space at `p` (for `d ≠ 0`, in characteristic zero). -/
theorem veroneseDeg_mem_tangentSpace {n d : ℕ} (hd : d ≠ 0) (p : Fin (n + 1) → 𝕜) :
    veroneseDeg n d p ∈ (veroneseDegParam n d p).tangentSpace := by
  refine ⟨(d : 𝕜)⁻¹ • p, ?_⟩
  show veroneseDegDeriv n d p ((d : 𝕜)⁻¹ • p) = _
  rw [map_smul, veroneseDegDeriv_self, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hd), one_smul]


section Residual

variable (n d : ℕ)

/-- The residual map `V_{d+1} → V_d`: `(resid φ)(s) = φ(x₀ · s)`. -/
def resid : (Sym (Fin (n + 2)) (d + 1) → 𝕜) →ₗ[𝕜] (Sym (Fin (n + 2)) d → 𝕜) :=
  LinearMap.funLeft 𝕜 𝕜 (Sym.cons 0)

omit [CharZero 𝕜] in
/-- The residual of a tangent vector: `∂_v(x₀ G)(p) = v₀ G(p) + p₀ ∂_v G(p)`. -/
theorem resid_veroneseDegDeriv (p v : Fin (n + 2) → 𝕜) :
    resid n d (veroneseDegDeriv (n + 1) (d + 1) p v)
      = v 0 • veroneseDeg (n + 1) d p + p 0 • veroneseDegDeriv (n + 1) d p v := by
  classical
  funext s
  have hpoly : veroneseDegPoly (𝕜 := 𝕜) (n + 1) (d + 1) (0 ::ₛ s)
      = X 0 * veroneseDegPoly (n + 1) d s := by
    simp [veroneseDegPoly, Sym.coe_cons]
  simp only [resid, LinearMap.funLeft_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    veroneseDegDeriv, ContinuousLinearMap.pi_apply, mvPolynomialDeriv, hpoly,
    FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, coordProj_apply, veroneseDeg,
    pderiv_mul, pderiv_X, map_add, map_mul, eval_X, Finset.mul_sum]
  simp only [add_mul, Finset.sum_add_distrib, Pi.single_apply, apply_ite (eval p), map_one,
    map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, mul_assoc]
  ring

omit [CharZero 𝕜] in
/-- The residual of a point of the cone: `x₀ G` at `p` is `p₀ G(p)`. -/
theorem resid_veroneseDeg (p : Fin (n + 2) → 𝕜) :
    resid n d (veroneseDeg (n + 1) (d + 1) p) = p 0 • veroneseDeg (n + 1) d p := by
  funext s
  simp [resid, veroneseDeg, veroneseDegPoly, Sym.coe_cons]

omit [CharZero 𝕜] in
/-- The kernel of the residual map is the trace part: the vectors supported on monomials
without `x₀`. -/
theorem ker_resid :
    LinearMap.ker (resid (𝕜 := 𝕜) n d)
      = LinearMap.range (pushAlong (𝕜 := 𝕜) (d := d + 1) (Fin.succ : Fin (n + 1) → _)).toLinearMap := by
  classical
  -- a monomial misses `x₀` iff it comes from `H`
  have hrange : ∀ t : Sym (Fin (n + 2)) (d + 1), t ∉ Set.range (Sym.map Fin.succ) → 0 ∈ t := by
    intro t ht
    by_contra h0
    exact ht (sym_mem_range_map fun a ha => Fin.exists_succ_eq.mpr (ne_of_mem_of_not_mem ha h0))
  have hcons : ∀ s : Sym (Fin (n + 2)) d, 0 ::ₛ s ∉ Set.range (Sym.map (Fin.succ (n := n + 1))) := by
    rintro s ⟨s', hs'⟩
    obtain ⟨a, -, ha⟩ := Sym.mem_map.mp (hs' ▸ Sym.mem_cons_self 0 s)
    exact Fin.succ_ne_zero a ha
  ext φ
  simp only [LinearMap.mem_ker, LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  constructor
  · intro hφ
    refine ⟨fun s' => φ (Sym.map Fin.succ s'), funext fun t => ?_⟩
    by_cases ht : t ∈ Set.range (Sym.map (Fin.succ (n := n + 1)))
    · obtain ⟨s', rfl⟩ := ht
      exact pushAlong_map (Fin.succ_injective _) _ s'
    · rw [pushAlong_of_not_mem _ ht, ← Sym.cons_erase (hrange t ht)]
      exact (congrFun hφ _).symm
  · rintro ⟨f, rfl⟩
    funext s
    exact pushAlong_of_not_mem f (hcons s)

end Residual

/-! ### §B — Counting dimensions along a split -/

section Split

variable {K V V' C : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [AddCommGroup C] [Module K C]
  [FiniteDimensional K C]

omit [FiniteDimensional K V'] in
/-- If `T ≤ S` lies in the kernel of `f`, then `dim f(S) + dim T ≤ dim S`. -/
theorem finrank_map_add_le_of_le_ker (f : V →ₗ[K] V') {S T : Submodule K V} (hTS : T ≤ S)
    (hT : T ≤ LinearMap.ker f) :
    Module.finrank K (S.map f) + Module.finrank K T ≤ Module.finrank K S := by
  have h := LinearMap.finrank_range_add_finrank_ker (f.domRestrict S)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h
  have hle : Module.finrank K T ≤ Module.finrank K ((LinearMap.ker f).comap S.subtype) := by
    rw [← (Submodule.comapSubtypeEquivOfLe hTS).finrank_eq]
    exact Submodule.finrank_mono (Submodule.comap_mono hT)
  omega

omit [FiniteDimensional K V] in
/-- Modulo `N`, a subspace `R` spans `dim (N + R) - dim N` dimensions. -/
theorem finrank_sup_le_add_map_mkQ (N R : Submodule K V') :
    Module.finrank K (N ⊔ R : Submodule K V')
      ≤ Module.finrank K N + Module.finrank K (R.map N.mkQ) := by
  have h := LinearMap.finrank_range_add_finrank_ker (N.mkQ.domRestrict (N ⊔ R))
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ,
    Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq] at h
  have hle : Module.finrank K (N.comap (N ⊔ R).subtype) ≤ Module.finrank K N := by
    rw [(Submodule.comapSubtypeEquivOfLe le_sup_left).finrank_eq]
  omega

omit [FiniteDimensional K V] [FiniteDimensional K V'] in
/-- The image of a linear map exceeds the image of a subspace `A` by at most `codim A`. -/
theorem finrank_range_le_map_add (g : C →ₗ[K] V') (A : Submodule K C) :
    Module.finrank K (LinearMap.range g)
      ≤ Module.finrank K (A.map g) + (Module.finrank K C - Module.finrank K A) := by
  obtain ⟨B, hB⟩ := Submodule.exists_isCompl A
  have hAB := Submodule.finrank_add_eq_of_isCompl hB
  have h1 : LinearMap.range g = A.map g ⊔ B.map g := by
    rw [← Submodule.map_sup, hB.sup_eq_top, Submodule.map_top]
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (A.map g) (B.map g)
  have h3 := Submodule.finrank_map_le g B
  rw [h1]
  omega

/-- **Counting along a split.** Let `r : V → V'` and let `ψ, ψ' : C → V, V'` be linear maps with
`r ∘ ψ = 0`. Suppose `W` and the image of `ψ` lie in `Y`, and every `c` with `ψ c ∈ W` lifts:
some `y ∈ Y` has `r y ≡ ψ' c` modulo `r(W)`. Then
`dim W + dim (r(W) + range ψ') ≤ dim Y + dim r(W)`. -/
theorem finrank_add_le_of_lift (r : V →ₗ[K] V') (ψ : C →ₗ[K] V) (ψ' : C →ₗ[K] V')
    {W Y : Submodule K V} (hWY : W ≤ Y) (hψY : LinearMap.range ψ ≤ Y)
    (hψr : ∀ c, r (ψ c) = 0) (hlift : ∀ c, ψ c ∈ W → ∃ y ∈ Y, r y - ψ' c ∈ W.map r) :
    Module.finrank K W + Module.finrank K (W.map r ⊔ LinearMap.range ψ' : Submodule K V')
      ≤ Module.finrank K Y + Module.finrank K (W.map r) := by
  set N := W.map r
  set ρ := N.mkQ ∘ₗ r
  set ρ' := N.mkQ ∘ₗ ψ'
  set A := W.comap ψ
  -- `Y` splits along `ρ`, and its kernel part contains `W + range ψ`
  have h1' := finrank_map_add_le_of_le_ker ρ (S := Y) (T := W ⊔ LinearMap.range ψ)
    (sup_le hWY hψY) (sup_le (fun w hw => by simp [ρ, N, Submodule.mem_map_of_mem hw])
      (by rintro _ ⟨c, rfl⟩; simp [ρ, hψr]))
  -- `W + range ψ` exceeds `W` by `codim A`
  have h2 : Module.finrank K W + (Module.finrank K C - Module.finrank K A)
      ≤ Module.finrank K (W ⊔ LinearMap.range ψ : Submodule K V) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (W.mkQ ∘ₗ ψ)
    have hker : LinearMap.ker (W.mkQ ∘ₗ ψ) = A := by
      ext c; simp [A, Submodule.Quotient.mk_eq_zero]
    have hmap := finrank_map_add_le_of_le_ker W.mkQ (S := W ⊔ LinearMap.range ψ) le_sup_left
      (by rw [Submodule.ker_mkQ])
    have hrange : LinearMap.range (W.mkQ ∘ₗ ψ) ≤ (W ⊔ LinearMap.range ψ).map W.mkQ := by
      rintro _ ⟨c, rfl⟩
      exact ⟨ψ c, Submodule.mem_sup_right ⟨c, rfl⟩, rfl⟩
    have := Submodule.finrank_mono hrange
    rw [hker] at hrn
    omega
  -- the lifts put `ρ'(A)` inside `ρ(Y)`
  have h3 : A.map ρ' ≤ Y.map ρ := by
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨y, hy, hyc⟩ := hlift c hc
    refine ⟨y, hy, ?_⟩
    simp only [ρ, ρ', LinearMap.comp_apply]
    rw [← sub_eq_zero, ← LinearMap.map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hyc
  have h4 := finrank_range_le_map_add ρ' A
  have h5 := finrank_sup_le_add_map_mkQ N (LinearMap.range ψ')
  have h6 : (LinearMap.range ψ').map N.mkQ = LinearMap.range ρ' := by
    rw [LinearMap.range_comp]
  have h7 := Submodule.finrank_mono h3
  have h8 := Submodule.finrank_le A
  rw [h6] at h5
  omega

end Split

/-! ### §C — Tangent vectors along a moving point -/

section Moving

variable {n d : ℕ}

omit [CharZero 𝕜] in
/-- A tangent vector is linear in the direction: `dv(p) v = ∑ⱼ vⱼ dv(p) eⱼ`. -/
theorem veroneseDegDeriv_eq_sum (p v : Fin (n + 1) → 𝕜) :
    veroneseDegDeriv n d p v = ∑ j, v j • veroneseDegDeriv n d p (Pi.single j 1) := by
  conv_lhs => rw [show v = ∑ j, v j • (Pi.single j 1 : Fin (n + 1) → 𝕜) by
    ext k; simp [Pi.single_apply]]
  simp [map_sum, map_smul]

omit [CharZero 𝕜] in
/-- The span of the tangent spaces at points `q i` is spanned by the coordinate derivatives. -/
theorem iSup_tangentSpace_eq_span {ι : Type*} (q : ι → Fin (n + 1) → 𝕜) :
    (⨆ i, (veroneseDegParam n d (q i)).tangentSpace : Submodule 𝕜 _)
      = Submodule.span 𝕜 (Set.range fun ij : ι × Fin (n + 1) =>
          veroneseDegDeriv n d (q ij.1) (Pi.single ij.2 1)) := by
  simp_rw [tangentSpace_eq_span, Submodule.span_range_eq_iSup]
  exact (iSup_prod (f := fun ij : ι × Fin (n + 1) => Submodule.span 𝕜
    {veroneseDegDeriv n d (q ij.1) (Pi.single ij.2 1)})).symm

/-- The coordinates of the moving point `Γ + t e₀`, as polynomials in `t`. -/
def movePoly (Γ : Fin (n + 2) → 𝕜) (l : Fin (n + 2)) : Polynomial 𝕜 :=
  Polynomial.C (Γ l) + if l = 0 then Polynomial.X else 0

/-- The tangent vector at `Γ + t e₀` in the direction `eⱼ`, at the monomial `s`, as a polynomial
in `t`. -/
def tanPoly (Γ : Fin (n + 2) → 𝕜) (j : Fin (n + 2)) (s : Sym (Fin (n + 2)) (d + 1)) :
    Polynomial 𝕜 :=
  aeval (movePoly Γ) (pderiv j (veroneseDegPoly (𝕜 := 𝕜) (n + 1) (d + 1) s))

omit [CharZero 𝕜] in
theorem eval_aeval_movePoly (Γ : Fin (n + 2) → 𝕜) (t : 𝕜) (q : MvPolynomial (Fin (n + 2)) 𝕜) :
    (aeval (movePoly Γ) q).eval t = eval (Γ + t • (Pi.single 0 1 : Fin (n + 2) → 𝕜)) q := by
  rw [← Polynomial.coe_aeval_eq_eval, ← AlgHom.comp_apply, comp_aeval, aeval_eq_eval]
  congr 2
  funext l
  by_cases hl : l = 0
  · subst hl; simp [movePoly]
  · simp [movePoly, hl]

omit [CharZero 𝕜] in
theorem eval_tanPoly (Γ : Fin (n + 2) → 𝕜) (j : Fin (n + 2)) (s : Sym (Fin (n + 2)) (d + 1))
    (t : 𝕜) : (tanPoly Γ j s).eval t
      = veroneseDegDeriv (n + 1) (d + 1) (Γ + t • (Pi.single 0 1 : Fin (n + 2) → 𝕜))
          (Pi.single j 1) s := by
  rw [tanPoly, eval_aeval_movePoly, veroneseDegDeriv_single]

omit [CharZero 𝕜] in
/-- At `t = 0`: the tangent vector at `Γ`. -/
theorem coeff_zero_tanPoly (Γ : Fin (n + 2) → 𝕜) (j : Fin (n + 2)) (s : Sym (Fin (n + 2)) (d + 1)) :
    (tanPoly Γ j s).coeff 0 = veroneseDegDeriv (n + 1) (d + 1) Γ (Pi.single j 1) s := by
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_tanPoly, zero_smul, add_zero]

omit [CharZero 𝕜] in
/-- The first-order term, at the monomial `x₀ s`, for `Γ ∈ H` and `j ≠ 0`: the tangent vector
at `Γ` in degree `d`. -/
theorem coeff_one_tanPoly {Γ : Fin (n + 2) → 𝕜} (hΓ : Γ 0 = 0) {j : Fin (n + 2)} (hj : j ≠ 0)
    (s : Sym (Fin (n + 2)) d) :
    (tanPoly Γ j (0 ::ₛ s)).coeff 1 = veroneseDegDeriv (n + 1) d Γ (Pi.single j 1) s := by
  have hpoly : veroneseDegPoly (𝕜 := 𝕜) (n + 1) (d + 1) (0 ::ₛ s)
      = X 0 * veroneseDegPoly (n + 1) d s := by
    simp [veroneseDegPoly, Sym.coe_cons]
  have hX : pderiv j (X 0 : MvPolynomial (Fin (n + 2)) 𝕜) = 0 := by
    rw [pderiv_X, Pi.single_eq_of_ne (Ne.symm hj)]
  rw [tanPoly, hpoly, pderiv_mul, hX, zero_mul, zero_add, map_mul, aeval_X, movePoly, hΓ,
    map_zero, zero_add, ite_eq_left rfl, Polynomial.coeff_X_mul, Polynomial.coeff_zero_eq_eval_zero,
    eval_aeval_movePoly, zero_smul, add_zero, veroneseDegDeriv_single]

omit [CharZero 𝕜] in
/-- A polynomial path, by its coefficients. -/
theorem polyPath_coeff {κ : Type*} (P : κ → Polynomial 𝕜) {m : ℕ}
    (hm : ∀ x, (P x).natDegree < m + 1) (t : 𝕜) :
    polyPath m (fun k x => (P x).coeff k) t = fun x => (P x).eval t := by
  funext x
  simp only [polyPath, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Polynomial.eval_eq_sum_range' (hm x)]
  simp [mul_comm]

end Moving

/-! ### §C — The Horace step -/

/-- **The Horace step.** Let `W` be a subspace of `V_{d+1}` and let `γᵢ` be points of `H`.
Moving them off `H` along `γᵢ + t e₀`, for general `t` the span of `W` and the tangent spaces at
the moved points has dimension at least
`dim (W + span v(γᵢ)) - dim r(W) + dim (r(W) + ∑ T^H_{γᵢ})`. -/
theorem horace_step {n d ε : ℕ} (W : Submodule 𝕜 (Sym (Fin (n + 2)) (d + 1) → 𝕜))
    (γ : Fin ε → Fin (n + 1) → 𝕜) :
    HoldsGenerically (𝕜 := 𝕜) Unit fun t =>
      Module.finrank 𝕜 ((W ⊔ Submodule.span 𝕜 (Set.range fun i =>
          veroneseDeg (n + 1) (d + 1) (extAlong Fin.succ (γ i))) : Submodule 𝕜 _))
        + Module.finrank 𝕜 ((W.map (resid n d) ⊔ ⨆ i,
          (veroneseDegParam n d (γ i)).tangentSpace.map (pushAlong Fin.succ).toLinearMap :
            Submodule 𝕜 _))
      ≤ Module.finrank 𝕜 ((W ⊔ ⨆ i, (veroneseDegParam (n + 1) (d + 1)
          (extAlong Fin.succ (γ i) + t () • (Pi.single 0 1 : Fin (n + 2) → 𝕜))).tangentSpace : Submodule 𝕜 _))
        + Module.finrank 𝕜 (W.map (resid n d)) := by
  classical
  set Γ : Fin ε → Fin (n + 2) → 𝕜 := fun i => extAlong Fin.succ (γ i) with hΓdef
  have hext0 : ∀ y : Fin (n + 1) → 𝕜, extAlong (𝕜 := 𝕜) Fin.succ y 0 = 0 := fun y =>
    extAlong_of_not_mem y (by rintro ⟨a, ha⟩; exact Fin.succ_ne_zero a ha)
  have hΓ0 : ∀ i, Γ i 0 = 0 := fun i => hext0 _
  have hd0 : ((d + 1 : ℕ) : 𝕜) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero d
  -- the paths `t ↦ dv(Γᵢ + t e₀) eⱼ`, by their coefficients
  let P : Fin ε × Fin (n + 2) → Sym (Fin (n + 2)) (d + 1) → Polynomial 𝕜 :=
    fun ij s => tanPoly (Γ ij.1) ij.2 s
  let m := max 1 (Finset.univ.sup fun x : (Fin ε × Fin (n + 2)) × Sym (Fin (n + 2)) (d + 1) =>
    (P x.1 x.2).natDegree)
  have hdeg : ∀ ij s, (P ij s).natDegree < m + 1 := fun ij s => Nat.lt_succ_of_le
    ((Finset.le_sup (f := fun x : (Fin ε × Fin (n + 2)) × Sym (Fin (n + 2)) (d + 1) =>
      (P x.1 x.2).natDegree) (Finset.mem_univ (ij, s))).trans (le_max_right _ _))
  let β : Fin ε × Fin (n + 2) → ℕ → Sym (Fin (n + 2)) (d + 1) → 𝕜 :=
    fun ij k s => (P ij s).coeff k
  have hpath : ∀ ij t, polyPath m (β ij) t = veroneseDegDeriv (n + 1) (d + 1)
      (Γ ij.1 + t • (Pi.single 0 1 : Fin (n + 2) → 𝕜)) (Pi.single ij.2 1) := by
    intro ij t
    rw [show β ij = fun k s => (P ij s).coeff k from rfl, polyPath_coeff _ (hdeg ij)]
    funext s
    exact eval_tanPoly _ _ _ _
  have hβ0 : ∀ ij, β ij 0 = veroneseDegDeriv (n + 1) (d + 1) (Γ ij.1) (Pi.single ij.2 1) :=
    fun ij => funext fun s => coeff_zero_tanPoly _ _ _
  have hβ1 : ∀ i j, j ≠ 0 →
      resid n d (β (i, j) 1) = veroneseDegDeriv (n + 1) d (Γ i) (Pi.single j 1) :=
    fun i j hj => funext fun s => coeff_one_tanPoly (hΓ0 i) hj s
  -- Lemma D: the limit `Z = W + X₀ + D` bounds the span at general `t`
  set Z := W ⊔ Submodule.span 𝕜 (Set.range fun ij => β ij 0) ⊔ horaceD W β with hZdef
  have hZ := differentialHorace W β (m := m) (by omega)
  -- every tangent vector at `Γᵢ` lies in `Z`
  have hTZ : ∀ i v, veroneseDegDeriv (n + 1) (d + 1) (Γ i) v ∈ Z := by
    intro i v
    rw [veroneseDegDeriv_eq_sum]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    rw [← hβ0 (i, j)]
    exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨(i, j), rfl⟩))
  -- the directions along `H`
  let ψ : (Fin ε → Fin (n + 1) → 𝕜) →ₗ[𝕜] (Sym (Fin (n + 2)) (d + 1) → 𝕜) :=
    { toFun := fun c => ∑ i, veroneseDegDeriv (n + 1) (d + 1) (Γ i) (extAlong Fin.succ (c i))
      map_add' := fun c c' => by simp [Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum] }
  let ψ' : (Fin ε → Fin (n + 1) → 𝕜) →ₗ[𝕜] (Sym (Fin (n + 2)) d → 𝕜) :=
    { toFun := fun c => ∑ i, veroneseDegDeriv (n + 1) d (Γ i) (extAlong Fin.succ (c i))
      map_add' := fun c c' => by simp [Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum] }
  set E := Submodule.span 𝕜 (Set.range fun i => veroneseDeg (n + 1) (d + 1) (Γ i)) with hEdef
  -- Euler: `v(Γᵢ) = (d+1)⁻¹ dv(Γᵢ) Γᵢ`
  have heuler : ∀ i, veroneseDeg (n + 1) (d + 1) (Γ i)
      = ((d + 1 : ℕ) : 𝕜)⁻¹ • veroneseDegDeriv (n + 1) (d + 1) (Γ i) (Γ i) := by
    intro i
    rw [veroneseDegDeriv_self, smul_smul, inv_mul_cancel₀ hd0, one_smul]
  have key := finrank_add_le_of_lift (resid n d) ψ ψ' (W := W ⊔ E) (Y := Z)
    (sup_le (le_sup_left.trans le_sup_left) (by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show veroneseDeg (n + 1) (d + 1) (Γ i) ∈ Z
      rw [heuler]
      exact Submodule.smul_mem _ _ (hTZ i _)))
    (by
      rintro _ ⟨c, rfl⟩
      show ∑ i, veroneseDegDeriv (n + 1) (d + 1) (Γ i) (extAlong Fin.succ (c i)) ∈ Z
      exact Submodule.sum_mem _ fun i _ => hTZ i _)
    (fun c => by
      simp only [ψ, LinearMap.coe_mk, AddHom.coe_mk, map_sum, resid_veroneseDegDeriv, hext0,
        hΓ0, zero_smul, add_zero, Finset.sum_const_zero])
    (by
      intro c hc
      obtain ⟨w, hw, e, he, hwe⟩ := Submodule.mem_sup.mp hc
      obtain ⟨lam, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp he
      -- the Euler part of `c`, and the relation part
      set ce : Fin ε → Fin (n + 1) → 𝕜 := fun i => (lam i * ((d + 1 : ℕ) : 𝕜)⁻¹) • γ i
      have hce : ψ ce = ∑ i, lam i • veroneseDeg (n + 1) (d + 1) (Γ i) := by
        simp only [ψ, ce, LinearMap.coe_mk, AddHom.coe_mk, map_smul, heuler, smul_smul]
        rfl
      set c' := c - ce
      have hc' : ψ c' ∈ W := by
        rw [map_sub, hce, ← hwe, add_sub_cancel_right]
        exact hw
      -- the relation, in Lemma D's coordinates
      let ĉ : Fin ε × Fin (n + 2) → 𝕜 := fun ij => extAlong Fin.succ (c' ij.1) ij.2
      have hL0 : Fintype.linearCombination 𝕜 (fun ij => β ij 0) ĉ = ψ c' := by
        simp only [Fintype.linearCombination_apply, Fintype.sum_prod_type, hβ0, ψ,
          LinearMap.coe_mk, AddHom.coe_mk]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [veroneseDegDeriv_eq_sum]
      have hD : Fintype.linearCombination 𝕜 (fun ij => β ij 1) ĉ ∈ Z :=
        Submodule.mem_sup_right ⟨ĉ, by simpa [hL0] using hc', rfl⟩
      have hrD : resid n d (Fintype.linearCombination 𝕜 (fun ij => β ij 1) ĉ) = ψ' c' := by
        simp only [Fintype.linearCombination_apply, Fintype.sum_prod_type, map_sum, map_smul, ψ',
          LinearMap.coe_mk, AddHom.coe_mk]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [veroneseDegDeriv_eq_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j = 0
        · subst hj; simp [ĉ, hext0]
        · rw [hβ1 i j hj]
      -- the Euler part lifts through the points `dv(Γᵢ) e₀ ∈ X₀`
      set ye := ∑ i, (lam i * ((d + 1 : ℕ) : 𝕜)⁻¹ * (d : 𝕜)) •
        veroneseDegDeriv (n + 1) (d + 1) (Γ i) (Pi.single 0 1)
      have hye : ye ∈ Z := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hTZ i _)
      have hrye : resid n d ye = ψ' ce := by
        simp only [ye, ψ', ce, map_sum, map_smul, resid_veroneseDegDeriv, hΓ0, LinearMap.coe_mk,
          AddHom.coe_mk, Pi.single_eq_same, one_smul, zero_smul, add_zero]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show extAlong Fin.succ (γ i) = Γ i from rfl, veroneseDegDeriv_self, smul_smul]
      refine ⟨Fintype.linearCombination 𝕜 (fun ij => β ij 1) ĉ + ye, Z.add_mem hD hye, ?_⟩
      rw [map_add, hrD, hrye, ← map_add, sub_add_cancel, sub_self]
      exact Submodule.zero_mem _)
  -- `r(E) = 0`, and the residual directions are the tangent spaces along `H`
  have hmapE : (W ⊔ E).map (resid n d) = W.map (resid n d) := by
    rw [Submodule.map_sup, hEdef, Submodule.map_span, ← Set.range_comp]
    simp only [Function.comp_def, resid_veroneseDeg, hΓ0, zero_smul]
    rw [sup_eq_left, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.zero_mem _
  have hrange : LinearMap.range ψ' = ⨆ i,
      (veroneseDegParam n d (γ i)).tangentSpace.map (pushAlong Fin.succ).toLinearMap := by
    have hcomp : ∀ i v, veroneseDegDeriv (n + 1) d (Γ i) (extAlong Fin.succ v)
        = pushAlong Fin.succ (veroneseDegDeriv n d (γ i) v) := fun i v =>
      congrArg (fun L : (Fin (n + 1) → 𝕜) →L[𝕜] _ => L v)
        (veroneseDegDeriv_extAlong (d := d) (Fin.succ_injective _) (γ i))
    apply le_antisymm
    · rintro _ ⟨c, rfl⟩
      show ∑ i, veroneseDegDeriv (n + 1) d (Γ i) (extAlong Fin.succ (c i)) ∈ _
      refine Submodule.sum_mem _ fun i _ => Submodule.mem_iSup_of_mem i ?_
      rw [hcomp]
      exact ⟨_, ⟨c i, rfl⟩, rfl⟩
    · refine iSup_le fun i => ?_
      rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
      refine ⟨(Pi.single i v : Fin ε → Fin (n + 1) → 𝕜), ?_⟩
      show ∑ j, veroneseDegDeriv (n + 1) d (Γ j)
        (extAlong Fin.succ ((Pi.single i v : Fin ε → Fin (n + 1) → 𝕜) j)) = _
      rw [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, map_zero, map_zero])
        (by simp), Pi.single_eq_same, hcomp]
      rfl
  refine hZ.mono fun t ht => ?_
  change Module.finrank 𝕜 Z ≤ _ at ht
  rw [hmapE, hrange] at key
  have hspan : (W ⊔ ⨆ i, (veroneseDegParam (n + 1) (d + 1)
      (Γ i + t () • (Pi.single 0 1 : Fin (n + 2) → 𝕜))).tangentSpace : Submodule 𝕜 _)
      = W ⊔ Submodule.span 𝕜 (Set.range fun ij => polyPath m (β ij) (t ())) := by
    rw [iSup_tangentSpace_eq_span]
    simp_rw [hpath]
  rw [hspan]
  omega

/-! ### §E — Tools for the step -/

section Tools

omit [CharZero 𝕜] in
/-- **Semicontinuity for polynomial families of vectors.** If vectors whose coordinates are
polynomials in parameters span `≥ m` dimensions at one parameter value, they do at general
values. -/
theorem holdsGenerically_le_finrank_span_eval {σ ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ι → κ → MvPolynomial σ 𝕜) {m : ℕ} (x₀ : σ → 𝕜)
    (h : m ≤ Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range fun i s => eval x₀ (F i s)))) :
    HoldsGenerically σ fun x =>
      m ≤ Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range fun i s => eval x (F i s))) := by
  let M : Matrix κ ι (MvPolynomial σ 𝕜) := Matrix.of fun s i => F i s
  have key : ∀ x : σ → 𝕜, (M.map (eval x)).rank
      = Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range fun i s => eval x (F i s))) := by
    intro x
    rw [Matrix.rank_eq_finrank_span_cols]
    rfl
  exact (HoldsGenerically.le_rank (k := m) M x₀ (by rw [key]; exact h)).mono fun x hx => by
    rwa [key] at hx

omit [CharZero 𝕜] in
/-- **General points fill.** Adding `ε` suitable vectors from a family `v` to a subspace `A`
gains `ε` dimensions, up to the dimension of `A + span v`. -/
theorem exists_finrank_sup_span_ge {V Y : Type*} [AddCommGroup V] [Module 𝕜 V]
    [FiniteDimensional 𝕜 V] [Nonempty Y] (A : Submodule 𝕜 V) (v : Y → V) :
    ∀ ε : ℕ, ∃ y : Fin ε → Y,
      min (Module.finrank 𝕜 A + ε) (Module.finrank 𝕜 (A ⊔ Submodule.span 𝕜 (Set.range v) :
          Submodule 𝕜 V))
        ≤ Module.finrank 𝕜 (A ⊔ Submodule.span 𝕜 (Set.range (v ∘ y)) : Submodule 𝕜 V)
  | 0 => ⟨Fin.elim0, by
      rw [show Set.range (v ∘ (Fin.elim0 : Fin 0 → Y)) = ∅ from Set.range_eq_empty _,
        Submodule.span_empty, sup_bot_eq]
      exact min_le_left _ _⟩
  | ε + 1 => by
    classical
    obtain ⟨y, hy⟩ := exists_finrank_sup_span_ge A v ε
    set S := A ⊔ Submodule.span 𝕜 (Set.range (v ∘ y))
    have hgrow : ∀ z, S ≤ A ⊔ Submodule.span 𝕜 (Set.range (v ∘ Fin.snoc y z)) := fun z =>
      sup_le_sup_left (Submodule.span_mono (by
        rintro _ ⟨i, rfl⟩
        exact ⟨Fin.castSucc i, by simp⟩)) _
    by_cases hfull : A ⊔ Submodule.span 𝕜 (Set.range v) ≤ S
    · refine ⟨Fin.snoc y (Classical.arbitrary Y), ?_⟩
      exact (min_le_right _ _).trans ((Submodule.finrank_mono hfull).trans
        (Submodule.finrank_mono (hgrow _)))
    · obtain ⟨z, hz⟩ : ∃ z, v z ∉ S := by
        by_contra! h
        exact hfull (sup_le le_sup_left (Submodule.span_le.mpr (by rintro _ ⟨z, rfl⟩; exact h z)))
      refine ⟨Fin.snoc y z, ?_⟩
      have hlt : S < A ⊔ Submodule.span 𝕜 (Set.range (v ∘ Fin.snoc y z)) :=
        lt_of_le_of_ne (hgrow z) fun h => hz (h ▸ Submodule.mem_sup_right
          (Submodule.subset_span ⟨Fin.last ε, by simp⟩))
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega

/-- The Veronese cone spans its ambient space. -/
theorem span_range_veroneseDeg (n e : ℕ) :
    Submodule.span 𝕜 (Set.range (veroneseDeg (𝕜 := 𝕜) n e)) = ⊤ := by
  by_contra h
  obtain ⟨χ, hχ, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr h)
    inferInstance
  obtain ⟨x, hx⟩ := exists_apply_veroneseDeg_ne_zero (𝕜 := 𝕜) hχ
  have : χ (veroneseDeg n e x) ∈ (Submodule.span 𝕜 (Set.range (veroneseDeg n e))).map χ :=
    Submodule.mem_map_of_mem (Submodule.subset_span ⟨x, rfl⟩)
  rw [hmap, Submodule.mem_bot] at this
  exact hx this

/-- Off `H`, the residual of a tangent space contains the tangent space one degree lower. -/
theorem tangentSpace_le_map_resid {n e : ℕ} (he : e ≠ 0) {σ : Fin (n + 2) → 𝕜} (hσ : σ 0 ≠ 0) :
    (veroneseDegParam (n + 1) e σ).tangentSpace
      ≤ (veroneseDegParam (n + 1) (e + 1) σ).tangentSpace.map (resid n e) := by
  rintro _ ⟨w, rfl⟩
  have he' : (e : 𝕜) ≠ 0 := by exact_mod_cast he
  have he1 : ((e : 𝕜) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero e
  set β := w 0 / (σ 0 * ((e : 𝕜) + 1))
  set w' := (σ 0)⁻¹ • (w - β • σ)
  refine ⟨veroneseDegDeriv (n + 1) (e + 1) σ w', ⟨w', rfl⟩, ?_⟩
  show resid n e (veroneseDegDeriv (n + 1) (e + 1) σ w') = veroneseDegDeriv (n + 1) e σ w
  rw [resid_veroneseDegDeriv]
  have heuler : veroneseDeg (n + 1) e σ = (e : 𝕜)⁻¹ • veroneseDegDeriv (n + 1) e σ σ := by
    rw [veroneseDegDeriv_self, smul_smul, inv_mul_cancel₀ he', one_smul]
  rw [heuler, smul_smul, ← map_smul, ← map_smul, ← map_add]
  congr 1
  funext l
  simp only [w', β, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

omit [CharZero 𝕜] in
theorem extAlong_succ_eq_cons {n : ℕ} (y : Fin (n + 1) → 𝕜) :
    extAlong (𝕜 := 𝕜) Fin.succ y = Fin.cons 0 y := by
  funext a
  refine Fin.cases ?_ (fun a => ?_) a
  · exact extAlong_of_not_mem y (by rintro ⟨b, hb⟩; exact Fin.succ_ne_zero b hb)
  · exact extAlong_apply (Fin.succ_injective _) y a

omit [CharZero 𝕜] in
theorem cons_zero_single {n : ℕ} (j : Fin (n + 1)) :
    (Fin.cons 0 (Pi.single j 1 : Fin (n + 1) → 𝕜) : Fin (n + 2) → 𝕜) = Pi.single j.succ 1 := by
  funext a
  refine Fin.cases ?_ (fun a => ?_) a
  · simp [(Fin.succ_ne_zero j).symm]
  · simp [Pi.single_apply]

omit [CharZero 𝕜] in
/-- The tangent vectors at a point of `H`, along `H`, come from `ℙⁿ`. -/
theorem veroneseDegDeriv_cons_succ {n e : ℕ} (y : Fin (n + 1) → 𝕜) (j : Fin (n + 1)) :
    veroneseDegDeriv (n + 1) e (Fin.cons 0 y) (Pi.single j.succ 1)
      = pushAlong Fin.succ (veroneseDegDeriv n e y (Pi.single j 1)) := by
  have := congrArg (fun L : (Fin (n + 1) → 𝕜) →L[𝕜] _ => L (Pi.single j 1))
    (veroneseDegDeriv_extAlong (d := e) (Fin.succ_injective _) y)
  simpa [extAlong_succ_eq_cons, cons_zero_single] using this

omit [CharZero 𝕜] in
theorem veroneseDeg_cons {n e : ℕ} (y : Fin (n + 1) → 𝕜) :
    veroneseDeg (n + 1) e (Fin.cons 0 y) = pushAlong Fin.succ (veroneseDeg n e y) := by
  rw [← extAlong_succ_eq_cons, veroneseDeg_extAlong (Fin.succ_injective _)]

omit [CharZero 𝕜] in
theorem map_tangentSpace_pushAlong_cons_le {n e : ℕ} (y : Fin (n + 1) → 𝕜) :
    (veroneseDegParam n e y).tangentSpace.map (pushAlong (𝕜 := 𝕜) Fin.succ).toLinearMap
      ≤ (veroneseDegParam (n + 1) e (Fin.cons 0 y)).tangentSpace := by
  have h := map_tangentSpace_pushAlong_le (𝕜 := 𝕜) (d := e) (Fin.succ_injective (n + 1)) y
  rwa [extAlong_succ_eq_cons] at h

/-! #### Points with polynomial coordinates -/

variable {σ : Type*}

/-- The tangent vector, in the direction `eⱼ`, at a point with polynomial coordinates `P`. -/
def tanVec {N : ℕ} (P : Fin (N + 1) → MvPolynomial σ 𝕜) (e : ℕ) (j : Fin (N + 1))
    (s : Sym (Fin (N + 1)) e) : MvPolynomial σ 𝕜 :=
  bind₁ P (pderiv j (veroneseDegPoly N e s))

/-- The point of the cone over a point with polynomial coordinates `P`. -/
def ptVec {N : ℕ} (P : Fin (N + 1) → MvPolynomial σ 𝕜) (e : ℕ) (s : Sym (Fin (N + 1)) e) :
    MvPolynomial σ 𝕜 :=
  bind₁ P (veroneseDegPoly N e s)

omit [CharZero 𝕜] in
theorem eval_tanVec {N : ℕ} (P : Fin (N + 1) → MvPolynomial σ 𝕜) (e : ℕ) (j : Fin (N + 1))
    (x : σ → 𝕜) : (fun s => eval x (tanVec P e j s))
      = veroneseDegDeriv N e (polyPoint P x) (Pi.single j 1) := by
  funext s
  rw [veroneseDegDeriv_single, tanVec]
  show eval₂Hom (RingHom.id 𝕜) x _ = _
  rw [eval₂Hom_bind₁]
  rfl

omit [CharZero 𝕜] in
theorem eval_ptVec {N : ℕ} (P : Fin (N + 1) → MvPolynomial σ 𝕜) (e : ℕ) (x : σ → 𝕜) :
    (fun s => eval x (ptVec P e s)) = veroneseDeg N e (polyPoint P x) := by
  funext s
  rw [ptVec, veroneseDeg]
  show eval₂Hom (RingHom.id 𝕜) x _ = _
  rw [eval₂Hom_bind₁]
  rfl

omit [CharZero 𝕜] in
theorem polyPoint_cons {N : ℕ} (P : Fin (N + 1) → MvPolynomial σ 𝕜) (x : σ → 𝕜) :
    polyPoint (Fin.cons 0 P : Fin (N + 2) → MvPolynomial σ 𝕜) x = Fin.cons 0 (polyPoint P x) := by
  funext a
  refine Fin.cases ?_ (fun a => ?_) a <;> simp [polyPoint]

omit [CharZero 𝕜] in
theorem span_eval_elim {ι ι' κ : Type*} (F : ι → κ → MvPolynomial σ 𝕜)
    (G : ι' → κ → MvPolynomial σ 𝕜) (x : σ → 𝕜) :
    Submodule.span 𝕜 (Set.range fun i s => eval x (Sum.elim F G i s))
      = Submodule.span 𝕜 (Set.range fun i s => eval x (F i s))
        ⊔ Submodule.span 𝕜 (Set.range fun i s => eval x (G i s)) := by
  rw [← Submodule.span_union, ← Set.Sum.elim_range]
  congr 2
  funext i
  rcases i with i | i <;> rfl

omit [CharZero 𝕜] in
theorem span_eval_tanVec {ι : Type*} {N : ℕ} (P : ι → Fin (N + 1) → MvPolynomial σ 𝕜) (e : ℕ)
    (x : σ → 𝕜) :
    Submodule.span 𝕜 (Set.range fun ij : ι × Fin (N + 1) => fun s => eval x (tanVec (P ij.1) e ij.2 s))
      = ⨆ i, (veroneseDegParam N e (polyPoint (P i) x)).tangentSpace := by
  have h : (fun ij : ι × Fin (N + 1) => fun s => eval x (tanVec (P ij.1) e ij.2 s))
      = fun ij => veroneseDegDeriv N e (polyPoint (P ij.1) x) (Pi.single ij.2 1) := by
    funext ij
    exact eval_tanVec (P ij.1) e ij.2 x
  rw [h]
  exact (iSup_tangentSpace_eq_span (fun i => polyPoint (P i) x)).symm

end Tools

/-! ### §C — The inductive step -/

variable (𝕜) in
/-- `AH_{n,d}(k)`: some `k` points of `𝕜^{n+1}` have tangent spaces to `v_d` spanning a space of
the expected dimension `min (N, k(n+1))`. By semicontinuity
(`forGeneralPoints_le_finrank_iSup`) general points then do too. -/
def AHHolds (n d k : ℕ) : Prop :=
  ∃ p : Fin k → Fin (n + 1) → 𝕜, min ((n + d).choose d) (k * (n + 1))
    ≤ Module.finrank 𝕜 ((⨆ i, (veroneseDegParam n d (p i)).tangentSpace : Submodule 𝕜 _))

/-- **The Alexander–Hirschowitz step** (Brambilla–Ottaviani, Theorem 6.4). In `ℙ^{n+1}` and
degree `d + 2`, choose `u` and `ε ≤ n` with `(n+1)u + ε + N_{d+1} = k(n+2)`. Then
`AH_{n,d+2}(u)` (the trace), `AH_{n+1,d+1}(k-u)` and `AH_{n+1,d}(k-u-ε)` filling (the residual)
give `AH_{n+1,d+2}(k)`. -/
theorem AHHolds.step {n d k u ε : ℕ} (hd : 1 ≤ d) (hε : ε ≤ n) (hεu : ε ≤ u) (hk : u + ε ≤ k)
    (hu : (n + 1) * u + ε + (n + 1 + (d + 1)).choose (d + 1) = k * (n + 2))
    (hfill : (n + 1 + d).choose d ≤ (k - u - ε) * (n + 2))
    (htr : AHHolds 𝕜 n (d + 2) u) (hres : AHHolds 𝕜 (n + 1) (d + 1) (k - u))
    (hres₂ : AHHolds 𝕜 (n + 1) d (k - u - ε)) :
    AHHolds 𝕜 (n + 1) (d + 2) k := by
  classical
  have : Infinite 𝕜 := CharZero.infinite 𝕜
  set a := k - u - ε with ha
  set NH := (n + (d + 2)).choose (d + 2) with hNH
  set N1 := (n + 1 + (d + 1)).choose (d + 1) with hN1
  set Nd := (n + 1 + d).choose d with hNd
  -- arithmetic
  have hka : k = a + u + ε := by omega
  have hmul : k * (n + 2) = a * (n + 2) + u * n + 2 * u + ε * n + 2 * ε := by
    rw [hka]; ring
  have hmul' : (n + 1) * u = u * n + u := by ring
  have hku : (k - u) * (n + 2) = a * (n + 2) + ε * n + 2 * ε := by
    rw [show k - u = a + ε by omega]; ring
  have hNN : N1 = a * (n + 2) + ε * n + ε + u := by omega
  -- parameters: the points `σᵢ ∉ H`, `φ_b ∈ H` and `γᵢ ∈ H`
  let Prm := (Fin a × Fin (n + 2)) ⊕ (Fin u × Fin (n + 1)) ⊕ (Fin ε × Fin (n + 1))
  let Pσ : Fin a → Fin (n + 2) → MvPolynomial Prm 𝕜 := fun i l => X (.inl (i, l))
  let Pφ : Fin u → Fin (n + 1) → MvPolynomial Prm 𝕜 := fun b l => X (.inr (.inl (b, l)))
  let Pγ : Fin ε → Fin (n + 1) → MvPolynomial Prm 𝕜 := fun i l => X (.inr (.inr (i, l)))
  let mk : (Fin a → Fin (n + 2) → 𝕜) → (Fin u → Fin (n + 1) → 𝕜) → (Fin ε → Fin (n + 1) → 𝕜) →
      Prm → 𝕜 := fun σ φ γ =>
    Sum.elim (fun p => σ p.1 p.2) (Sum.elim (fun p => φ p.1 p.2) (fun p => γ p.1 p.2))
  have hmkσ : ∀ σ φ γ i, polyPoint (Pσ i) (mk σ φ γ) = σ i := fun _ _ _ _ => by
    funext l; simp [polyPoint, Pσ, mk]
  have hmkφ : ∀ σ φ γ b, polyPoint (Pφ b) (mk σ φ γ) = φ b := fun _ _ _ _ => by
    funext l; simp [polyPoint, Pφ, mk]
  have hmkγ : ∀ σ φ γ i, polyPoint (Pγ i) (mk σ φ γ) = γ i := fun _ _ _ _ => by
    funext l; simp [polyPoint, Pγ, mk]
  -- the families of vectors
  let F1 : (Fin u × Fin (n + 1)) ⊕ Fin ε → Sym (Fin (n + 1)) (d + 2) → MvPolynomial Prm 𝕜 :=
    Sum.elim (fun bj => tanVec (Pφ bj.1) (d + 2) bj.2) (fun i => ptVec (Pγ i) (d + 2))
  let FD : (Fin a × Fin (n + 2)) ⊕ (Fin ε × Fin (n + 1)) → Sym (Fin (n + 2)) (d + 1) →
      MvPolynomial Prm 𝕜 :=
    Sum.elim (fun ij => tanVec (Pσ ij.1) (d + 1) ij.2)
      (fun ij => tanVec (Fin.cons 0 (Pγ ij.1)) (d + 1) ij.2.succ)
  let F2 : Fin a × Fin (n + 2) → Sym (Fin (n + 2)) d → MvPolynomial Prm 𝕜 :=
    fun ij => tanVec (Pσ ij.1) d ij.2
  let FC := Sum.elim FD (fun b : Fin u => ptVec (Fin.cons 0 (Pφ b)) (d + 1))
  -- their spans
  have hF1 : ∀ x, Submodule.span 𝕜 (Set.range fun i s => eval x (F1 i s))
      = (⨆ b, (veroneseDegParam n (d + 2) (polyPoint (Pφ b) x)).tangentSpace)
        ⊔ Submodule.span 𝕜 (Set.range fun i => veroneseDeg n (d + 2) (polyPoint (Pγ i) x)) := by
    intro x
    have h : (fun i : Fin ε => fun s => eval x (ptVec (Pγ i) (d + 2) s))
        = fun i => veroneseDeg n (d + 2) (polyPoint (Pγ i) x) :=
      funext fun i => eval_ptVec (Pγ i) (d + 2) x
    rw [span_eval_elim, span_eval_tanVec]
    rw [h]
  have hFD : ∀ x, Submodule.span 𝕜 (Set.range fun i s => eval x (FD i s))
      = (⨆ i, (veroneseDegParam (n + 1) (d + 1) (polyPoint (Pσ i) x)).tangentSpace)
        ⊔ Submodule.span 𝕜 (Set.range fun ij : Fin ε × Fin (n + 1) =>
          pushAlong Fin.succ (veroneseDegDeriv n (d + 1) (polyPoint (Pγ ij.1) x)
            (Pi.single ij.2 1))) := by
    intro x
    have h : (fun ij : Fin ε × Fin (n + 1) => fun s =>
        eval x (tanVec (Fin.cons 0 (Pγ ij.1)) (d + 1) ij.2.succ s))
        = fun ij => pushAlong Fin.succ (veroneseDegDeriv n (d + 1) (polyPoint (Pγ ij.1) x)
            (Pi.single ij.2 1)) := by
      funext ij
      rw [eval_tanVec, polyPoint_cons, veroneseDegDeriv_cons_succ]
    rw [span_eval_elim, span_eval_tanVec]
    rw [h]
  have hF2 : ∀ x, Submodule.span 𝕜 (Set.range fun i s => eval x (F2 i s))
      = ⨆ i, (veroneseDegParam (n + 1) d (polyPoint (Pσ i) x)).tangentSpace :=
    fun x => span_eval_tanVec Pσ d x
  have hFC : ∀ x, Submodule.span 𝕜 (Set.range fun i s => eval x (FC i s))
      = Submodule.span 𝕜 (Set.range fun i s => eval x (FD i s))
        ⊔ Submodule.span 𝕜 (Set.range fun b =>
          veroneseDeg (n + 1) (d + 1) (Fin.cons 0 (polyPoint (Pφ b) x))) := by
    intro x
    have h : (fun b : Fin u => fun s => eval x (ptVec (Fin.cons 0 (Pφ b)) (d + 1) s))
        = fun b => veroneseDeg (n + 1) (d + 1) (Fin.cons 0 (polyPoint (Pφ b) x)) := by
      funext b
      rw [eval_ptVec, polyPoint_cons]
    rw [span_eval_elim]
    rw [h]
  -- `σᵢ ∉ H` for general parameters
  have G3 : HoldsGenerically (𝕜 := 𝕜) Prm fun x => ∀ i, polyPoint (Pσ i) x 0 ≠ 0 := by
    refine ⟨∏ i, X (.inl (i, 0)), Finset.prod_ne_zero_iff.mpr fun i _ => X_ne_zero _,
      fun x hx i => ?_⟩
    rw [map_prod] at hx
    simpa [polyPoint, Pσ] using Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ i)
  -- the trace: `AH_{n,d+2}(u)` and `ε` general points of `H`
  have G1 : HoldsGenerically (𝕜 := 𝕜) Prm fun x => min NH ((n + 1) * u + ε)
      ≤ Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range fun i s => eval x (F1 i s))) := by
    obtain ⟨φ₀, hφ₀⟩ := htr
    set A := (⨆ b, (veroneseDegParam n (d + 2) (φ₀ b)).tangentSpace : Submodule 𝕜 _)
    obtain ⟨γ₀, hγ₀⟩ := exists_finrank_sup_span_ge A (veroneseDeg (𝕜 := 𝕜) n (d + 2)) ε
    rw [span_range_veroneseDeg, sup_top_eq, finrank_top, finrank_ambient_veroneseDeg] at hγ₀
    refine holdsGenerically_le_finrank_span_eval F1 (mk 0 φ₀ γ₀) ?_
    rw [hF1]
    have e1 : ∀ b, polyPoint (Pφ b) (mk 0 φ₀ γ₀) = φ₀ b := hmkφ 0 φ₀ γ₀
    have e2 : ∀ i, polyPoint (Pγ i) (mk 0 φ₀ γ₀) = γ₀ i := hmkγ 0 φ₀ γ₀
    rw [iSup_congr fun b => by rw [e1 b],
      show (fun i => veroneseDeg n (d + 2) (polyPoint (Pγ i) (mk 0 φ₀ γ₀)))
        = veroneseDeg n (d + 2) ∘ γ₀ from funext fun i => by rw [e2 i]; rfl]
    have h1 : min NH (u * (n + 1)) ≤ Module.finrank 𝕜 A := hφ₀
    have h2 := hγ₀
    rw [← hNH] at h2
    have hc : u * (n + 1) = (n + 1) * u := mul_comm _ _
    exact le_trans (by omega) h2
  -- the residual, before adding `Φ`: `AH_{n+1,d+1}(k-u)` with `ε` of the points moved into `H`
  have GD : HoldsGenerically (𝕜 := 𝕜) Prm fun x => (k - u) * (n + 2) - ε
      ≤ Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range fun i s => eval x (FD i s))) := by
    obtain ⟨q, hq⟩ := hres
    have hq' : (k - u) * (n + 2) ≤ Module.finrank 𝕜
        ((⨆ m, (veroneseDegParam (n + 1) (d + 1) (q m)).tangentSpace : Submodule 𝕜 _)) := by
      have h22 : (k - u) * (n + 1 + 1) = (k - u) * (n + 2) := rfl
      rw [h22, ← hN1] at hq
      exact le_trans (le_min (by omega) le_rfl) hq
    have hεk : ε ≤ k - u := by omega
    let qγ : Fin ε → Fin (n + 2) → 𝕜 := fun i => q (Fin.castLE hεk i)
    obtain ⟨L, L', hLL, hL0⟩ := exists_linear_zero_of_lt (n := n + 1) (by omega) qγ
    have hmono := finrank_iSup_tangentSpace_le_comp (d := d + 1) hLL q
    let σL : Fin a → Fin (n + 2) → 𝕜 := fun i => L (q ⟨ε + i, by omega⟩)
    let γL : Fin ε → Fin (n + 1) → 𝕜 := fun i => Fin.tail (L (qγ i))
    refine holdsGenerically_le_finrank_span_eval FD (mk σL 0 γL) ?_
    rw [hFD, iSup_congr fun i => by rw [hmkσ σL 0 γL i],
      show (fun ij : Fin ε × Fin (n + 1) => pushAlong Fin.succ (veroneseDegDeriv n (d + 1)
          (polyPoint (Pγ ij.1) (mk σL 0 γL)) (Pi.single ij.2 1)))
        = fun ij => pushAlong Fin.succ (veroneseDegDeriv n (d + 1) (γL ij.1) (Pi.single ij.2 1))
        from funext fun ij => by rw [hmkγ]]
    set B := (⨆ i, (veroneseDegParam (n + 1) (d + 1) (σL i)).tangentSpace)
      ⊔ Submodule.span 𝕜 (Set.range fun ij : Fin ε × Fin (n + 1) => pushAlong Fin.succ
          (veroneseDegDeriv n (d + 1) (γL ij.1) (Pi.single ij.2 1)))
    set Ex := Submodule.span 𝕜 (Set.range fun i : Fin ε =>
      veroneseDegDeriv (n + 1) (d + 1) (L (qγ i)) (Pi.single 0 1))
    have hle : (⨆ m, (veroneseDegParam (n + 1) (d + 1) (L (q m))).tangentSpace :
        Submodule 𝕜 _) ≤ B ⊔ Ex := by
      refine iSup_le fun m => ?_
      rw [tangentSpace_eq_span, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      show veroneseDegDeriv (n + 1) (d + 1) (L (q m)) (Pi.single j 1) ∈ B ⊔ Ex
      by_cases hm : (m : ℕ) < ε
      · set i : Fin ε := ⟨m, hm⟩
        have hqi : q m = qγ i := congrArg q (Fin.ext rfl)
        have hcons : L (qγ i) = Fin.cons 0 (γL i) := by
          rw [← hL0 i]
          exact (Fin.cons_self_tail _).symm
        rw [hqi]
        refine Fin.cases ?_ (fun j' => ?_) j
        · exact Submodule.mem_sup_right (Submodule.subset_span ⟨i, rfl⟩)
        · refine Submodule.mem_sup_left (Submodule.mem_sup_right
            (Submodule.subset_span ⟨(i, j'), ?_⟩))
          show pushAlong Fin.succ (veroneseDegDeriv n (d + 1) (γL i) (Pi.single j' 1))
            = veroneseDegDeriv (n + 1) (d + 1) (L (qγ i)) (Pi.single j'.succ 1)
          rw [hcons, veroneseDegDeriv_cons_succ]
      · set i : Fin a := ⟨m - ε, by omega⟩
        have hqi : q m = q ⟨ε + i, by omega⟩ := congrArg q (Fin.ext (by simp [i]; omega))
        refine Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_iSup_of_mem i ?_))
        rw [hqi]
        exact ⟨Pi.single j 1, rfl⟩
    have hEx : Module.finrank 𝕜 Ex ≤ ε := by
      have := finrank_range_le_card (R := 𝕜) (fun i : Fin ε =>
        veroneseDegDeriv (n + 1) (d + 1) (L (qγ i)) (Pi.single 0 1))
      simpa [Set.finrank] using this
    have h1 := Submodule.finrank_mono hle
    have h2 := Submodule.finrank_add_le_finrank_add_finrank B Ex
    exact Nat.sub_le_iff_le_add.mpr
      (hq'.trans (hmono.trans (h1.trans (h2.trans (Nat.add_le_add_left hEx _)))))
  -- fill one degree lower: `AH_{n+1,d}(k-u-ε)`
  have G2 : HoldsGenerically (𝕜 := 𝕜) Prm fun x => Nd
      ≤ Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range fun i s => eval x (F2 i s))) := by
    obtain ⟨σ', hσ'⟩ := hres₂
    refine holdsGenerically_le_finrank_span_eval F2 (mk σ' 0 0) ?_
    rw [hF2, iSup_congr fun i => by rw [hmkσ σ' 0 0 i]]
    have h22 : a * (n + 1 + 1) = a * (n + 2) := rfl
    rw [h22, ← hNd] at hσ'
    exact le_trans (le_min le_rfl hfill) hσ'
  -- the residual: add `u` general points of `H` to a general configuration of `GD`
  have GC : HoldsGenerically (𝕜 := 𝕜) Prm fun x => N1
      ≤ Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range fun i s => eval x (FC i s))) := by
    obtain ⟨x₁, ⟨h1, h2⟩, h3⟩ := ((GD.and G2).and G3).exists_point
    set σ₁ := fun i => polyPoint (Pσ i) x₁ with hσ₁
    set γ₁ := fun i => polyPoint (Pγ i) x₁ with hγ₁
    set A := Submodule.span 𝕜 (Set.range fun i s => eval x₁ (FD i s)) with hAdef
    let v : (Fin (n + 1) → 𝕜) → (Sym (Fin (n + 2)) (d + 1) → 𝕜) :=
      fun y => veroneseDeg (n + 1) (d + 1) (Fin.cons 0 y)
    have htop : A ⊔ Submodule.span 𝕜 (Set.range v) = ⊤ := by
      -- one degree lower the points `σᵢ` fill
      have hF2top : (⨆ i, (veroneseDegParam (n + 1) d (σ₁ i)).tangentSpace :
          Submodule 𝕜 _) = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        apply le_antisymm (Submodule.finrank_le _)
        rw [finrank_ambient_veroneseDeg, ← hF2]
        exact (show (n + 1 + d).choose d = Nd from rfl) ▸ h2
      -- so the residual of `A` is everything
      have hrA : A.map (resid n d) = ⊤ := by
        rw [eq_top_iff, ← hF2top]
        refine iSup_le fun i => (tangentSpace_le_map_resid (by omega) (h3 i)).trans
          (Submodule.map_mono ?_)
        rw [hAdef, hFD]
        exact le_sup_of_le_left (le_iSup (fun i =>
          (veroneseDegParam (n + 1) (d + 1) (polyPoint (Pσ i) x₁)).tangentSpace) i)
      rw [eq_top_iff]
      intro f _
      obtain ⟨g, hg, hgf⟩ : resid n d f ∈ A.map (resid n d) := hrA ▸ Submodule.mem_top
      have hker : f - g ∈ LinearMap.ker (resid n d) := by
        rw [LinearMap.mem_ker, map_sub, hgf, sub_self]
      rw [ker_resid] at hker
      obtain ⟨h, hh⟩ := hker
      have hfg : f - g ∈ Submodule.span 𝕜 (Set.range v) := by
        have hspan : h ∈ Submodule.span 𝕜 (Set.range (veroneseDeg (𝕜 := 𝕜) n (d + 1))) := by
          rw [span_range_veroneseDeg]; trivial
        have := Submodule.mem_map_of_mem (f := (pushAlong (𝕜 := 𝕜) (d := d + 1)
          (Fin.succ : Fin (n + 1) → Fin (n + 2))).toLinearMap) hspan
        rw [Submodule.map_span, ← Set.range_comp] at this
        rw [← hh]
        convert this using 3
        funext y
        simp [v, veroneseDeg_cons]
      have := Submodule.add_mem_sup hg hfg
      rwa [add_sub_cancel] at this
    obtain ⟨φ₁, hφ₁⟩ := exists_finrank_sup_span_ge A v u
    rw [htop, finrank_top, finrank_ambient_veroneseDeg] at hφ₁
    refine holdsGenerically_le_finrank_span_eval FC (mk σ₁ φ₁ γ₁) ?_
    have hA : Submodule.span 𝕜 (Set.range fun i s => eval (mk σ₁ φ₁ γ₁) (FD i s)) = A := by
      rw [hAdef, hFD, hFD, iSup_congr fun i => by rw [hmkσ σ₁ φ₁ γ₁ i],
        show (fun ij : Fin ε × Fin (n + 1) => pushAlong Fin.succ (veroneseDegDeriv n (d + 1)
            (polyPoint (Pγ ij.1) (mk σ₁ φ₁ γ₁)) (Pi.single ij.2 1)))
          = fun ij => pushAlong Fin.succ (veroneseDegDeriv n (d + 1) (γ₁ ij.1) (Pi.single ij.2 1))
          from funext fun ij => by rw [hmkγ]]
    rw [hFC, hA, show (fun b => veroneseDeg (n + 1) (d + 1)
        (Fin.cons 0 (polyPoint (Pφ b) (mk σ₁ φ₁ γ₁)))) = v ∘ φ₁ from
      funext fun b => by rw [hmkφ]; rfl]
    have hAf : (k - u) * (n + 2) - ε ≤ Module.finrank 𝕜 A := h1
    rw [show (n + 1 + (d + 1)).choose (d + 1) = N1 from rfl] at hφ₁
    exact le_trans (le_min (by omega) le_rfl) hφ₁
  -- a general configuration, and the Horace step
  obtain ⟨x, ⟨h1, h2⟩, h3⟩ := ((G1.and GC).and G3).exists_point
  rw [hF1] at h1
  rw [hFC, hFD] at h2
  set σ := fun i => polyPoint (Pσ i) x with hσ
  set φ := fun b => polyPoint (Pφ b) x with hφ
  set γ := fun i => polyPoint (Pγ i) x with hγ
  set W := (⨆ i, (veroneseDegParam (n + 1) (d + 2) (σ i)).tangentSpace)
    ⊔ ⨆ b, (veroneseDegParam (n + 1) (d + 2) (Fin.cons 0 (φ b))).tangentSpace with hW
  obtain ⟨t, ht⟩ := (horace_step (n := n) (d := d + 1) W γ).exists_point
  set E := Submodule.span 𝕜 (Set.range fun i =>
    veroneseDeg (n + 1) (d + 2) (extAlong Fin.succ (γ i))) with hE
  set Tm := (⨆ i, (veroneseDegParam (n + 1) (d + 2)
    (extAlong Fin.succ (γ i) + t () • (Pi.single 0 1 : Fin (n + 2) → 𝕜))).tangentSpace :
      Submodule 𝕜 _) with hTm
  set R := W.map (resid n (d + 1)) ⊔ ⨆ i,
    (veroneseDegParam n (d + 1) (γ i)).tangentSpace.map (pushAlong Fin.succ).toLinearMap with hR
  have ht' : Module.finrank 𝕜 (W ⊔ E : Submodule 𝕜 _) + Module.finrank 𝕜 R
      ≤ Module.finrank 𝕜 (W ⊔ Tm : Submodule 𝕜 _) + Module.finrank 𝕜 (W.map (resid n (d + 1))) :=
    ht
  -- the trace
  set C := (⨆ b, (veroneseDegParam n (d + 2) (φ b)).tangentSpace)
    ⊔ Submodule.span 𝕜 (Set.range fun i => veroneseDeg n (d + 2) (γ i)) with hC
  have hT : Module.finrank 𝕜 (W.map (resid n (d + 1))) + Module.finrank 𝕜 C
      ≤ Module.finrank 𝕜 (W ⊔ E : Submodule 𝕜 _) := by
    have hinj := pushAlong_injective (𝕜 := 𝕜) (d := d + 2) (Fin.succ_injective (n + 1))
    have hCeq : Module.finrank 𝕜 (C.map (pushAlong Fin.succ).toLinearMap)
        = Module.finrank 𝕜 C :=
      (Submodule.equivMapOfInjective _ hinj C).finrank_eq.symm
    have hCle : C.map (pushAlong Fin.succ).toLinearMap ≤ W ⊔ E := by
      rw [hC, Submodule.map_sup, Submodule.map_iSup, Submodule.map_span, ← Set.range_comp]
      refine sup_le_sup (iSup_le fun b => (map_tangentSpace_pushAlong_cons_le (φ b)).trans
        (le_sup_of_le_right (le_iSup (fun b =>
          (veroneseDegParam (n + 1) (d + 2) (Fin.cons 0 (φ b))).tangentSpace) b))) ?_
      rw [hE]
      apply le_of_eq
      congr 2
      funext i
      simp [veroneseDeg_extAlong (Fin.succ_injective _)]
    have hker : C.map (pushAlong Fin.succ).toLinearMap ≤ LinearMap.ker (resid n (d + 1)) := by
      rw [ker_resid]
      exact LinearMap.map_le_range
    have hle := finrank_map_add_le_of_le_ker (resid n (d + 1)) hCle hker
    have hmono := Submodule.finrank_mono (Submodule.map_mono (f := resid n (d + 1))
      (le_sup_left : W ≤ W ⊔ E))
    omega
  -- the residual
  have hRle : N1 ≤ Module.finrank 𝕜 R := by
    refine h2.trans (Submodule.finrank_mono (sup_le (sup_le ?_ ?_) ?_))
    · refine iSup_le fun i => (tangentSpace_le_map_resid (by omega) (h3 i)).trans
        (le_sup_of_le_left (Submodule.map_mono ?_))
      exact le_sup_of_le_left (le_iSup (fun i =>
        (veroneseDegParam (n + 1) (d + 2) (σ i)).tangentSpace) i)
    · rw [Submodule.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      exact le_sup_right (a := W.map (resid n (d + 1))) (Submodule.mem_iSup_of_mem i
        ⟨_, ⟨Pi.single j 1, rfl⟩, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      refine le_sup_left (b := ⨆ i, (veroneseDegParam n (d + 1) (γ i)).tangentSpace.map
        (pushAlong Fin.succ).toLinearMap) ⟨veroneseDegDeriv (n + 1) (d + 2) (Fin.cons 0 (φ b))
          (Pi.single 0 1), le_sup_of_le_right (le_iSup (fun b =>
            (veroneseDegParam (n + 1) (d + 2) (Fin.cons 0 (φ b))).tangentSpace) b)
          ⟨Pi.single 0 1, rfl⟩, ?_⟩
      show resid n (d + 1) (veroneseDegDeriv (n + 1) (d + 1 + 1) (Fin.cons 0 (φ b))
        (Pi.single 0 1)) = _
      rw [resid_veroneseDegDeriv]
      simp
      rfl
  -- the configuration
  let g : Fin a ⊕ (Fin u ⊕ Fin ε) → Fin (n + 2) → 𝕜 := Sum.elim σ (Sum.elim
    (fun b => Fin.cons 0 (φ b)) (fun i => extAlong Fin.succ (γ i) + t () • Pi.single 0 1))
  let e : Fin k ≃ Fin a ⊕ (Fin u ⊕ Fin ε) := (finCongr (by omega : k = a + (u + ε))).trans
    (finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv.symm))
  refine ⟨g ∘ e, ?_⟩
  have hsup : (⨆ m, (veroneseDegParam (n + 1) (d + 2) ((g ∘ e) m)).tangentSpace :
      Submodule 𝕜 _) = W ⊔ Tm := by
    rw [show (⨆ m, (veroneseDegParam (n + 1) (d + 2) ((g ∘ e) m)).tangentSpace :
        Submodule 𝕜 _) = ⨆ z, (veroneseDegParam (n + 1) (d + 2) (g z)).tangentSpace from
      e.iSup_comp (g := fun z => (veroneseDegParam (n + 1) (d + 2) (g z)).tangentSpace),
      iSup_sum, iSup_sum, hW, hTm, sup_assoc]
    rfl
  rw [hsup]
  have hpascal : (n + 1 + (d + 2)).choose (d + 2) = NH + N1 := by
    rw [hNH, hN1, show n + 1 + (d + 2) = (n + (d + 2)) + 1 by ring, Nat.choose_succ_succ,
      show n + 1 + (d + 1) = n + (d + 2) by ring]
    ring
  have h22 : k * (n + 1 + 1) = k * (n + 2) := rfl
  rw [hpascal, h22]
  omega

end AHStep
