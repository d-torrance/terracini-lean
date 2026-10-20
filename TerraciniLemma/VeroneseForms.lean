module

public import TerraciniLemma.VeroneseDegree
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Forms on the Veronese cone, and the singular-form bound

A linear functional `χ` on the ambient space `Sym (Fin (n+1)) d → 𝕜` of `v_d(ℙⁿ)` pulls back
along the cone parametrization `veroneseDeg n d` to a degree-`d` form `x ↦ χ (v_d(x))` on
`𝕜^{n+1}`; conversely every degree-`d` form arises this way (its coefficients are the values of
`χ` on the coordinate vectors). This is the dictionary behind all of the
Alexander–Hirschowitz exceptional cases (Brambilla–Ottaviani, *On the Alexander–Hirschowitz
theorem*, J. Pure Appl. Algebra **212** (2008)):

> *If a nonzero degree-`d` form `F` is singular at `p₁, …, p_r`, then the hyperplane `{F = 0}`
> of `ℙ^N` contains all the tangent spaces `T_{v_d(pₖ)} v_d(ℙⁿ)`, so their span has dimension
> at most `N`, one less than the ambient cone.*

In the cone model this reads: if `F = χ ∘ v_d ≠ 0` has zero derivative at each `pₖ`, then the
chain rule gives `χ ∘ dv_d(pₖ) = 0`, i.e. every tangent space lies in `ker χ`
(`finrank_iSup_tangentSpace_le_of_singular`).

The file also sets up the bookkeeping for "general points":

* `veroneseForms n d` — the degree-`d` forms, as the submodule of functions
  `𝕜^{n+1} → 𝕜` of the shape `χ ∘ v_d`, closed under products (`mul_mem_veroneseForms`) and
  containing all linear forms (`linearMap_mem_veroneseForms`);
* `veroneseFormOf_injective` — the Veronese variety is nondegenerate: a functional vanishing on
  the image of `v_d` is zero (equivalently, a nonzero form is a nonzero function);
* `ForGeneralPoints r m P` — `P` holds for all `r`-tuples of points of `𝕜^m` off the zero
  locus of a nonzero polynomial in their coordinates, the formal meaning of "for general
  points".
-/

@[expose] public section

noncomputable section VeroneseForms

open MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-! ### §A — Forms as pullbacks of functionals -/

omit [CharZero 𝕜] in
/-- Pull a linear functional on the ambient space back along the cone parametrization `v_d`,
giving a degree-`d` form on `𝕜^{n+1}`. -/
def veroneseFormOf (n d : ℕ) :
    Module.Dual 𝕜 (Sym (Fin (n + 1)) d → 𝕜) →ₗ[𝕜] ((Fin (n + 1) → 𝕜) → 𝕜) where
  toFun χ x := χ (veroneseDeg n d x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [CharZero 𝕜] in
@[simp]
theorem veroneseFormOf_apply (n d : ℕ) (χ : Module.Dual 𝕜 (Sym (Fin (n + 1)) d → 𝕜))
    (x : Fin (n + 1) → 𝕜) : veroneseFormOf n d χ x = χ (veroneseDeg n d x) := rfl

omit [CharZero 𝕜] in
/-- The degree-`d` forms on `𝕜^{n+1}`. -/
def veroneseForms (n d : ℕ) : Submodule 𝕜 ((Fin (n + 1) → 𝕜) → 𝕜) :=
  LinearMap.range (veroneseFormOf n d)

omit [CharZero 𝕜] in
/-- The Veronese coordinate at the concatenation of two multisets is the product of the
coordinates. -/
theorem veroneseDeg_append (n d₁ d₂ : ℕ) (x : Fin (n + 1) → 𝕜) (a : Sym (Fin (n + 1)) d₁)
    (b : Sym (Fin (n + 1)) d₂) :
    veroneseDeg n (d₁ + d₂) x (a.append b) = veroneseDeg n d₁ x a * veroneseDeg n d₂ x b := by
  simp [veroneseDeg, veroneseDegPoly, Sym.coe_append, Multiset.map_add, Multiset.prod_add]

omit [CharZero 𝕜] in
/-- A functional on `Sym (Fin (n+1)) d → 𝕜` is determined by its values on the coordinate
vectors. -/
theorem dual_apply_eq_sum (n d : ℕ) (χ : Module.Dual 𝕜 (Sym (Fin (n + 1)) d → 𝕜))
    (f : Sym (Fin (n + 1)) d → 𝕜) :
    χ f = ∑ s, f s * χ (Pi.single s 1) := by
  classical
  rw [LinearMap.pi_apply_eq_sum_univ χ f]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [smul_eq_mul]
  congr 2
  funext t
  simp [Pi.single_apply, eq_comm]

omit [CharZero 𝕜] in
/-- **Forms multiply.** The product of a degree-`d₁` and a degree-`d₂` form is a form of
degree `d₁ + d₂`. -/
theorem mul_mem_veroneseForms {n d₁ d₂ d : ℕ} (hd : d₁ + d₂ = d)
    {f g : (Fin (n + 1) → 𝕜) → 𝕜} (hf : f ∈ veroneseForms n d₁) (hg : g ∈ veroneseForms n d₂) :
    f * g ∈ veroneseForms n d := by
  subst hd
  obtain ⟨χ₁, rfl⟩ := hf
  obtain ⟨χ₂, rfl⟩ := hg
  refine ⟨∑ a, ∑ b, (χ₁ (Pi.single a 1) * χ₂ (Pi.single b 1)) •
    LinearMap.proj (R := 𝕜) (φ := fun _ : Sym (Fin (n + 1)) (d₁ + d₂) => 𝕜) (a.append b), ?_⟩
  funext x
  rw [Pi.mul_apply, veroneseFormOf_apply, veroneseFormOf_apply, veroneseFormOf_apply,
    dual_apply_eq_sum n d₁ χ₁, dual_apply_eq_sum n d₂ χ₂, Finset.sum_mul_sum]
  simp only [LinearMap.coe_sum, LinearMap.coe_smul, LinearMap.coe_proj, Finset.sum_apply,
    Pi.smul_apply, Function.eval, veroneseDeg_append, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

omit [CharZero 𝕜] in
/-- Every linear form is a form of degree `1`. -/
theorem linearMap_mem_veroneseForms (n : ℕ) (ℓ : Module.Dual 𝕜 (Fin (n + 1) → 𝕜)) :
    ⇑ℓ ∈ veroneseForms n 1 := by
  classical
  refine ⟨∑ i, ℓ (Pi.single i 1) •
    LinearMap.proj (R := 𝕜) (φ := fun _ : Sym (Fin (n + 1)) 1 => 𝕜) (Sym.replicate 1 i), ?_⟩
  funext x
  rw [veroneseFormOf_apply, LinearMap.pi_apply_eq_sum_univ ℓ x]
  simp only [LinearMap.coe_sum, LinearMap.coe_smul, LinearMap.coe_proj, Finset.sum_apply,
    Pi.smul_apply, Function.eval, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hsingle : (fun j => if i = j then (1 : 𝕜) else 0) = Pi.single i 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  simp [veroneseDeg, veroneseDegPoly, Sym.replicate, hsingle, mul_comm]

/-! ### §B — Nondegeneracy: a nonzero form is a nonzero function -/

omit [CharZero 𝕜] in
private theorem prod_map_X_eq_monomial (n : ℕ) (m : Multiset (Fin (n + 1))) :
    (Multiset.map X m).prod = (monomial (Multiset.toFinsupp m) 1 : MvPolynomial (Fin (n + 1)) 𝕜) := by
  classical
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add,
      Multiset.toFinsupp_add, Multiset.toFinsupp_singleton, X, monomial_mul_monomial, one_mul]

/-- **The Veronese variety is nondegenerate**: a functional vanishing on the whole image of
`v_d` is zero. Equivalently, `χ ↦ χ ∘ v_d` is injective, so a nonzero form is a nonzero
function. -/
theorem veroneseFormOf_injective (n d : ℕ) :
    Function.Injective (veroneseFormOf (𝕜 := 𝕜) n d) := by
  classical
  have := CharZero.infinite 𝕜
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro χ hχ
  -- The form `χ ∘ v_d` is evaluation of the polynomial `P = ∑ₛ χ(eₛ) Xˢ`.
  set P : MvPolynomial (Fin (n + 1)) 𝕜 :=
    ∑ s : Sym (Fin (n + 1)) d, monomial (Multiset.toFinsupp s.val) (χ (Pi.single s 1))
  have hP : P = 0 := by
    apply MvPolynomial.funext
    intro x
    have hx := congrFun hχ x
    simp only [veroneseFormOf_apply, Pi.zero_apply] at hx
    rw [dual_apply_eq_sum] at hx
    rw [map_zero, ← hx, map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [veroneseDeg, veroneseDegPoly, prod_map_X_eq_monomial, eval_monomial, eval_monomial,
      one_mul, mul_comm]
  -- So every coefficient `χ(eₛ)` vanishes.
  have hcoeff : ∀ s : Sym (Fin (n + 1)) d, χ (Pi.single s 1) = 0 := by
    intro s
    have h := congrArg (fun Q : MvPolynomial (Fin (n + 1)) 𝕜 =>
      Q.coeff (Multiset.toFinsupp s.val)) hP
    simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial] at h
    rwa [Finset.sum_eq_single s (fun t _ hts => ite_eq_right fun h' =>
      hts (Subtype.ext (Multiset.toFinsupp.injective h'))) (by simp), ite_eq_left rfl] at h
  refine LinearMap.ext fun f => ?_
  rw [dual_apply_eq_sum]
  simp [hcoeff]

/-- A nonzero functional is nonzero somewhere on the Veronese cone. -/
theorem exists_apply_veroneseDeg_ne_zero {n d : ℕ} {χ : Module.Dual 𝕜 (Sym (Fin (n + 1)) d → 𝕜)}
    (hχ : χ ≠ 0) : ∃ x, χ (veroneseDeg n d x) ≠ 0 := by
  by_contra! h
  exact hχ (veroneseFormOf_injective n d (funext h))

/-! ### §B' — Tangent spaces at arbitrary nonzero points -/

/-- If `v ≠ 0`, `veroneseDegDeriv n d v` is injective: pick `a` with `v a ≠ 0`; the monomial
`X_a^d` forces `dv a = 0`, and then each monomial `Xⱼ X_a^{d-1}` forces `dv j = 0`. -/
theorem veroneseDegDeriv_injective_of_ne_zero' (n d : ℕ) (hd : 1 ≤ d) {v : Fin (n + 1) → 𝕜}
    (hv : v ≠ 0) : Function.Injective (veroneseDegDeriv n d v) := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, v a ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  suffices h : Function.Injective (veroneseDegDeriv n d v).toLinearMap from h
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  have hw' : ∀ s, veroneseDegDeriv n d v w s = 0 := fun s => congrFun hw s
  have hd0 : (d : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hwa : w a = 0 := by
    have h := hw' (Sym.replicate d a)
    rw [veroneseDegDeriv_apply_replicate' n d hd a] at h
    exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hd0 (pow_ne_zero _ ha))
  funext j
  by_cases hja : j = a
  · rw [hja, hwa]; rfl
  have h := hw' (veroneseDegElt n d hd a j)
  rw [veroneseDegDeriv_apply, Finset.sum_eq_single j] at h
  · rw [veroneseDegElt_val, Multiset.count_cons_self, Multiset.count_replicate,
      ite_eq_right (Ne.symm hja), Multiset.erase_cons_head, Multiset.map_replicate,
      Multiset.prod_replicate] at h
    simpa [pow_ne_zero _ ha] using h
  · intro k _ hk
    by_cases hka : k = a
    · rw [hka, hwa, mul_zero]
    · rw [veroneseDegElt_val, Multiset.count_cons, Multiset.count_replicate,
        ite_eq_right (Ne.symm hka), ite_eq_right hk]
      simp
  · simp

/-- At any nonzero point, the tangent space to the cone over `v_d(ℙⁿ)` has dimension `n+1`. -/
theorem finrank_tangentSpace_veroneseDegParam (n d : ℕ) (hd : 1 ≤ d) {v : Fin (n + 1) → 𝕜}
    (hv : v ≠ 0) : Module.finrank 𝕜 (veroneseDegParam n d v).tangentSpace = n + 1 := by
  show Module.finrank 𝕜 (LinearMap.range (veroneseDegDeriv (𝕜 := 𝕜) n d v).toLinearMap) = n + 1
  rw [LinearMap.finrank_range_of_inj (veroneseDegDeriv_injective_of_ne_zero' n d hd hv),
    Module.finrank_pi, Fintype.card_fin]

/-! ### §C — The singular-form bound -/

omit [CharZero 𝕜] in
/-- A functional on the ambient space as a continuous linear map: a finite combination of
coordinate projections. -/
def dualCLM {n d : ℕ} (χ : Module.Dual 𝕜 (Sym (Fin (n + 1)) d → 𝕜)) :
    (Sym (Fin (n + 1)) d → 𝕜) →L[𝕜] 𝕜 :=
  ∑ s, χ (Pi.single s 1) • ContinuousLinearMap.proj s

omit [CharZero 𝕜] in
@[simp]
theorem dualCLM_apply {n d : ℕ} (χ : Module.Dual 𝕜 (Sym (Fin (n + 1)) d → 𝕜))
    (f : Sym (Fin (n + 1)) d → 𝕜) : dualCLM χ f = χ f := by
  rw [dual_apply_eq_sum]
  simp [dualCLM, mul_comm]

omit [CharZero 𝕜] in
/-- The derivative of the form `χ ∘ v_d`, by the chain rule. -/
theorem hasFDerivAt_veroneseFormOf (n d : ℕ) (χ : Module.Dual 𝕜 (Sym (Fin (n + 1)) d → 𝕜))
    (p : Fin (n + 1) → 𝕜) :
    HasFDerivAt (veroneseFormOf n d χ) ((dualCLM χ).comp (veroneseDegDeriv n d p)) p := by
  have h := (dualCLM χ).hasFDerivAt.comp p (hasFDerivAt_veroneseDeg n d p)
  rwa [show ⇑(dualCLM χ) ∘ veroneseDeg n d = veroneseFormOf n d χ from
    funext fun x => dualCLM_apply χ (veroneseDeg n d x)] at h

omit [CharZero 𝕜] in
/-- If the form `χ ∘ v_d` has zero derivative at `p`, then `χ` kills the tangent space to the
cone at `v_d(p)`. -/
theorem tangentSpace_le_ker_of_hasFDerivAt_zero {n d : ℕ}
    (χ : Module.Dual 𝕜 (Sym (Fin (n + 1)) d → 𝕜)) {p : Fin (n + 1) → 𝕜}
    (hsing : HasFDerivAt (veroneseFormOf n d χ) (0 : (Fin (n + 1) → 𝕜) →L[𝕜] 𝕜) p) :
    (veroneseDegParam n d p).tangentSpace ≤ LinearMap.ker χ := by
  have hchain := hasFDerivAt_veroneseFormOf n d χ p
  have hzero := hchain.unique hsing
  rintro _ ⟨w, rfl⟩
  have := congrArg (fun L : (Fin (n + 1) → 𝕜) →L[𝕜] 𝕜 => L w) hzero
  rwa [ContinuousLinearMap.comp_apply, dualCLM_apply, zero_apply] at this

omit [CharZero 𝕜] in
/-- A nonzero functional on the ambient space has kernel of dimension `binom(n+d,d) - 1`. -/
theorem finrank_ker_dual_veroneseDeg {n d : ℕ} {χ : Module.Dual 𝕜 (Sym (Fin (n + 1)) d → 𝕜)}
    (hχ : χ ≠ 0) : Module.finrank 𝕜 (LinearMap.ker χ) = (n + d).choose d - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker χ
  rw [Module.Dual.range_eq_top_of_ne_zero hχ, finrank_top, Module.finrank_self,
    finrank_ambient_veroneseDeg] at h
  omega

omit [CharZero 𝕜] in
/-- **The singular-form bound** (Brambilla–Ottaviani). If a nonzero degree-`d` form `F` is
singular (has zero derivative) at every point `p k`, the tangent spaces to the cone over
`v_d(ℙⁿ)` at the `v_d(p k)` span a subspace of dimension at most `binom(n+d,d) - 1`: they all
lie in the hyperplane dual to `F`. -/
theorem finrank_iSup_tangentSpace_le_of_singular {n d r : ℕ} (p : Fin r → Fin (n + 1) → 𝕜)
    {F : (Fin (n + 1) → 𝕜) → 𝕜} (hF : F ∈ veroneseForms n d) (hF0 : F ≠ 0)
    (hsing : ∀ k, HasFDerivAt F (0 : (Fin (n + 1) → 𝕜) →L[𝕜] 𝕜) (p k)) :
    Module.finrank 𝕜 (⨆ k, (veroneseDegParam n d (p k)).tangentSpace : Submodule 𝕜 _)
      ≤ (n + d).choose d - 1 := by
  obtain ⟨χ, rfl⟩ := hF
  have hχ : χ ≠ 0 := by rintro rfl; exact hF0 (map_zero _)
  rw [← finrank_ker_dual_veroneseDeg hχ]
  exact Submodule.finrank_mono
    (iSup_le fun k => tangentSpace_le_ker_of_hasFDerivAt_zero χ (hsing k))

/-- **Defectivity from a dimension drop.** If the points are nonzero (so each tangent space has
the full dimension `n+1`) and the configuration is superabundant (`binom(n+d,d) ≤ r(n+1)`, so the
expected dimension is the whole ambient cone), then any bound `≤ binom(n+d,d) - 1` on the span of
the tangent spaces makes them defective. -/
theorem isDefective_of_finrank_le {n d r : ℕ} (hd : 1 ≤ d) (p : Fin r → Fin (n + 1) → 𝕜)
    (hp : ∀ k, p k ≠ 0) (hN : (n + d).choose d ≤ r * (n + 1))
    (hle : Module.finrank 𝕜 (⨆ k, (veroneseDegParam n d (p k)).tangentSpace : Submodule 𝕜 _)
      ≤ (n + d).choose d - 1) :
    IsDefective (fun k => (veroneseDegParam n d (p k)).tangentSpace) := by
  have hdim : ∀ k, Module.finrank 𝕜 (veroneseDegParam n d (p k)).tangentSpace = n + 1 :=
    fun k => finrank_tangentSpace_veroneseDegParam n d hd (hp k)
  have hpos : 0 < (n + d).choose d := Nat.choose_pos (by omega)
  unfold IsDefective expectedDim
  simp only [hdim, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    finrank_ambient_veroneseDeg]
  omega

/-- **Defectivity from a singular form**: combine `finrank_iSup_tangentSpace_le_of_singular`
with `isDefective_of_finrank_le`. -/
theorem isDefective_of_singular {n d r : ℕ} (hd : 1 ≤ d) (p : Fin r → Fin (n + 1) → 𝕜)
    (hp : ∀ k, p k ≠ 0) (hN : (n + d).choose d ≤ r * (n + 1))
    {F : (Fin (n + 1) → 𝕜) → 𝕜} (hF : F ∈ veroneseForms n d) (hF0 : F ≠ 0)
    (hsing : ∀ k, HasFDerivAt F (0 : (Fin (n + 1) → 𝕜) →L[𝕜] 𝕜) (p k)) :
    IsDefective (fun k => (veroneseDegParam n d (p k)).tangentSpace) :=
  isDefective_of_finrank_le hd p hp hN (finrank_iSup_tangentSpace_le_of_singular p hF hF0 hsing)

/-! ### §D — General points -/

omit [CharZero 𝕜] in
/-- `P` holds **for general `r`-tuples of points of `𝕜^m`**: there is a nonzero polynomial `G`
in the `r·m` coordinates such that `P p` holds whenever `G(p) ≠ 0`. Over an infinite field the
locus `G ≠ 0` is a dense Zariski-open set, so this is the classical meaning of "for general
points". -/
def ForGeneralPoints (r m : ℕ) (P : (Fin r → Fin m → 𝕜) → Prop) : Prop :=
  ∃ G : MvPolynomial (Fin r × Fin m) 𝕜, G ≠ 0 ∧
    ∀ p : Fin r → Fin m → 𝕜, eval (fun ki => p ki.1 ki.2) G ≠ 0 → P p

namespace ForGeneralPoints

variable {r m : ℕ} {P Q : (Fin r → Fin m → 𝕜) → Prop}

omit [CharZero 𝕜] in
theorem mono (h : ForGeneralPoints r m P) (hPQ : ∀ p, P p → Q p) : ForGeneralPoints r m Q :=
  let ⟨G, hG, hP⟩ := h
  ⟨G, hG, fun p hp => hPQ p (hP p hp)⟩

omit [CharZero 𝕜] in
theorem of_forall (h : ∀ p, P p) : ForGeneralPoints r m P :=
  ⟨1, one_ne_zero, fun p _ => h p⟩

omit [CharZero 𝕜] in
theorem and (hP : ForGeneralPoints r m P) (hQ : ForGeneralPoints r m Q) :
    ForGeneralPoints r m (fun p => P p ∧ Q p) := by
  obtain ⟨G, hG, hGP⟩ := hP
  obtain ⟨H, hH, hHQ⟩ := hQ
  refine ⟨G * H, mul_ne_zero hG hH, fun p hp => ?_⟩
  rw [map_mul] at hp
  exact ⟨hGP p (left_ne_zero_of_mul hp), hHQ p (right_ne_zero_of_mul hp)⟩

/-- A property of general points holds for *some* points (over an infinite field), so the
notion is never vacuous. -/
theorem exists_point (h : ForGeneralPoints r m P) : ∃ p, P p := by
  have := CharZero.infinite 𝕜
  obtain ⟨G, hG, hP⟩ := h
  by_contra! hno
  apply hG
  apply MvPolynomial.funext
  intro x
  by_contra hx
  exact hno (fun k i => x (k, i)) (hP _ (by simpa using hx))

omit [CharZero 𝕜] in
/-- General points are nonzero (here: have nonzero first coordinate). -/
theorem ne_zero {m : ℕ} : ForGeneralPoints (𝕜 := 𝕜) r (m + 1) (fun p => ∀ k, p k ≠ 0) := by
  classical
  refine ⟨∏ k, X (k, 0), ?_, fun p hp k hk => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    exact fun k _ => X_ne_zero _
  · rw [map_prod, Finset.prod_ne_zero_iff] at hp
    simpa [hk] using hp k (Finset.mem_univ _)

end ForGeneralPoints

end VeroneseForms
