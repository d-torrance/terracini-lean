import TerraciniLemma.PolynomialCalculus
import TerraciniLemma.Defect
import Mathlib.Data.Sym.Card

/-!
# Degree-`d` Veronese ambient space `v_d(ℙⁿ) ⊂ ℙ^N`, and non-defectivity for `d ≥ 3`, `r ≤ n+1`

This file generalizes `TerraciniLemma.VeroneseGeneral` (the `d = 2` quadratic Veronese,
indexed by `Sym2 (Fin (n+1))`) to an arbitrary degree `d ≥ 1`, modeling the ambient space
`𝕜^{N+1}` of degree-`d` forms in `n+1` variables as `Sym (Fin (n+1)) d → 𝕜` (one coordinate
per size-`d` multiset of variable indices, i.e. per monomial `∏ᵢ Xᵢ`). By
`Sym.card_sym_eq_choose`, `Fintype.card (Sym (Fin (n+1)) d) = (n+d).choose d`, matching
`N + 1 = binom(n+d,d)`.

For `r ≤ n + 1` general points, taken (as in `VeroneseGeneral`) to be the `r` standard basis
points `e₀, …, e_{r-1}`, the tangent space at `eₖ` always has dimension `n+1` (for any
`d ≥ 1`). For `d = 2` the `r` tangent spaces overlap pairwise in exactly one coordinate
(`VeroneseGeneral`'s `badPairs` story), giving the classical defect for `2 ≤ r ≤ n`. For
`d ≥ 3`, by contrast, the `r` tangent spaces have **pairwise disjoint supports**, so their
combined span is a direct sum of dimension `r(n+1)` — exactly the expected dimension, so
`σ_r(v_d(ℙⁿ))` is *never* defective for `r ≤ n+1` when `d ≥ 3` (the "easy half" of
Alexander–Hirschowitz: every defective case with `d ≥ 3` has `r > n+1`).
-/

noncomputable section VeroneseDegreeExample

open MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-! ### §A — Ambient space -/

/-- The monomial `∏ᵢ Xᵢ`, indexed by the multiset `s` of variable indices (with multiplicity),
whose common evaluation map `𝕜^{n+1} → (Sym (Fin (n+1)) d → 𝕜)` parametrizes the affine cone
over the degree-`d` Veronese `v_d(ℙⁿ)`. -/
def veroneseDegPoly (n d : ℕ) (s : Sym (Fin (n + 1)) d) : MvPolynomial (Fin (n + 1)) 𝕜 :=
  (Multiset.map X s.val).prod

/-- The cone parametrization `v ↦ (∏ᵢ vᵢ)_{i ∈ s}`, viewed as a map
`𝕜^{n+1} → (Sym (Fin (n+1)) d → 𝕜)`. -/
def veroneseDeg (n d : ℕ) (v : Fin (n + 1) → 𝕜) (s : Sym (Fin (n + 1)) d) : 𝕜 :=
  eval v (veroneseDegPoly n d s)

omit [CharZero 𝕜] in
/-- The ambient space `Sym (Fin (n+1)) d → 𝕜` has dimension `(n+d).choose d`, matching
`binom(n+d,d) = N + 1` for `v_d(ℙⁿ) ⊂ ℙ^N`. -/
theorem finrank_ambient_veroneseDeg (n d : ℕ) :
    Module.finrank 𝕜 (Sym (Fin (n + 1)) d → 𝕜) = (n + d).choose d := by
  rw [Module.finrank_fintype_fun_eq_card, Sym.card_sym_eq_choose, Fintype.card_fin]
  congr 1
  omega

/-! ### §B — Derivative, in closed form -/

omit [CharZero 𝕜] in
private theorem eval_multisetMapProdX (n : ℕ) (s : Multiset (Fin (n + 1))) (v : Fin (n + 1) → 𝕜) :
    eval v (Multiset.map X s).prod = (Multiset.map v s).prod := by
  rw [map_multiset_prod, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl (fun i _ => eval_X i)

omit [CharZero 𝕜] in
/-- The `k`-th partial derivative of `∏_{i ∈ s} Xᵢ`, evaluated at `v`, is `(count of k in s)`
times the product of `v i` over the multiset `s` with one copy of `k` removed. -/
theorem eval_pderiv_multisetMapProdX (n : ℕ) (s : Multiset (Fin (n + 1)))
    (v : Fin (n + 1) → 𝕜) (k : Fin (n + 1)) :
    eval v (pderiv k (Multiset.map X s).prod : MvPolynomial (Fin (n + 1)) 𝕜)
      = (s.count k) * (Multiset.map v (s.erase k)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s' ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, pderiv_mul, map_add, map_mul, map_mul,
      eval_multisetMapProdX, eval_X, ih, Multiset.count_cons]
    simp only [pderiv_X, Pi.single_apply, apply_ite (eval v), map_zero, map_one]
    by_cases hak : a = k
    · subst hak
      rw [Multiset.erase_cons_head, if_pos rfl, if_pos rfl]
      rcases Nat.eq_zero_or_pos (s'.count a) with h0 | hpos
      · simp [h0]
      · obtain ⟨t, ht⟩ := Multiset.exists_cons_of_mem (Multiset.count_pos.mp hpos)
        rw [ht, Multiset.map_cons, Multiset.prod_cons, Multiset.erase_cons_head,
          Multiset.count_cons_self]
        push_cast
        ring
    · rw [Multiset.erase_cons_tail s' hak, Multiset.map_cons, Multiset.prod_cons,
        if_neg hak, if_neg (Ne.symm hak)]
      push_cast
      ring

/-- The derivative of `veroneseDeg n d` at `v`, as a continuous linear map
`𝕜^{n+1} →L[𝕜] (Sym (Fin (n+1)) d → 𝕜)`. -/
def veroneseDegDeriv (n d : ℕ) (v : Fin (n + 1) → 𝕜) :
    (Fin (n + 1) → 𝕜) →L[𝕜] (Sym (Fin (n + 1)) d → 𝕜) :=
  ContinuousLinearMap.pi (fun s => mvPolynomialDeriv (veroneseDegPoly n d s) v)

omit [CharZero 𝕜] in
/-- `veroneseDegDeriv n d v` is the Fréchet derivative of `veroneseDeg n d` at `v`. -/
theorem hasFDerivAt_veroneseDeg (n d : ℕ) (v : Fin (n + 1) → 𝕜) :
    HasFDerivAt (veroneseDeg n d) (veroneseDegDeriv n d v) v := by
  apply (hasFDerivAt_pi (φ := fun s y => eval y (veroneseDegPoly n d s))
    (φ' := fun s => mvPolynomialDeriv (veroneseDegPoly n d s) v) (x := v)).2
  intro s
  exact hasFDerivAt_eval_mvPolynomial (veroneseDegPoly n d s) v

omit [CharZero 𝕜] in
/-- Closed form for `veroneseDegDeriv n d v dv`, evaluated at `s`, as an explicit sum over
variable indices `k`. -/
theorem veroneseDegDeriv_apply (n d : ℕ) (v dv : Fin (n + 1) → 𝕜) (s : Sym (Fin (n + 1)) d) :
    veroneseDegDeriv n d v dv s
      = ∑ k : Fin (n + 1), (s.val.count k : 𝕜) * (Multiset.map v (s.val.erase k)).prod * dv k := by
  simp only [veroneseDegDeriv, ContinuousLinearMap.pi_apply, mvPolynomialDeriv, veroneseDegPoly,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, coordProj_apply, smul_eq_mul,
    eval_pderiv_multisetMapProdX]

omit [CharZero 𝕜] in
/-- The image of a multiset `t` under `Pi.single a 1`, multiplied together, is `1` if every
element of `t` equals `a`, and `0` otherwise. -/
private theorem prod_map_single (n : ℕ) (t : Multiset (Fin (n + 1))) (a : Fin (n + 1)) :
    (Multiset.map (Pi.single a (1 : 𝕜)) t).prod = if ∀ x ∈ t, x = a then 1 else 0 := by
  split_ifs with h
  · rw [Multiset.map_congr rfl (fun x hx => by rw [h x hx, Pi.single_eq_same])]
    simp
  · push Not at h
    obtain ⟨b, hb, hba⟩ := h
    exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨b, hb, Pi.single_eq_of_ne hba 1⟩)

omit [CharZero 𝕜] in
/-- Closed form for `veroneseDegDeriv n d (Pi.single a 1) dv` at the "all `a`" monomial
`X_a^d`: it equals `d * dv a`. -/
theorem veroneseDegDeriv_apply_replicate (n d : ℕ) (hd : 1 ≤ d) (a : Fin (n + 1))
    (dv : Fin (n + 1) → 𝕜) :
    veroneseDegDeriv n d (Pi.single a 1) dv (Sym.replicate d a) = (d : 𝕜) * dv a := by
  rw [veroneseDegDeriv_apply, Finset.sum_eq_single a]
  · obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    rw [Sym.val_replicate, Multiset.count_replicate, if_pos rfl, Multiset.replicate_succ,
      Multiset.erase_cons_head, prod_map_single,
      if_pos (fun x hx => Multiset.eq_of_mem_replicate hx)]
    push_cast
    ring
  · intro k _ hk
    rw [Sym.val_replicate, Multiset.count_replicate, if_neg (Ne.symm hk)]
    push_cast
    ring
  · simp

/-- The element of `Sym (Fin (n+1)) d` (for `1 ≤ d`) consisting of one copy of `j` and `d - 1`
copies of `a`. -/
def veroneseDegElt (n d : ℕ) (hd : 1 ≤ d) (a j : Fin (n + 1)) : Sym (Fin (n + 1)) d :=
  ⟨j ::ₘ Multiset.replicate (d - 1) a, by
    rw [Multiset.card_cons, Multiset.card_replicate]; omega⟩

theorem veroneseDegElt_val (n d : ℕ) (hd : 1 ≤ d) (a j : Fin (n + 1)) :
    (veroneseDegElt n d hd a j).val = j ::ₘ Multiset.replicate (d - 1) a := rfl

omit [CharZero 𝕜] in
/-- Closed form for `veroneseDegDeriv n d (Pi.single a 1) dv` at the monomial `Xⱼ Xₐ^{d-1}`
(`j ≠ a`): it equals `dv j`. -/
theorem veroneseDegDeriv_apply_cons (n d : ℕ) (hd : 1 ≤ d) (a j : Fin (n + 1)) (hj : j ≠ a)
    (dv : Fin (n + 1) → 𝕜) :
    veroneseDegDeriv n d (Pi.single a 1) dv (veroneseDegElt n d hd a j) = dv j := by
  rw [veroneseDegDeriv_apply]
  rw [Finset.sum_eq_single j]
  · rw [veroneseDegElt_val, Multiset.count_cons_self, Multiset.count_replicate,
      if_neg (Ne.symm hj), Multiset.erase_cons_head, prod_map_single,
      if_pos (fun x hx => Multiset.eq_of_mem_replicate hx)]
    push_cast
    ring
  · intro k _ hk
    rw [veroneseDegElt_val]
    by_cases hka : k = a
    · have hmem : j ∈ (j ::ₘ Multiset.replicate (d - 1) a).erase k := by
        rw [hka]
        exact (Multiset.mem_erase_of_ne hj).mpr (Multiset.mem_cons_self j _)
      have hnall : ¬ (∀ x ∈ (j ::ₘ Multiset.replicate (d - 1) a).erase k, x = a) :=
        fun hcon => hj (hcon j hmem)
      rw [prod_map_single, if_neg hnall]
      ring
    · rw [Multiset.count_cons, Multiset.count_replicate, if_neg (Ne.symm hka), if_neg hk]
      push_cast
      ring
  · simp

omit [CharZero 𝕜] in
/-- For any `s` that is neither the "all `a`" monomial `X_a^d` nor a monomial `Xⱼ Xₐ^{d-1}`
(`j ≠ a`), the derivative `veroneseDegDeriv n d (Pi.single a 1) dv s` vanishes. -/
theorem veroneseDegDeriv_apply_eq_zero (n d : ℕ) (hd : 1 ≤ d) (a : Fin (n + 1))
    (s : Sym (Fin (n + 1)) d) (h1 : s ≠ Sym.replicate d a)
    (h2 : ∀ j, j ≠ a → s ≠ veroneseDegElt n d hd a j) (dv : Fin (n + 1) → 𝕜) :
    veroneseDegDeriv n d (Pi.single a 1) dv s = 0 := by
  rw [veroneseDegDeriv_apply]
  apply Finset.sum_eq_zero
  intro k _
  by_cases hk : k ∈ s.val
  · rw [prod_map_single]
    by_cases hall : ∀ x ∈ s.val.erase k, x = a
    · exfalso
      have hcons : s.val = k ::ₘ Multiset.replicate (d - 1) a := by
        have herase : s.val.erase k = Multiset.replicate (d - 1) a :=
          Multiset.eq_replicate.mpr
            ⟨by rw [Multiset.card_erase_of_mem hk, s.2, Nat.pred_eq_sub_one], hall⟩
        rw [← herase, Multiset.cons_erase hk]
      by_cases hka : k = a
      · have hall_s : ∀ b ∈ s.val, b = a := by
          intro b hb
          rw [← Multiset.cons_erase hk] at hb
          rcases Multiset.mem_cons.mp hb with h | h
          · rw [h, hka]
          · exact hall b h
        exact h1 (Subtype.ext
          ((Multiset.eq_replicate.mpr ⟨s.2, hall_s⟩).trans (Sym.val_replicate).symm))
      · exact h2 k hka (Subtype.ext (hcons.trans (veroneseDegElt_val n d hd a k).symm))
    · rw [if_neg hall]
      ring
  · rw [Multiset.count_eq_zero.mpr hk]
    simp

/-- A multiset all of whose element-counts are `≤ b < d` can't be the "all `a`" monomial
`Sym.replicate d a` (which has count `d` at `a`). -/
theorem ne_replicate_of_count_le {n d : ℕ} (s : Sym (Fin (n + 1)) d) (b : ℕ)
    (hb : ∀ x, s.val.count x ≤ b) (hbd : b < d) (a : Fin (n + 1)) :
    s ≠ Sym.replicate d a := by
  intro h
  have := hb a
  rw [h, Sym.val_replicate, Multiset.count_replicate, if_pos rfl] at this
  omega

/-- A multiset all of whose element-counts are `≤ b < d - 1` can't be a monomial
`Xⱼ Xₐ^{d-1}` (`j ≠ a`, which has count `d - 1` at `a`). -/
theorem ne_veroneseDegElt_of_count_le {n d : ℕ} (hd : 1 ≤ d) (s : Sym (Fin (n + 1)) d) (b : ℕ)
    (hb : ∀ x, s.val.count x ≤ b) (hbd : b < d - 1) (a j : Fin (n + 1)) (hj : j ≠ a) :
    s ≠ veroneseDegElt n d hd a j := by
  intro h
  have := hb a
  rw [h, veroneseDegElt_val, Multiset.count_cons, Multiset.count_replicate, if_pos rfl,
    if_neg (Ne.symm hj)] at this
  omega

/-! ### §C — `r` points, tangent space dimension `n+1` -/

/-- Closed form for `veroneseDegDeriv n d v dv` at the monomial `X_a^d`, for arbitrary `v`
(not just `Pi.single a 1`). -/
theorem veroneseDegDeriv_apply_replicate' (n d : ℕ) (hd : 1 ≤ d) (a : Fin (n + 1))
    (v dv : Fin (n + 1) → 𝕜) :
    veroneseDegDeriv n d v dv (Sym.replicate d a) = (d : 𝕜) * (v a) ^ (d - 1) * dv a := by
  rw [veroneseDegDeriv_apply, Finset.sum_eq_single a]
  · rw [Sym.val_replicate, Multiset.count_replicate, if_pos rfl]
    obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
    rw [Multiset.replicate_succ, Multiset.erase_cons_head, Multiset.map_replicate,
      Multiset.prod_replicate]
    simp
  · intro k _ hk
    rw [Sym.val_replicate, Multiset.count_replicate, if_neg (Ne.symm hk)]
    push_cast
    ring
  · simp

/-- If every coordinate of `v` is nonzero, `veroneseDegDeriv n d v` is injective — so the
tangent space at `v` has the maximal possible dimension `n+1`. -/
theorem veroneseDegDeriv_injective_of_ne_zero (n d : ℕ) (hd : 1 ≤ d) (v : Fin (n + 1) → 𝕜)
    (hv : ∀ a, v a ≠ 0) : Function.Injective (veroneseDegDeriv n d v) := by
  intro dv₁ dv₂ heq
  rw [← sub_eq_zero, ← map_sub] at heq
  rw [← sub_eq_zero]
  funext a
  have h := congrFun heq (Sym.replicate d a)
  rw [veroneseDegDeriv_apply_replicate' n d hd a] at h
  simp only [Pi.sub_apply, Pi.zero_apply] at h ⊢
  have hd0 : (d : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hva0 : (v a) ^ (d - 1) ≠ 0 := pow_ne_zero _ (hv a)
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero hd0 hva0)

/-- At any point `v` with every coordinate nonzero, the tangent space has the maximal possible
dimension `n+1`. -/
theorem finrank_tangentSpace_of_ne_zero (n d : ℕ) (hd : 1 ≤ d) (v : Fin (n + 1) → 𝕜)
    (hv : ∀ a, v a ≠ 0) :
    Module.finrank 𝕜 (LinearMap.range (veroneseDegDeriv (𝕜 := 𝕜) n d v).toLinearMap) = n + 1 := by
  have hinj' : Function.Injective (veroneseDegDeriv (𝕜 := 𝕜) n d v).toLinearMap :=
    veroneseDegDeriv_injective_of_ne_zero n d hd v hv
  rw [LinearMap.finrank_range_of_inj hinj', Module.finrank_pi, Fintype.card_fin]

/-- At any coordinate point `eₐ` (for any `a`, with no constraint `r ≤ n+1`),
`veroneseDegDeriv n d (Pi.single a 1)` is injective — so its tangent space has the maximal
possible dimension `n+1`. -/
theorem veroneseDegDeriv_injective_single (n d : ℕ) (hd : 1 ≤ d) (a : Fin (n + 1)) :
    Function.Injective (veroneseDegDeriv (𝕜 := 𝕜) n d (Pi.single a 1)) := by
  intro dv₁ dv₂ heq
  rw [← sub_eq_zero, ← map_sub] at heq
  rw [← sub_eq_zero]
  funext j
  by_cases hja : j = a
  · rw [hja]
    have hr1 := congrFun heq (Sym.replicate d a)
    rw [veroneseDegDeriv_apply_replicate n d hd a] at hr1
    have hd0 : (d : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    exact (mul_eq_zero.mp hr1).resolve_left hd0
  · have hr2 := congrFun heq (veroneseDegElt n d hd a j)
    rwa [veroneseDegDeriv_apply_cons n d hd a j hja] at hr2

/-- The tangent space at any coordinate point `eₐ` has dimension `n+1`. -/
theorem finrank_tangentSpace_single (n d : ℕ) (hd : 1 ≤ d) (a : Fin (n + 1)) :
    Module.finrank 𝕜
      (LinearMap.range (veroneseDegDeriv (𝕜 := 𝕜) n d (Pi.single a 1)).toLinearMap) = n + 1 := by
  have hinj' : Function.Injective (veroneseDegDeriv (𝕜 := 𝕜) n d (Pi.single a 1)).toLinearMap :=
    veroneseDegDeriv_injective_single n d hd a
  rw [LinearMap.finrank_range_of_inj hinj', Module.finrank_pi, Fintype.card_fin]

omit [CharZero 𝕜] in
/-- The `k`-th standard basis point `eₖ ∈ 𝕜^{n+1}`, for `k : Fin r` cast into `Fin (n+1)` via
`hr : r ≤ n + 1`. -/
def veroneseDegPt (n r : ℕ) (hr : r ≤ n + 1) (k : Fin r) : Fin (n + 1) → 𝕜 :=
  Pi.single (Fin.castLE hr k) 1

omit [CharZero 𝕜] in
/-- The local parametrization of `veroneseDeg n d` at parameter `v`. -/
def veroneseDegParam (n d : ℕ) (v : Fin (n + 1) → 𝕜) :
    LocalParam (𝕜 := 𝕜) (𝔸 := Fin (n + 1) → 𝕜)
      (Set.range (veroneseDeg n d)) (veroneseDeg n d v) where
  basePoint := v
  chart := veroneseDeg n d
  chart_eval := rfl
  tangent := veroneseDegDeriv n d v
  hasFDerivAt := hasFDerivAt_veroneseDeg n d v

omit [CharZero 𝕜] in
/-- The family of `r` local parametrizations of `veroneseDeg n d` at the `r` standard basis
points `e₀, …, e_{r-1}`. -/
def veroneseDegFamily (n d r : ℕ) (hr : r ≤ n + 1) (k : Fin r) :
    LocalParam (𝕜 := 𝕜) (𝔸 := Fin (n + 1) → 𝕜)
      (Set.range (veroneseDeg n d)) (veroneseDeg n d (veroneseDegPt (𝕜 := 𝕜) n r hr k)) :=
  veroneseDegParam n d (veroneseDegPt (𝕜 := 𝕜) n r hr k)

/-- Each of the `r` tangent spaces `T_{eₖ^{⊗d}} X̂` has dimension `n + 1`. -/
theorem finrank_tangentSpace_veroneseDegFamily (n d r : ℕ) (hd : 1 ≤ d) (hr : r ≤ n + 1)
    (k : Fin r) :
    Module.finrank 𝕜 (veroneseDegFamily (𝕜 := 𝕜) n d r hr k).tangentSpace = n + 1 := by
  show Module.finrank 𝕜
      (LinearMap.range (veroneseDegDeriv n d (Pi.single (Fin.castLE hr k) (1 : 𝕜))).toLinearMap)
      = n + 1
  exact finrank_tangentSpace_single n d hd (Fin.castLE hr k)

/-! ### §D — Disjoint supports, direct sum, non-defectivity for `d ≥ 3` -/

omit [CharZero 𝕜] in
/-- `veroneseDegElt n d hd a a` is the "all `a`" monomial. -/
theorem veroneseDegElt_self (n d : ℕ) (hd : 1 ≤ d) (a : Fin (n + 1)) :
    veroneseDegElt n d hd a a = Sym.replicate d a := by
  apply Subtype.ext
  rw [veroneseDegElt_val, Sym.val_replicate]
  obtain ⟨d', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  simp [Multiset.replicate_succ]

omit [CharZero 𝕜] in
theorem veroneseDegElt_injective (n d : ℕ) (hd : 1 ≤ d) (a : Fin (n + 1)) :
    Function.Injective (veroneseDegElt n d hd a) := by
  intro j j' heq
  have hcount := congrArg (fun s => Multiset.count j s.val) heq
  simp only [veroneseDegElt_val, Multiset.count_cons] at hcount
  by_contra hne
  rw [if_neg hne] at hcount
  simp at hcount

/-- The `n+1`-element support of the tangent space at `eₐ`: the monomials `X_a^d` and
`Xⱼ Xₐ^{d-1}` for `j ≠ a`. -/
def veroneseDegSupport (n d : ℕ) (hd : 1 ≤ d) (a : Fin (n + 1)) : Finset (Sym (Fin (n + 1)) d) :=
  Finset.image (veroneseDegElt n d hd a) Finset.univ

omit [CharZero 𝕜] in
theorem card_veroneseDegSupport (n d : ℕ) (hd : 1 ≤ d) (a : Fin (n + 1)) :
    (veroneseDegSupport n d hd a).card = n + 1 := by
  rw [veroneseDegSupport, Finset.card_image_of_injective _ (veroneseDegElt_injective n d hd a),
    Finset.card_univ, Fintype.card_fin]

omit [CharZero 𝕜] in
theorem mem_veroneseDegSupport_iff (n d : ℕ) (hd : 1 ≤ d) (a : Fin (n + 1))
    (s : Sym (Fin (n + 1)) d) :
    s ∈ veroneseDegSupport n d hd a
      ↔ s = Sym.replicate d a ∨ ∃ j, j ≠ a ∧ s = veroneseDegElt n d hd a j := by
  simp only [veroneseDegSupport, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, rfl⟩
    by_cases hj : j = a
    · rw [hj]; exact Or.inl (veroneseDegElt_self n d hd a)
    · exact Or.inr ⟨j, hj, rfl⟩
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact ⟨a, veroneseDegElt_self n d hd a⟩
    · exact ⟨j, rfl⟩

omit [CharZero 𝕜] in
/-- For `d ≥ 3`, the supports of the tangent spaces at `eₐ` and `eₐ'` (`a ≠ a'`) are disjoint. -/
theorem disjoint_veroneseDegSupport (n d : ℕ) (hd : 3 ≤ d) {a a' : Fin (n + 1)} (hne : a ≠ a') :
    Disjoint (veroneseDegSupport n d (by omega) a) (veroneseDegSupport n d (by omega) a') := by
  rw [Finset.disjoint_left]
  intro s hsa hsa'
  simp only [veroneseDegSupport, Finset.mem_image, Finset.mem_univ, true_and] at hsa hsa'
  obtain ⟨j, rfl⟩ := hsa
  obtain ⟨j', hj'⟩ := hsa'
  have hcount := congrArg (fun t => Multiset.count a t.val) hj'
  simp only [veroneseDegElt_val, Multiset.count_cons, Multiset.count_replicate] at hcount
  split_ifs at hcount <;> omega

omit [CharZero 𝕜] in
theorem veroneseDegDeriv_apply_eq_zero_of_notMem (n d : ℕ) (hd : 1 ≤ d) (a : Fin (n + 1))
    (s : Sym (Fin (n + 1)) d) (hs : s ∉ veroneseDegSupport n d hd a) (dv : Fin (n + 1) → 𝕜) :
    veroneseDegDeriv n d (Pi.single a 1) dv s = 0 := by
  rw [mem_veroneseDegSupport_iff, not_or] at hs
  exact veroneseDegDeriv_apply_eq_zero n d hd a s hs.1 (fun j hj hcon => hs.2 ⟨j, hj, hcon⟩) dv

omit [CharZero 𝕜] in
/-- The union of the `r` supports `veroneseDegSupport n d hd (eₖ)`, `k : Fin r`. -/
def veroneseDegGoodElts (n d r : ℕ) (hd : 1 ≤ d) (hr : r ≤ n + 1) : Finset (Sym (Fin (n + 1)) d) :=
  Finset.univ.biUnion (fun k : Fin r => veroneseDegSupport n d hd (Fin.castLE hr k))

omit [CharZero 𝕜] in
/-- The combined tangent space: functions vanishing outside `veroneseDegGoodElts n d r hd hr`. -/
def veroneseDegTangentSum (n d r : ℕ) (hd : 1 ≤ d) (hr : r ≤ n + 1) :
    Submodule 𝕜 (Sym (Fin (n + 1)) d → 𝕜) :=
  ⨅ s ∈ (veroneseDegGoodElts n d r hd hr)ᶜ,
    LinearMap.ker (LinearMap.proj s : (Sym (Fin (n + 1)) d → 𝕜) →ₗ[𝕜] 𝕜)

omit [CharZero 𝕜] in
theorem mem_veroneseDegTangentSum {n d r : ℕ} {hd : 1 ≤ d} {hr : r ≤ n + 1}
    (f : Sym (Fin (n + 1)) d → 𝕜) :
    f ∈ veroneseDegTangentSum n d r hd hr
      ↔ ∀ s, s ∉ veroneseDegGoodElts n d r hd hr → f s = 0 := by
  simp [veroneseDegTangentSum, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply,
    Finset.mem_compl]

omit [CharZero 𝕜] in
/-- Closed form for the combined derivative of the `r`-point family. -/
theorem combinedDerivative_veroneseDeg_apply (n d r : ℕ) (hr : r ≤ n + 1)
    (w : Fin r → Fin (n + 1) → 𝕜) (s : Sym (Fin (n + 1)) d) :
    combinedDerivative (veroneseDegFamily (𝕜 := 𝕜) n d r hr) w s
      = ∑ k : Fin r, veroneseDegDeriv n d (veroneseDegPt (𝕜 := 𝕜) n r hr k) (w k) s := by
  simp [combinedDerivative, veroneseDegFamily, veroneseDegParam, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, coordProj_apply, Finset.sum_apply]

/-- **The combined tangent space of the `r ≤ n+1` coordinate points, for `d ≥ 3`,** is exactly
`veroneseDegTangentSum n d r _ hr`: the functions supported on the union of the `r` pairwise
disjoint blocks `veroneseDegSupport n d _ (eₖ)`. -/
theorem range_combinedDerivative_veroneseDeg (n d r : ℕ) (hd : 3 ≤ d) (hr : r ≤ n + 1) :
    LinearMap.range (combinedDerivative (veroneseDegFamily (𝕜 := 𝕜) n d r hr)).toLinearMap
      = veroneseDegTangentSum n d r (by omega) hr := by
  have hd1 : 1 ≤ d := by omega
  apply le_antisymm
  · rintro f ⟨w, rfl⟩
    rw [mem_veroneseDegTangentSum]
    intro s hs
    show combinedDerivative (veroneseDegFamily (𝕜 := 𝕜) n d r hr) w s = 0
    rw [combinedDerivative_veroneseDeg_apply]
    apply Finset.sum_eq_zero
    intro k _
    apply veroneseDegDeriv_apply_eq_zero_of_notMem n d hd1 (Fin.castLE hr k) s
    intro hmem
    exact hs (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hmem⟩)
  · intro f hf
    rw [mem_veroneseDegTangentSum] at hf
    set w : Fin r → Fin (n + 1) → 𝕜 := fun k j =>
      if j = Fin.castLE hr k then f (Sym.replicate d (Fin.castLE hr k)) / d
      else f (veroneseDegElt n d hd1 (Fin.castLE hr k) j) with hw
    refine ⟨w, ?_⟩
    funext s
    show combinedDerivative (veroneseDegFamily (𝕜 := 𝕜) n d r hr) w s = f s
    rw [combinedDerivative_veroneseDeg_apply]
    by_cases hgood : s ∈ veroneseDegGoodElts n d r hd1 hr
    · obtain ⟨k₀, _, hk₀⟩ := Finset.mem_biUnion.mp hgood
      rw [Finset.sum_eq_single k₀]
      · rcases (mem_veroneseDegSupport_iff n d hd1 (Fin.castLE hr k₀) s).mp hk₀ with
          hrep | ⟨j, hj, hej⟩
        · rw [hrep]
          show (veroneseDegDeriv n d (Pi.single (Fin.castLE hr k₀) 1)) (w k₀)
              (Sym.replicate d (Fin.castLE hr k₀)) = f (Sym.replicate d (Fin.castLE hr k₀))
          rw [veroneseDegDeriv_apply_replicate n d hd1 (Fin.castLE hr k₀)]
          have hwk : w k₀ (Fin.castLE hr k₀) = f (Sym.replicate d (Fin.castLE hr k₀)) / d := by
            simp [hw]
          have hd0 : (d : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
          rw [hwk, mul_comm, div_mul_cancel₀ _ hd0]
        · rw [hej]
          show (veroneseDegDeriv n d (Pi.single (Fin.castLE hr k₀) 1)) (w k₀)
              (veroneseDegElt n d hd1 (Fin.castLE hr k₀) j)
              = f (veroneseDegElt n d hd1 (Fin.castLE hr k₀) j)
          rw [veroneseDegDeriv_apply_cons n d hd1 (Fin.castLE hr k₀) j hj, hw]
          simp only [if_neg hj]
      · intro k _ hk
        apply veroneseDegDeriv_apply_eq_zero_of_notMem n d hd1 (Fin.castLE hr k) s
        intro hmem
        exact Finset.disjoint_left.mp
          (disjoint_veroneseDegSupport n d hd (fun hc => hk (Fin.castLE_injective hr hc)))
          hmem hk₀
      · exact fun h => absurd (Finset.mem_univ k₀) h
    · rw [hf s hgood]
      apply Finset.sum_eq_zero
      intro k _
      apply veroneseDegDeriv_apply_eq_zero_of_notMem n d hd1 (Fin.castLE hr k) s
      intro hmem
      exact hgood (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ k, hmem⟩)

omit [CharZero 𝕜] in
/-- **Dimension count.** `veroneseDegTangentSum n d r _ hr` has dimension `(n+d).choose d -
(veroneseDegGoodElts n d r _ hr)ᶜ.card`. -/
theorem finrank_veroneseDegTangentSum (n d r : ℕ) (hd : 1 ≤ d) (hr : r ≤ n + 1) :
    Module.finrank 𝕜 (veroneseDegTangentSum (𝕜 := 𝕜) n d r hd hr)
      = (n + d).choose d - (veroneseDegGoodElts n d r hd hr)ᶜ.card := by
  classical
  set g : (Sym (Fin (n + 1)) d → 𝕜) →ₗ[𝕜]
      (↥((veroneseDegGoodElts n d r hd hr)ᶜ) → 𝕜) :=
    LinearMap.funLeft 𝕜 𝕜
      (Subtype.val : ↥((veroneseDegGoodElts n d r hd hr)ᶜ) → _)
    with hg
  have hker : LinearMap.ker g = veroneseDegTangentSum n d r hd hr := by
    ext f
    rw [LinearMap.mem_ker, mem_veroneseDegTangentSum]
    constructor
    · intro hfz s hs
      have h := congrFun hfz ⟨s, by simpa using hs⟩
      simpa using h
    · intro hfz
      funext p
      obtain ⟨s, hs⟩ := p
      simp only [hg, LinearMap.funLeft_apply, Pi.zero_apply]
      exact hfz s (by simpa using hs)
  have hsurj : Function.Surjective g :=
    LinearMap.funLeft_surjective_of_injective 𝕜 𝕜 _ Subtype.val_injective
  have hrange : LinearMap.range g = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange, hker, finrank_top, finrank_ambient_veroneseDeg, Module.finrank_pi,
    Fintype.card_coe] at hrn
  omega

omit [CharZero 𝕜] in
/-- For `d ≥ 3`, the `r` supports `veroneseDegSupport n d _ (eₖ)` (`k : Fin r`) are pairwise
disjoint and each has size `n+1`, so their union has size `r * (n+1)`. -/
theorem card_veroneseDegGoodElts (n d r : ℕ) (hd : 3 ≤ d) (hr : r ≤ n + 1) :
    (veroneseDegGoodElts n d r (by omega) hr).card = r * (n + 1) := by
  rw [veroneseDegGoodElts, Finset.card_biUnion
    (fun k _ k' _ hkk' => disjoint_veroneseDegSupport n d hd
      (fun hc => hkk' (Fin.castLE_injective hr hc)))]
  simp [card_veroneseDegSupport n d (show 1 ≤ d by omega)]

/-- **Dimension of the combined tangent space** of the `r` coordinate points, for `d ≥ 3`: it is
exactly `r * (n+1)`, the sum of the `r` individual tangent-space dimensions (no overlap). -/
theorem finrank_iSup_veroneseDeg (n d r : ℕ) (hd : 3 ≤ d) (hr : r ≤ n + 1) :
    Module.finrank 𝕜 (⨆ k, (veroneseDegFamily (𝕜 := 𝕜) n d r hr k).tangentSpace :
      Submodule 𝕜 (Sym (Fin (n + 1)) d → 𝕜)) = r * (n + 1) := by
  have hcard_sym : Fintype.card (Sym (Fin (n + 1)) d) = (n + d).choose d := by
    rw [Sym.card_sym_eq_choose, Fintype.card_fin]
    congr 1
    omega
  have hle : r * (n + 1) ≤ (n + d).choose d := by
    rw [← hcard_sym, ← card_veroneseDegGoodElts n d r hd hr]
    exact Finset.card_le_univ _
  rw [show (⨆ k, (veroneseDegFamily (𝕜 := 𝕜) n d r hr k).tangentSpace :
        Submodule 𝕜 (Sym (Fin (n + 1)) d → 𝕜))
      = LinearMap.range (combinedDerivative (veroneseDegFamily (𝕜 := 𝕜) n d r hr)).toLinearMap
    from (range_combinedParam_eq_iSup
      (fun k => (veroneseDegFamily (𝕜 := 𝕜) n d r hr k).tangent)).symm,
    range_combinedDerivative_veroneseDeg n d r hd hr, finrank_veroneseDegTangentSum,
    Finset.card_compl, hcard_sym, card_veroneseDegGoodElts n d r hd hr]
  omega

/-- **Expected dimension** of the `r`-point family: `min((n+d).choose d, r * (n+1))`. -/
theorem expectedDim_veroneseDeg (n d r : ℕ) (hd : 1 ≤ d) (hr : r ≤ n + 1) :
    expectedDim (fun k : Fin r => (veroneseDegFamily (𝕜 := 𝕜) n d r hr k).tangentSpace)
      = min ((n + d).choose d) (r * (n + 1)) := by
  unfold expectedDim
  rw [finrank_ambient_veroneseDeg, Finset.sum_congr rfl
    (fun k _ => finrank_tangentSpace_veroneseDegFamily n d r hd hr k)]
  simp

/-- **Main result.** For `d ≥ 3` and `r ≤ n+1` coordinate points, `σ_r(v_d(ℙⁿ))` is *not*
Alexander–Hirschowitz defective: the combined tangent space achieves the expected dimension
`r * (n+1)` exactly. -/
theorem veroneseDeg_not_isDefective (n d r : ℕ) (hd : 3 ≤ d) (hr : r ≤ n + 1) :
    ¬ IsDefective (fun k : Fin r => (veroneseDegFamily (𝕜 := 𝕜) n d r hr k).tangentSpace) := by
  have hle : r * (n + 1) ≤ (n + d).choose d := by
    rw [← finrank_iSup_veroneseDeg (𝕜 := 𝕜) n d r hd hr, ← finrank_ambient_veroneseDeg (𝕜 := 𝕜) n d]
    exact Submodule.finrank_le _
  unfold IsDefective
  rw [finrank_iSup_veroneseDeg (𝕜 := 𝕜) n d r hd hr, expectedDim_veroneseDeg n d r (by omega) hr,
    min_eq_right hle]
  exact lt_irrefl _

end VeroneseDegreeExample
