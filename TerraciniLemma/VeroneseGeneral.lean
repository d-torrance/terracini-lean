import TerraciniLemma.PolynomialCalculus
import TerraciniLemma.Defect
import Mathlib.Data.Sym.Card

/-!
# General quadric Veronese `v₂(ℙⁿ) ⊂ ℙ^N`

This file generalizes `TerraciniLemma.VeroneseSurface` (the `n = 2`, `r = 2` case) to the
affine cone over `v₂(ℙⁿ) ⊂ ℙ^N`, `N = binom(n+2,2) - 1`, for an arbitrary number `r ≤ n + 1`
of general points.

The cone `X̂ ⊆ 𝕜^{N+1}` over `v₂(ℙⁿ)` is the set of rank-`≤ 1` symmetric `(n+1) × (n+1)`
matrices `v vᵗ`. We model the ambient space `𝕜^{N+1}` as `Sym2 (Fin (n+1)) → 𝕜`, one
coordinate per unordered pair `{i, j}` (including `i = j`), representing the entries of a
symmetric matrix. By `Sym2.card`, `Fintype.card (Sym2 (Fin (n+1))) = (n+2).choose 2`, matching
`N + 1 = binom(n+2,2)`.
-/

noncomputable section VeroneseGeneralExample

open MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-- The monomials `Xᵢ Xⱼ` indexed by unordered pairs `{i, j} : Sym2 (Fin (n+1))`, whose common
evaluation map `𝕜^{n+1} → (Sym2 (Fin (n+1)) → 𝕜)` parametrizes the affine cone `X̂` over the
quadric Veronese `v₂(ℙⁿ)`. -/
def veroneseGeneralPoly (n : ℕ) : Sym2 (Fin (n + 1)) → MvPolynomial (Fin (n + 1)) 𝕜 :=
  Sym2.lift ⟨fun i j => X i * X j, fun i j => mul_comm (X i) (X j)⟩

/-- The cone parametrization `v ↦ v vᵗ`, viewed as a map `𝕜^{n+1} → (Sym2 (Fin (n+1)) → 𝕜)`. -/
def veroneseGeneral (n : ℕ) (v : Fin (n + 1) → 𝕜) : Sym2 (Fin (n + 1)) → 𝕜 :=
  fun s => eval v (veroneseGeneralPoly n s)

omit [CharZero 𝕜] in
/-- The ambient space `Sym2 (Fin (n+1)) → 𝕜` has dimension `(n+2).choose 2`, matching
`binom(n+2,2) = N + 1` for `v₂(ℙⁿ) ⊂ ℙ^N`. -/
theorem finrank_ambient_veroneseGeneral (n : ℕ) :
    Module.finrank 𝕜 (Sym2 (Fin (n + 1)) → 𝕜) = (n + 2).choose 2 := by
  rw [Module.finrank_fintype_fun_eq_card, Sym2.card, Fintype.card_fin]

/-- The derivative of `veroneseGeneral n` at `v`, as a continuous linear map
`𝕜^{n+1} →L[𝕜] (Sym2 (Fin (n+1)) → 𝕜)`. -/
def veroneseGeneralDeriv (n : ℕ) (v : Fin (n + 1) → 𝕜) :
    (Fin (n + 1) → 𝕜) →L[𝕜] (Sym2 (Fin (n + 1)) → 𝕜) :=
  ContinuousLinearMap.pi (fun s => mvPolynomialDeriv (veroneseGeneralPoly n s) v)

omit [CharZero 𝕜] in
/-- `veroneseGeneralDeriv n v` is the Fréchet derivative of `veroneseGeneral n` at `v`. -/
theorem hasFDerivAt_veroneseGeneral (n : ℕ) (v : Fin (n + 1) → 𝕜) :
    HasFDerivAt (veroneseGeneral n) (veroneseGeneralDeriv n v) v := by
  apply (hasFDerivAt_pi (φ := fun s y => eval y (veroneseGeneralPoly n s))
    (φ' := fun s => mvPolynomialDeriv (veroneseGeneralPoly n s) v) (x := v)).2
  intro s
  exact hasFDerivAt_eval_mvPolynomial (veroneseGeneralPoly n s) v

omit [CharZero 𝕜] in
/-- Closed form for the formal derivative of the `{i, j}` monomial `Xᵢ Xⱼ`:
`dv ↦ vⱼ dvᵢ + vᵢ dvⱼ`. Holds also for `i = j`, where it gives `2 vᵢ dvᵢ`, the derivative of
`Xᵢ²`. -/
theorem mvPolynomialDeriv_veroneseGeneralPoly_mk (n : ℕ) (v : Fin (n + 1) → 𝕜) (i j : Fin (n + 1)) :
    mvPolynomialDeriv (veroneseGeneralPoly n (s(i, j) : Sym2 (Fin (n + 1)))) v
      = v j • coordProj (n + 1) i + v i • coordProj (n + 1) j := by
  classical
  have hpoly : veroneseGeneralPoly n (s(i, j) : Sym2 (Fin (n + 1)))
      = (X i * X j : MvPolynomial (Fin (n + 1)) 𝕜) := rfl
  have hterm : ∀ (k : Fin (n + 1)) (dv : Fin (n + 1) → 𝕜),
      eval v (pderiv k (X i * X j : MvPolynomial (Fin (n + 1)) 𝕜)) * dv k
        = (if i = k then v j * dv k else 0) + (if j = k then v i * dv k else 0) := by
    intro k dv
    simp only [pderiv_mul, map_add, map_mul, pderiv_X, Pi.single_apply, apply_ite, map_one,
      map_zero, eval_X]
    split_ifs <;> ring
  apply ContinuousLinearMap.ext
  intro dv
  rw [hpoly]
  simp only [mvPolynomialDeriv, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    coordProj_apply, smul_eq_mul, hterm, ContinuousLinearMap.add_apply]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq Finset.univ i (fun k => v j * dv k),
    Finset.sum_ite_eq Finset.univ j (fun k => v i * dv k)]
  simp

omit [CharZero 𝕜] in
/-- Closed form for `veroneseGeneralDeriv n v dv` evaluated at the pair `{i, j}`. -/
theorem veroneseGeneralDeriv_apply_mk (n : ℕ) (v dv : Fin (n + 1) → 𝕜) (i j : Fin (n + 1)) :
    veroneseGeneralDeriv n v dv (s(i, j) : Sym2 (Fin (n + 1))) = v j * dv i + v i * dv j := by
  rw [veroneseGeneralDeriv, ContinuousLinearMap.pi_apply, mvPolynomialDeriv_veroneseGeneralPoly_mk]
  simp

omit [CharZero 𝕜] in
/-- The `k`-th standard basis point `eₖ ∈ 𝕜^{n+1}`, for `k : Fin r` cast into `Fin (n+1)` via
`hr : r ≤ n + 1`. The corresponding cone point `veroneseGeneral n (veroneseGeneralPt (𝕜 := 𝕜) n r hr k)`
is the rank-`1` diagonal matrix `eₖ eₖᵗ`. -/
def veroneseGeneralPt (n r : ℕ) (hr : r ≤ n + 1) (k : Fin r) : Fin (n + 1) → 𝕜 :=
  Pi.single (Fin.castLE hr k) 1

omit [CharZero 𝕜] in
/-- The local parametrization of `veroneseGeneral n` (the cone over `v₂(ℙⁿ)`) at parameter `v`. -/
def veroneseGeneralParam (n : ℕ) (v : Fin (n + 1) → 𝕜) :
    LocalParam (𝕜 := 𝕜) (𝔸 := Fin (n + 1) → 𝕜)
      (Set.range (veroneseGeneral n)) (veroneseGeneral n v) where
  basePoint := v
  chart := veroneseGeneral n
  chart_eval := rfl
  tangent := veroneseGeneralDeriv n v
  hasFDerivAt := hasFDerivAt_veroneseGeneral n v

omit [CharZero 𝕜] in
/-- The family of `r` local parametrizations of `veroneseGeneral n` at the `r` standard basis
points `e₀, …, e_{r-1}`. -/
def veroneseGeneralFamily (n r : ℕ) (hr : r ≤ n + 1) (k : Fin r) :
    LocalParam (𝕜 := 𝕜) (𝔸 := Fin (n + 1) → 𝕜)
      (Set.range (veroneseGeneral n)) (veroneseGeneral n (veroneseGeneralPt (𝕜 := 𝕜) n r hr k)) :=
  veroneseGeneralParam n (veroneseGeneralPt (𝕜 := 𝕜) n r hr k)

/-- Each of the `r` tangent spaces `T_{eₖ eₖᵗ} X̂` has dimension `n + 1`. -/
theorem finrank_tangentSpace_veroneseGeneralFamily (n r : ℕ) (hr : r ≤ n + 1) (k : Fin r) :
    Module.finrank 𝕜 (veroneseGeneralFamily (𝕜 := 𝕜) n r hr k).tangentSpace = n + 1 := by
  classical
  set k' : Fin (n + 1) := Fin.castLE hr k with hk'
  have hpt : ∀ a : Fin (n + 1), veroneseGeneralPt (𝕜 := 𝕜) n r hr k a = if a = k' then 1 else 0 := by
    intro a
    simp [veroneseGeneralPt, Pi.single_apply, ← hk']
  have hinj : Function.Injective (veroneseGeneralDeriv n (veroneseGeneralPt (𝕜 := 𝕜) n r hr k)) := by
    intro dv₁ dv₂ heq
    have hsub : veroneseGeneralDeriv n (veroneseGeneralPt (𝕜 := 𝕜) n r hr k) (dv₁ - dv₂) = 0 := by
      rw [map_sub, heq, sub_self]
    rw [← sub_eq_zero]
    have hsub' : ∀ s, veroneseGeneralDeriv n (veroneseGeneralPt (𝕜 := 𝕜) n r hr k) (dv₁ - dv₂) s = 0 :=
      fun s => congrFun hsub s
    funext a
    by_cases ha : a = k'
    · have h2 := hsub' (s(k', k') : Sym2 (Fin (n + 1)))
      rw [veroneseGeneralDeriv_apply_mk, hpt, if_pos rfl, one_mul] at h2
      rw [ha, Pi.sub_apply]
      have h2' : (2 : 𝕜) * (dv₁ - dv₂) k' = 0 := by rw [two_mul]; exact h2
      exact (mul_eq_zero.mp h2').resolve_left two_ne_zero
    · have h2 := hsub' (s(k', a) : Sym2 (Fin (n + 1)))
      rw [veroneseGeneralDeriv_apply_mk, hpt, hpt, if_neg ha, if_pos rfl] at h2
      rw [Pi.sub_apply]
      simpa using h2
  have hinj' :
      Function.Injective (veroneseGeneralDeriv n (veroneseGeneralPt (𝕜 := 𝕜) n r hr k)).toLinearMap :=
    hinj
  show Module.finrank 𝕜 (LinearMap.range (veroneseGeneralDeriv n (veroneseGeneralPt (𝕜 := 𝕜) n r hr k)).toLinearMap) = n + 1
  rw [LinearMap.finrank_range_of_inj hinj', Module.finrank_pi, Fintype.card_fin]

omit [CharZero 𝕜] in
/-- The basis point `eₖ`, evaluated at `a`. -/
theorem veroneseGeneralPt_apply (n r : ℕ) (hr : r ≤ n + 1) (k : Fin r) (a : Fin (n + 1)) :
    veroneseGeneralPt (𝕜 := 𝕜) n r hr k a = if a = Fin.castLE hr k then 1 else 0 := by
  simp [veroneseGeneralPt, Pi.single_apply]

omit [CharZero 𝕜] in
/-- Closed form for the combined derivative of the `r`-point family, evaluated at the pair
`{i, j}`. -/
theorem combinedDerivative_veroneseGeneral_apply (n r : ℕ) (hr : r ≤ n + 1)
    (w : Fin r → Fin (n + 1) → 𝕜) (i j : Fin (n + 1)) :
    combinedDerivative (veroneseGeneralFamily (𝕜 := 𝕜) n r hr) w (s(i, j) : Sym2 (Fin (n + 1)))
      = ∑ k : Fin r, (veroneseGeneralPt (𝕜 := 𝕜) n r hr k j * w k i
          + veroneseGeneralPt (𝕜 := 𝕜) n r hr k i * w k j) := by
  simp [combinedDerivative, veroneseGeneralFamily, veroneseGeneralParam, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, coordProj_apply, Finset.sum_apply, veroneseGeneralDeriv_apply_mk]

omit [CharZero 𝕜] in
/-- Summing `δ(a = castLE hr k)` against `F k` over `k : Fin r` picks out the unique preimage of
`a` under `castLE hr`, if `a.val < r`, and vanishes otherwise. -/
theorem sum_ite_castLE_eq {r n : ℕ} (hr : r ≤ n + 1) (a : Fin (n + 1)) (F : Fin r → 𝕜) :
    (∑ k : Fin r, if a = Fin.castLE hr k then F k else 0)
      = if h : a.val < r then F ⟨a.val, h⟩ else 0 := by
  split_ifs with h
  · have hcast : Fin.castLE hr (⟨a.val, h⟩ : Fin r) = a := Fin.ext rfl
    rw [Finset.sum_eq_single (⟨a.val, h⟩ : Fin r)]
    · rw [if_pos hcast.symm]
    · intro k _ hk
      rw [if_neg]
      intro hc
      exact hk (Fin.castLE_injective hr (hcast.trans hc)).symm
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg]
    intro hc
    exact h (by rw [hc]; exact k.isLt)

/-- `Sym2` pairs `{i, j}` with both `i, j ≥ r` — the "bottom-right block" of the symmetric
matrix that is unconstrained by the tangent spaces at `e₀, …, e_{r-1}`. -/
def badPairs (n r : ℕ) : Set (Sym2 (Fin (n + 1))) := {s | ∀ a ∈ s, r ≤ a.val}

omit [CharZero 𝕜] in
/-- The combined tangent space: functions vanishing on `badPairs n r`. -/
def veroneseTangentSum (n r : ℕ) : Submodule 𝕜 (Sym2 (Fin (n + 1)) → 𝕜) :=
  ⨅ s : badPairs n r,
    LinearMap.ker (LinearMap.proj (s : Sym2 (Fin (n + 1))) : (Sym2 (Fin (n + 1)) → 𝕜) →ₗ[𝕜] 𝕜)

omit [CharZero 𝕜] in
theorem mem_veroneseTangentSum {n r : ℕ} (f : Sym2 (Fin (n + 1)) → 𝕜) :
    f ∈ veroneseTangentSum n r ↔ ∀ s ∈ badPairs n r, f s = 0 := by
  simp [veroneseTangentSum, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.proj_apply,
    Subtype.forall]

/-- **The combined tangent space of `r` general points on the cone over `v₂(ℙⁿ)`** is exactly
`veroneseTangentSum n r`: the functions vanishing on the "bottom-right `(n+1-r)×(n+1-r)` block"
`badPairs n r`. -/
theorem range_combinedDerivative_veroneseGeneral (n r : ℕ) (hr : r ≤ n + 1) :
    LinearMap.range (combinedDerivative (veroneseGeneralFamily (𝕜 := 𝕜) n r hr)).toLinearMap
      = veroneseTangentSum n r := by
  apply le_antisymm
  · rintro f ⟨w, rfl⟩
    rw [mem_veroneseTangentSum]
    intro s hs
    induction s using Sym2.ind with
    | _ i j =>
    show combinedDerivative (veroneseGeneralFamily (𝕜 := 𝕜) n r hr) w (s(i, j)) = 0
    rw [combinedDerivative_veroneseGeneral_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hi : i.val < r → False := by
      intro hi'
      have := hs i (Sym2.mem_mk_left i j)
      omega
    have hj : j.val < r → False := by
      intro hj'
      have := hs j (Sym2.mem_mk_right i j)
      omega
    have hcik : Fin.castLE hr k ≠ i := by
      intro hc
      exact hi (hc ▸ k.isLt)
    have hcjk : Fin.castLE hr k ≠ j := by
      intro hc
      exact hj (hc ▸ k.isLt)
    rw [veroneseGeneralPt_apply, veroneseGeneralPt_apply, if_neg (Ne.symm hcjk),
      if_neg (Ne.symm hcik)]
    ring
  · intro f hf
    rw [mem_veroneseTangentSum] at hf
    set w : Fin r → Fin (n + 1) → 𝕜 :=
      fun k a => if a.val < r then f (s(Fin.castLE hr k, a)) / 2 else f (s(Fin.castLE hr k, a))
      with hw
    refine ⟨w, ?_⟩
    show combinedDerivative (veroneseGeneralFamily (𝕜 := 𝕜) n r hr) w = f
    funext s
    induction s using Sym2.ind with
    | _ i j =>
    rw [combinedDerivative_veroneseGeneral_apply]
    have e1 : ∀ k : Fin r,
        veroneseGeneralPt (𝕜 := 𝕜) n r hr k j * w k i + veroneseGeneralPt (𝕜 := 𝕜) n r hr k i * w k j
          = (if j = Fin.castLE hr k then w k i else 0) + (if i = Fin.castLE hr k then w k j else 0) := by
      intro k
      rw [veroneseGeneralPt_apply, veroneseGeneralPt_apply]
      split_ifs <;> ring
    simp_rw [e1]
    rw [Finset.sum_add_distrib, sum_ite_castLE_eq hr j (fun k => w k i),
      sum_ite_castLE_eq hr i (fun k => w k j)]
    by_cases hjr : j.val < r <;> by_cases hir : i.val < r
    · rw [dif_pos hjr, dif_pos hir]
      have hcj : Fin.castLE hr (⟨j.val, hjr⟩ : Fin r) = j := Fin.ext rfl
      have hci : Fin.castLE hr (⟨i.val, hir⟩ : Fin r) = i := Fin.ext rfl
      simp only [hw, hcj, hci, if_pos hir, if_pos hjr, Sym2.eq_swap (a := j) (b := i)]
      field_simp
      ring
    · rw [dif_pos hjr, dif_neg hir]
      have hcj : Fin.castLE hr (⟨j.val, hjr⟩ : Fin r) = j := Fin.ext rfl
      simp only [hw, hcj, if_neg hir, Sym2.eq_swap (a := j) (b := i), add_zero]
    · rw [dif_neg hjr, dif_pos hir]
      have hci : Fin.castLE hr (⟨i.val, hir⟩ : Fin r) = i := Fin.ext rfl
      simp only [hw, hci, if_neg hjr, zero_add]
    · rw [dif_neg hjr, dif_neg hir, add_zero]
      refine (hf s(i, j) ?_).symm
      intro a ha
      rcases Sym2.mem_iff.mp ha with rfl | rfl
      · exact not_lt.mp hir
      · exact not_lt.mp hjr

/-! ### §E — Dimension count of `veroneseTangentSum` -/

/-- Shift a `Fin (n + 1 - r)` index up by `r` into `Fin (n + 1)`. -/
def finShiftUp (n r : ℕ) (hr : r ≤ n + 1) (b : Fin (n + 1 - r)) : Fin (n + 1) :=
  ⟨b.val + r, by omega⟩

theorem finShiftUp_val (n r : ℕ) (hr : r ≤ n + 1) (b : Fin (n + 1 - r)) :
    (finShiftUp n r hr b).val = b.val + r := rfl

theorem r_le_finShiftUp (n r : ℕ) (hr : r ≤ n + 1) (b : Fin (n + 1 - r)) :
    r ≤ (finShiftUp n r hr b).val := by
  rw [finShiftUp_val]; omega

/-- Shift a `Fin (n + 1)` index with `r ≤ a.val` down by `r` into `Fin (n + 1 - r)`. -/
def finShiftDown (n r : ℕ) (a : Fin (n + 1)) (ha : r ≤ a.val) : Fin (n + 1 - r) :=
  ⟨a.val - r, by omega⟩

theorem finShiftUp_finShiftDown (n r : ℕ) (hr : r ≤ n + 1) (a : Fin (n + 1)) (ha : r ≤ a.val) :
    finShiftUp n r hr (finShiftDown n r a ha) = a := by
  apply Fin.ext
  simp only [finShiftUp, finShiftDown]
  omega

theorem finShiftDown_finShiftUp (n r : ℕ) (hr : r ≤ n + 1) (b : Fin (n + 1 - r))
    (h : r ≤ (finShiftUp n r hr b).val) :
    finShiftDown n r (finShiftUp n r hr b) h = b := by
  apply Fin.ext
  simp only [finShiftUp, finShiftDown]
  omega

/-- The "bad pairs" `{i,j}` with `r ≤ i.val` and `r ≤ j.val` correspond to `Sym2 (Fin (n+1-r))`,
via shifting indices down by `r`. -/
def badPairsEquiv (n r : ℕ) (hr : r ≤ n + 1) :
    ↥(badPairs n r) ≃ Sym2 (Fin (n + 1 - r)) where
  toFun p := Sym2.pmap (finShiftDown n r) p.1 p.2
  invFun t := ⟨Sym2.map (finShiftUp n r hr) t, by
    intro a ha
    obtain ⟨b, _, rfl⟩ := Sym2.mem_map.mp ha
    exact r_le_finShiftUp n r hr b⟩
  left_inv := fun ⟨s, hs⟩ => by
    apply Subtype.ext
    revert hs
    induction s using Sym2.ind with
    | _ x y =>
      intro hs
      simp only [Sym2.pmap_pair, Sym2.map_mk, finShiftUp_finShiftDown]
  right_inv := fun t => by
    induction t using Sym2.ind with
    | _ b c =>
      simp only [Sym2.map_mk, Sym2.pmap_pair, finShiftDown_finShiftUp]

omit [CharZero 𝕜] in
/-- **Dimension count.** `veroneseTangentSum n r` has codimension `(n+2-r).choose 2` in the
ambient space `Sym2 (Fin (n+1)) → 𝕜` (of dimension `(n+2).choose 2`), since it is cut out by
one linear condition for each of the `(n+2-r).choose 2` "bad pairs". -/
theorem finrank_veroneseTangentSum (n r : ℕ) (hr : r ≤ n + 1) :
    Module.finrank 𝕜 (veroneseTangentSum (𝕜 := 𝕜) n r) = (n + 2).choose 2 - (n + 2 - r).choose 2 := by
  classical
  set g : (Sym2 (Fin (n + 1)) → 𝕜) →ₗ[𝕜] (↥(badPairs n r) → 𝕜) :=
    LinearMap.funLeft 𝕜 𝕜 (Subtype.val : ↥(badPairs n r) → Sym2 (Fin (n + 1)))
    with hg
  have hker : LinearMap.ker g = veroneseTangentSum n r := by
    ext f
    rw [LinearMap.mem_ker, mem_veroneseTangentSum]
    constructor
    · intro hf s hs
      have h := congrFun hf ⟨s, hs⟩
      simp only [hg, LinearMap.funLeft_apply, Pi.zero_apply] at h
      exact h
    · intro hf
      funext p
      obtain ⟨s, hs⟩ := p
      simp only [hg, LinearMap.funLeft_apply, Pi.zero_apply]
      exact hf s hs
  have hsurj : Function.Surjective g :=
    LinearMap.funLeft_surjective_of_injective 𝕜 𝕜 _ Subtype.val_injective
  have hrange : LinearMap.range g = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange, hker, finrank_top, finrank_ambient_veroneseGeneral] at hrn
  haveI : Fintype ↥(badPairs n r) := Fintype.ofEquiv _ (badPairsEquiv n r hr).symm
  have hcard : Fintype.card ↥(badPairs n r) = (n + 2 - r).choose 2 := by
    rw [Fintype.card_congr (badPairsEquiv n r hr), Sym2.card, Fintype.card_fin]
    congr 1
    omega
  rw [Module.finrank_pi, hcard] at hrn
  omega

/-! ### §F — Defect formulas and the main theorem -/

/-- `2 * n.choose 2 = n * (n - 1)`, the doubled triangular-number formula, avoiding `ℕ`-division.
-/
theorem two_mul_choose_two (m : ℕ) : 2 * m.choose 2 = m * (m - 1) := by
  rw [Nat.choose_two_right, mul_comm 2, Nat.div_mul_cancel (Nat.two_dvd_mul_sub_one m)]

/-- **Dimension of the combined tangent space** of the `r`-point family: it is exactly
`finrank (veroneseTangentSum n r)`, computed in §E. -/
theorem finrank_iSup_veroneseGeneral (n r : ℕ) (hr2 : r ≤ n + 1) :
    Module.finrank 𝕜 ((⨆ k, (veroneseGeneralFamily (𝕜 := 𝕜) n r hr2 k).tangentSpace :
      Submodule 𝕜 (Sym2 (Fin (n + 1)) → 𝕜)))
      = (n + 2).choose 2 - (n + 2 - r).choose 2 := by
  rw [show (⨆ k, (veroneseGeneralFamily (𝕜 := 𝕜) n r hr2 k).tangentSpace :
          Submodule 𝕜 (Sym2 (Fin (n + 1)) → 𝕜))
        = LinearMap.range (combinedDerivative (veroneseGeneralFamily (𝕜 := 𝕜) n r hr2)).toLinearMap
      from (range_combinedParam_eq_iSup
        (fun k => (veroneseGeneralFamily (𝕜 := 𝕜) n r hr2 k).tangent)).symm,
    range_combinedDerivative_veroneseGeneral, finrank_veroneseTangentSum n r hr2]

/-- **Expected dimension** of the `r`-point family: `min(N+1, r(n+1))`, where `N+1 = (n+2).choose 2`
is the ambient dimension and `n+1` is the dimension of each tangent space. -/
theorem expectedDim_veroneseGeneral (n r : ℕ) (hr2 : r ≤ n + 1) :
    expectedDim (fun k : Fin r => (veroneseGeneralFamily (𝕜 := 𝕜) n r hr2 k).tangentSpace)
      = min ((n + 2).choose 2) (r * (n + 1)) := by
  unfold expectedDim
  rw [finrank_ambient_veroneseGeneral, Finset.sum_congr rfl
    (fun k _ => finrank_tangentSpace_veroneseGeneralFamily n r hr2 k)]
  simp

/-- **Main result.** `σ_r(v₂(ℙⁿ))` is Alexander–Hirschowitz defective iff `2 ≤ r ≤ n`. -/
theorem isDefective_veroneseGeneral_iff (n r : ℕ) (hr2 : r ≤ n + 1) :
    IsDefective (fun k : Fin r => (veroneseGeneralFamily (𝕜 := 𝕜) n r hr2 k).tangentSpace)
      ↔ 2 ≤ r ∧ r ≤ n := by
  unfold IsDefective
  rw [finrank_iSup_veroneseGeneral n r hr2, expectedDim_veroneseGeneral n r hr2]
  set A := (n + 2).choose 2 with hA
  set B := (n + 2 - r).choose 2 with hB
  set R := r * (n + 1) with hR
  have hBA : B ≤ A := Nat.choose_le_choose 2 (by omega)
  rw [lt_min_iff]
  have h1iff : A - B < A ↔ r ≤ n := by
    rw [show A - B < A ↔ 0 < B from by omega, hB]
    constructor
    · intro h
      by_contra hc
      rw [Nat.choose_eq_zero_iff.mpr (show n + 2 - r < 2 by omega)] at h
      omega
    · intro h
      exact Nat.choose_pos (by omega)
  have h2iff : A - B < R ↔ 2 ≤ r := by
    rw [show A - B < R ↔ A < R + B from by omega]
    obtain ⟨s, hs⟩ : ∃ s, n + 1 = r + s := ⟨n + 1 - r, by omega⟩
    have e1 : n + 2 - r = s + 1 := by omega
    have e2 : n + 2 = r + s + 1 := by omega
    have hA2 : 2 * A = (r + s + 1) * (r + s) := by
      rw [hA, two_mul_choose_two, e2, Nat.add_sub_cancel]
    have hB2 : 2 * B = (s + 1) * s := by
      rw [hB, two_mul_choose_two, e1, Nat.add_sub_cancel]
    rw [show A < R + B ↔ 2 * A < 2 * (R + B) from
        (Nat.mul_lt_mul_left (show (0:ℕ) < 2 by norm_num)).symm,
      mul_add, hA2, hR, hs, hB2]
    have key1 : (r + s + 1) * (r + s) = r * (r + 2 * s + 1) + (s + 1) * s := by ring
    rw [key1, show ∀ x y c : ℕ, x + c < y + c ↔ x < y from fun x y c => by omega]
    rcases lt_or_ge r 2 with h | h
    · interval_cases r <;> omega
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 2 := ⟨r - 2, by omega⟩
      have hcomm : 2 * ((r' + 2) * (r' + 2 + s)) = (r' + 2) * (2 * (r' + 2 + s)) := by ring
      rw [hcomm, Nat.mul_lt_mul_left (show (0:ℕ) < r' + 2 by omega)]
      omega
  rw [h1iff, h2iff]
  exact and_comm

/-- **`r = n + 1` fills the ambient space**: `σ_{n+1}(v₂(ℙⁿ))` is non-defective and
*superabundant*, the boundary case between the defective regime `2 ≤ r ≤ n` and the
non-defective regime `r ≥ n + 1`. -/
theorem veroneseGeneral_sup_eq_top (n : ℕ) :
    (⨆ k, (veroneseGeneralFamily (𝕜 := 𝕜) n (n + 1) (le_refl (n + 1)) k).tangentSpace) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_iSup_veroneseGeneral n (n + 1) (le_refl (n + 1)), finrank_ambient_veroneseGeneral]
  have h : n + 2 - (n + 1) = 1 := by omega
  rw [h, Nat.choose_eq_zero_iff.mpr (by norm_num : 1 < 2), Nat.sub_zero]

/-- **Non-defectivity for `r ≥ n + 1`.** Any family of tangent submodules containing the
`n + 1` tangent spaces `(veroneseGeneralFamily n (n+1) _ k).tangentSpace` (`k : Fin (n+1)`) among
its members is non-defective, regardless of the remaining members — the `(n+1)`-point analogue
of `parabola_not_isDefective` etc. -/
theorem veroneseGeneral_not_isDefective_of_succ_le (n : ℕ) {ι : Type*} [Fintype ι]
    [DecidableEq ι] (S : ι → Submodule 𝕜 (Sym2 (Fin (n + 1)) → 𝕜)) (e : Fin (n + 1) → ι)
    (he : ∀ k, S (e k)
      = (veroneseGeneralFamily (𝕜 := 𝕜) n (n + 1) (le_refl (n + 1)) k).tangentSpace) :
    ¬ IsDefective S := by
  apply not_isDefective_of_finsetSup_eq_top S (T := Finset.image e Finset.univ)
  apply le_antisymm le_top
  calc (⊤ : Submodule 𝕜 (Sym2 (Fin (n + 1)) → 𝕜))
      = ⨆ k, (veroneseGeneralFamily (𝕜 := 𝕜) n (n + 1) (le_refl (n + 1)) k).tangentSpace :=
        (veroneseGeneral_sup_eq_top n).symm
    _ = ⨆ k, S (e k) := by simp_rw [← he]
    _ ≤ (Finset.image e Finset.univ).sup S :=
        iSup_le fun k => Finset.le_sup (Finset.mem_image_of_mem e (Finset.mem_univ k))

end VeroneseGeneralExample
