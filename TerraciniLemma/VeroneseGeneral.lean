module

public import TerraciniLemma.PolynomialCalculus
public import TerraciniLemma.Defect
public import Mathlib.Data.Sym.Card

/-!
# General quadric Veronese `v₂(ℙⁿ) ⊂ ℙ^N`

This file works in the affine cone over `v₂(ℙⁿ) ⊂ ℙ^N`, `N = binom(n+2,2) - 1`, for an
arbitrary number `r ≤ n + 1` of general points.

The cone `X̂ ⊆ 𝕜^{N+1}` over `v₂(ℙⁿ)` is the set of rank-`≤ 1` symmetric `(n+1) × (n+1)`
matrices `v vᵗ`. We model the ambient space `𝕜^{N+1}` as `Sym2 (Fin (n+1)) → 𝕜`, one
coordinate per unordered pair `{i, j}` (including `i = j`), representing the entries of a
symmetric matrix. By `Sym2.card`, `Fintype.card (Sym2 (Fin (n+1))) = (n+2).choose 2`, matching
`N + 1 = binom(n+2,2)`.
-/

@[expose] public section

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
  simp only [mvPolynomialDeriv, sum_apply, smul_apply,
    coordProj_apply, smul_eq_mul, hterm, add_apply]
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
  chart_mem := Filter.Eventually.of_forall fun _ => Set.mem_range_self _
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
      rw [veroneseGeneralDeriv_apply_mk, hpt, ite_eq_left rfl, one_mul] at h2
      rw [ha, Pi.sub_apply]
      have h2' : (2 : 𝕜) * (dv₁ - dv₂) k' = 0 := by rw [two_mul]; exact h2
      exact (mul_eq_zero.mp h2').resolve_left two_ne_zero
    · have h2 := hsub' (s(k', a) : Sym2 (Fin (n + 1)))
      rw [veroneseGeneralDeriv_apply_mk, hpt, hpt, ite_eq_right ha, ite_eq_left rfl] at h2
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
  simp [combinedDerivative, veroneseGeneralFamily, veroneseGeneralParam, sum_apply,
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
    · rw [ite_eq_left hcast.symm]
    · intro k _ hk
      rw [ite_eq_right]
      intro hc
      exact hk (Fin.castLE_injective hr (hcast.trans hc)).symm
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · refine Finset.sum_eq_zero fun k _ => ?_
    rw [ite_eq_right]
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
    rw [veroneseGeneralPt_apply, veroneseGeneralPt_apply, ite_eq_right (Ne.symm hcjk),
      ite_eq_right (Ne.symm hcik)]
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
    · rw [dite_eq_left hjr, dite_eq_left hir]
      have hcj : Fin.castLE hr (⟨j.val, hjr⟩ : Fin r) = j := Fin.ext rfl
      have hci : Fin.castLE hr (⟨i.val, hir⟩ : Fin r) = i := Fin.ext rfl
      simp only [hw, hcj, hci, ite_eq_left hir, ite_eq_left hjr, Sym2.eq_swap (a := j) (b := i)]
      field_simp
      ring
    · rw [dite_eq_left hjr, dite_eq_right hir]
      have hcj : Fin.castLE hr (⟨j.val, hjr⟩ : Fin r) = j := Fin.ext rfl
      simp only [hw, hcj, ite_eq_right hir, Sym2.eq_swap (a := j) (b := i), add_zero]
    · rw [dite_eq_right hjr, dite_eq_left hir]
      have hci : Fin.castLE hr (⟨i.val, hir⟩ : Fin r) = i := Fin.ext rfl
      simp only [hw, hci, ite_eq_right hjr, zero_add]
    · rw [dite_eq_right hjr, dite_eq_right hir, add_zero]
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
  toFun p := Sym2.pmap (finShiftDown n r) p.1 fun a ha => p.2 a ha
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
  have : Fintype ↥(badPairs n r) := Fintype.ofEquiv _ (badPairsEquiv n r hr).symm
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

/-- **`σ_{n+1}(v₂(ℙⁿ))` fills the ambient space**, stated intrinsically: the tangent cone to the
secant variety at `e₀e₀ᵗ + ⋯ + eₙeₙᵗ` spans all of `Sym2 (Fin (n+1)) → 𝕜`. No
generic-smoothness hypothesis is needed (`span_tangentConeAt_secantVariety_eq_top`). -/
theorem veroneseGeneral_span_tangentConeAt_eq_top (n : ℕ) :
    Submodule.span 𝕜 (tangentConeAt 𝕜 (secantVariety (n + 1) (Set.range (veroneseGeneral n)))
      (∑ k, veroneseGeneral n (veroneseGeneralPt (𝕜 := 𝕜) n (n + 1) (le_refl (n + 1)) k))) = ⊤ :=
  span_tangentConeAt_secantVariety_eq_top _ _ (veroneseGeneral_sup_eq_top n)

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

/-! ### §G — Generic defectivity for any linearly independent `r`-point family

The preceding results prove `isDefective_veroneseGeneral_iff` only for the **coordinate-point
family** `veroneseGeneralFamily`. This section strengthens the defective direction to work for
**any** `r` linearly independent vectors `p₀, …, p_{r-1} ∈ 𝕜^{n+1}`.

The key is an explicit `r.choose 2`-dimensional subspace of the kernel of
`combinedDerivative (fun k => veroneseGeneralParam n (p k))`: for each pair `k < l`, the
velocity family `w^{k,l}_m = if m = k then p l else if m = l then -p k else 0` lies in the kernel
(the cross terms cancel by symmetry). These `r.choose 2` kernel elements are linearly independent
(when `p` is), so the combined tangent span has dimension
`≤ r·(n+1) − r.choose 2 = (n+2).choose 2 − (n+2−r).choose 2 < expectedDim` for `2 ≤ r ≤ n`.
-/

omit [CharZero 𝕜] in
theorem combinedDerivative_veroneseGeneral_apply' (n r : ℕ)
    (p : Fin r → Fin (n + 1) → 𝕜) (w : Fin r → Fin (n + 1) → 𝕜) (i j : Fin (n + 1)) :
    combinedDerivative (fun k => veroneseGeneralParam n (p k)) w (s(i, j) : Sym2 (Fin (n + 1)))
      = ∑ k : Fin r, (p k j * w k i + p k i * w k j) := by
  simp [combinedDerivative, veroneseGeneralParam, sum_apply,
    ContinuousLinearMap.comp_apply, coordProj_apply, veroneseGeneralDeriv_apply_mk]

/-- For `k ≠ l`, the velocity family `w^{k,l}_m = if m = k then p l else if m = l then -p k
else 0` lies in the kernel of `combinedDerivative (fun m => veroneseGeneralParam n (p m))`:
the two cross terms `p k j · p l i + p k i · p l j` and `p l j · (-p k i) + p l i · (-p k j)`
cancel. -/
def veroneseKerElt {n r : ℕ} (p : Fin r → Fin (n + 1) → 𝕜) (k l : Fin r) :
    Fin r → Fin (n + 1) → 𝕜 :=
  fun m => if m = k then p l else if m = l then -(p k) else 0

omit [CharZero 𝕜] in
theorem veroneseKerElt_combinedDerivative_eq_zero {n r : ℕ}
    (p : Fin r → Fin (n + 1) → 𝕜) {k l : Fin r} (hkl : k ≠ l) :
    combinedDerivative (fun m => veroneseGeneralParam n (p m)) (veroneseKerElt p k l) = 0 := by
  ext s
  induction s using Sym2.ind with | _ i j =>
  simp only [Pi.zero_apply]
  rw [combinedDerivative_veroneseGeneral_apply']
  have hkl' : l ≠ k := Ne.symm hkl
  have hcomp : ∀ m ∈ ({k, l} : Finset (Fin r))ᶜ,
      p m j * veroneseKerElt p k l m i + p m i * veroneseKerElt p k l m j = 0 := by
    intro m hm
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    simp [veroneseKerElt, hm.1, hm.2]
  rw [← Finset.sum_compl_add_sum ({k, l} : Finset (Fin r)), add_comm,
    Finset.sum_eq_zero hcomp, add_zero,
    Finset.sum_insert (mt Finset.mem_singleton.mp hkl), Finset.sum_singleton]
  simp only [veroneseKerElt, ite_true, ite_eq_right hkl, ite_eq_right hkl', Pi.neg_apply]
  ring

omit [CharZero 𝕜] in
/-- The `r.choose 2` kernel elements `veroneseKerElt p k l` (for `k < l`) are linearly
independent when `p₀, …, p_{r-1}` are linearly independent. -/
theorem linearIndependent_veroneseKerElt {n r : ℕ} (p : Fin r → Fin (n + 1) → 𝕜)
    (hp : LinearIndependent 𝕜 p) :
    LinearIndependent 𝕜
      (fun kl : {kl : Fin r × Fin r // kl.1 < kl.2} => veroneseKerElt p kl.1.1 kl.1.2) := by
  classical
  rw [Fintype.linearIndependent_iff] at hp ⊢
  rintro c hc ⟨⟨k₀, l₀⟩, hkl₀⟩
  -- Slot `k₀` of the relation is a linear relation among the `p j`: the coefficient of
  -- `p j` is `c (k₀, j) - c (j, k₀)` (only one of which is a valid ordered pair).
  have hslot := congr_fun hc k₀
  have hexp : ∀ kl : {kl : Fin r × Fin r // kl.1 < kl.2}, veroneseKerElt p kl.1.1 kl.1.2 k₀ =
      ∑ j, ((if kl.1 = (k₀, j) then 1 else 0) - (if kl.1 = (j, k₀) then 1 else 0) : 𝕜) • p j := by
    rintro ⟨⟨k, l⟩, hkl⟩
    simp only [sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Prod.mk.injEq]
    by_cases hk : k₀ = k
    · subst hk
      simp [veroneseKerElt, (Fin.ne_of_lt hkl).symm]
    · by_cases hl : k₀ = l
      · subst hl
        simp [veroneseKerElt, hk, eq_comm]
      · simp [veroneseKerElt, hk, hl, Ne.symm hk, Ne.symm hl]
  simp only [Finset.sum_apply, Pi.smul_apply, hexp, Finset.smul_sum, smul_smul,
    Pi.zero_apply] at hslot
  rw [Finset.sum_comm] at hslot
  simp_rw [← Finset.sum_smul] at hslot
  -- By independence of `p`, the coefficient of `p l₀` vanishes, and it is `c (k₀, l₀)`.
  have hcoef := hp _ hslot l₀
  simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib] at hcoef
  have hsnd : ∀ x : {kl : Fin r × Fin r // kl.1 < kl.2}, ¬ (x : Fin r × Fin r) = (l₀, k₀) :=
    fun x hx => by have := x.2; rw [hx] at this; exact lt_asymm hkl₀ this
  have hfst : ∀ x : {kl : Fin r × Fin r // kl.1 < kl.2},
      (x : Fin r × Fin r) = (k₀, l₀) ↔ x = ⟨(k₀, l₀), hkl₀⟩ := fun x => by rw [Subtype.ext_iff]
  simpa [hsnd, hfst] using hcoef

omit [CharZero 𝕜] in
/-- The `r.choose 2` independent kernel elements show `dim ker(combinedDerivative) ≥ r.choose 2`. -/
theorem finrank_ker_combinedDerivative_veroneseGeneral_ge {n r : ℕ}
    (p : Fin r → Fin (n + 1) → 𝕜) (hp : LinearIndependent 𝕜 p) :
    r.choose 2 ≤
      Module.finrank 𝕜 (LinearMap.ker
        (combinedDerivative (fun k => veroneseGeneralParam n (p k))).toLinearMap) := by
  have hli := linearIndependent_veroneseKerElt p hp
  have hmem : ∀ kl : {kl : Fin r × Fin r // kl.1 < kl.2},
      veroneseKerElt p kl.1.1 kl.1.2 ∈
        LinearMap.ker (combinedDerivative (fun k => veroneseGeneralParam n (p k))).toLinearMap := by
    intro ⟨⟨k, l⟩, hkl⟩
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    exact veroneseKerElt_combinedDerivative_eq_zero p (Fin.ne_of_lt hkl)
  have hli_ker : LinearIndependent 𝕜
      (fun kl : {kl : Fin r × Fin r // kl.1 < kl.2} =>
        (⟨veroneseKerElt p kl.1.1 kl.1.2, hmem kl⟩ :
          LinearMap.ker
            (combinedDerivative (fun k => veroneseGeneralParam n (p k))).toLinearMap)) :=
    LinearIndependent.of_comp (LinearMap.ker _).subtype hli
  have hcard : Fintype.card {kl : Fin r × Fin r // kl.1 < kl.2} = r.choose 2 := by
    rw [Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_fin]
  calc r.choose 2 = Fintype.card {kl : Fin r × Fin r // kl.1 < kl.2} := hcard.symm
    _ ≤ Module.finrank 𝕜 (LinearMap.ker
          (combinedDerivative (fun k => veroneseGeneralParam n (p k))).toLinearMap) :=
        hli_ker.fintype_card_le_finrank

omit [CharZero 𝕜] in
/-- **Upper bound on the combined tangent span dimension** for an arbitrary linearly independent
`r`-point family: at most `r·(n+1) − r.choose 2 = (n+2).choose 2 − (n+2−r).choose 2`. -/
theorem finrank_range_combinedDerivative_veroneseGeneral_le {n r : ℕ}
    (p : Fin r → Fin (n + 1) → 𝕜) (hp : LinearIndependent 𝕜 p) :
    Module.finrank 𝕜 (LinearMap.range
        (combinedDerivative (fun k => veroneseGeneralParam n (p k))).toLinearMap)
      ≤ r * (n + 1) - r.choose 2 := by
  have hker := finrank_ker_combinedDerivative_veroneseGeneral_ge p hp
  have hrn := (combinedDerivative (fun k => veroneseGeneralParam n (p k))).toLinearMap
    |>.finrank_range_add_finrank_ker
  have hsrc : Module.finrank 𝕜 (Fin r → Fin (n + 1) → 𝕜) = r * (n + 1) := by
    simp only [Module.finrank_pi_fintype, Fintype.card_fin, Module.finrank_self,
               Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  omega

/-- `veroneseGeneralDeriv n v` is injective for any nonzero `v`. -/
theorem injective_veroneseGeneralDeriv_of_ne_zero (n : ℕ) (v : Fin (n + 1) → 𝕜) (hv : v ≠ 0) :
    Function.Injective (veroneseGeneralDeriv n v) := by
  obtain ⟨k', hk'⟩ : ∃ k' : Fin (n + 1), v k' ≠ 0 := by
    contrapose! hv; ext a; exact hv a
  intro dv₁ dv₂ heq
  have hzero : veroneseGeneralDeriv n v (dv₁ - dv₂) = 0 := by rw [map_sub, heq, sub_self]
  have ha : ∀ a : Fin (n + 1), v a * (dv₁ - dv₂) k' + v k' * (dv₁ - dv₂) a = 0 := fun a => by
    have := congr_fun hzero (s(k', a) : Sym2 (Fin (n + 1)))
    rwa [veroneseGeneralDeriv_apply_mk, Pi.zero_apply] at this
  have hk'zero : (dv₁ - dv₂) k' = 0 := by
    have h2 : (2 : 𝕜) * (v k' * (dv₁ - dv₂) k') = 0 :=
      calc (2 : 𝕜) * (v k' * (dv₁ - dv₂) k')
          = v k' * (dv₁ - dv₂) k' + v k' * (dv₁ - dv₂) k' := by ring
        _ = 0 := ha k'
    have hvx : v k' * (dv₁ - dv₂) k' = 0 := (mul_eq_zero.mp h2).resolve_left two_ne_zero
    exact (mul_eq_zero.mp hvx).resolve_left hk'
  funext a
  have hda : (dv₁ - dv₂) a = 0 := by
    have ha_eq := ha a
    rw [hk'zero, mul_zero, zero_add] at ha_eq
    exact (mul_eq_zero.mp ha_eq).resolve_left hk'
  rw [Pi.sub_apply] at hda
  exact sub_eq_zero.mp hda

/-- The tangent space to the cone over `v₂(ℙⁿ)` at any nonzero `v` has dimension `n + 1`. -/
theorem finrank_tangentSpace_veroneseGeneralParam_of_ne_zero (n : ℕ) (v : Fin (n + 1) → 𝕜)
    (hv : v ≠ 0) :
    Module.finrank 𝕜 (veroneseGeneralParam n v).tangentSpace = n + 1 := by
  show Module.finrank 𝕜 (LinearMap.range (veroneseGeneralDeriv n v).toLinearMap) = n + 1
  rw [LinearMap.finrank_range_of_inj (injective_veroneseGeneralDeriv_of_ne_zero n v hv),
    Module.finrank_pi, Fintype.card_fin]

/-- **Generic defectivity of `σ_r(v₂(ℙⁿ))`** for any `r` linearly independent points with
`2 ≤ r ≤ n`. Unlike `isDefective_veroneseGeneral_iff`, this works for **any** `r` linearly
independent vectors, not just coordinate points — the defect bound `r.choose 2 ≥ 1` applies
uniformly to any such configuration. -/
theorem isDefective_veroneseGeneral_of_linearIndependent {n r : ℕ} (hrn : r ≤ n)
    (p : Fin r → Fin (n + 1) → 𝕜) (hp : LinearIndependent 𝕜 p) (h2r : 2 ≤ r) :
    IsDefective (fun k => (veroneseGeneralParam n (p k)).tangentSpace) := by
  classical
  unfold IsDefective expectedDim
  -- Each tangent space has dim n+1 (since each p k ≠ 0 by linear independence)
  have hne : ∀ k : Fin r, p k ≠ 0 := hp.ne_zero
  have htdim : ∀ k : Fin r,
      Module.finrank 𝕜 (veroneseGeneralParam n (p k)).tangentSpace = n + 1 :=
    fun k => finrank_tangentSpace_veroneseGeneralParam_of_ne_zero n (p k) (hne k)
  rw [show (∑ k : Fin r, Module.finrank 𝕜 (veroneseGeneralParam n (p k)).tangentSpace)
      = r * (n + 1) by simp [htdim, Finset.sum_const, Finset.card_univ, Fintype.card_fin]]
  -- The combined span dim ≤ r*(n+1) - r.choose 2
  have hrange_le := finrank_range_combinedDerivative_veroneseGeneral_le p hp
  -- The combined span = range(combinedDerivative)
  rw [show (⨆ k, (veroneseGeneralParam n (p k)).tangentSpace : Submodule 𝕜 _)
      = LinearMap.range (combinedDerivative (fun k => veroneseGeneralParam n (p k))).toLinearMap
    from (range_combinedParam_eq_iSup (fun k => (veroneseGeneralParam n (p k)).tangent)).symm]
  -- We need: finrank(range) < min(ambient, r*(n+1))
  -- Use: finrank(range) ≤ r*(n+1) - r.choose 2 < min(ambient, r*(n+1))
  have h_choose_pos : 0 < r.choose 2 := Nat.choose_pos h2r
  -- r*(n+1) - r.choose 2 < r*(n+1)
  have h_lt_sum : r * (n + 1) - r.choose 2 < r * (n + 1) :=
    Nat.sub_lt (Nat.mul_pos (by omega) (Nat.succ_pos n)) h_choose_pos
  -- r*(n+1) - r.choose 2 < ambient = (n+2).choose 2
  have h_lt_amb : r * (n + 1) - r.choose 2 < (n + 2).choose 2 := by
    have heq : r * (n + 1) - r.choose 2 = (n + 2).choose 2 - (n + 2 - r).choose 2 := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hrn
      rw [show r + m + 2 - r = m + 2 by omega]
      have two_mul_choose : ∀ a : ℕ, 2 * a.choose 2 = a * (a - 1) := fun a => by
        rw [Nat.choose_two_right, Nat.mul_div_cancel' (Nat.even_mul_pred_self a).two_dvd]
      have hA := two_mul_choose r
      have hB := two_mul_choose (m + 2)
      have hD := two_mul_choose (r + m + 2)
      -- `C(r+m+2, 2) = C(r, 2) + C(m+2, 2) + r(m+2)` and `r(r+m+1) = 2 C(r, 2) + r(m+2)`
      rcases r with _ | s
      · simp
      · simp only [Nat.add_sub_cancel, show s + 1 + m + 2 - 1 = s + m + 2 by omega,
          show m + 2 - 1 = m + 1 by omega] at hA hB hD
        have : (s + 1 + m + 2).choose 2
            = (s + 1).choose 2 + (m + 2).choose 2 + (s + 1) * (m + 2) := by
          nlinarith
        have : (s + 1) * (s + 1 + m + 1) = 2 * (s + 1).choose 2 + (s + 1) * (m + 2) := by
          rw [hA]; ring
        omega
    rw [heq]
    have hpos : 0 < (n + 2 - r).choose 2 := Nat.choose_pos (by omega)
    have hpos_amb : 0 < (n + 2).choose 2 := Nat.choose_pos (by omega)
    exact Nat.sub_lt hpos_amb hpos
  apply lt_of_le_of_lt hrange_le
  rw [finrank_ambient_veroneseGeneral]
  omega

end VeroneseGeneralExample
