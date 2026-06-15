import TerraciniLemma.VeroneseDegree

/-!
# `σ₇(v₃(ℙ⁴))` is Alexander–Hirschowitz defective: the `(n,d,r) = (4,3,7)` exceptional case

`TerraciniLemma.VeroneseDegree` shows that `σ_r(v_d(ℙⁿ))` is *never* defective for `d ≥ 3`
and `r ≤ n+1` coordinate points (`veroneseDeg_not_isDefective`). This file exhibits the
smallest case where that bound is sharp: `(n,d,r) = (4,3,7)`, one of the four exceptional
cases of the Alexander–Hirschowitz theorem (the others being `(2,4,5)`, `(3,4,9)`,
`(4,4,14)`). Here `r = 7 > n+1 = 5`, so the 7 points cannot all be coordinate points: we
take the 5 coordinate points `e₀,…,e₄` together with two further points
`p₆ = (1,1,1,1,1)` and `p₇ = (1,2,3,4,5)`.

## Geometric picture (Brambilla–Ottaviani)

Through any 7 general points of `ℙ⁴` there passes a unique rational normal curve: the
locus where a `3×3` "Hankel matrix" built from the points' coordinates drops to rank `≤ 1`.
The secant variety of that curve is a cubic hypersurface — the vanishing locus of the
Hankel determinant — and this hypersurface is *singular* along the curve itself. Since all
7 points lie on the curve, their tangent spaces to `v₃(ℙ⁴)` lie in the tangent space of
this singular cubic hypersurface at a singular point, i.e. in the kernel of the linear
functional "differentiate the Hankel determinant". That linear functional is `dualCubicφ'`
below; up to scaling it is exactly the Hankel-determinant cubic
```
G = 10y₀y₁y₂ - 45y₀y₁y₃ + 36y₀y₁y₄ + 45y₀y₂y₃ - 64y₀y₂y₄ + 18y₀y₃y₄
    - 10y₁y₂y₃ + 18y₁y₂y₄ - 9y₁y₃y₄ + y₂y₃y₄
```
for the 7 chosen points.

## Proof strategy

1. `dualCubicφ'` is a nonzero linear functional on the `35`-dimensional ambient space
   (`dualCubicφ'_ne_zero`).
2. `dualCubicφ'` vanishes on the tangent space of each of the 7 points, so the combined
   tangent space is contained in `ker dualCubicφ'`, which has dimension `34`
   (`range_combinedDerivative_ah437_le_ker`, `finrank_ker_dualCubicφ'`).
3. Each of the 7 tangent spaces individually has dimension `5`
   (`finrank_tangentSpace_ah437`), so the *expected* dimension is `min(35, 7·5) = 35`.
4. Since `34 < 35`, `σ₇(v₃(ℙ⁴))` is defective (`ah437_isDefective`).
-/

noncomputable section VeroneseAH437

open MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-! ### §A — The 7 points -/

/-- The element of `Sym (Fin 5) 3` corresponding to the squarefree triple `{i,j,k}`. -/
def sym3 (i j k : Fin 5) : Sym (Fin 5) 3 := ⟨{i, j, k}, by simp⟩

/-- Closed form for `veroneseDegDeriv 4 3 v dv` at a squarefree monomial `sym3 i j k`
(pairwise-distinct `i,j,k`): only the variables `i,j,k` contribute, each through the
product of the other two coordinates of `v`. -/
theorem veroneseDegDeriv_apply_sym3 (v dv : Fin 5 → 𝕜) (i j k : Fin 5)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    veroneseDegDeriv 4 3 v dv (sym3 i j k)
      = dv i * (v j * v k) + dv j * (v i * v k) + dv k * (v i * v j) := by
  rw [veroneseDegDeriv_apply]
  rw [← Finset.sum_add_sum_compl ({i, j, k} : Finset (Fin 5))]
  have hrest : ∑ m ∈ ({i, j, k} : Finset (Fin 5))ᶜ,
      ((sym3 i j k).val.count m : 𝕜) * (Multiset.map v ((sym3 i j k).val.erase m)).prod * dv m
        = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    obtain ⟨hmi, hmj, hmk⟩ := hm
    have : (sym3 i j k).val.count m = 0 := by
      show Multiset.count m {i, j, k} = 0
      simp [hmi, hmj, hmk]
    rw [this]
    simp
  rw [hrest, add_zero]
  rw [Finset.sum_insert (by simp [hij, hik]), Finset.sum_insert (by simp [hjk]),
    Finset.sum_singleton]
  have hci : (sym3 i j k).val.count i = 1 := by
    show Multiset.count i {i, j, k} = 1
    simp [hij, hik]
  have hcj : (sym3 i j k).val.count j = 1 := by
    show Multiset.count j {i, j, k} = 1
    simp [Ne.symm hij, hjk]
  have hck : (sym3 i j k).val.count k = 1 := by
    show Multiset.count k {i, j, k} = 1
    simp [Ne.symm hik, Ne.symm hjk]
  have hei : (sym3 i j k).val.erase i = {j, k} := by
    show Multiset.erase {i, j, k} i = {j, k}
    rw [show ({i, j, k} : Multiset (Fin 5)) = i ::ₘ j ::ₘ {k} from rfl, Multiset.erase_cons_head,
      Multiset.insert_eq_cons]
  have hej : (sym3 i j k).val.erase j = {i, k} := by
    show Multiset.erase {i, j, k} j = {i, k}
    rw [show ({i, j, k} : Multiset (Fin 5)) = i ::ₘ j ::ₘ {k} from rfl,
      Multiset.erase_cons_tail _ hij, Multiset.erase_cons_head, Multiset.insert_eq_cons]
  have hek : (sym3 i j k).val.erase k = {i, j} := by
    show Multiset.erase {i, j, k} k = {i, j}
    rw [show ({i, j, k} : Multiset (Fin 5)) = i ::ₘ j ::ₘ {k} from rfl,
      Multiset.erase_cons_tail _ hik, Multiset.erase_cons_tail _ hjk]
    simp
  rw [hci, hcj, hck, hei, hej, hek]
  simp [Multiset.map_cons]
  ring

/-- The sixth of the 7 points, `p₆ = (1,1,1,1,1)`. -/
def ah437Pt6 : Fin 5 → 𝕜 := fun _ => 1

/-- The seventh of the 7 points, `p₇ = (1,2,3,4,5)`. -/
def ah437Pt7 : Fin 5 → 𝕜 := ![1, 2, 3, 4, 5]

/-- The 7 points: the coordinate points `e₀,…,e₄`, plus `p₆ = (1,1,1,1,1)` and
`p₇ = (1,2,3,4,5)`. -/
def ah437Pt : Fin 7 → Fin 5 → 𝕜 :=
  ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, Pi.single 3 1, Pi.single 4 1,
    ah437Pt6, ah437Pt7]

/-- The family of 7 local parametrizations of `v₃(ℙ⁴)` at the 7 points `ah437Pt`. -/
def ah437Family (k : Fin 7) := veroneseDegParam (𝕜 := 𝕜) 4 3 (ah437Pt k)

/-! ### §B — The dual cubic certificate -/

/-- The dual cubic functional: the linear functional on the ambient space
`Sym (Fin 5) 3 → 𝕜` whose coefficients (one per squarefree triple `{i,j,k} ⊆ Fin 5`)
are the coefficients of the Hankel-determinant cubic `G` from the module docstring. -/
def dualCubicφ' : (Sym (Fin 5) 3 → 𝕜) →ₗ[𝕜] 𝕜 :=
  (10 : 𝕜) • LinearMap.proj (sym3 0 1 2) - (45 : 𝕜) • LinearMap.proj (sym3 0 1 3)
  + (36 : 𝕜) • LinearMap.proj (sym3 0 1 4) + (45 : 𝕜) • LinearMap.proj (sym3 0 2 3)
  - (64 : 𝕜) • LinearMap.proj (sym3 0 2 4) + (18 : 𝕜) • LinearMap.proj (sym3 0 3 4)
  - (10 : 𝕜) • LinearMap.proj (sym3 1 2 3) + (18 : 𝕜) • LinearMap.proj (sym3 1 2 4)
  - (9 : 𝕜) • LinearMap.proj (sym3 1 3 4) + LinearMap.proj (sym3 2 3 4)

/-- `dualCubicφ'` is not the zero functional: it takes the value `1` on the basis vector
dual to `sym3 2 3 4`. -/
theorem dualCubicφ'_ne_zero : (dualCubicφ' (𝕜 := 𝕜)) ≠ 0 := by
  intro h
  have := congrFun (congrArg (DFunLike.coe) h) (Pi.single (sym3 2 3 4) 1)
  simp only [dualCubicφ', LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, LinearMap.zero_apply] at this
  rw [Pi.single_eq_of_ne (show sym3 0 1 2 ≠ sym3 2 3 4 from by decide),
      Pi.single_eq_of_ne (show sym3 0 1 3 ≠ sym3 2 3 4 from by decide),
      Pi.single_eq_of_ne (show sym3 0 1 4 ≠ sym3 2 3 4 from by decide),
      Pi.single_eq_of_ne (show sym3 0 2 3 ≠ sym3 2 3 4 from by decide),
      Pi.single_eq_of_ne (show sym3 0 2 4 ≠ sym3 2 3 4 from by decide),
      Pi.single_eq_of_ne (show sym3 0 3 4 ≠ sym3 2 3 4 from by decide),
      Pi.single_eq_of_ne (show sym3 1 2 3 ≠ sym3 2 3 4 from by decide),
      Pi.single_eq_of_ne (show sym3 1 2 4 ≠ sym3 2 3 4 from by decide),
      Pi.single_eq_of_ne (show sym3 1 3 4 ≠ sym3 2 3 4 from by decide),
      Pi.single_eq_same] at this
  norm_num at this

/-! ### §C — Vanishing on all 7 tangent spaces -/

/-- A monomial `X_a^3` (i.e. `Sym.replicate 3 a`) is never squarefree. -/
theorem not_nodup_replicate (a : Fin 5) : ¬ (Sym.replicate 3 a).val.Nodup := by
  rw [Sym.val_replicate, Multiset.nodup_iff_count_le_one]
  push Not
  exact ⟨a, by simp⟩

/-- A monomial `X_{j'} X_a^2` (i.e. `veroneseDegElt 4 3 _ a j'` with `j' ≠ a`) is never
squarefree. -/
theorem not_nodup_veroneseDegElt (a j' : Fin 5) (hj' : j' ≠ a) :
    ¬ (veroneseDegElt 4 3 (by norm_num) a j').val.Nodup := by
  rw [veroneseDegElt_val, Multiset.nodup_iff_count_le_one]
  push Not
  refine ⟨a, ?_⟩
  rw [Multiset.count_cons, Multiset.count_replicate, if_neg (Ne.symm hj'), if_pos rfl]
  norm_num

/-- A squarefree multiset can't equal a non-squarefree one. -/
theorem ne_of_nodup_left {s t : Sym (Fin 5) 3} (hs : s.val.Nodup) (ht : ¬ t.val.Nodup) :
    s ≠ t := fun h => ht (h ▸ hs)

omit [CharZero 𝕜] in
/-- `dualCubicφ'` vanishes on the tangent space of every coordinate point `eₐ`: the support
of `veroneseDegDeriv 4 3 (Pi.single a 1) dv` is contained in the non-squarefree monomials
`X_a^3` and `X_{j'} X_a^2` (`not_nodup_replicate`, `not_nodup_veroneseDegElt`), while
`dualCubicφ'` only involves squarefree monomials `sym3 i j k`. -/
theorem dualCubicφ'_comp_veroneseDegDeriv_coord (a : Fin 5) (dv : Fin 5 → 𝕜) :
    dualCubicφ' (veroneseDegDeriv 4 3 (Pi.single a 1) dv) = 0 := by
  have key : ∀ (i j k : Fin 5), (sym3 i j k).val.Nodup →
      veroneseDegDeriv 4 3 (Pi.single a 1) dv (sym3 i j k) = 0 := by
    intro i j k hnodup
    exact veroneseDegDeriv_apply_eq_zero 4 3 (by norm_num) a (sym3 i j k)
      (ne_of_nodup_left hnodup (not_nodup_replicate a))
      (fun j' hj' => ne_of_nodup_left hnodup (not_nodup_veroneseDegElt a j' hj')) dv
  simp only [dualCubicφ', LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  rw [key 0 1 2 (by decide), key 0 1 3 (by decide), key 0 1 4 (by decide),
      key 0 2 3 (by decide), key 0 2 4 (by decide), key 0 3 4 (by decide),
      key 1 2 3 (by decide), key 1 2 4 (by decide), key 1 3 4 (by decide),
      key 2 3 4 (by decide)]
  ring

/-- `dualCubicφ'` vanishes on the tangent space at `p₆ = (1,1,1,1,1)`. -/
theorem dualCubicφ'_comp_veroneseDegDeriv_pt6 (dv : Fin 5 → 𝕜) :
    dualCubicφ' (veroneseDegDeriv 4 3 ah437Pt6 dv) = 0 := by
  simp only [dualCubicφ', LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  rw [veroneseDegDeriv_apply_sym3 _ _ 0 1 2 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym3 _ _ 0 1 3 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym3 _ _ 0 1 4 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym3 _ _ 0 2 3 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym3 _ _ 0 2 4 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym3 _ _ 0 3 4 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym3 _ _ 1 2 3 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym3 _ _ 1 2 4 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym3 _ _ 1 3 4 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym3 _ _ 2 3 4 (by decide) (by decide) (by decide)]
  simp only [ah437Pt6]
  ring

/-- `dualCubicφ'` vanishes on the tangent space at `p₇ = (1,2,3,4,5)`. -/
theorem dualCubicφ'_comp_veroneseDegDeriv_pt7 (dv : Fin 5 → 𝕜) :
    dualCubicφ' (veroneseDegDeriv 4 3 ah437Pt7 dv) = 0 := by
  simp only [dualCubicφ', LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  rw [veroneseDegDeriv_apply_sym3 _ _ 0 1 2 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym3 _ _ 0 1 3 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym3 _ _ 0 1 4 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym3 _ _ 0 2 3 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym3 _ _ 0 2 4 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym3 _ _ 0 3 4 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym3 _ _ 1 2 3 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym3 _ _ 1 2 4 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym3 _ _ 1 3 4 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym3 _ _ 2 3 4 (by decide) (by decide) (by decide)]
  simp only [ah437Pt7, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three, Matrix.cons_val_four]
  ring

/-- `dualCubicφ'` vanishes on the tangent space of every one of the 7 points. -/
theorem dualCubicφ'_comp_veroneseDegDeriv_ah437Pt (k : Fin 7) (dv : Fin 5 → 𝕜) :
    dualCubicφ' (veroneseDegDeriv 4 3 (ah437Pt k) dv) = 0 := by
  fin_cases k
  · exact dualCubicφ'_comp_veroneseDegDeriv_coord 0 dv
  · exact dualCubicφ'_comp_veroneseDegDeriv_coord 1 dv
  · exact dualCubicφ'_comp_veroneseDegDeriv_coord 2 dv
  · exact dualCubicφ'_comp_veroneseDegDeriv_coord 3 dv
  · exact dualCubicφ'_comp_veroneseDegDeriv_coord 4 dv
  · exact dualCubicφ'_comp_veroneseDegDeriv_pt6 dv
  · exact dualCubicφ'_comp_veroneseDegDeriv_pt7 dv

omit [CharZero 𝕜] in
/-- Closed form for the combined derivative of the 7-point family. -/
theorem combinedDerivative_ah437_apply (w : Fin 7 → Fin 5 → 𝕜) (s : Sym (Fin 5) 3) :
    combinedDerivative (ah437Family (𝕜 := 𝕜)) w s
      = ∑ k : Fin 7, veroneseDegDeriv 4 3 (ah437Pt k) (w k) s := by
  simp [combinedDerivative, ah437Family, veroneseDegParam, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, coordProj_apply, Finset.sum_apply]

/-- The combined tangent space of the 7 points is contained in `ker dualCubicφ'`. -/
theorem range_combinedDerivative_ah437_le_ker :
    LinearMap.range (combinedDerivative (ah437Family (𝕜 := 𝕜))).toLinearMap
      ≤ LinearMap.ker (dualCubicφ' (𝕜 := 𝕜)) := by
  rintro f ⟨w, rfl⟩
  rw [LinearMap.mem_ker]
  show dualCubicφ' (combinedDerivative (ah437Family (𝕜 := 𝕜)) w) = 0
  rw [show combinedDerivative (ah437Family (𝕜 := 𝕜)) w
      = ∑ k : Fin 7, veroneseDegDeriv 4 3 (ah437Pt k) (w k) from by
    funext s; rw [combinedDerivative_ah437_apply, Finset.sum_apply], map_sum]
  exact Finset.sum_eq_zero fun k _ => dualCubicφ'_comp_veroneseDegDeriv_ah437Pt k (w k)

/-! ### §D — `finrank(ker dualCubicφ') = 34` -/

omit [CharZero 𝕜] in
/-- `dualCubicφ'` takes the value `1` on the basis vector dual to `sym3 2 3 4`. -/
theorem dualCubicφ'_single_eq_one :
    (dualCubicφ' (𝕜 := 𝕜)) (Pi.single (sym3 2 3 4) 1) = 1 := by
  simp only [dualCubicφ', LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  rw [Pi.single_eq_of_ne (show sym3 0 1 2 ≠ sym3 2 3 4 from by decide),
      Pi.single_eq_of_ne (show sym3 0 1 3 ≠ sym3 2 3 4 from by decide),
      Pi.single_eq_of_ne (show sym3 0 1 4 ≠ sym3 2 3 4 from by decide),
      Pi.single_eq_of_ne (show sym3 0 2 3 ≠ sym3 2 3 4 from by decide),
      Pi.single_eq_of_ne (show sym3 0 2 4 ≠ sym3 2 3 4 from by decide),
      Pi.single_eq_of_ne (show sym3 0 3 4 ≠ sym3 2 3 4 from by decide),
      Pi.single_eq_of_ne (show sym3 1 2 3 ≠ sym3 2 3 4 from by decide),
      Pi.single_eq_of_ne (show sym3 1 2 4 ≠ sym3 2 3 4 from by decide),
      Pi.single_eq_of_ne (show sym3 1 3 4 ≠ sym3 2 3 4 from by decide),
      Pi.single_eq_same]
  norm_num

omit [CharZero 𝕜] in
/-- `dualCubicφ'` is surjective. -/
theorem range_dualCubicφ'_eq_top : LinearMap.range (dualCubicφ' (𝕜 := 𝕜)) = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro c
  exact ⟨c • (Pi.single (sym3 2 3 4) 1 : Sym (Fin 5) 3 → 𝕜), by
    rw [map_smul, dualCubicφ'_single_eq_one, smul_eq_mul, mul_one]⟩

omit [CharZero 𝕜] in
/-- The kernel of `dualCubicφ'` has dimension `34 = 35 - 1`, by rank-nullity together with
`range_dualCubicφ'_eq_top` and `finrank_ambient_veroneseDeg 4 3 = (4+3).choose 3 = 35`. -/
theorem finrank_ker_dualCubicφ' :
    Module.finrank 𝕜 (LinearMap.ker (dualCubicφ' (𝕜 := 𝕜))) = 34 := by
  have h := LinearMap.finrank_range_add_finrank_ker (dualCubicφ' (𝕜 := 𝕜))
  rw [range_dualCubicφ'_eq_top, finrank_top, Module.finrank_self,
    finrank_ambient_veroneseDeg (𝕜 := 𝕜) 4 3] at h
  have h35 : (4 + 3).choose 3 = 35 := by decide
  rw [h35] at h
  omega

/-! ### §E — Each of the 7 tangent spaces has dimension 5 -/

/-- Closed form for `veroneseDegDeriv n d v dv` at the monomial `X_a^d`. -/
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

/-- The tangent space at `p₆ = (1,1,1,1,1)` has dimension `5`. -/
theorem finrank_tangentSpace_ah437Pt6 :
    Module.finrank 𝕜 (LinearMap.range (veroneseDegDeriv (𝕜 := 𝕜) 4 3 ah437Pt6).toLinearMap) = 5 := by
  have hinj : Function.Injective (veroneseDegDeriv (𝕜 := 𝕜) 4 3 ah437Pt6) :=
    veroneseDegDeriv_injective_of_ne_zero 4 3 (by norm_num) ah437Pt6 (fun a => by
      simp [ah437Pt6])
  have hinj' : Function.Injective (veroneseDegDeriv (𝕜 := 𝕜) 4 3 ah437Pt6).toLinearMap := hinj
  rw [LinearMap.finrank_range_of_inj hinj', Module.finrank_pi, Fintype.card_fin]

/-- The tangent space at `p₇ = (1,2,3,4,5)` has dimension `5`. -/
theorem finrank_tangentSpace_ah437Pt7 :
    Module.finrank 𝕜 (LinearMap.range (veroneseDegDeriv (𝕜 := 𝕜) 4 3 ah437Pt7).toLinearMap) = 5 := by
  have hinj : Function.Injective (veroneseDegDeriv (𝕜 := 𝕜) 4 3 ah437Pt7) := by
    apply veroneseDegDeriv_injective_of_ne_zero 4 3 (by norm_num) ah437Pt7
    intro a
    fin_cases a <;> norm_num [ah437Pt7]
  have hinj' : Function.Injective (veroneseDegDeriv (𝕜 := 𝕜) 4 3 ah437Pt7).toLinearMap := hinj
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

/-- Each of the 7 tangent spaces has dimension `5`. -/
theorem finrank_tangentSpace_ah437 (k : Fin 7) :
    Module.finrank 𝕜 (ah437Family (𝕜 := 𝕜) k).tangentSpace = 5 := by
  show Module.finrank 𝕜
    (LinearMap.range (veroneseDegDeriv (𝕜 := 𝕜) 4 3 (ah437Pt k)).toLinearMap) = 5
  fin_cases k
  · exact finrank_tangentSpace_single 4 3 (by norm_num) 0
  · exact finrank_tangentSpace_single 4 3 (by norm_num) 1
  · exact finrank_tangentSpace_single 4 3 (by norm_num) 2
  · exact finrank_tangentSpace_single 4 3 (by norm_num) 3
  · exact finrank_tangentSpace_single 4 3 (by norm_num) 4
  · exact finrank_tangentSpace_ah437Pt6
  · exact finrank_tangentSpace_ah437Pt7

/-! ### §F — Main theorem -/

/-- **Main result.** `σ₇(v₃(ℙ⁴))` is Alexander–Hirschowitz defective: the combined tangent
space of the 7 points (`e₀,…,e₄`, `p₆ = (1,1,1,1,1)`, `p₇ = (1,2,3,4,5)`) has dimension at
most `34` (`finrank_ker_dualCubicφ'`, via the Hankel-determinant cubic `dualCubicφ'`), while
the expected dimension is `min(35, 7·5) = 35` (`finrank_tangentSpace_ah437`). This is the
`(n,d,r) = (4,3,7)` exceptional case of the Alexander–Hirschowitz theorem, with defect `1`. -/
theorem ah437_isDefective :
    IsDefective (fun k : Fin 7 => (ah437Family (𝕜 := 𝕜) k).tangentSpace) := by
  unfold IsDefective
  rw [show (⨆ k, (ah437Family (𝕜 := 𝕜) k).tangentSpace : Submodule 𝕜 (Sym (Fin 5) 3 → 𝕜))
      = LinearMap.range (combinedDerivative (ah437Family (𝕜 := 𝕜))).toLinearMap
    from (range_combinedParam_eq_iSup (fun k => (ah437Family (𝕜 := 𝕜) k).tangent)).symm]
  have hle : Module.finrank 𝕜
      (LinearMap.range (combinedDerivative (ah437Family (𝕜 := 𝕜))).toLinearMap) ≤ 34 := by
    rw [← finrank_ker_dualCubicφ' (𝕜 := 𝕜)]
    exact Submodule.finrank_mono range_combinedDerivative_ah437_le_ker
  have hexp : expectedDim (fun k : Fin 7 => (ah437Family (𝕜 := 𝕜) k).tangentSpace) = 35 := by
    unfold expectedDim
    rw [finrank_ambient_veroneseDeg (𝕜 := 𝕜) 4 3, Finset.sum_congr rfl
      (fun k _ => finrank_tangentSpace_ah437 k)]
    decide
  omega

end VeroneseAH437
