import TerraciniLemma.VeroneseDegree

/-!
# `σ₅(v₄(ℙ²))` is Alexander–Hirschowitz defective: the `(n,d,r) = (2,4,5)` exceptional case

`TerraciniLemma.VeroneseDegree` shows that `σ_r(v_d(ℙⁿ))` is *never* defective for `d ≥ 3`
and `r ≤ n+1` coordinate points (`veroneseDeg_not_isDefective`). This file exhibits the
smallest exceptional case in the AH family `(2,4,5), (3,4,9), (4,4,14)`: `(n,d,r) = (2,4,5)`,
one of the four exceptional cases of the Alexander–Hirschowitz theorem (the others being
`(4,3,7)`, formalized in `TerraciniLemma.VeroneseAH437`). Here `r = 5 > n+1 = 3`, so the 5
points cannot all be coordinate points: we take the 3 coordinate points `e₀, e₁, e₂` together
with two further points `p₃ = (1,1,1)` and `p₄ = (1,2,3)`.

## Geometric picture: the double conic

The unique (up to scale) conic through all 5 points `e₀, e₁, e₂, p₃, p₄ ⊂ ℙ²` is
```
Q = 3x₀x₁ - 4x₀x₂ + x₁x₂.
```
Consider the quartic `F = Q²`. By the product rule, `∇F = 2Q·∇Q`, which vanishes identically
on the conic `{Q = 0}`. Since all 5 points lie on `{Q = 0}`, the gradient `∇F` vanishes at
each of them — so the linear functional on the ambient space `Sym (Fin 3) 4 → 𝕜` given by
`F`'s coefficients, `dualQuarticφ` below, annihilates the image of the derivative map at
every one of the 5 points.

## Proof strategy

1. `dualQuarticφ` is a nonzero linear functional on the `15`-dimensional ambient space
   (`dualQuarticφ_ne_zero`).
2. `dualQuarticφ` vanishes on the tangent space of each of the 5 points, so the combined
   tangent space is contained in `ker dualQuarticφ`, which has dimension `14`
   (`range_combinedDerivative_ah245_le_ker`, `finrank_ker_dualQuarticφ`).
3. Each of the 5 tangent spaces individually has dimension `3`
   (`finrank_tangentSpace_ah245`), so the *expected* dimension is `min(15, 5·3) = 15`.
4. Since `14 < 15`, `σ₅(v₄(ℙ²))` is defective (`ah245_isDefective`).
-/

noncomputable section VeroneseAH245

open MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-! ### §A — `sym2_2`, `sym2_1_1` and their derivative closed forms -/

/-- The element of `Sym (Fin (n+1)) 4` corresponding to the monomial `Xᵢ² Xⱼ²` (`i ≠ j`). -/
def sym2_2 {n : ℕ} (i j : Fin (n + 1)) : Sym (Fin (n + 1)) 4 := ⟨{i, i, j, j}, by simp⟩

/-- The element of `Sym (Fin (n+1)) 4` corresponding to the monomial `Xᵢ² Xⱼ Xₖ`
(`i, j, k` pairwise distinct). -/
def sym2_1_1 {n : ℕ} (i j k : Fin (n + 1)) : Sym (Fin (n + 1)) 4 := ⟨{i, i, j, k}, by simp⟩

/-- Closed form for `veroneseDegDeriv n 4 v dv` at `sym2_2 i j` (`i ≠ j`). -/
theorem veroneseDegDeriv_apply_sym2_2 {n : ℕ} (v dv : Fin (n + 1) → 𝕜) (i j : Fin (n + 1))
    (hij : i ≠ j) :
    veroneseDegDeriv n 4 v dv (sym2_2 i j)
      = 2 * v i * (v j) ^ 2 * dv i + 2 * (v i) ^ 2 * v j * dv j := by
  rw [veroneseDegDeriv_apply]
  rw [← Finset.sum_add_sum_compl ({i, j} : Finset (Fin (n + 1)))]
  have hrest : ∑ m ∈ ({i, j} : Finset (Fin (n + 1)))ᶜ,
      ((sym2_2 i j).val.count m : 𝕜) * (Multiset.map v ((sym2_2 i j).val.erase m)).prod * dv m
        = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    obtain ⟨hmi, hmj⟩ := hm
    have hc : (sym2_2 i j).val.count m = 0 := by
      show Multiset.count m ({i, i, j, j} : Multiset (Fin (n + 1))) = 0
      simp [hmi, hmj]
    rw [hc]
    simp
  rw [hrest, add_zero, Finset.sum_insert (by simp [hij]), Finset.sum_singleton]
  have hci : (sym2_2 i j).val.count i = 2 := by
    show Multiset.count i ({i, i, j, j} : Multiset (Fin (n + 1))) = 2
    simp [hij]
  have hcj : (sym2_2 i j).val.count j = 2 := by
    show Multiset.count j ({i, i, j, j} : Multiset (Fin (n + 1))) = 2
    simp [Ne.symm hij]
  have hei : (sym2_2 i j).val.erase i = i ::ₘ j ::ₘ ({j} : Multiset (Fin (n + 1))) := by
    show Multiset.erase ({i, i, j, j} : Multiset (Fin (n + 1))) i = i ::ₘ j ::ₘ {j}
    rw [show ({i, i, j, j} : Multiset (Fin (n + 1))) = i ::ₘ i ::ₘ j ::ₘ {j} from rfl,
      Multiset.erase_cons_head]
  have hej : (sym2_2 i j).val.erase j = i ::ₘ i ::ₘ ({j} : Multiset (Fin (n + 1))) := by
    show Multiset.erase ({i, i, j, j} : Multiset (Fin (n + 1))) j = i ::ₘ i ::ₘ {j}
    rw [show ({i, i, j, j} : Multiset (Fin (n + 1))) = i ::ₘ i ::ₘ j ::ₘ {j} from rfl,
      Multiset.erase_cons_tail _ hij, Multiset.erase_cons_tail _ hij, Multiset.erase_cons_head]
  rw [hci, hcj, hei, hej]
  simp [Multiset.map_cons]
  ring

/-- Closed form for `veroneseDegDeriv n 4 v dv` at `sym2_1_1 i j k`
(`i, j, k` pairwise distinct). -/
theorem veroneseDegDeriv_apply_sym2_1_1 {n : ℕ} (v dv : Fin (n + 1) → 𝕜) (i j k : Fin (n + 1))
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    veroneseDegDeriv n 4 v dv (sym2_1_1 i j k)
      = 2 * v i * v j * v k * dv i + (v i) ^ 2 * v k * dv j + (v i) ^ 2 * v j * dv k := by
  rw [veroneseDegDeriv_apply]
  rw [← Finset.sum_add_sum_compl ({i, j, k} : Finset (Fin (n + 1)))]
  have hrest : ∑ m ∈ ({i, j, k} : Finset (Fin (n + 1)))ᶜ,
      ((sym2_1_1 i j k).val.count m : 𝕜)
        * (Multiset.map v ((sym2_1_1 i j k).val.erase m)).prod * dv m = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    obtain ⟨hmi, hmj, hmk⟩ := hm
    have hc : (sym2_1_1 i j k).val.count m = 0 := by
      show Multiset.count m ({i, i, j, k} : Multiset (Fin (n + 1))) = 0
      simp [hmi, hmj, hmk]
    rw [hc]
    simp
  rw [hrest, add_zero]
  rw [Finset.sum_insert (by simp [hij, hik]), Finset.sum_insert (by simp [hjk]),
    Finset.sum_singleton]
  have hci : (sym2_1_1 i j k).val.count i = 2 := by
    show Multiset.count i ({i, i, j, k} : Multiset (Fin (n + 1))) = 2
    simp [hij, hik]
  have hcj : (sym2_1_1 i j k).val.count j = 1 := by
    show Multiset.count j ({i, i, j, k} : Multiset (Fin (n + 1))) = 1
    simp [Ne.symm hij, hjk]
  have hck : (sym2_1_1 i j k).val.count k = 1 := by
    show Multiset.count k ({i, i, j, k} : Multiset (Fin (n + 1))) = 1
    simp [Ne.symm hik, Ne.symm hjk]
  have hei : (sym2_1_1 i j k).val.erase i = i ::ₘ j ::ₘ ({k} : Multiset (Fin (n + 1))) := by
    show Multiset.erase ({i, i, j, k} : Multiset (Fin (n + 1))) i = i ::ₘ j ::ₘ {k}
    rw [show ({i, i, j, k} : Multiset (Fin (n + 1))) = i ::ₘ i ::ₘ j ::ₘ {k} from rfl,
      Multiset.erase_cons_head]
  have hej : (sym2_1_1 i j k).val.erase j = i ::ₘ i ::ₘ ({k} : Multiset (Fin (n + 1))) := by
    show Multiset.erase ({i, i, j, k} : Multiset (Fin (n + 1))) j = i ::ₘ i ::ₘ {k}
    rw [show ({i, i, j, k} : Multiset (Fin (n + 1))) = i ::ₘ i ::ₘ j ::ₘ {k} from rfl,
      Multiset.erase_cons_tail _ hij, Multiset.erase_cons_tail _ hij, Multiset.erase_cons_head]
  have hek : (sym2_1_1 i j k).val.erase k = i ::ₘ i ::ₘ ({j} : Multiset (Fin (n + 1))) := by
    show Multiset.erase ({i, i, j, k} : Multiset (Fin (n + 1))) k = i ::ₘ i ::ₘ {j}
    rw [show ({i, i, j, k} : Multiset (Fin (n + 1))) = i ::ₘ i ::ₘ j ::ₘ {k} from rfl,
      Multiset.erase_cons_tail _ hik, Multiset.erase_cons_tail _ hik, Multiset.erase_cons_tail _ hjk]
    simp
  rw [hci, hcj, hck, hei, hej, hek]
  simp [Multiset.map_cons]
  ring

/-! ### §B — The dual quartic certificate -/

/-- The dual quartic functional: the linear functional on the ambient space
`Sym (Fin 3) 4 → 𝕜` given by the coefficients of `F = Q²`, where
`Q = 3x₀x₁ - 4x₀x₂ + x₁x₂` is the unique (up to scale) quadric through the 5 points
`e₀, e₁, e₂, (1,1,1), (1,2,3)`. -/
def dualQuarticφ : (Sym (Fin 3) 4 → 𝕜) →ₗ[𝕜] 𝕜 :=
  (9 : 𝕜) • LinearMap.proj (sym2_2 0 1) + (16 : 𝕜) • LinearMap.proj (sym2_2 0 2)
    + LinearMap.proj (sym2_2 1 2) - (24 : 𝕜) • LinearMap.proj (sym2_1_1 0 1 2)
    + (6 : 𝕜) • LinearMap.proj (sym2_1_1 1 0 2) - (8 : 𝕜) • LinearMap.proj (sym2_1_1 2 0 1)

/-- `dualQuarticφ` is not the zero functional: it takes the value `1` on the basis vector
dual to `sym2_2 1 2`. -/
theorem dualQuarticφ_ne_zero : (dualQuarticφ (𝕜 := 𝕜)) ≠ 0 := by
  intro h
  have := congrFun (congrArg (DFunLike.coe) h) (Pi.single (sym2_2 1 2) 1)
  simp only [dualQuarticφ, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul, LinearMap.zero_apply] at this
  rw [Pi.single_eq_of_ne (show sym2_2 0 1 ≠ sym2_2 1 2 from by decide),
      Pi.single_eq_of_ne (show sym2_2 0 2 ≠ sym2_2 1 2 from by decide),
      Pi.single_eq_of_ne (show sym2_1_1 0 1 2 ≠ sym2_2 1 2 from by decide),
      Pi.single_eq_of_ne (show sym2_1_1 1 0 2 ≠ sym2_2 1 2 from by decide),
      Pi.single_eq_of_ne (show sym2_1_1 2 0 1 ≠ sym2_2 1 2 from by decide),
      Pi.single_eq_same] at this
  norm_num at this

/-! ### §C — `dualQuarticφ` vanishes on all 5 tangent spaces -/

omit [CharZero 𝕜] in
/-- `dualQuarticφ` vanishes on the tangent space of every coordinate point `eₐ` (`a : Fin 3`):
since `2 < 4` and `2 < 4 - 1 = 3`, none of the 6 monomials in `dualQuarticφ` (each with every
element-count `≤ 2`) can equal `Sym.replicate 4 a` or `veroneseDegElt 2 4 _ a j'` (`j' ≠ a`),
so `veroneseDegDeriv_apply_eq_zero` kills every term. -/
theorem dualQuarticφ_comp_veroneseDegDeriv_coord (a : Fin 3) (dv : Fin 3 → 𝕜) :
    dualQuarticφ (veroneseDegDeriv 2 4 (Pi.single a 1) dv) = 0 := by
  have key : ∀ (s : Sym (Fin 3) 4), (∀ x, s.val.count x ≤ 2) →
      veroneseDegDeriv 2 4 (Pi.single a 1) dv s = 0 := fun s hs =>
    veroneseDegDeriv_apply_eq_zero 2 4 (by norm_num) a s
      (ne_replicate_of_count_le s 2 hs (by norm_num) a)
      (fun j' hj' => ne_veroneseDegElt_of_count_le (by norm_num) s 2 hs (by norm_num) a j' hj')
      dv
  simp only [dualQuarticφ, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  rw [key (sym2_2 0 1) (by decide), key (sym2_2 0 2) (by decide), key (sym2_2 1 2) (by decide),
    key (sym2_1_1 0 1 2) (by decide), key (sym2_1_1 1 0 2) (by decide),
    key (sym2_1_1 2 0 1) (by decide)]
  ring

/-- The point `p₃ = (1,1,1)`. -/
def ah245Pt3 : Fin 3 → 𝕜 := fun _ => 1

/-- The point `p₄ = (1,2,3)`. -/
def ah245Pt4 : Fin 3 → 𝕜 := ![1, 2, 3]

/-- `dualQuarticφ` vanishes on the tangent space at `p₃ = (1,1,1)`: this is the structural
fact that, for `F = Q²`, `∇F = 2Q ∇Q`, and `Q(p₃) = 0`. -/
theorem dualQuarticφ_comp_veroneseDegDeriv_pt3 (dv : Fin 3 → 𝕜) :
    dualQuarticφ (veroneseDegDeriv 2 4 ah245Pt3 dv) = 0 := by
  simp only [dualQuarticφ, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  rw [veroneseDegDeriv_apply_sym2_2 _ _ 0 1 (by decide),
      veroneseDegDeriv_apply_sym2_2 _ _ 0 2 (by decide),
      veroneseDegDeriv_apply_sym2_2 _ _ 1 2 (by decide),
      veroneseDegDeriv_apply_sym2_1_1 _ _ 0 1 2 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym2_1_1 _ _ 1 0 2 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym2_1_1 _ _ 2 0 1 (by decide) (by decide) (by decide)]
  simp only [ah245Pt3]
  ring

/-- `dualQuarticφ` vanishes on the tangent space at `p₄ = (1,2,3)`. -/
theorem dualQuarticφ_comp_veroneseDegDeriv_pt4 (dv : Fin 3 → 𝕜) :
    dualQuarticφ (veroneseDegDeriv 2 4 ah245Pt4 dv) = 0 := by
  simp only [dualQuarticφ, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  rw [veroneseDegDeriv_apply_sym2_2 _ _ 0 1 (by decide),
      veroneseDegDeriv_apply_sym2_2 _ _ 0 2 (by decide),
      veroneseDegDeriv_apply_sym2_2 _ _ 1 2 (by decide),
      veroneseDegDeriv_apply_sym2_1_1 _ _ 0 1 2 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym2_1_1 _ _ 1 0 2 (by decide) (by decide) (by decide),
      veroneseDegDeriv_apply_sym2_1_1 _ _ 2 0 1 (by decide) (by decide) (by decide)]
  simp only [ah245Pt4, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ### §D — `finrank(ker dualQuarticφ) = 14` -/

omit [CharZero 𝕜] in
/-- `dualQuarticφ` takes the value `1` on the basis vector dual to `sym2_2 1 2`. -/
theorem dualQuarticφ_single_eq_one :
    (dualQuarticφ (𝕜 := 𝕜)) (Pi.single (sym2_2 1 2) 1) = 1 := by
  simp only [dualQuarticφ, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.proj_apply, smul_eq_mul]
  rw [Pi.single_eq_of_ne (show sym2_2 0 1 ≠ sym2_2 1 2 from by decide),
      Pi.single_eq_of_ne (show sym2_2 0 2 ≠ sym2_2 1 2 from by decide),
      Pi.single_eq_of_ne (show sym2_1_1 0 1 2 ≠ sym2_2 1 2 from by decide),
      Pi.single_eq_of_ne (show sym2_1_1 1 0 2 ≠ sym2_2 1 2 from by decide),
      Pi.single_eq_of_ne (show sym2_1_1 2 0 1 ≠ sym2_2 1 2 from by decide),
      Pi.single_eq_same]
  norm_num

omit [CharZero 𝕜] in
/-- `dualQuarticφ` is surjective. -/
theorem range_dualQuarticφ_eq_top : LinearMap.range (dualQuarticφ (𝕜 := 𝕜)) = ⊤ := by
  rw [LinearMap.range_eq_top]
  intro c
  exact ⟨c • (Pi.single (sym2_2 1 2) 1 : Sym (Fin 3) 4 → 𝕜), by
    rw [map_smul, dualQuarticφ_single_eq_one, smul_eq_mul, mul_one]⟩

omit [CharZero 𝕜] in
/-- The kernel of `dualQuarticφ` has dimension `14 = 15 - 1`, by rank-nullity together with
`range_dualQuarticφ_eq_top` and `finrank_ambient_veroneseDeg 2 4 = (2+4).choose 4 = 15`. -/
theorem finrank_ker_dualQuarticφ :
    Module.finrank 𝕜 (LinearMap.ker (dualQuarticφ (𝕜 := 𝕜))) = 14 := by
  have h := LinearMap.finrank_range_add_finrank_ker (dualQuarticφ (𝕜 := 𝕜))
  rw [range_dualQuarticφ_eq_top, finrank_top, Module.finrank_self,
    finrank_ambient_veroneseDeg (𝕜 := 𝕜) 2 4] at h
  have h15 : (2 + 4).choose 4 = 15 := by decide
  rw [h15] at h
  omega

/-! ### §E — Each of the 5 tangent spaces has dimension 3 -/

/-- The 5 points: the coordinate points `e₀, e₁, e₂`, plus `p₃ = (1,1,1)` and
`p₄ = (1,2,3)`. -/
def ah245Pt : Fin 5 → Fin 3 → 𝕜 :=
  ![Pi.single 0 1, Pi.single 1 1, Pi.single 2 1, ah245Pt3, ah245Pt4]

/-- The family of 5 local parametrizations of `v₄(ℙ²)` at the 5 points `ah245Pt`. -/
def ah245Family (k : Fin 5) := veroneseDegParam (𝕜 := 𝕜) 2 4 (ah245Pt k)

/-- Each of the 5 tangent spaces has dimension `3`. -/
theorem finrank_tangentSpace_ah245 (k : Fin 5) :
    Module.finrank 𝕜 (ah245Family (𝕜 := 𝕜) k).tangentSpace = 3 := by
  show Module.finrank 𝕜
    (LinearMap.range (veroneseDegDeriv (𝕜 := 𝕜) 2 4 (ah245Pt k)).toLinearMap) = 3
  fin_cases k
  · exact finrank_tangentSpace_single 2 4 (by norm_num) 0
  · exact finrank_tangentSpace_single 2 4 (by norm_num) 1
  · exact finrank_tangentSpace_single 2 4 (by norm_num) 2
  · exact finrank_tangentSpace_of_ne_zero 2 4 (by norm_num) ah245Pt3 (fun a => by simp [ah245Pt3])
  · exact finrank_tangentSpace_of_ne_zero 2 4 (by norm_num) ah245Pt4 (fun a => by
      fin_cases a <;> norm_num [ah245Pt4])

/-! ### §F — Main theorem -/

/-- `dualQuarticφ` vanishes on the tangent space of every one of the 5 points. -/
theorem dualQuarticφ_comp_veroneseDegDeriv_ah245Pt (k : Fin 5) (dv : Fin 3 → 𝕜) :
    dualQuarticφ (veroneseDegDeriv 2 4 (ah245Pt k) dv) = 0 := by
  fin_cases k
  · exact dualQuarticφ_comp_veroneseDegDeriv_coord 0 dv
  · exact dualQuarticφ_comp_veroneseDegDeriv_coord 1 dv
  · exact dualQuarticφ_comp_veroneseDegDeriv_coord 2 dv
  · exact dualQuarticφ_comp_veroneseDegDeriv_pt3 dv
  · exact dualQuarticφ_comp_veroneseDegDeriv_pt4 dv

omit [CharZero 𝕜] in
/-- Closed form for the combined derivative of the 5-point family. -/
theorem combinedDerivative_ah245_apply (w : Fin 5 → Fin 3 → 𝕜) (s : Sym (Fin 3) 4) :
    combinedDerivative (ah245Family (𝕜 := 𝕜)) w s
      = ∑ k : Fin 5, veroneseDegDeriv 2 4 (ah245Pt k) (w k) s := by
  simp [combinedDerivative, ah245Family, veroneseDegParam, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, coordProj_apply, Finset.sum_apply]

/-- The combined tangent space of the 5 points is contained in `ker dualQuarticφ`. -/
theorem range_combinedDerivative_ah245_le_ker :
    LinearMap.range (combinedDerivative (ah245Family (𝕜 := 𝕜))).toLinearMap
      ≤ LinearMap.ker (dualQuarticφ (𝕜 := 𝕜)) := by
  rintro f ⟨w, rfl⟩
  rw [LinearMap.mem_ker]
  show dualQuarticφ (combinedDerivative (ah245Family (𝕜 := 𝕜)) w) = 0
  rw [show combinedDerivative (ah245Family (𝕜 := 𝕜)) w
      = ∑ k : Fin 5, veroneseDegDeriv 2 4 (ah245Pt k) (w k) from by
    funext s; rw [combinedDerivative_ah245_apply, Finset.sum_apply], map_sum]
  exact Finset.sum_eq_zero fun k _ => dualQuarticφ_comp_veroneseDegDeriv_ah245Pt k (w k)

/-- **Main result.** `σ₅(v₄(ℙ²))` is Alexander–Hirschowitz defective: the combined tangent
space of the 5 points (`e₀, e₁, e₂`, `p₃ = (1,1,1)`, `p₄ = (1,2,3)`) has dimension at most
`14` (`finrank_ker_dualQuarticφ`, via the double-conic quartic `dualQuarticφ`), while the
expected dimension is `min(15, 5·3) = 15` (`finrank_tangentSpace_ah245`). This is the
`(n,d,r) = (2,4,5)` exceptional case of the Alexander–Hirschowitz theorem, with defect `1`. -/
theorem ah245_isDefective :
    IsDefective (fun k : Fin 5 => (ah245Family (𝕜 := 𝕜) k).tangentSpace) := by
  unfold IsDefective
  rw [show (⨆ k, (ah245Family (𝕜 := 𝕜) k).tangentSpace : Submodule 𝕜 (Sym (Fin 3) 4 → 𝕜))
      = LinearMap.range (combinedDerivative (ah245Family (𝕜 := 𝕜))).toLinearMap
    from (range_combinedParam_eq_iSup (fun k => (ah245Family (𝕜 := 𝕜) k).tangent)).symm]
  have hle : Module.finrank 𝕜
      (LinearMap.range (combinedDerivative (ah245Family (𝕜 := 𝕜))).toLinearMap) ≤ 14 := by
    rw [← finrank_ker_dualQuarticφ (𝕜 := 𝕜)]
    exact Submodule.finrank_mono range_combinedDerivative_ah245_le_ker
  have hexp : expectedDim (fun k : Fin 5 => (ah245Family (𝕜 := 𝕜) k).tangentSpace) = 15 := by
    unfold expectedDim
    rw [finrank_ambient_veroneseDeg (𝕜 := 𝕜) 2 4, Finset.sum_congr rfl
      (fun k _ => finrank_tangentSpace_ah245 k)]
    decide
  omega

end VeroneseAH245
