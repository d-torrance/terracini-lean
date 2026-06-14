import TerraciniLemma.VeroneseSurface
import TerraciniLemma.RationalNormalCurves
import TerraciniLemma.Segre
import TerraciniLemma.EllipticCurve
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# §7 — Expected dimension and defect

Terracini's Lemma computes the combined tangent space `⨆ i, (param i).tangentSpace` of `r`
points on `X̂`. This file packages the resulting dimension count into the classical
**Alexander–Hirschowitz** language of *expected dimension* and *defect*:

* `expectedDim S = min (finrank E) (∑ i, finrank (S i))` is the naive ("non-defective")
  prediction for `finrank (⨆ i, S i)`: the sum of the individual tangent-space dimensions,
  capped by the ambient dimension.
* `finrank_iSup_le_expectedDim` shows this is always an *upper bound*:
  `finrank (⨆ i, S i) ≤ expectedDim S`.
* `IsDefective S` holds when this bound is *not* attained, i.e. the combined tangent space
  falls short of the naive prediction. `defect S` is the size of the shortfall, and
  `IsDefective S ↔ 0 < defect S`.
* `finrank_finsetSup_eq_sum_of_not_isDefective_subabundant` and
  `not_isDefective_of_finsetSup_eq_top` give **monotonicity of non-defectivity** in the number
  of points `r`: in the *subabundant* regime (`∑ i, finrank (S i) ≤ finrank E`), non-defectivity
  for `r` points implies non-defectivity for any smaller sub-collection of those points; in the
  *superabundant* regime (the combined span fills `E`), non-defectivity for `r` points implies
  non-defectivity for any larger super-collection.
* `not_isDefective_of_sup_eq_top` is the two-point specialization of
  `not_isDefective_of_finsetSup_eq_top` (via the helper `iSup_fin_two : ⨆ i : Fin 2, f i = f 0
  ⊔ f 1`), used to extend the `σ₂`-fills-`E` examples (`parabola_terracini`, `segre_terracini`,
  `elliptic_terracini`) to non-defectivity of `σ_r` for every `r ≥ 2`:
  `parabola_not_isDefective`, `segre_not_isDefective`, `elliptic_not_isDefective`.

## Caveat: cone vs. chart

As for `TerraciniLemma.Projective`, `IsDefective` applied to `S = fun i => (param i).tangentSpace`
for an `r`-point configuration only has its *intended* meaning — genuine
Alexander–Hirschowitz defectivity of the projective variety `X = ℙ(X̂)` — when `E` is the affine
**cone** over `X`. This holds for `TerraciniLemma.VeroneseSurface`, instantiated below:
`veroneseSurface_isDefective` and `defect_veroneseSurface` formalize the "defect `1`" claim from
that file's docstring. For the affine-**chart** examples
(`TerraciniLemma.RationalNormalCurves`, `TerraciniLemma.Segre`, `TerraciniLemma.EllipticCurve`),
tangent spaces have dimension `dim X` (not `dim X + 1`), so `expectedDim` there computes
`min(N, r · dim X)` rather than the true projective expectation `min(N, r · (dim X + 1) - 1)` —
a systematically different quantity, not (in general) equal to AH-defectivity. We therefore do
not instantiate `IsDefective`/`defect` for those examples.
-/

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- `finrank` is subadditive over a finite `Finset.sup` of submodules. -/
theorem finrank_finsetSup_le {ι : Type*} [DecidableEq ι] (S : ι → Submodule 𝕜 E)
    (s : Finset ι) :
    Module.finrank 𝕜 ((s.sup S : Submodule 𝕜 E)) ≤ ∑ i ∈ s, Module.finrank 𝕜 (S i) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s hi ih =>
    rw [Finset.sup_insert, Finset.sum_insert hi]
    exact (Submodule.finrank_add_le_finrank_add_finrank _ _).trans (Nat.add_le_add_left ih _)

omit [FiniteDimensional 𝕜 E] in
/-- A finite supremum of submodules is the `Finset.sup` over `Finset.univ`. -/
theorem iSup_eq_finsetSup_univ {ι : Type*} [Fintype ι] (S : ι → Submodule 𝕜 E) :
    (⨆ i, S i : Submodule 𝕜 E) = Finset.univ.sup S :=
  le_antisymm (iSup_le fun i => Finset.le_sup (Finset.mem_univ i))
    (Finset.sup_le fun i _ => le_iSup S i)

/-- `finrank` is subadditive over a finite supremum of submodules. -/
theorem finrank_iSup_le {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ι → Submodule 𝕜 E) :
    Module.finrank 𝕜 ((⨆ i, S i : Submodule 𝕜 E)) ≤ ∑ i, Module.finrank 𝕜 (S i) := by
  rw [iSup_eq_finsetSup_univ]
  exact finrank_finsetSup_le S Finset.univ

/-- If a finite family `S` attains the upper bound `finrank_iSup_le` on the nose
(`finrank (⨆ i, S i) = ∑ i, finrank (S i)`), then so does every sub-family indexed by a
`Finset T ⊆ ι`: the combined span of `{S i | i ∈ T}` already has dimension `∑ i ∈ T, finrank
(S i)`. -/
theorem finrank_finsetSup_eq_sum_of_finrank_iSup_eq_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ι → Submodule 𝕜 E)
    (h : Module.finrank 𝕜 ((⨆ i, S i : Submodule 𝕜 E)) = ∑ i, Module.finrank 𝕜 (S i))
    (T : Finset ι) :
    Module.finrank 𝕜 ((T.sup S : Submodule 𝕜 E)) = ∑ i ∈ T, Module.finrank 𝕜 (S i) := by
  have hT := finrank_finsetSup_le S T
  have hTc := finrank_finsetSup_le S Tᶜ
  have hsup : (T.sup S ⊔ Tᶜ.sup S : Submodule 𝕜 E) = ⨆ i, S i := by
    rw [← Finset.sup_union, Finset.union_compl, ← iSup_eq_finsetSup_univ]
  have hadd := Submodule.finrank_sup_add_finrank_inf_eq (T.sup S) (Tᶜ.sup S)
  rw [hsup, h, ← Finset.sum_add_sum_compl T] at hadd
  omega

/-- The *expected dimension* of the combined span `⨆ i, S i` of a finite family of submodules:
the naive ("non-defective") prediction `min (finrank E) (∑ i, finrank (S i))`. -/
def expectedDim {ι : Type*} [Fintype ι] (S : ι → Submodule 𝕜 E) : ℕ :=
  min (Module.finrank 𝕜 E) (∑ i, Module.finrank 𝕜 (S i))

/-- `expectedDim` is always an upper bound for `finrank (⨆ i, S i)` — this is what makes
`IsDefective` a meaningful (non-vacuous) notion. -/
theorem finrank_iSup_le_expectedDim {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule 𝕜 E) :
    Module.finrank 𝕜 ((⨆ i, S i : Submodule 𝕜 E)) ≤ expectedDim S :=
  le_min (Submodule.finrank_le _) (finrank_iSup_le S)

/-- A finite family of submodules is *defective* if their combined span falls short of the
expected (non-defective) dimension `expectedDim S`. -/
def IsDefective {ι : Type*} [Fintype ι] (S : ι → Submodule 𝕜 E) : Prop :=
  Module.finrank 𝕜 ((⨆ i, S i : Submodule 𝕜 E)) < expectedDim S

/-- The *defect*: how far short of `expectedDim S` the combined span `⨆ i, S i` falls
(zero iff `S` is non-defective). -/
def defect {ι : Type*} [Fintype ι] (S : ι → Submodule 𝕜 E) : ℕ :=
  expectedDim S - Module.finrank 𝕜 ((⨆ i, S i : Submodule 𝕜 E))

omit [FiniteDimensional 𝕜 E] in
/-- `S` is defective iff its `defect` is positive. -/
theorem isDefective_iff_defect_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Submodule 𝕜 E) :
    IsDefective S ↔ 0 < defect S :=
  Nat.sub_pos_iff_lt.symm

/-- **Subabundant monotonicity of non-defectivity.** If `S` is non-defective and *subabundant*
(`∑ i, finrank (S i) ≤ finrank E`, so `expectedDim S = ∑ i, finrank (S i)`), then every
sub-family `{S i | i ∈ T}` indexed by a `Finset T ⊆ ι` is non-defective too: its combined span
already has the naive dimension `∑ i ∈ T, finrank (S i)`.

Geometrically: if `σ_r(X)` is non-defective and subabundant, then `σ_s(X)` is non-defective for
every `s < r` (take `T` to be any `s`-element subset of the `r` general points witnessing
`σ_r(X)`). -/
theorem finrank_finsetSup_eq_sum_of_not_isDefective_subabundant
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ι → Submodule 𝕜 E)
    (hsub : ∑ i, Module.finrank 𝕜 (S i) ≤ Module.finrank 𝕜 E)
    (h : ¬ IsDefective S) (T : Finset ι) :
    Module.finrank 𝕜 ((T.sup S : Submodule 𝕜 E)) = ∑ i ∈ T, Module.finrank 𝕜 (S i) := by
  refine finrank_finsetSup_eq_sum_of_finrank_iSup_eq_sum S ?_ T
  have hle := finrank_iSup_le_expectedDim S
  simp only [IsDefective, expectedDim, not_lt, min_eq_right hsub] at h hle
  exact le_antisymm hle h

omit [FiniteDimensional 𝕜 E] in
/-- **Superabundant monotonicity of non-defectivity.** If the combined span of a sub-family
`{S i | i ∈ T}` (for some `T : Finset ι`) already fills the ambient space, then `S` itself is
non-defective: its combined span fills the ambient space too, attaining the `expectedDim` bound
`finrank E`.

Geometrically: if `σ_r(X)` is non-defective and superabundant (fills the ambient space), then
`σ_s(X)` is non-defective for every `s > r` (extend the `r` general points witnessing
`σ_r(X) = E` to `s` general points; `σ_r(X) ⊆ σ_s(X)` already fills the ambient space). -/
theorem not_isDefective_of_finsetSup_eq_top
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ι → Submodule 𝕜 E)
    {T : Finset ι} (hT : (T.sup S : Submodule 𝕜 E) = ⊤) :
    ¬ IsDefective S := by
  have htop : (⨆ i, S i : Submodule 𝕜 E) = ⊤ := by
    rw [iSup_eq_finsetSup_univ]
    exact le_antisymm le_top (hT ▸ Finset.sup_mono (Finset.subset_univ T))
  unfold IsDefective expectedDim
  rw [htop, finrank_top, not_lt]
  exact min_le_left _ _

/-- The supremum over `Fin 2` is a binary join: `⨆ i : Fin 2, f i = f 0 ⊔ f 1`. -/
theorem iSup_fin_two {α : Type*} [CompleteLattice α] (f : Fin 2 → α) :
    (⨆ i, f i) = f 0 ⊔ f 1 := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  · exact sup_le (le_iSup f 0) (le_iSup f 1)

omit [FiniteDimensional 𝕜 E] in
/-- A binary specialization of `not_isDefective_of_finsetSup_eq_top`: if two members `S i₀` and
`S i₁` of a family already span `E` between them, then `S` is non-defective — whatever the
remaining members of `S` happen to be. -/
theorem not_isDefective_of_sup_eq_top
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ι → Submodule 𝕜 E)
    {i₀ i₁ : ι} (htop : S i₀ ⊔ S i₁ = ⊤) :
    ¬ IsDefective S :=
  not_isDefective_of_finsetSup_eq_top S (T := {i₀, i₁})
    (by rw [Finset.sup_insert, Finset.sup_singleton, htop])

end

/-!
## Worked example: the quadric Veronese surface

`TerraciniLemma.VeroneseSurface`'s ambient space `Fin 6 → 𝕜` *is* the affine cone over
`v₂(ℙ²) ⊂ ℙ⁵`, so `IsDefective`/`defect` for the two-point tangent-space family there compute
genuine Alexander–Hirschowitz defectivity: `expectedDim = min(6, 3 + 3) = 6` (each tangent space
has dimension `3`), while the combined tangent space `T` has dimension `5`
(`finrank_ker_coordProj_six_two`), so the defect is exactly `1`.
-/

noncomputable section VeroneseSurfaceDefect

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-- `veroneseSurfaceDeriv (1,0,0)` is injective: in closed form it sends `dv` to
`(2dv₀, 0, 0, dv₁, dv₂, 0)`, with left inverse `x ↦ (x₀/2, x₃, x₄)`. -/
theorem injective_veroneseSurfaceDeriv_one :
    Function.Injective (veroneseSurfaceDeriv (![1, 0, 0] : Fin 3 → 𝕜)).toLinearMap := by
  simp only [ContinuousLinearMap.coe_coe]
  apply Function.LeftInverse.injective (g := fun x : Fin 6 → 𝕜 => ![x 0 / 2, x 3, x 4])
  intro dv
  rw [veroneseSurfaceDeriv_apply']
  funext i
  fin_cases i <;> simp

/-- `veroneseSurfaceDeriv (0,1,0)` is injective: in closed form it sends `dv` to
`(0, 2dv₁, 0, dv₀, 0, dv₂)`, with left inverse `x ↦ (x₃, x₁/2, x₅)`. -/
theorem injective_veroneseSurfaceDeriv_two :
    Function.Injective (veroneseSurfaceDeriv (![0, 1, 0] : Fin 3 → 𝕜)).toLinearMap := by
  simp only [ContinuousLinearMap.coe_coe]
  apply Function.LeftInverse.injective (g := fun x : Fin 6 → 𝕜 => ![x 3, x 1 / 2, x 5])
  intro dv
  rw [veroneseSurfaceDeriv_apply']
  funext i
  fin_cases i <;> simp

/-- The tangent space to `X̂` at `(1,0,0)⊗(1,0,0)` has dimension `3` (the full dimension of the
parameter space `Fin 3 → 𝕜`), since `veroneseSurfaceDeriv (1,0,0)` is injective. -/
theorem finrank_tangentSpace_veroneseSurfaceParam_one :
    Module.finrank 𝕜 (veroneseSurfaceParam (![1, 0, 0] : Fin 3 → 𝕜)).tangentSpace = 3 := by
  show Module.finrank 𝕜
      (LinearMap.range (veroneseSurfaceDeriv (![1, 0, 0] : Fin 3 → 𝕜)).toLinearMap) = 3
  rw [LinearMap.finrank_range_of_inj injective_veroneseSurfaceDeriv_one, Module.finrank_fin_fun]

/-- The tangent space to `X̂` at `(0,1,0)⊗(0,1,0)` has dimension `3`, since
`veroneseSurfaceDeriv (0,1,0)` is injective. -/
theorem finrank_tangentSpace_veroneseSurfaceParam_two :
    Module.finrank 𝕜 (veroneseSurfaceParam (![0, 1, 0] : Fin 3 → 𝕜)).tangentSpace = 3 := by
  show Module.finrank 𝕜
      (LinearMap.range (veroneseSurfaceDeriv (![0, 1, 0] : Fin 3 → 𝕜)).toLinearMap) = 3
  rw [LinearMap.finrank_range_of_inj injective_veroneseSurfaceDeriv_two, Module.finrank_fin_fun]

/-- The expected (non-defective) dimension for the two-point family at `e₁ = (1,0,0)` and
`e₂ = (0,1,0)` is `min(6, 3+3) = 6`. -/
theorem expectedDim_veroneseSurface :
    expectedDim (fun i : Fin 2 =>
      (veroneseSurfaceParamPair (![1, 0, 0] : Fin 3 → 𝕜) (![0, 1, 0] : Fin 3 → 𝕜) i).tangentSpace)
      = 6 := by
  unfold expectedDim
  rw [Module.finrank_fin_fun, Fin.sum_univ_two]
  show min 6
      (Module.finrank 𝕜 (veroneseSurfaceParam (![1, 0, 0] : Fin 3 → 𝕜)).tangentSpace +
        Module.finrank 𝕜 (veroneseSurfaceParam (![0, 1, 0] : Fin 3 → 𝕜)).tangentSpace) = 6
  rw [finrank_tangentSpace_veroneseSurfaceParam_one, finrank_tangentSpace_veroneseSurfaceParam_two]
  decide

/-- The combined tangent space of `e₁ = (1,0,0)` and `e₂ = (0,1,0)` has dimension `5`, by
`veroneseSurface_terracini` and `finrank_ker_coordProj_six_two`. -/
theorem finrank_iSup_veroneseSurface :
    Module.finrank 𝕜 ((⨆ i : Fin 2,
      (veroneseSurfaceParamPair (![1, 0, 0] : Fin 3 → 𝕜) (![0, 1, 0] : Fin 3 → 𝕜) i).tangentSpace)
      : Submodule 𝕜 (Fin 6 → 𝕜))
      = 5 := by
  rw [← veroneseSurface_terracini, finrank_ker_coordProj_six_two]

/-- **The quadric Veronese surface `v₂(ℙ²) ⊂ ℙ⁵` is Alexander–Hirschowitz defective.** The
combined tangent space of the two points `e₁ = (1,0,0)` and `e₂ = (0,1,0)` falls short of the
expected (non-defective) dimension `min(6, 3+3) = 6`. -/
theorem veroneseSurface_isDefective :
    IsDefective (fun i : Fin 2 =>
      (veroneseSurfaceParamPair (![1, 0, 0] : Fin 3 → 𝕜) (![0, 1, 0] : Fin 3 → 𝕜) i).tangentSpace) := by
  simp only [IsDefective, finrank_iSup_veroneseSurface, expectedDim_veroneseSurface]
  decide

/-- **The defect of `σ₂(v₂(ℙ²))` is exactly `1`**: the classical Alexander–Hirschowitz defect of
the quadric Veronese surface, matching the `1`-dimensional shortfall of the determinantal cubic
hypersurface `σ₂(v₂(ℙ²)) ⊂ ℙ⁵` (of dimension `4`) below the expected `5`. -/
theorem defect_veroneseSurface :
    defect (fun i : Fin 2 =>
      (veroneseSurfaceParamPair (![1, 0, 0] : Fin 3 → 𝕜) (![0, 1, 0] : Fin 3 → 𝕜) i).tangentSpace)
      = 1 := by
  simp only [defect, finrank_iSup_veroneseSurface, expectedDim_veroneseSurface]

end VeroneseSurfaceDefect

/-!
## Extending `σ₂` to `σ_r`: the parabola, Segre quadric, and elliptic curve

`parabola_terracini`, `segre_terracini`, and `elliptic_terracini` each show that the combined
tangent space of *two* general points already fills the ambient space — the superabundant case
of §7's monotonicity. By `not_isDefective_of_sup_eq_top`, this propagates to *any* larger family
containing those two tangent spaces among its members: `σ_r` is non-defective for every `r ≥ 2`,
no matter what the other `r - 2` points are or what their tangent spaces look like.
-/

noncomputable section ExtendedExamples

variable {𝕜 : Type*}

/-- **`σ_r(v₂(ℙ¹))` is non-defective for every `r ≥ 2`.** If two members of a family `S` of
tangent spaces in `𝕜²` are the tangent lines to the parabola at `(t₁,t₁²)` and `(t₂,t₂²)`
(`t₁ ≠ t₂`), then `S` is non-defective — these two tangent lines already span `𝕜²`
(`parabola_terracini`), so adding any further points cannot create a defect. -/
theorem parabola_not_isDefective [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    {t₁ t₂ : 𝕜} (h : t₁ ≠ t₂)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ι → Submodule 𝕜 (𝕜 × 𝕜))
    {i₀ i₁ : ι}
    (h₀ : S i₀ = (parabolaParamPair t₁ t₂ 0).tangentSpace)
    (h₁ : S i₁ = (parabolaParamPair t₁ t₂ 1).tangentSpace) :
    ¬ IsDefective S := by
  apply not_isDefective_of_sup_eq_top S (i₀ := i₀) (i₁ := i₁)
  rw [h₀, h₁, parabola_terracini t₁ t₂ h, iSup_fin_two]

/-- **`σ_r(ℙ¹ × ℙ¹ ⊂ ℙ³)` is non-defective for every `r ≥ 2`.** If two members of a family `S`
of tangent spaces in `𝕜³` are the tangent planes to the Segre quadric at `segre p₁` and
`segre p₂` (`p₁ ≠ p₂`), then `S` is non-defective — these two tangent planes already span `𝕜³`
(`segre_terracini`), so adding any further points cannot create a defect. -/
theorem segre_not_isDefective [NontriviallyNormedField 𝕜]
    {p₁ p₂ : 𝕜 × 𝕜} (h : p₁ ≠ p₂)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ι → Submodule 𝕜 (𝕜 × 𝕜 × 𝕜))
    {i₀ i₁ : ι}
    (h₀ : S i₀ = (segreParamPair p₁ p₂ 0).tangentSpace)
    (h₁ : S i₁ = (segreParamPair p₁ p₂ 1).tangentSpace) :
    ¬ IsDefective S := by
  apply not_isDefective_of_sup_eq_top S (i₀ := i₀) (i₁ := i₁)
  rw [h₀, h₁, segre_terracini p₁ p₂ h, iSup_fin_two]

/-- **`σ_r(y² = x³ + 1)` is non-defective for every `r ≥ 2`.** If two members of a family `S`
of tangent spaces in `𝕜²` (modeled as `Fin 2 → 𝕜`) are the tangent lines to the elliptic curve
at `(0,1)` and `(2,3)`, then `S` is non-defective — these two tangent lines already span `𝕜²`
(`elliptic_terracini`), so adding any further points cannot create a defect. -/
theorem elliptic_not_isDefective [RCLike 𝕜]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ι → Submodule 𝕜 (Fin 2 → 𝕜))
    {i₀ i₁ : ι}
    (h₀ : S i₀ = (ellipticParamPair (𝕜 := 𝕜) 0).tangentSpace)
    (h₁ : S i₁ = (ellipticParamPair (𝕜 := 𝕜) 1).tangentSpace) :
    ¬ IsDefective S := by
  apply not_isDefective_of_sup_eq_top S (i₀ := i₀) (i₁ := i₁)
  rw [h₀, h₁, elliptic_terracini, iSup_fin_two]

end ExtendedExamples
