import TerraciniLemma.VeroneseSurface
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

/-- `finrank` is subadditive over a finite supremum of submodules. -/
theorem finrank_iSup_le {ι : Type*} [Fintype ι] [DecidableEq ι] (S : ι → Submodule 𝕜 E) :
    Module.finrank 𝕜 ((⨆ i, S i : Submodule 𝕜 E)) ≤ ∑ i, Module.finrank 𝕜 (S i) := by
  have hsup : (⨆ i, S i) = Finset.univ.sup S :=
    le_antisymm (iSup_le fun i => Finset.le_sup (Finset.mem_univ i))
      (Finset.sup_le fun i _ => le_iSup S i)
  rw [hsup]
  exact finrank_finsetSup_le S Finset.univ

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
