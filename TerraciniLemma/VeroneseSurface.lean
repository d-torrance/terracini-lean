import TerraciniLemma.PolynomialCalculus
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Complex.Basic

/-!
# Worked example: the quadric Veronese surface `v₂(ℙ²) ⊂ ℙ⁵` (a genuinely defective case)

Every previous Veronese example (`TerraciniLemma.RationalNormalCurves`) used the **affine chart** model:
`X ⊆ 𝕜^N` is the affine chart of `v_d(ℙⁿ) ⊂ ℙᴺ` (so `dim X = n`, ambient `N`), and tangent
spaces have dimension `n`. As explained there, for that model the combined tangent space of
`r` general points has dimension `min(N, r·n)`, which is *always* self-consistent — it can
never witness a genuine Alexander–Hirschowitz defect, since rational normal curves (`n = 1`)
are never defective and higher Veroneses need `n ≥ 2`, where the affine-chart "expected"
dimension and the true projective expected dimension differ by a systematic shift.

Here we instead use the **affine cone** model directly, as described in the project's `README`:
the cone `X̂ ⊆ 𝕜^{N+1}` over `v₂(ℙ²) ⊂ ℙ⁵` is

    X̂ = { v ⊗ v : v ∈ 𝕜³ } = { (v₀², v₁², v₂², v₀v₁, v₀v₂, v₁v₂) : v ∈ 𝕜³ } ⊆ 𝕜⁶,

i.e. the cone of symmetric `3×3` matrices `v·vᵗ` of rank `≤ 1`. Here `dim X̂ = n + 1 = 3` and
the ambient dimension is `N + 1 = 6`, so for `r = 2` general points the **non-defective
expectation** is `min(6, 2·3) = 6 = dim 𝕜⁶`, i.e. `σ₂(v₂(ℙ²))` should fill `ℙ⁵`.

It does not: by the Alexander–Hirschowitz theorem, `σ₂(v₂(ℙ²))` is the classical
**determinantal cubic hypersurface** `{rank ≤ 2 symmetric 3×3 matrices} ⊂ ℙ⁵`, of (projective)
dimension `4`, one short of the expected `5` — the defect is `1`. We exhibit this directly: at
the two points `e₁ = (1,0,0)` and `e₂ = (0,1,0)` (two of the three coordinate points of `ℙ²`,
corresponding to the rank-1 matrices `diag(1,0,0)` and `diag(0,1,0)`), the combined derivative
of the two-point parametrization has image *exactly* the hyperplane

    T = ker (coordProj 6 2) = { x : Fin 6 → 𝕜 | x 2 = 0 } ⊆ 𝕜⁶,

a `5`-dimensional subspace, **not** all of `𝕜⁶`. Terracini's Lemma then gives

    T = T_{e₁⊗e₁} X̂ + T_{e₂⊗e₂} X̂  ⊊ 𝕜⁶ = (the non-defective expectation),

which is exactly the Alexander–Hirschowitz defect of the quadric Veronese surface, in contrast
to `TerraciniLemma.RationalNormalCurves`'s twisted cubic (where the analogous "shortfall" was the *expected,
generic* outcome, not a defect).

The calculus of the six degree-`2` monomials `v₀², v₁², v₂², v₀v₁, v₀v₂, v₁v₂` is obtained, as
for the elliptic curve, from `TerraciniLemma.PolynomialCalculus`'s generic `MvPolynomial.pderiv`
↔ `HasFDerivAt` bridge.
-/

noncomputable section VeroneseSurfaceExample

open MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-- The six degree-`2` monomials `x₀², x₁², x₂², x₀x₁, x₀x₂, x₁x₂` whose common evaluation map
`𝕜³ → 𝕜⁶` parametrizes the affine cone `X̂` over the quadric Veronese surface `v₂(ℙ²) ⊂ ℙ⁵`. -/
def veronesePoly : Fin 6 → MvPolynomial (Fin 3) 𝕜
  | 0 => X 0 ^ 2
  | 1 => X 1 ^ 2
  | 2 => X 2 ^ 2
  | 3 => X 0 * X 1
  | 4 => X 0 * X 2
  | 5 => X 1 * X 2

/-- The affine cone `X̂ = {(v₀², v₁², v₂², v₀v₁, v₀v₂, v₁v₂) : v ∈ 𝕜³} ⊆ 𝕜⁶` over the quadric
Veronese surface `v₂(ℙ²) ⊂ ℙ⁵` (equivalently, the rank-`≤1` symmetric `3×3` matrices `v·vᵗ`). -/
def veroneseSurface (v : Fin 3 → 𝕜) : Fin 6 → 𝕜 :=
  fun i => eval v (veronesePoly i)

/-- The components of the derivative of `veroneseSurface` at `v`:
`(2v₀)•π₀, (2v₁)•π₁, (2v₂)•π₂, v₁•π₀+v₀•π₁, v₂•π₀+v₀•π₂, v₂•π₁+v₁•π₂`, where `πᵢ = coordProj 3 i`. -/
def veroneseSurfaceDerivComp (v : Fin 3 → 𝕜) : Fin 6 → (Fin 3 → 𝕜) →L[𝕜] 𝕜
  | 0 => (2 * v 0) • coordProj 3 0
  | 1 => (2 * v 1) • coordProj 3 1
  | 2 => (2 * v 2) • coordProj 3 2
  | 3 => v 1 • coordProj 3 0 + v 0 • coordProj 3 1
  | 4 => v 2 • coordProj 3 0 + v 0 • coordProj 3 2
  | 5 => v 2 • coordProj 3 1 + v 1 • coordProj 3 2

/-- The derivative of `veroneseSurface` at `v`, as a continuous linear map `𝕜³ →L[𝕜] 𝕜⁶`. -/
def veroneseSurfaceDeriv (v : Fin 3 → 𝕜) : (Fin 3 → 𝕜) →L[𝕜] (Fin 6 → 𝕜) :=
  ContinuousLinearMap.pi (veroneseSurfaceDerivComp v)

omit [CharZero 𝕜] in
@[simp]
theorem veroneseSurfaceDeriv_apply (v dv : Fin 3 → 𝕜) (i : Fin 6) :
    veroneseSurfaceDeriv v dv i = veroneseSurfaceDerivComp v i dv :=
  ContinuousLinearMap.pi_apply _ _ _

omit [CharZero 𝕜] in
/-- `veroneseSurfaceDerivComp v i` agrees with the formal derivative
`mvPolynomialDeriv (veronesePoly i) v` from `TerraciniLemma.PolynomialCalculus`. -/
theorem mvPolynomialDeriv_veronesePoly (v : Fin 3 → 𝕜) (i : Fin 6) :
    mvPolynomialDeriv (veronesePoly i) v = veroneseSurfaceDerivComp v i := by
  fin_cases i <;>
  · apply ContinuousLinearMap.ext
    intro dv
    simp [mvPolynomialDeriv, veronesePoly, veroneseSurfaceDerivComp, Fin.sum_univ_three,
      coordProj_apply, eval_mul, eval_X, smul_eq_mul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply]

omit [CharZero 𝕜] in
/-- `veroneseSurfaceDeriv v` is the Fréchet derivative of `veroneseSurface` at `v`. -/
theorem hasFDerivAt_veroneseSurface (v : Fin 3 → 𝕜) :
    HasFDerivAt veroneseSurface (veroneseSurfaceDeriv v) v := by
  apply (hasFDerivAt_pi (φ := fun i y => eval y (veronesePoly i))
    (φ' := fun i => veroneseSurfaceDerivComp v i) (x := v)).2
  intro i
  rw [← mvPolynomialDeriv_veronesePoly v i]
  exact hasFDerivAt_eval_mvPolynomial (veronesePoly i) v

omit [CharZero 𝕜] in
/-- Closed form for `veroneseSurfaceDeriv v dv`:
`dv ↦ (2v₀dv₀, 2v₁dv₁, 2v₂dv₂, v₁dv₀+v₀dv₁, v₂dv₀+v₀dv₂, v₂dv₁+v₁dv₂)`. -/
theorem veroneseSurfaceDeriv_apply' (v dv : Fin 3 → 𝕜) :
    veroneseSurfaceDeriv v dv =
      ![2 * v 0 * dv 0, 2 * v 1 * dv 1, 2 * v 2 * dv 2, v 1 * dv 0 + v 0 * dv 1,
        v 2 * dv 0 + v 0 * dv 2, v 2 * dv 1 + v 1 * dv 2] := by
  funext i
  fin_cases i <;>
    simp [veroneseSurfaceDeriv_apply, veroneseSurfaceDerivComp, coordProj_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- The local parametrization of `veroneseSurface` (the cone over `v₂(ℙ²)`) at parameter `v`. -/
def veroneseSurfaceParam (v : Fin 3 → 𝕜) :
    LocalParam (𝕜 := 𝕜) (𝔸 := Fin 3 → 𝕜) (Set.range veroneseSurface) (veroneseSurface v) where
  basePoint := v
  chart := veroneseSurface
  chart_eval := rfl
  tangent := veroneseSurfaceDeriv v
  hasFDerivAt := hasFDerivAt_veroneseSurface v

/-- The pair of local parametrizations at `v₁` and `v₂` (see `parabolaParamPair` for why this
needs a pattern-matching definition rather than `![·, ·]` notation). -/
def veroneseSurfaceParamPair (v₁ v₂ : Fin 3 → 𝕜) :
    ∀ i : Fin 2, LocalParam (𝕜 := 𝕜) (𝔸 := Fin 3 → 𝕜)
      (Set.range veroneseSurface) (![veroneseSurface v₁, veroneseSurface v₂] i)
  | 0 => veroneseSurfaceParam v₁
  | 1 => veroneseSurfaceParam v₂

/-- The first of the two points used below: `e₁ = (1,0,0)`, one of the three coordinate points
of `ℙ²` (corresponding to the rank-`1` matrix `diag(1,0,0)`). Written as local notation (as in
`Segre.lean`'s `segre3Pt1`/`segre3Pt2`) so that each use site elaborates `𝕜` as the ambient
declaration's own field. -/
local notation "vsPt1" => (![1, 0, 0] : Fin 3 → 𝕜)

/-- The second point: `e₂ = (0,1,0)`, corresponding to the rank-`1` matrix `diag(0,1,0)`. -/
local notation "vsPt2" => (![0, 1, 0] : Fin 3 → 𝕜)

omit [CharZero 𝕜] in
/-- The combined derivative of the two-point parametrization at `e₁ = (1,0,0)` and
`e₂ = (0,1,0)`, in closed form. -/
theorem combinedDerivative_veroneseSurface_apply (w : Fin 2 → Fin 3 → 𝕜) :
    combinedDerivative (v := ![veroneseSurface vsPt1, veroneseSurface vsPt2])
      (veroneseSurfaceParamPair vsPt1 vsPt2) w =
      ![2 * w 0 0, 2 * w 1 1, 0, w 0 1 + w 1 0, w 0 2, w 1 2] := by
  funext i
  simp only [combinedDerivative, veroneseSurfaceParamPair, veroneseSurfaceParam, Fin.sum_univ_two,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, coordProj_apply,
    veroneseSurfaceDeriv_apply', Pi.add_apply]
  fin_cases i <;> simp

omit [CharZero 𝕜] in
/-- The image of the combined derivative at `e₁` and `e₂` lies in `ker (coordProj 6 2)`: every
tangent vector to `σ₂` at this pair of points satisfies `x₂ = 0`. -/
theorem hdominant_veroneseSurface :
    LinearMap.range (combinedDerivative (v := ![veroneseSurface vsPt1, veroneseSurface vsPt2])
      (veroneseSurfaceParamPair vsPt1 vsPt2)).toLinearMap ≤
      LinearMap.ker (coordProj (𝕜 := 𝕜) 6 2).toLinearMap := by
  rintro x ⟨w, rfl⟩
  simp [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, coordProj_apply,
    combinedDerivative_veroneseSurface_apply]

/-- The range of the combined derivative at `e₁ = (1,0,0)` and `e₂ = (0,1,0)` is *exactly* the
hyperplane `ker (coordProj 6 2) = {x : x₂ = 0}`: given `x` with `x 2 = 0`, the preimage
`w = ((x₀/2, x₃, x₄), (0, x₁/2, x₅))` satisfies `combinedDerivative w = (x₀, x₁, 0, x₃, x₄, x₅) = x`. -/
theorem range_combinedDerivative_veroneseSurface :
    LinearMap.range (combinedDerivative (v := ![veroneseSurface vsPt1, veroneseSurface vsPt2])
      (veroneseSurfaceParamPair vsPt1 vsPt2)).toLinearMap =
      LinearMap.ker (coordProj (𝕜 := 𝕜) 6 2).toLinearMap := by
  refine le_antisymm hdominant_veroneseSurface fun x hx => ?_
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, coordProj_apply] at hx
  refine ⟨![![x 0 / 2, x 3, x 4], ![0, x 1 / 2, x 5]], ?_⟩
  simp only [ContinuousLinearMap.coe_coe, combinedDerivative_veroneseSurface_apply]
  funext i
  fin_cases i <;> simp [hx] <;> field_simp

/-- The "defect" functional `coordProj 6 2 : x ↦ x₂` is nonzero, so `ker (coordProj 6 2)` is a
proper hyperplane. -/
theorem coordProj_six_two_ne_zero : (coordProj (𝕜 := 𝕜) (𝔸 := 𝕜) 6 2).toLinearMap ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg DFunLike.coe h) (Pi.single 2 1)
  simp at h2

/-- `ker (coordProj 6 2)` has dimension `5` (a hyperplane in `𝕜⁶`). -/
theorem finrank_ker_coordProj_six_two :
    Module.finrank 𝕜 (LinearMap.ker (coordProj (𝕜 := 𝕜) (𝔸 := 𝕜) 6 2).toLinearMap) = 5 := by
  have hrange : LinearMap.range (coordProj (𝕜 := 𝕜) (𝔸 := 𝕜) 6 2).toLinearMap = ⊤ :=
    Module.Dual.range_eq_top_of_ne_zero coordProj_six_two_ne_zero
  have hsum := LinearMap.finrank_range_add_finrank_ker (coordProj (𝕜 := 𝕜) (𝔸 := 𝕜) 6 2).toLinearMap
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at hsum
  omega

/-- **Terracini's Lemma for the quadric Veronese surface `v₂(ℙ²) ⊂ ℙ⁵`.** At `e₁ = (1,0,0)`
and `e₂ = (0,1,0)`, the sum of the two tangent spaces (to the affine cone `X̂`) is exactly the
hyperplane `T = ker (coordProj 6 2)`, of dimension `5` — *not* all of `𝕜⁶`, even though
`min(6, 2·3) = 6` would be the non-defective expectation. This is the Alexander–Hirschowitz
defect of `σ₂(v₂(ℙ²))` (the determinantal cubic hypersurface, of dimension `4` in `ℙ⁵`, one
short of the expected `5`). -/
theorem veroneseSurface_terracini :
    LinearMap.ker (coordProj (𝕜 := 𝕜) 6 2).toLinearMap =
      ⨆ i : Fin 2, (veroneseSurfaceParamPair vsPt1 vsPt2 i).tangentSpace := by
  have hgeneric : Module.finrank 𝕜 (LinearMap.ker (coordProj (𝕜 := 𝕜) 6 2).toLinearMap) ≤
      Module.finrank 𝕜 (LinearMap.range (combinedDerivative
        (v := ![veroneseSurface vsPt1, veroneseSurface vsPt2])
        (veroneseSurfaceParamPair vsPt1 vsPt2)).toLinearMap) :=
    le_of_eq (by rw [range_combinedDerivative_veroneseSurface])
  exact terraciniLemma ![veroneseSurface vsPt1, veroneseSurface vsPt2]
    (fun i => by fin_cases i <;> exact ⟨_, rfl⟩)
    (veroneseSurfaceParamPair vsPt1 vsPt2) (LinearMap.ker (coordProj (𝕜 := 𝕜) 6 2).toLinearMap)
    hdominant_veroneseSurface hgeneric

/-- The defective secant variety `σ₂(v₂(ℙ²))` is a proper (hyperplane) subvariety of the cone
`𝕜⁶`: the combined tangent space `T` has dimension `5`, not `6 = min(6, 2 · 3)`. -/
theorem veroneseSurface_terracini_ne_top :
    LinearMap.ker (coordProj (𝕜 := 𝕜) (𝔸 := 𝕜) 6 2).toLinearMap ≠ ⊤ := by
  intro h
  have h6 : Module.finrank 𝕜 (LinearMap.ker (coordProj (𝕜 := 𝕜) (𝔸 := 𝕜) 6 2).toLinearMap) = 6 := by
    rw [h, finrank_top, Module.finrank_fin_fun]
  rw [finrank_ker_coordProj_six_two] at h6
  exact absurd h6 (by norm_num)

/-- Sanity check: the quadric Veronese surface example specializes to `ℂ` for free. -/
example :
    LinearMap.ker (coordProj (𝕜 := ℂ) 6 2).toLinearMap =
      ⨆ i : Fin 2,
        (veroneseSurfaceParamPair (![1, 0, 0] : Fin 3 → ℂ) (![0, 1, 0] : Fin 3 → ℂ) i).tangentSpace :=
  veroneseSurface_terracini

end VeroneseSurfaceExample
