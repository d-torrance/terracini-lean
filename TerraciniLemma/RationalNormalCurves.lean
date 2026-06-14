import TerraciniLemma.Core
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Basic

/-!
# Worked examples: rational normal curves

The `r`-th Veronese embedding `v_r : ℙ¹ → ℙ^r` sends `[s:t]` to the vector of
all monomials of degree `r` in `s, t`; its image is the rational normal curve
of degree `r`. Its affine chart is `t ↦ (t, t², …, tʳ) ⊆ 𝕜^r`.

This file contains the case `r = 2`, the plane conic (parabola), and the case
`r = 3`, the twisted cubic. Further rational normal curve examples can be
added here following the same `parabolaParamPair`/`twistedCubicParamPair`
pattern. (For Veronese varieties `v_d(ℙⁿ)` with `n ≥ 2`, see
`TerraciniLemma.VeroneseSurface`.)
-/

/-!
## Example: Terracini's Lemma for a plane conic

As a concrete sanity check, we apply `terraciniLemma` to the simplest
nontrivial case: the standard parabola X = {(t, t²) : t ∈ 𝕜} ⊆ 𝕜², the
affine picture of a smooth conic (a rational normal curve of degree 2), for
an arbitrary `NontriviallyNormedField 𝕜` of characteristic zero (e.g. `ℝ` or
`ℂ`).

For t₁ ≠ t₂, the tangent line to X at (tᵢ, tᵢ²) is spanned by (1, 2tᵢ). We
show that the combined derivative of the two-point parametrization is
surjective onto 𝕜², so Terracini's Lemma gives

    𝕜² = T_{(t₁,t₁²)} X + T_{(t₂,t₂²)} X,

matching the classical fact that the second secant variety of a
non-degenerate plane conic is the whole plane. The proof solves
`s₁ = (b - 2 t₂ a) / (2 (t₁ - t₂))`, which requires `2 ≠ 0`, i.e.
characteristic zero (the parabola is genuinely special in characteristic 2:
its tangent direction `(1, 2t) = (1, 0)` is constant, so the tangent lines
never span `𝕜²`).

**Affine chart vs. cone.** The ambient `𝕜²` here is the affine chart
`{[1:s:u]} ⊂ ℙ²` of the conic `v₂(ℙ¹) ⊂ ℙ²`, not the affine cone
`𝕜³ = Sym²(𝕜²)` over it. So `parabola_terracini` is a *chart-level*
computation: it does not descend via `Submodule.projectivization`
(`TerraciniLemma.Projective`) to a statement about `ℙ(σ₂(v₂(ℙ¹)))`. For that,
one would need to redo the computation in the cone `𝕜³`, as
`TerraciniLemma.VeroneseSurface` does for `v₂(ℙ²)`.
-/

noncomputable section ParabolaExample

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-- The standard parabola `t ↦ (t, t²)`. -/
def parabola (t : 𝕜) : 𝕜 × 𝕜 := (t, t ^ 2)

/-- The derivative of the parabola at `t`: the linear map `s ↦ (s, 2 t s)`. -/
def parabolaDeriv (t : 𝕜) : 𝕜 →L[𝕜] 𝕜 × 𝕜 :=
  (ContinuousLinearMap.id 𝕜 𝕜).prod ((2 * t) • ContinuousLinearMap.id 𝕜 𝕜)

omit [CharZero 𝕜] in
@[simp]
theorem parabolaDeriv_apply (t s : 𝕜) : parabolaDeriv t s = (s, 2 * t * s) := by
  simp [parabolaDeriv]

omit [CharZero 𝕜] in
theorem hasFDerivAt_parabola (t : 𝕜) : HasFDerivAt parabola (parabolaDeriv t) t := by
  have h2 : HasFDerivAt (fun x : 𝕜 => x ^ 2) ((2 * t) • ContinuousLinearMap.id 𝕜 𝕜) t := by
    have hp := (Polynomial.X ^ 2 : Polynomial 𝕜).hasFDerivAt t
    have heval : (fun x : 𝕜 => (Polynomial.X ^ 2 : Polynomial 𝕜).eval x) = fun x : 𝕜 => x ^ 2 := by
      funext x; simp
    have hderiv : (Polynomial.X ^ 2 : Polynomial 𝕜).derivative.eval t = 2 * t := by
      simp only [Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Nat.cast_ofNat]
      norm_num
    rw [heval, hderiv] at hp
    have hsmul : ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) (2 * t)
        = (2 * t) • ContinuousLinearMap.id 𝕜 𝕜 :=
      ContinuousLinearMap.ext fun x => by simp [mul_comm]
    rwa [hsmul] at hp
  exact (hasFDerivAt_id t).prodMk h2

/-- The local parametrization of the parabola at parameter `t`. -/
def parabolaParam (t : 𝕜) :
    LocalParam (𝕜 := 𝕜) (𝔸 := 𝕜) (Set.range parabola) (parabola t) where
  basePoint := t
  chart := parabola
  chart_eval := rfl
  tangent := parabolaDeriv t
  hasFDerivAt := hasFDerivAt_parabola t

/-- The pair of local parametrizations at `t₁` and `t₂`, as a dependent
function `Fin 2 → LocalParam ...` (the types at `0` and `1` differ, since
the base points `parabola t₁ ≠ parabola t₂`, so `![·, ·]` notation does
not apply). -/
def parabolaParamPair (t₁ t₂ : 𝕜) :
    ∀ i : Fin 2, LocalParam (𝕜 := 𝕜) (𝔸 := 𝕜)
      (Set.range parabola) (![parabola t₁, parabola t₂] i)
  | 0 => parabolaParam t₁
  | 1 => parabolaParam t₂

/-- For `t₁ ≠ t₂`, the combined derivative `Dφ_{t₁} + Dφ_{t₂}` of the
two-point parametrization is surjective onto `𝕜²`: every `(a, b)` equals
`parabolaDeriv t₁ s₁ + parabolaDeriv t₂ s₂` for suitable `s₁, s₂`. -/
theorem combinedDerivative_parabola_surjective (t₁ t₂ : 𝕜) (h : t₁ ≠ t₂) :
    Function.Surjective
      (combinedDerivative (v := ![parabola t₁, parabola t₂])
        (parabolaParamPair t₁ t₂)) := by
  have ht : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h
  rintro ⟨a, b⟩
  set s₁ : 𝕜 := (b - 2 * t₂ * a) / (2 * (t₁ - t₂)) with hs₁
  refine ⟨![s₁, a - s₁], ?_⟩
  simp only [combinedDerivative, parabolaParamPair, parabolaParam, Fin.sum_univ_two,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, coordProj_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    parabolaDeriv_apply, Prod.mk_add_mk]
  rw [Prod.mk.injEq]
  refine ⟨by ring, ?_⟩
  rw [hs₁]
  field_simp
  ring

/-- **Terracini's Lemma for the parabola**, over an arbitrary
`NontriviallyNormedField 𝕜` of characteristic zero. For `t₁ ≠ t₂`, the
tangent lines to the parabola at `(t₁,t₁²)` and `(t₂,t₂²)` together span all
of `𝕜²` — matching the fact that the second secant variety of a
non-degenerate plane conic is the whole plane, over `ℝ`, `ℂ`, or any other
characteristic-zero field. -/
theorem parabola_terracini (t₁ t₂ : 𝕜) (h : t₁ ≠ t₂) :
    (⊤ : Submodule 𝕜 (𝕜 × 𝕜)) =
      ⨆ i : Fin 2, (parabolaParamPair t₁ t₂ i).tangentSpace := by
  have hrange : LinearMap.range
      (combinedDerivative (v := ![parabola t₁, parabola t₂])
        (parabolaParamPair t₁ t₂)).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr (combinedDerivative_parabola_surjective t₁ t₂ h)
  have hgeneric : Module.finrank 𝕜 (⊤ : Submodule 𝕜 (𝕜 × 𝕜)) ≤
      Module.finrank 𝕜 (LinearMap.range
        (combinedDerivative (v := ![parabola t₁, parabola t₂])
          (parabolaParamPair t₁ t₂)).toLinearMap) :=
    le_of_eq (by rw [hrange])
  exact terraciniLemma ![parabola t₁, parabola t₂]
    (fun i => by fin_cases i <;> exact ⟨_, rfl⟩)
    (parabolaParamPair t₁ t₂) ⊤ le_top hgeneric

/-- Sanity check: the parabola example specializes to `ℂ` for free. -/
example (t₁ t₂ : ℂ) (h : t₁ ≠ t₂) :
    (⊤ : Submodule ℂ (ℂ × ℂ)) =
      ⨆ i : Fin 2, (parabolaParamPair t₁ t₂ i).tangentSpace :=
  parabola_terracini t₁ t₂ h

end ParabolaExample

/-!
## Example: Terracini's Lemma for the twisted cubic (a proper hyperplane span)

We now turn to the twisted cubic `X = {(t, t², t³) : t ∈ 𝕜} ⊆ 𝕜³`, the affine
chart of the rational normal curve `v₃(ℙ¹) ⊂ ℙ³`. The tangent line to `X` at
`(t, t², t³)` is spanned by `(1, 2t, 3t²)`.

Unlike the parabola (`r = 2`, ambient `𝕜²`, where `r · dim X = 2 · 1 = 2`
equals the ambient dimension, so the two tangent directions fill `𝕜²`), here
`r · dim X = 2 < 3 = dim 𝕜³`: two 1-dimensional tangent directions can only
ever span a 2-dimensional subspace, so their combined span is necessarily a
*proper* (hyperplane) subspace of `𝕜³`. This is the **expected/generic**
outcome whenever `r · dim X < N` — it is *not* an instance of defectivity in
the sense of the Alexander–Hirschowitz theorem (which concerns higher Veronese
varieties `v_d(ℙⁿ)`, `n ≥ 2`; rational normal curves such as the twisted cubic
are never defective).

Concretely, at the points `t₁ = 0` and `t₂ = 1` the tangent directions are
`(1, 0, 0)` and `(1, 2, 3)`, which are linearly independent and both satisfy
`3y = 2z`. We show that their span is *exactly* the hyperplane
`{(x, y, z) : 3y = 2z}`, so Terracini's Lemma gives

    {(x, y, z) : 3y = 2z} = T_{(0,0,0)} X + T_{(1,1,1)} X.

**Affine chart vs. cone.** As with the parabola above, `𝕜³` here is the
affine chart `{[1:s:u:w]} ⊂ ℙ³` of the twisted cubic `v₃(ℙ¹) ⊂ ℙ³`, not the
4-dimensional affine cone over it. So `twistedCubic_terracini` is a
chart-level computation and does not directly feed into
`TerraciniLemma.Projective`'s `Submodule.projectivization` descent.
-/

noncomputable section TwistedCubicExample

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-- The twisted cubic `t ↦ (t, t², t³)`. -/
def twistedCubic (t : 𝕜) : 𝕜 × 𝕜 × 𝕜 := (t, t ^ 2, t ^ 3)

/-- The derivative of the twisted cubic at `t`: the linear map `s ↦ (s, 2 t s, 3 t² s)`. -/
def twistedCubicDeriv (t : 𝕜) : 𝕜 →L[𝕜] 𝕜 × 𝕜 × 𝕜 :=
  (ContinuousLinearMap.id 𝕜 𝕜).prod
    (((2 * t) • ContinuousLinearMap.id 𝕜 𝕜).prod ((3 * t ^ 2) • ContinuousLinearMap.id 𝕜 𝕜))

omit [CharZero 𝕜] in
@[simp]
theorem twistedCubicDeriv_apply (t s : 𝕜) :
    twistedCubicDeriv t s = (s, 2 * t * s, 3 * t ^ 2 * s) := by
  simp [twistedCubicDeriv]

omit [CharZero 𝕜] in
theorem hasFDerivAt_twistedCubic (t : 𝕜) : HasFDerivAt twistedCubic (twistedCubicDeriv t) t := by
  have h2 : HasFDerivAt (fun x : 𝕜 => x ^ 2) ((2 * t) • ContinuousLinearMap.id 𝕜 𝕜) t := by
    have hp := (Polynomial.X ^ 2 : Polynomial 𝕜).hasFDerivAt t
    have heval : (fun x : 𝕜 => (Polynomial.X ^ 2 : Polynomial 𝕜).eval x) = fun x : 𝕜 => x ^ 2 := by
      funext x; simp
    have hderiv : (Polynomial.X ^ 2 : Polynomial 𝕜).derivative.eval t = 2 * t := by
      simp only [Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Nat.cast_ofNat]
      norm_num
    rw [heval, hderiv] at hp
    have hsmul : ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) (2 * t)
        = (2 * t) • ContinuousLinearMap.id 𝕜 𝕜 :=
      ContinuousLinearMap.ext fun x => by simp [mul_comm]
    rwa [hsmul] at hp
  have h3 : HasFDerivAt (fun x : 𝕜 => x ^ 3) ((3 * t ^ 2) • ContinuousLinearMap.id 𝕜 𝕜) t := by
    have hp := (Polynomial.X ^ 3 : Polynomial 𝕜).hasFDerivAt t
    have heval : (fun x : 𝕜 => (Polynomial.X ^ 3 : Polynomial 𝕜).eval x) = fun x : 𝕜 => x ^ 3 := by
      funext x; simp
    have hderiv : (Polynomial.X ^ 3 : Polynomial 𝕜).derivative.eval t = 3 * t ^ 2 := by
      simp only [Polynomial.derivative_X_pow, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_pow, Polynomial.eval_X, Nat.cast_ofNat]
    rw [heval, hderiv] at hp
    have hsmul : ContinuousLinearMap.smulRight (1 : 𝕜 →L[𝕜] 𝕜) (3 * t ^ 2)
        = (3 * t ^ 2) • ContinuousLinearMap.id 𝕜 𝕜 :=
      ContinuousLinearMap.ext fun x => by simp [mul_comm]
    rwa [hsmul] at hp
  exact (hasFDerivAt_id t).prodMk (h2.prodMk h3)

/-- The local parametrization of the twisted cubic at parameter `t`. -/
def twistedCubicParam (t : 𝕜) :
    LocalParam (𝕜 := 𝕜) (𝔸 := 𝕜) (Set.range twistedCubic) (twistedCubic t) where
  basePoint := t
  chart := twistedCubic
  chart_eval := rfl
  tangent := twistedCubicDeriv t
  hasFDerivAt := hasFDerivAt_twistedCubic t

/-- The pair of local parametrizations at `t₁` and `t₂` (see `parabolaParamPair`). -/
def twistedCubicParamPair (t₁ t₂ : 𝕜) :
    ∀ i : Fin 2, LocalParam (𝕜 := 𝕜) (𝔸 := 𝕜)
      (Set.range twistedCubic) (![twistedCubic t₁, twistedCubic t₂] i)
  | 0 => twistedCubicParam t₁
  | 1 => twistedCubicParam t₂

/-- The linear functional `(x, y, z) ↦ 3y - 2z` on `𝕜 × 𝕜 × 𝕜`. Its kernel is the
hyperplane spanned by the tangent directions `(1, 0, 0)` and `(1, 2, 3)` to the
twisted cubic at `t = 0` and `t = 1`. -/
def twistedCubicDefect : (𝕜 × 𝕜 × 𝕜) →L[𝕜] 𝕜 :=
  (3 : 𝕜) • (ContinuousLinearMap.fst 𝕜 𝕜 𝕜).comp (ContinuousLinearMap.snd 𝕜 𝕜 (𝕜 × 𝕜)) -
    (2 : 𝕜) • (ContinuousLinearMap.snd 𝕜 𝕜 𝕜).comp (ContinuousLinearMap.snd 𝕜 𝕜 (𝕜 × 𝕜))

omit [CharZero 𝕜] in
@[simp]
theorem twistedCubicDefect_apply (q : 𝕜 × 𝕜 × 𝕜) :
    twistedCubicDefect q = 3 * q.2.1 - 2 * q.2.2 := by
  simp [twistedCubicDefect, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, smul_eq_mul]

omit [CharZero 𝕜] in
/-- The combined derivative of the two-point parametrization at `t₁ = 0`, `t₂ = 1`,
in closed form: `(s₀, s₁) ↦ (s₀ + s₁, 2 s₁, 3 s₁)`. -/
theorem combinedDerivative_twistedCubic_apply (w : Fin 2 → 𝕜) :
    combinedDerivative (v := ![twistedCubic (0 : 𝕜), twistedCubic 1])
      (twistedCubicParamPair 0 1) w = (w 0 + w 1, 2 * w 1, 3 * w 1) := by
  simp [combinedDerivative, twistedCubicParamPair, twistedCubicParam, Fin.sum_univ_two,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, coordProj_apply,
    twistedCubicDeriv_apply, Prod.mk_add_mk]

omit [CharZero 𝕜] in
/-- Every vector in the range of the combined derivative satisfies `3y = 2z`: the
image lands inside `ker twistedCubicDefect`. -/
theorem hdominant_twistedCubic :
    LinearMap.range (combinedDerivative (v := ![twistedCubic (0 : 𝕜), twistedCubic 1])
      (twistedCubicParamPair 0 1)).toLinearMap ≤
      LinearMap.ker (twistedCubicDefect).toLinearMap := by
  rintro x ⟨w, rfl⟩
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, twistedCubicDefect_apply,
    combinedDerivative_twistedCubic_apply]
  ring

/-- The range of the combined derivative at `t₁ = 0`, `t₂ = 1` is *exactly* the
hyperplane `ker twistedCubicDefect = {(x, y, z) : 3y = 2z}`: given `(a, b, c)` with
`3b = 2c`, the preimage `w = (a - b/2, b/2)` satisfies
`combinedDerivative w = (a - b/2 + b/2, 2·(b/2), 3·(b/2)) = (a, b, c)`. -/
theorem range_combinedDerivative_twistedCubic :
    LinearMap.range (combinedDerivative (v := ![twistedCubic (0 : 𝕜), twistedCubic 1])
      (twistedCubicParamPair 0 1)).toLinearMap = LinearMap.ker twistedCubicDefect.toLinearMap := by
  refine le_antisymm hdominant_twistedCubic fun x hx => ?_
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, twistedCubicDefect_apply] at hx
  refine ⟨![x.1 - x.2.1 / 2, x.2.1 / 2], ?_⟩
  simp only [ContinuousLinearMap.coe_coe, combinedDerivative_twistedCubic_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Prod.ext_iff, Prod.ext_iff]
  refine ⟨by ring, by field_simp, ?_⟩
  field_simp
  linear_combination hx

/-- **Terracini's Lemma for the twisted cubic `v₃(ℙ¹) ⊂ ℙ³`** (at `t₁ = 0`, `t₂ = 1`):
the tangent lines to the twisted cubic at `(0,0,0)` and `(1,1,1)` together span exactly
the hyperplane `ker twistedCubicDefect = {(x,y,z) : 3y = 2z}` — a proper subspace of
`𝕜³`, since two 1-dimensional tangent directions can span at most a 2-dimensional
subspace. This is the expected/generic outcome (not an instance of defectivity in the
Alexander–Hirschowitz sense; rational normal curves are never defective). -/
theorem twistedCubic_terracini :
    LinearMap.ker twistedCubicDefect.toLinearMap =
      ⨆ i : Fin 2, (twistedCubicParamPair (0 : 𝕜) 1 i).tangentSpace := by
  have hgeneric : Module.finrank 𝕜 (LinearMap.ker twistedCubicDefect.toLinearMap) ≤
      Module.finrank 𝕜 (LinearMap.range (combinedDerivative
        (v := ![twistedCubic (0 : 𝕜), twistedCubic 1])
        (twistedCubicParamPair 0 1)).toLinearMap) :=
    le_of_eq (by rw [range_combinedDerivative_twistedCubic])
  exact terraciniLemma ![twistedCubic (0 : 𝕜), twistedCubic 1]
    (fun i => by fin_cases i <;> exact ⟨_, rfl⟩)
    (twistedCubicParamPair 0 1) (LinearMap.ker twistedCubicDefect.toLinearMap)
    hdominant_twistedCubic hgeneric

/-- Sanity check: the twisted cubic example specializes to `ℂ` for free. -/
example :
    LinearMap.ker twistedCubicDefect.toLinearMap =
      ⨆ i : Fin 2, (twistedCubicParamPair (0 : ℂ) 1 i).tangentSpace :=
  twistedCubic_terracini

end TwistedCubicExample
