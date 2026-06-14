import TerraciniLemma.Core
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Basic

/-!
# Worked examples: Veronese varieties

The `r`-th Veronese embedding `v_r : ℙ¹ → ℙ^r` sends `[s:t]` to the vector of
all monomials of degree `r` in `s, t`. Its affine chart is the rational
normal curve `t ↦ (t, t², …, tʳ) ⊆ 𝕜^r`.

This file currently contains the case `r = 2`, the plane conic (parabola).
Further Veronese examples (e.g. the twisted cubic `v₃(ℙ¹) ⊂ ℙ³`) can be added
here following the same `parabolaParamPair` pattern.
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
