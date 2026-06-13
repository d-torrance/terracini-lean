import TerraciniLemma.Core

/-!
# Worked examples: Veronese varieties

The `r`-th Veronese embedding `v_r : ℙ¹ → ℙ^r` sends `[s:t]` to the vector of
all monomials of degree `r` in `s, t`. Its affine chart is the rational
normal curve `t ↦ (t, t², …, tʳ) ⊆ ℝ^r`.

This file currently contains the case `r = 2`, the plane conic (parabola).
Further Veronese examples (e.g. the twisted cubic `v₃(ℙ¹) ⊂ ℙ³`) can be added
here following the same `parabolaParamPair` pattern.
-/

/-!
## Example: Terracini's Lemma for a plane conic

As a concrete sanity check, we apply `terraciniLemma` to the simplest
nontrivial case: the standard parabola X = {(t, t²) : t ∈ ℝ} ⊆ ℝ², the
affine picture of a smooth conic (a rational normal curve of degree 2).

For t₁ ≠ t₂, the tangent line to X at (tᵢ, tᵢ²) is spanned by (1, 2tᵢ). We
show that the combined derivative of the two-point parametrization is
surjective onto ℝ², so Terracini's Lemma gives

    ℝ² = T_{(t₁,t₁²)} X + T_{(t₂,t₂²)} X,

matching the classical fact that the second secant variety of a
non-degenerate plane conic is the whole plane.
-/

noncomputable section ParabolaExample

/-- The standard parabola `t ↦ (t, t²)`. -/
def parabola (t : ℝ) : ℝ × ℝ := (t, t ^ 2)

/-- The derivative of the parabola at `t`: the linear map `s ↦ (s, 2 t s)`. -/
def parabolaDeriv (t : ℝ) : ℝ →L[ℝ] ℝ × ℝ :=
  (ContinuousLinearMap.id ℝ ℝ).prod ((2 * t) • ContinuousLinearMap.id ℝ ℝ)

@[simp]
theorem parabolaDeriv_apply (t s : ℝ) : parabolaDeriv t s = (s, 2 * t * s) := by
  simp [parabolaDeriv]

theorem hasFDerivAt_parabola (t : ℝ) : HasFDerivAt parabola (parabolaDeriv t) t := by
  have h2 : HasFDerivAt (fun x : ℝ => x ^ 2) ((2 * t) • ContinuousLinearMap.id ℝ ℝ) t := by
    simpa [nsmul_eq_mul] using hasFDerivAt_pow (𝕜 := ℝ) 2 (x := t)
  exact (hasFDerivAt_id t).prodMk h2

/-- The local parametrization of the parabola at parameter `t`. -/
def parabolaParam (t : ℝ) :
    LocalParam (𝕜 := ℝ) (𝔸 := ℝ) (Set.range parabola) (parabola t) where
  basePoint := t
  chart := parabola
  chart_eval := rfl
  tangent := parabolaDeriv t
  hasFDerivAt := hasFDerivAt_parabola t

/-- The pair of local parametrizations at `t₁` and `t₂`, as a dependent
function `Fin 2 → LocalParam ...` (the types at `0` and `1` differ, since
the base points `parabola t₁ ≠ parabola t₂`, so `![·, ·]` notation does
not apply). -/
def parabolaParamPair (t₁ t₂ : ℝ) :
    ∀ i : Fin 2, LocalParam (𝕜 := ℝ) (𝔸 := ℝ)
      (Set.range parabola) (![parabola t₁, parabola t₂] i)
  | 0 => parabolaParam t₁
  | 1 => parabolaParam t₂

/-- For `t₁ ≠ t₂`, the combined derivative `Dφ_{t₁} + Dφ_{t₂}` of the
two-point parametrization is surjective onto ℝ²: every `(a, b)` equals
`parabolaDeriv t₁ s₁ + parabolaDeriv t₂ s₂` for suitable `s₁, s₂`. -/
theorem combinedDerivative_parabola_surjective (t₁ t₂ : ℝ) (h : t₁ ≠ t₂) :
    Function.Surjective
      (combinedDerivative (v := ![parabola t₁, parabola t₂])
        (parabolaParamPair t₁ t₂)) := by
  have ht : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr h
  rintro ⟨a, b⟩
  set s₁ : ℝ := (b - 2 * t₂ * a) / (2 * (t₁ - t₂)) with hs₁
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

/-- **Terracini's Lemma for the parabola.** For `t₁ ≠ t₂`, the tangent lines
to the parabola at `(t₁,t₁²)` and `(t₂,t₂²)` together span all of `ℝ²` —
matching the fact that the second secant variety of a non-degenerate plane
conic is the whole plane. -/
theorem parabola_terracini (t₁ t₂ : ℝ) (h : t₁ ≠ t₂) :
    (⊤ : Submodule ℝ (ℝ × ℝ)) =
      ⨆ i : Fin 2, (parabolaParamPair t₁ t₂ i).tangentSpace := by
  have hrange : LinearMap.range
      (combinedDerivative (v := ![parabola t₁, parabola t₂])
        (parabolaParamPair t₁ t₂)).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr (combinedDerivative_parabola_surjective t₁ t₂ h)
  have hgeneric : Module.finrank ℝ (⊤ : Submodule ℝ (ℝ × ℝ)) ≤
      Module.finrank ℝ (LinearMap.range
        (combinedDerivative (v := ![parabola t₁, parabola t₂])
          (parabolaParamPair t₁ t₂)).toLinearMap) :=
    le_of_eq (by rw [hrange])
  exact terraciniLemma ![parabola t₁, parabola t₂]
    (fun i => by fin_cases i <;> exact ⟨_, rfl⟩)
    (parabolaParamPair t₁ t₂) ⊤ le_top hgeneric

end ParabolaExample
