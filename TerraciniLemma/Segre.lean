import TerraciniLemma.Core
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Worked examples: Segre varieties

The Segre embedding `ℙ¹ × ℙ¹ × ⋯ × ℙ¹ → ℙ^{2ⁱ-1}` (i factors) sends a tuple of
points to the tensor product of their homogeneous coordinates. This file
contains two examples:

* the Segre quadric `ℙ¹ × ℙ¹ ⊂ ℙ³` (non-defective, §`SegreExample`), and
* the Segre threefold `ℙ¹ × ℙ¹ × ℙ¹ ⊂ ℙ⁷` (defective, §`SegreCubicExample`).
-/

/-!
## Example: Terracini's Lemma for the Segre quadric P¹×P¹ ⊂ P³

As a second worked example, we consider the affine chart of the Segre
variety `P¹ × P¹ ⊂ P³`, the classical "saddle surface"
`{(s, t, s·t) : s, t ∈ ℝ} ⊆ ℝ³`. As a non-degenerate quadric surface in `P³`,
its second secant variety should fill the ambient `P³`.

For two distinct points `p₁ ≠ p₂ ∈ ℝ²`, the tangent plane to the surface at
`segre pᵢ = (pᵢ.1, pᵢ.2, pᵢ.1 * pᵢ.2)` is the image of `segreDeriv pᵢ`. We
show that the combined derivative of the two-point parametrization is
surjective onto ℝ³, so Terracini's Lemma gives

    ℝ³ = T_{segre p₁} X + T_{segre p₂} X,

matching the classical fact that the second secant variety of the Segre
quadric `P¹ × P¹ ⊂ P³` is the whole `P³` (it is not defective).
-/

noncomputable section SegreExample

/-- The affine chart of the Segre variety `P¹ × P¹ ⊂ P³`: the "saddle
surface" `(s, t) ↦ (s, t, s * t)`. -/
def segre (p : ℝ × ℝ) : ℝ × ℝ × ℝ := (p.1, p.2, p.1 * p.2)

/-- The derivative of `segre` at `p`: the linear map
`(ds, dt) ↦ (ds, dt, p.2 * ds + p.1 * dt)`. -/
def segreDeriv (p : ℝ × ℝ) : (ℝ × ℝ) →L[ℝ] ℝ × ℝ × ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    ((ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (p.1 • ContinuousLinearMap.snd ℝ ℝ ℝ + p.2 • ContinuousLinearMap.fst ℝ ℝ ℝ))

@[simp]
theorem segreDeriv_apply (p q : ℝ × ℝ) :
    segreDeriv p q = (q.1, q.2, p.1 * q.2 + p.2 * q.1) := by
  simp [segreDeriv]

theorem hasFDerivAt_segre (p : ℝ × ℝ) : HasFDerivAt segre (segreDeriv p) p := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => q.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) p :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => q.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt
  exact h1.prodMk (h2.prodMk (h1.mul h2))

/-- The local parametrization of the Segre surface at parameter `p`. -/
def segreParam (p : ℝ × ℝ) :
    LocalParam (𝕜 := ℝ) (𝔸 := ℝ × ℝ) (Set.range segre) (segre p) where
  basePoint := p
  chart := segre
  chart_eval := rfl
  tangent := segreDeriv p
  hasFDerivAt := hasFDerivAt_segre p

/-- The pair of local parametrizations at `p₁` and `p₂` (see
`parabolaParamPair` for why this needs a pattern-matching definition rather
than `![·, ·]` notation). -/
def segreParamPair (p₁ p₂ : ℝ × ℝ) :
    ∀ i : Fin 2, LocalParam (𝕜 := ℝ) (𝔸 := ℝ × ℝ)
      (Set.range segre) (![segre p₁, segre p₂] i)
  | 0 => segreParam p₁
  | 1 => segreParam p₂

/-- For `p₁ ≠ p₂`, the combined derivative of the two-point parametrization
is surjective onto ℝ³. -/
theorem combinedDerivative_segre_surjective (p₁ p₂ : ℝ × ℝ) (h : p₁ ≠ p₂) :
    Function.Surjective
      (combinedDerivative (v := ![segre p₁, segre p₂]) (segreParamPair p₁ p₂)) := by
  obtain ⟨s₁, t₁⟩ := p₁
  obtain ⟨s₂, t₂⟩ := p₂
  have hD : (t₁ - t₂) ^ 2 + (s₁ - s₂) ^ 2 ≠ 0 := by
    intro hD0
    obtain ⟨ht, hs⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp hD0
    rw [sq_eq_zero_iff, sub_eq_zero] at ht hs
    exact h (Prod.ext_iff.mpr ⟨hs, ht⟩)
  rintro ⟨a, b, c⟩
  set k : ℝ := (c - t₂ * a - s₂ * b) / ((t₁ - t₂) ^ 2 + (s₁ - s₂) ^ 2) with hk
  set ds₁ : ℝ := (t₁ - t₂) * k with hds₁
  set dt₁ : ℝ := (s₁ - s₂) * k with hdt₁
  refine ⟨![(ds₁, dt₁), (a - ds₁, b - dt₁)], ?_⟩
  simp only [combinedDerivative, segreParamPair, segreParam, Fin.sum_univ_two,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, coordProj_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, segreDeriv_apply, Prod.mk_add_mk]
  rw [Prod.mk.injEq, Prod.mk.injEq]
  refine ⟨by ring, by ring, ?_⟩
  rw [hds₁, hdt₁, hk]
  field_simp
  ring

/-- **Terracini's Lemma for the Segre quadric.** For `p₁ ≠ p₂`, the tangent
planes to the Segre surface `{(s,t,s·t)}` at `segre p₁` and `segre p₂`
together span all of `ℝ³` — matching the fact that the second secant
variety of the (non-degenerate) Segre quadric `P¹ × P¹ ⊂ P³` is the whole
`P³`. -/
theorem segre_terracini (p₁ p₂ : ℝ × ℝ) (h : p₁ ≠ p₂) :
    (⊤ : Submodule ℝ (ℝ × ℝ × ℝ)) =
      ⨆ i : Fin 2, (segreParamPair p₁ p₂ i).tangentSpace := by
  have hrange : LinearMap.range
      (combinedDerivative (v := ![segre p₁, segre p₂])
        (segreParamPair p₁ p₂)).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr (combinedDerivative_segre_surjective p₁ p₂ h)
  have hgeneric : Module.finrank ℝ (⊤ : Submodule ℝ (ℝ × ℝ × ℝ)) ≤
      Module.finrank ℝ (LinearMap.range
        (combinedDerivative (v := ![segre p₁, segre p₂])
          (segreParamPair p₁ p₂)).toLinearMap) :=
    le_of_eq (by rw [hrange])
  exact terraciniLemma ![segre p₁, segre p₂]
    (fun i => by fin_cases i <;> exact ⟨_, rfl⟩)
    (segreParamPair p₁ p₂) ⊤ le_top hgeneric

end SegreExample

/-!
## Example: Terracini's Lemma for the Segre threefold P¹×P¹×P¹ ⊂ P⁷ (defective)

Our final example is the famous **defective** secant variety: the affine
chart of the Segre threefold `P¹ × P¹ × P¹ ⊂ P⁷`,

    segre3(r, s, t) = (r, s, t, rs, rt, st, rst) ∈ ℝ⁷.

This is a 3-dimensional variety in `ℝ⁷`, so the *expected* dimension of its
second secant variety σ₂ is `min(7, 2·(3+1) - 1) = 7`, i.e. σ₂ should fill
`ℝ⁷`. In fact it does not: for `p₁ = (0,0,0)` and `p₂ = (1,1,1)`, the
combined derivative of the two-point parametrization is *injective* (its
image has dimension 6, not 7), and its image is exactly the hyperplane

    T = { x : Fin 7 → ℝ | 2 * x 6 = x 3 + x 4 + x 5 }.

Terracini's Lemma then gives `T = T_{segre3 p₁}X + T_{segre3 p₂}X`, and since
`T ≠ ⊤`, this exhibits σ₂(P¹×P¹×P¹) as a proper (hypersurface) subvariety of
`P⁷` — the classical defectiveness of the Segre threefold.
-/

noncomputable section SegreCubicExample

/-- Projection onto the first coordinate `r` of `(r, s, t) ∈ ℝ × ℝ × ℝ`. -/
def proj1 : (ℝ × ℝ × ℝ) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)

/-- Projection onto the second coordinate `s` of `(r, s, t) ∈ ℝ × ℝ × ℝ`. -/
def proj2 : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

/-- Projection onto the third coordinate `t` of `(r, s, t) ∈ ℝ × ℝ × ℝ`. -/
def proj3 : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))

@[simp] theorem proj1_apply (q : ℝ × ℝ × ℝ) : proj1 q = q.1 := rfl
@[simp] theorem proj2_apply (q : ℝ × ℝ × ℝ) : proj2 q = q.2.1 := rfl
@[simp] theorem proj3_apply (q : ℝ × ℝ × ℝ) : proj3 q = q.2.2 := rfl

/-- The affine chart of the Segre threefold `P¹ × P¹ × P¹ ⊂ P⁷`:
`(r, s, t) ↦ (r, s, t, rs, rt, st, rst)`, as a function `Fin 7 → ℝ`. -/
def segre3 (p : ℝ × ℝ × ℝ) : Fin 7 → ℝ
  | 0 => p.1
  | 1 => p.2.1
  | 2 => p.2.2
  | 3 => p.1 * p.2.1
  | 4 => p.1 * p.2.2
  | 5 => p.2.1 * p.2.2
  | 6 => p.1 * p.2.1 * p.2.2

/-- The components of the derivative of `segre3` at `p`. -/
def segre3DerivComp (p : ℝ × ℝ × ℝ) : Fin 7 → (ℝ × ℝ × ℝ) →L[ℝ] ℝ
  | 0 => proj1
  | 1 => proj2
  | 2 => proj3
  | 3 => p.1 • proj2 + p.2.1 • proj1
  | 4 => p.1 • proj3 + p.2.2 • proj1
  | 5 => p.2.1 • proj3 + p.2.2 • proj2
  | 6 => (p.1 * p.2.1) • proj3 + p.2.2 • (p.1 • proj2 + p.2.1 • proj1)

/-- The derivative of `segre3` at `p`, as a continuous linear map
`ℝ × ℝ × ℝ →L[ℝ] (Fin 7 → ℝ)`. -/
def segre3Deriv (p : ℝ × ℝ × ℝ) : (ℝ × ℝ × ℝ) →L[ℝ] (Fin 7 → ℝ) :=
  ContinuousLinearMap.pi (segre3DerivComp p)

@[simp]
theorem segre3Deriv_apply (p q : ℝ × ℝ × ℝ) (i : Fin 7) :
    segre3Deriv p q i = segre3DerivComp p i q :=
  ContinuousLinearMap.pi_apply _ _ _

theorem hasFDerivAt_segre3 (p : ℝ × ℝ × ℝ) : HasFDerivAt segre3 (segre3Deriv p) p := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ × ℝ => q.1) proj1 p := proj1.hasFDerivAt
  have h2 : HasFDerivAt (fun q : ℝ × ℝ × ℝ => q.2.1) proj2 p := proj2.hasFDerivAt
  have h3 : HasFDerivAt (fun q : ℝ × ℝ × ℝ => q.2.2) proj3 p := proj3.hasFDerivAt
  have h13 : HasFDerivAt (fun q : ℝ × ℝ × ℝ => q.1 * q.2.1) (p.1 • proj2 + p.2.1 • proj1) p :=
    h1.mul h2
  apply (hasFDerivAt_pi (φ := fun i q => segre3 q i)
    (φ' := fun i => segre3DerivComp p i) (x := p)).2
  intro i
  fin_cases i
  · exact h1
  · exact h2
  · exact h3
  · exact h13
  · exact h1.mul h3
  · exact h2.mul h3
  · exact h13.mul h3

/-- The local parametrization of the Segre threefold at parameter `p`. -/
def segre3Param (p : ℝ × ℝ × ℝ) :
    LocalParam (𝕜 := ℝ) (𝔸 := ℝ × ℝ × ℝ) (Set.range segre3) (segre3 p) where
  basePoint := p
  chart := segre3
  chart_eval := rfl
  tangent := segre3Deriv p
  hasFDerivAt := hasFDerivAt_segre3 p

/-- The pair of local parametrizations at `p₁` and `p₂` (see `parabolaParamPair`
for why this needs a pattern-matching definition rather than `![·, ·]` notation). -/
def segre3ParamPair (p₁ p₂ : ℝ × ℝ × ℝ) :
    ∀ i : Fin 2, LocalParam (𝕜 := ℝ) (𝔸 := ℝ × ℝ × ℝ)
      (Set.range segre3) (![segre3 p₁, segre3 p₂] i)
  | 0 => segre3Param p₁
  | 1 => segre3Param p₂

/-- Componentwise formula for the combined derivative at the two-point
parametrization `(0,0,0), (1,1,1)`. -/
theorem combinedDerivative_segre3_apply (w : Fin 2 → ℝ × ℝ × ℝ) (i : Fin 7) :
    combinedDerivative (v := ![segre3 (0,0,0), segre3 (1,1,1)])
      (segre3ParamPair (0,0,0) (1,1,1)) w i =
      segre3DerivComp (0,0,0) i (w 0) + segre3DerivComp (1,1,1) i (w 1) := by
  simp only [combinedDerivative, segre3ParamPair, segre3Param, Fin.sum_univ_two,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, coordProj_apply,
    Pi.add_apply, segre3Deriv_apply]

/-- The combined derivative of the two-point parametrization at
`(0,0,0)` and `(1,1,1)` is injective: σ₂(P¹×P¹×P¹) has dimension exactly 6,
not 7, at this pair of points. -/
theorem combinedDerivative_segre3_injective :
    Function.Injective (combinedDerivative (v := ![segre3 (0,0,0), segre3 (1,1,1)])
      (segre3ParamPair (0,0,0) (1,1,1))) := by
  intro u v huv
  have hsub : combinedDerivative (v := ![segre3 (0,0,0), segre3 (1,1,1)])
      (segre3ParamPair (0,0,0) (1,1,1)) (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have key : ∀ i : Fin 7,
      segre3DerivComp (0,0,0) i ((u - v) 0) + segre3DerivComp (1,1,1) i ((u - v) 1) = 0 := by
    intro i
    rw [← combinedDerivative_segre3_apply, hsub]
    rfl
  have h0 := key 0
  have h1 := key 1
  have h2 := key 2
  have h3 := key 3
  have h4 := key 4
  have h5 := key 5
  simp only [segre3DerivComp, proj1_apply, proj2_apply, proj3_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    zero_mul, one_mul, zero_add, add_zero] at h0 h1 h2 h3 h4 h5
  have hw1a : ((u - v) 1).1 = 0 := by linarith
  have hw1b : ((u - v) 1).2.1 = 0 := by linarith
  have hw1c : ((u - v) 1).2.2 = 0 := by linarith
  have hw0a : ((u - v) 0).1 = 0 := by linarith
  have hw0b : ((u - v) 0).2.1 = 0 := by linarith
  have hw0c : ((u - v) 0).2.2 = 0 := by linarith
  have hw0 : (u - v) 0 = 0 := by
    rw [Prod.ext_iff, Prod.ext_iff]
    exact ⟨hw0a, hw0b, hw0c⟩
  have hw1 : (u - v) 1 = 0 := by
    rw [Prod.ext_iff, Prod.ext_iff]
    exact ⟨hw1a, hw1b, hw1c⟩
  have huv0 : u - v = 0 := funext (fun i => by fin_cases i <;> assumption)
  exact sub_eq_zero.mp huv0

/-- The "defect" linear functional `L(x) = 2x₆ - x₃ - x₄ - x₅`. Its kernel is
exactly the image of the combined derivative at `(0,0,0)` and `(1,1,1)`. -/
def segre3Defect : (Fin 7 → ℝ) →L[ℝ] ℝ :=
  (2 : ℝ) • coordProj 7 6 - coordProj 7 3 - coordProj 7 4 - coordProj 7 5

theorem segre3Defect_apply (x : Fin 7 → ℝ) :
    segre3Defect x = 2 * x 6 - x 3 - x 4 - x 5 := by
  simp [segre3Defect, coordProj_apply, smul_eq_mul]

/-- The image of the combined derivative at `(0,0,0)` and `(1,1,1)` lies in
`ker segre3Defect`: every tangent vector to `σ₂` at this pair of points
satisfies the linear relation `2x₆ = x₃ + x₄ + x₅`. -/
theorem hdominant_segre3 :
    LinearMap.range (combinedDerivative (v := ![segre3 (0,0,0), segre3 (1,1,1)])
      (segre3ParamPair (0,0,0) (1,1,1))).toLinearMap ≤
      LinearMap.ker segre3Defect.toLinearMap := by
  rintro x ⟨w, rfl⟩
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, segre3Defect_apply,
    combinedDerivative_segre3_apply, segre3DerivComp, proj1_apply, proj2_apply, proj3_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    zero_mul, one_mul, zero_add, add_zero]
  ring

theorem segre3Defect_ne_zero : segre3Defect.toLinearMap ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg DFunLike.coe h) (Pi.single 6 1)
  simp [segre3Defect_apply] at h2

/-- `ker segre3Defect` has dimension 6 (a hyperplane in `ℝ⁷`). -/
theorem finrank_ker_segre3Defect :
    Module.finrank ℝ (LinearMap.ker segre3Defect.toLinearMap) = 6 := by
  have hrange : LinearMap.range segre3Defect.toLinearMap = ⊤ :=
    Module.Dual.range_eq_top_of_ne_zero segre3Defect_ne_zero
  have hsum := LinearMap.finrank_range_add_finrank_ker segre3Defect.toLinearMap
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at hsum
  omega

/-- The image of the combined derivative at `(0,0,0)` and `(1,1,1)` has
dimension 6 (the derivative is injective on the 6-dimensional parameter
space `Fin 2 → ℝ × ℝ × ℝ`). -/
theorem finrank_range_combinedDerivative_segre3 :
    Module.finrank ℝ (LinearMap.range (combinedDerivative
      (v := ![segre3 (0,0,0), segre3 (1,1,1)]) (segre3ParamPair (0,0,0) (1,1,1))).toLinearMap)
      = 6 := by
  rw [LinearMap.finrank_range_of_inj combinedDerivative_segre3_injective]
  simp [Module.finrank_pi_fintype, Module.finrank_prod, Module.finrank_self]

/-- **Terracini's Lemma for the defective Segre threefold `P¹×P¹×P¹ ⊂ P⁷`.**
At `p₁=(0,0,0)` and `p₂=(1,1,1)`, the sum of the two tangent spaces is exactly
the hyperplane `T = ker segre3Defect` — *not* all of `ℝ⁷`. This exhibits the
classical defectiveness of `σ₂(P¹×P¹×P¹)`. -/
theorem segre3_terracini :
    LinearMap.ker segre3Defect.toLinearMap =
      ⨆ i : Fin 2, (segre3ParamPair (0,0,0) (1,1,1) i).tangentSpace := by
  have hgeneric : Module.finrank ℝ (LinearMap.ker segre3Defect.toLinearMap) ≤
      Module.finrank ℝ (LinearMap.range (combinedDerivative
        (v := ![segre3 (0,0,0), segre3 (1,1,1)])
        (segre3ParamPair (0,0,0) (1,1,1))).toLinearMap) :=
    le_of_eq (by rw [finrank_ker_segre3Defect, finrank_range_combinedDerivative_segre3])
  exact terraciniLemma ![segre3 (0,0,0), segre3 (1,1,1)]
    (fun i => by fin_cases i <;> exact ⟨_, rfl⟩)
    (segre3ParamPair (0,0,0) (1,1,1))
    (LinearMap.ker segre3Defect.toLinearMap) hdominant_segre3 hgeneric

/-- The defective secant variety `σ₂(P¹×P¹×P¹)` is a proper (hypersurface)
subvariety of `P⁷`: its tangent space `T` has dimension 6, not 7. -/
theorem segre3_terracini_ne_top :
    LinearMap.ker segre3Defect.toLinearMap ≠ ⊤ := by
  intro h
  have h7 : Module.finrank ℝ (LinearMap.ker segre3Defect.toLinearMap) = 7 := by
    rw [h, finrank_top, Module.finrank_fin_fun]
  rw [finrank_ker_segre3Defect] at h7
  exact absurd h7 (by norm_num)

end SegreCubicExample
