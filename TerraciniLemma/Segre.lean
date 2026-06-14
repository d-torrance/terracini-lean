import TerraciniLemma.Core
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Complex.Basic

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
`{(s, t, s·t) : s, t ∈ 𝕜} ⊆ 𝕜³`, for an arbitrary `NontriviallyNormedField 𝕜`
(e.g. `ℝ` or `ℂ`). As a non-degenerate quadric surface in `P³`, its second
secant variety should fill the ambient `P³`.

For two distinct points `p₁ ≠ p₂ ∈ 𝕜²`, the tangent plane to the surface at
`segre pᵢ = (pᵢ.1, pᵢ.2, pᵢ.1 * pᵢ.2)` is the image of `segreDeriv pᵢ`. We
show that the combined derivative of the two-point parametrization is
surjective onto `𝕜³`, so Terracini's Lemma gives

    𝕜³ = T_{segre p₁} X + T_{segre p₂} X,

matching the classical fact that the second secant variety of the Segre
quadric `P¹ × P¹ ⊂ P³` is the whole `P³` (it is not defective) — over *any*
field, not just `ℝ`. The surjectivity proof solves a 2×2 linear system: since
`p₁ ≠ p₂`, either `s₁ ≠ s₂` or `t₁ ≠ t₂`, and either inequality yields a
nonzero coefficient that can be inverted in `𝕜`. (This replaces the classical
real argument "a sum of two squares vanishes iff both terms do", which needs
an ordered field and fails over `ℂ`.)

**Affine chart vs. cone.** `𝕜³` here is the affine chart `{(1, s, t, st)}` of
`P³`, not the 4-dimensional cone `𝕜²⊗𝕜²` over the Segre embedding
`P¹×P¹ ⊂ P³`. So `segre_terracini` is a chart-level computation and does not
directly feed into `TerraciniLemma.Projective`'s `Submodule.projectivization`
descent.
-/

noncomputable section SegreExample

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The affine chart of the Segre variety `P¹ × P¹ ⊂ P³`: the "saddle
surface" `(s, t) ↦ (s, t, s * t)`. -/
def segre (p : 𝕜 × 𝕜) : 𝕜 × 𝕜 × 𝕜 := (p.1, p.2, p.1 * p.2)

/-- The derivative of `segre` at `p`: the linear map
`(ds, dt) ↦ (ds, dt, p.2 * ds + p.1 * dt)`. -/
def segreDeriv (p : 𝕜 × 𝕜) : (𝕜 × 𝕜) →L[𝕜] 𝕜 × 𝕜 × 𝕜 :=
  (ContinuousLinearMap.fst 𝕜 𝕜 𝕜).prod
    ((ContinuousLinearMap.snd 𝕜 𝕜 𝕜).prod
      (p.1 • ContinuousLinearMap.snd 𝕜 𝕜 𝕜 + p.2 • ContinuousLinearMap.fst 𝕜 𝕜 𝕜))

@[simp]
theorem segreDeriv_apply (p q : 𝕜 × 𝕜) :
    segreDeriv p q = (q.1, q.2, p.1 * q.2 + p.2 * q.1) := by
  simp [segreDeriv]

theorem hasFDerivAt_segre (p : 𝕜 × 𝕜) : HasFDerivAt segre (segreDeriv p) p := by
  have h1 : HasFDerivAt (fun q : 𝕜 × 𝕜 => q.1) (ContinuousLinearMap.fst 𝕜 𝕜 𝕜) p :=
    (ContinuousLinearMap.fst 𝕜 𝕜 𝕜).hasFDerivAt
  have h2 : HasFDerivAt (fun q : 𝕜 × 𝕜 => q.2) (ContinuousLinearMap.snd 𝕜 𝕜 𝕜) p :=
    (ContinuousLinearMap.snd 𝕜 𝕜 𝕜).hasFDerivAt
  exact h1.prodMk (h2.prodMk (h1.mul h2))

/-- The local parametrization of the Segre surface at parameter `p`. -/
def segreParam (p : 𝕜 × 𝕜) :
    LocalParam (𝕜 := 𝕜) (𝔸 := 𝕜 × 𝕜) (Set.range segre) (segre p) where
  basePoint := p
  chart := segre
  chart_eval := rfl
  tangent := segreDeriv p
  hasFDerivAt := hasFDerivAt_segre p

/-- The pair of local parametrizations at `p₁` and `p₂` (see
`parabolaParamPair` for why this needs a pattern-matching definition rather
than `![·, ·]` notation). -/
def segreParamPair (p₁ p₂ : 𝕜 × 𝕜) :
    ∀ i : Fin 2, LocalParam (𝕜 := 𝕜) (𝔸 := 𝕜 × 𝕜)
      (Set.range segre) (![segre p₁, segre p₂] i)
  | 0 => segreParam p₁
  | 1 => segreParam p₂

/-- For `p₁ ≠ p₂`, the combined derivative of the two-point parametrization
is surjective onto `𝕜³`. Since `p₁ ≠ p₂`, either `s₁ ≠ s₂` or `t₁ ≠ t₂`; in
each case we set the corresponding "shift" parameter for one point to `0`
and solve the resulting single linear equation for the other. -/
theorem combinedDerivative_segre_surjective (p₁ p₂ : 𝕜 × 𝕜) (h : p₁ ≠ p₂) :
    Function.Surjective
      (combinedDerivative (v := ![segre p₁, segre p₂]) (segreParamPair p₁ p₂)) := by
  obtain ⟨s₁, t₁⟩ := p₁
  obtain ⟨s₂, t₂⟩ := p₂
  have hor : s₁ ≠ s₂ ∨ t₁ ≠ t₂ := by
    rw [← not_and_or]
    rintro ⟨hs, ht⟩
    exact h (Prod.ext_iff.mpr ⟨hs, ht⟩)
  rintro ⟨a, b, c⟩
  rcases hor with hs | ht
  · -- s₁ ≠ s₂: take ds₁ := 0 and solve for dt₁.
    have hne : s₁ - s₂ ≠ 0 := sub_ne_zero.mpr hs
    set dt₁ : 𝕜 := (c - s₂ * b - t₂ * a) / (s₁ - s₂) with hdt₁
    refine ⟨![(0, dt₁), (a, b - dt₁)], ?_⟩
    simp only [combinedDerivative, segreParamPair, segreParam, Fin.sum_univ_two,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, coordProj_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, segreDeriv_apply, Prod.mk_add_mk]
    rw [Prod.mk.injEq, Prod.mk.injEq]
    refine ⟨by ring, by ring, ?_⟩
    rw [hdt₁]
    field_simp
    ring
  · -- t₁ ≠ t₂: take dt₁ := 0 and solve for ds₁.
    have hne : t₁ - t₂ ≠ 0 := sub_ne_zero.mpr ht
    set ds₁ : 𝕜 := (c - s₂ * b - t₂ * a) / (t₁ - t₂) with hds₁
    refine ⟨![(ds₁, 0), (a - ds₁, b)], ?_⟩
    simp only [combinedDerivative, segreParamPair, segreParam, Fin.sum_univ_two,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, coordProj_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, segreDeriv_apply, Prod.mk_add_mk]
    rw [Prod.mk.injEq, Prod.mk.injEq]
    refine ⟨by ring, by ring, ?_⟩
    rw [hds₁]
    field_simp
    ring

/-- **Terracini's Lemma for the Segre quadric**, over an arbitrary
`NontriviallyNormedField 𝕜`. For `p₁ ≠ p₂`, the tangent planes to the Segre
surface `{(s,t,s·t)}` at `segre p₁` and `segre p₂` together span all of `𝕜³`
— matching the fact that the second secant variety of the (non-degenerate)
Segre quadric `P¹ × P¹ ⊂ P³` is the whole `P³`, over `ℝ`, `ℂ`, or any other
field. -/
theorem segre_terracini (p₁ p₂ : 𝕜 × 𝕜) (h : p₁ ≠ p₂) :
    (⊤ : Submodule 𝕜 (𝕜 × 𝕜 × 𝕜)) =
      ⨆ i : Fin 2, (segreParamPair p₁ p₂ i).tangentSpace := by
  have hrange : LinearMap.range
      (combinedDerivative (v := ![segre p₁, segre p₂])
        (segreParamPair p₁ p₂)).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr (combinedDerivative_segre_surjective p₁ p₂ h)
  have hgeneric : Module.finrank 𝕜 (⊤ : Submodule 𝕜 (𝕜 × 𝕜 × 𝕜)) ≤
      Module.finrank 𝕜 (LinearMap.range
        (combinedDerivative (v := ![segre p₁, segre p₂])
          (segreParamPair p₁ p₂)).toLinearMap) :=
    le_of_eq (by rw [hrange])
  exact terraciniLemma ![segre p₁, segre p₂]
    (fun i => by fin_cases i <;> exact ⟨_, rfl⟩)
    (segreParamPair p₁ p₂) ⊤ le_top hgeneric

/-- Sanity check: the Segre quadric example specializes to `ℂ` for free,
once `combinedDerivative_segre_surjective` is proved over a general field. -/
example (p₁ p₂ : ℂ × ℂ) (h : p₁ ≠ p₂) :
    (⊤ : Submodule ℂ (ℂ × ℂ × ℂ)) =
      ⨆ i : Fin 2, (segreParamPair p₁ p₂ i).tangentSpace :=
  segre_terracini p₁ p₂ h

end SegreExample

/-!
## Example: Terracini's Lemma for the Segre threefold P¹×P¹×P¹ ⊂ P⁷ (defective)

Our final example is the famous **defective** secant variety: the affine
chart of the Segre threefold `P¹ × P¹ × P¹ ⊂ P⁷`,

    segre3(r, s, t) = (r, s, t, rs, rt, st, rst) ∈ 𝕜⁷,

for an arbitrary `NontriviallyNormedField 𝕜` of characteristic zero (e.g.
`ℝ` or `ℂ`).

This is a 3-dimensional variety in `𝕜⁷`, so the *expected* dimension of its
second secant variety σ₂ is `min(7, 2·(3+1) - 1) = 7`, i.e. σ₂ should fill
`𝕜⁷`. In fact it does not: for `p₁ = (0,0,0)` and `p₂ = (1,1,1)`, the
combined derivative of the two-point parametrization is *injective* (its
image has dimension 6, not 7), and its image is exactly the hyperplane

    T = { x : Fin 7 → 𝕜 | 2 * x 6 = x 3 + x 4 + x 5 }.

Terracini's Lemma then gives `T = T_{segre3 p₁}X + T_{segre3 p₂}X`, and since
`T ≠ ⊤`, this exhibits σ₂(P¹×P¹×P¹) as a proper (hypersurface) subvariety of
`P⁷` — the classical defectiveness of the Segre threefold. The proof of
injectivity solves `2x = 0 ⟹ x = 0`, which requires `2 ≠ 0`, i.e.
characteristic zero.

**Affine chart vs. cone.** `𝕜⁷` here is the affine chart `{(1,r,s,t,rs,rt,st,rst)}`
of `P⁷`, not the 8-dimensional cone `𝕜²⊗𝕜²⊗𝕜²` over the Segre embedding
`P¹×P¹×P¹ ⊂ P⁷`. So `segre3_terracini` is a chart-level computation and does
not directly feed into `TerraciniLemma.Projective`'s
`Submodule.projectivization` descent — a genuinely projective version of this
defective example would need to be redone in the cone `𝕜⁸`.
-/

noncomputable section SegreCubicExample

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-- Projection onto the first coordinate `r` of `(r, s, t) ∈ 𝕜 × 𝕜 × 𝕜`. -/
def proj1 : (𝕜 × 𝕜 × 𝕜) →L[𝕜] 𝕜 := ContinuousLinearMap.fst 𝕜 𝕜 (𝕜 × 𝕜)

/-- Projection onto the second coordinate `s` of `(r, s, t) ∈ 𝕜 × 𝕜 × 𝕜`. -/
def proj2 : (𝕜 × 𝕜 × 𝕜) →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.fst 𝕜 𝕜 𝕜).comp (ContinuousLinearMap.snd 𝕜 𝕜 (𝕜 × 𝕜))

/-- Projection onto the third coordinate `t` of `(r, s, t) ∈ 𝕜 × 𝕜 × 𝕜`. -/
def proj3 : (𝕜 × 𝕜 × 𝕜) →L[𝕜] 𝕜 :=
  (ContinuousLinearMap.snd 𝕜 𝕜 𝕜).comp (ContinuousLinearMap.snd 𝕜 𝕜 (𝕜 × 𝕜))

omit [CharZero 𝕜] in
@[simp] theorem proj1_apply (q : 𝕜 × 𝕜 × 𝕜) : proj1 q = q.1 := rfl
omit [CharZero 𝕜] in
@[simp] theorem proj2_apply (q : 𝕜 × 𝕜 × 𝕜) : proj2 q = q.2.1 := rfl
omit [CharZero 𝕜] in
@[simp] theorem proj3_apply (q : 𝕜 × 𝕜 × 𝕜) : proj3 q = q.2.2 := rfl

/-- The affine chart of the Segre threefold `P¹ × P¹ × P¹ ⊂ P⁷`:
`(r, s, t) ↦ (r, s, t, rs, rt, st, rst)`, as a function `Fin 7 → 𝕜`. -/
def segre3 (p : 𝕜 × 𝕜 × 𝕜) : Fin 7 → 𝕜
  | 0 => p.1
  | 1 => p.2.1
  | 2 => p.2.2
  | 3 => p.1 * p.2.1
  | 4 => p.1 * p.2.2
  | 5 => p.2.1 * p.2.2
  | 6 => p.1 * p.2.1 * p.2.2

/-- The components of the derivative of `segre3` at `p`. -/
def segre3DerivComp (p : 𝕜 × 𝕜 × 𝕜) : Fin 7 → (𝕜 × 𝕜 × 𝕜) →L[𝕜] 𝕜
  | 0 => proj1
  | 1 => proj2
  | 2 => proj3
  | 3 => p.1 • proj2 + p.2.1 • proj1
  | 4 => p.1 • proj3 + p.2.2 • proj1
  | 5 => p.2.1 • proj3 + p.2.2 • proj2
  | 6 => (p.1 * p.2.1) • proj3 + p.2.2 • (p.1 • proj2 + p.2.1 • proj1)

/-- The derivative of `segre3` at `p`, as a continuous linear map
`𝕜 × 𝕜 × 𝕜 →L[𝕜] (Fin 7 → 𝕜)`. -/
def segre3Deriv (p : 𝕜 × 𝕜 × 𝕜) : (𝕜 × 𝕜 × 𝕜) →L[𝕜] (Fin 7 → 𝕜) :=
  ContinuousLinearMap.pi (segre3DerivComp p)

omit [CharZero 𝕜] in
@[simp]
theorem segre3Deriv_apply (p q : 𝕜 × 𝕜 × 𝕜) (i : Fin 7) :
    segre3Deriv p q i = segre3DerivComp p i q :=
  ContinuousLinearMap.pi_apply _ _ _

omit [CharZero 𝕜] in
theorem hasFDerivAt_segre3 (p : 𝕜 × 𝕜 × 𝕜) : HasFDerivAt segre3 (segre3Deriv p) p := by
  have h1 : HasFDerivAt (fun q : 𝕜 × 𝕜 × 𝕜 => q.1) proj1 p :=
    (ContinuousLinearMap.fst 𝕜 𝕜 (𝕜 × 𝕜)).hasFDerivAt
  have h2 : HasFDerivAt (fun q : 𝕜 × 𝕜 × 𝕜 => q.2.1) proj2 p :=
    ((ContinuousLinearMap.fst 𝕜 𝕜 𝕜).comp (ContinuousLinearMap.snd 𝕜 𝕜 (𝕜 × 𝕜))).hasFDerivAt
  have h3 : HasFDerivAt (fun q : 𝕜 × 𝕜 × 𝕜 => q.2.2) proj3 p :=
    ((ContinuousLinearMap.snd 𝕜 𝕜 𝕜).comp (ContinuousLinearMap.snd 𝕜 𝕜 (𝕜 × 𝕜))).hasFDerivAt
  have h13 : HasFDerivAt (fun q : 𝕜 × 𝕜 × 𝕜 => q.1 * q.2.1) (p.1 • proj2 + p.2.1 • proj1) p :=
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
def segre3Param (p : 𝕜 × 𝕜 × 𝕜) :
    LocalParam (𝕜 := 𝕜) (𝔸 := 𝕜 × 𝕜 × 𝕜) (Set.range segre3) (segre3 p) where
  basePoint := p
  chart := segre3
  chart_eval := rfl
  tangent := segre3Deriv p
  hasFDerivAt := hasFDerivAt_segre3 p

/-- The pair of local parametrizations at `p₁` and `p₂` (see `parabolaParamPair`
for why this needs a pattern-matching definition rather than `![·, ·]` notation). -/
def segre3ParamPair (p₁ p₂ : 𝕜 × 𝕜 × 𝕜) :
    ∀ i : Fin 2, LocalParam (𝕜 := 𝕜) (𝔸 := 𝕜 × 𝕜 × 𝕜)
      (Set.range segre3) (![segre3 p₁, segre3 p₂] i)
  | 0 => segre3Param p₁
  | 1 => segre3Param p₂

/-- The first of the two points, `(0,0,0)`, used in the concrete
defective-Segre-threefold computation below. Written as local notation
(rather than a `def`) so that each use site elaborates `0` directly at type
`𝕜`, avoiding spurious metavariables for the ambient field. -/
local notation "segre3Pt1" => ((0, 0, 0) : 𝕜 × 𝕜 × 𝕜)

/-- The second of the two points, `(1,1,1)`. -/
local notation "segre3Pt2" => ((1, 1, 1) : 𝕜 × 𝕜 × 𝕜)

omit [CharZero 𝕜] in
/-- Componentwise formula for the combined derivative at the two-point
parametrization `(0,0,0), (1,1,1)`. -/
theorem combinedDerivative_segre3_apply (w : Fin 2 → 𝕜 × 𝕜 × 𝕜) (i : Fin 7) :
    combinedDerivative (v := ![segre3 segre3Pt1, segre3 segre3Pt2])
      (segre3ParamPair segre3Pt1 segre3Pt2) w i =
      segre3DerivComp segre3Pt1 i (w 0) + segre3DerivComp segre3Pt2 i (w 1) := by
  simp only [combinedDerivative, segre3ParamPair, segre3Param, Fin.sum_univ_two,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, coordProj_apply,
    Pi.add_apply, segre3Deriv_apply]

/-- The combined derivative of the two-point parametrization at
`(0,0,0)` and `(1,1,1)` is injective: σ₂(P¹×P¹×P¹) has dimension exactly 6,
not 7, at this pair of points. The argument needs `2 ≠ 0`, i.e.
characteristic zero. -/
theorem combinedDerivative_segre3_injective :
    Function.Injective (combinedDerivative (v := ![segre3 segre3Pt1, segre3 segre3Pt2])
      (segre3ParamPair segre3Pt1 segre3Pt2)) := by
  intro u v huv
  have hsub : combinedDerivative (v := ![segre3 segre3Pt1, segre3 segre3Pt2])
      (segre3ParamPair segre3Pt1 segre3Pt2) (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have key : ∀ i : Fin 7,
      segre3DerivComp segre3Pt1 i ((u - v) 0) + segre3DerivComp segre3Pt2 i ((u - v) 1) = 0 := by
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
  have e1 : (2 : 𝕜) * ((u - v) 1).1 = 0 := by linear_combination h3 + h4 - h5
  have hw1a : ((u - v) 1).1 = 0 := (mul_eq_zero.mp e1).resolve_left two_ne_zero
  have e2 : (2 : 𝕜) * ((u - v) 1).2.1 = 0 := by linear_combination h3 + h5 - h4
  have hw1b : ((u - v) 1).2.1 = 0 := (mul_eq_zero.mp e2).resolve_left two_ne_zero
  have e3 : (2 : 𝕜) * ((u - v) 1).2.2 = 0 := by linear_combination h4 + h5 - h3
  have hw1c : ((u - v) 1).2.2 = 0 := (mul_eq_zero.mp e3).resolve_left two_ne_zero
  have hw0a : ((u - v) 0).1 = 0 := by linear_combination h0 - hw1a
  have hw0b : ((u - v) 0).2.1 = 0 := by linear_combination h1 - hw1b
  have hw0c : ((u - v) 0).2.2 = 0 := by linear_combination h2 - hw1c
  have hw0 : (u - v) 0 = 0 := by
    rw [Prod.ext_iff, Prod.ext_iff]
    exact ⟨hw0a, hw0b, hw0c⟩
  have hw1 : (u - v) 1 = 0 := by
    rw [Prod.ext_iff, Prod.ext_iff]
    exact ⟨hw1a, hw1b, hw1c⟩
  have huv0 : u - v = 0 := funext (fun i => by fin_cases i <;> assumption)
  exact sub_eq_zero.mp huv0

/-- The "defect" linear functional `L(x) = 2x₆ - x₃ - x₄ - x₅`. Its kernel is
exactly the image of the combined derivative at `(0,0,0)` and `(1,1,1)`.
Written as local notation (like `segre3Pt1`/`segre3Pt2`) so that each use site
elaborates `𝕜` as the ambient declaration's own field, avoiding spurious
metavariables for the ambient field. -/
local notation "segre3Defect" =>
  ((2 : 𝕜) • coordProj 7 6 - coordProj 7 3 - coordProj 7 4 - coordProj 7 5 :
    (Fin 7 → 𝕜) →L[𝕜] 𝕜)

omit [CharZero 𝕜] in
theorem segre3Defect_apply (x : Fin 7 → 𝕜) :
    segre3Defect x = 2 * x 6 - x 3 - x 4 - x 5 := by
  simp [coordProj_apply, smul_eq_mul]

omit [CharZero 𝕜] in
/-- The image of the combined derivative at `(0,0,0)` and `(1,1,1)` lies in
`ker segre3Defect`: every tangent vector to `σ₂` at this pair of points
satisfies the linear relation `2x₆ = x₃ + x₄ + x₅`. -/
theorem hdominant_segre3 :
    LinearMap.range (combinedDerivative (v := ![segre3 segre3Pt1, segre3 segre3Pt2])
      (segre3ParamPair segre3Pt1 segre3Pt2)).toLinearMap ≤
      LinearMap.ker (segre3Defect).toLinearMap := by
  rintro x ⟨w, rfl⟩
  simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, segre3Defect_apply,
    combinedDerivative_segre3_apply, segre3DerivComp,
    proj1_apply, proj2_apply, proj3_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    zero_mul, one_mul, zero_add, add_zero]
  ring

theorem segre3Defect_ne_zero : (segre3Defect).toLinearMap ≠ 0 := by
  intro h
  have h2 := congrFun (congrArg DFunLike.coe h) (Pi.single 6 1)
  simp at h2

/-- `ker segre3Defect` has dimension 6 (a hyperplane in `𝕜⁷`). -/
theorem finrank_ker_segre3Defect :
    Module.finrank 𝕜 (LinearMap.ker (segre3Defect).toLinearMap) = 6 := by
  have hrange : LinearMap.range (segre3Defect).toLinearMap = ⊤ :=
    Module.Dual.range_eq_top_of_ne_zero segre3Defect_ne_zero
  have hsum := LinearMap.finrank_range_add_finrank_ker (segre3Defect).toLinearMap
  rw [hrange, finrank_top, Module.finrank_self, Module.finrank_fin_fun] at hsum
  omega

/-- The image of the combined derivative at `(0,0,0)` and `(1,1,1)` has
dimension 6 (the derivative is injective on the 6-dimensional parameter
space `Fin 2 → 𝕜 × 𝕜 × 𝕜`). -/
theorem finrank_range_combinedDerivative_segre3 :
    Module.finrank 𝕜 (LinearMap.range (combinedDerivative
      (v := ![segre3 segre3Pt1, segre3 segre3Pt2])
      (segre3ParamPair segre3Pt1 segre3Pt2)).toLinearMap)
      = 6 := by
  rw [LinearMap.finrank_range_of_inj combinedDerivative_segre3_injective]
  simp [Module.finrank_pi_fintype, Module.finrank_prod, Module.finrank_self]

/-- **Terracini's Lemma for the defective Segre threefold `P¹×P¹×P¹ ⊂ P⁷`.**
At `p₁=(0,0,0)` and `p₂=(1,1,1)`, the sum of the two tangent spaces is exactly
the hyperplane `T = ker segre3Defect` — *not* all of `𝕜⁷`. This exhibits the
classical defectiveness of `σ₂(P¹×P¹×P¹)`. -/
theorem segre3_terracini :
    LinearMap.ker (segre3Defect).toLinearMap =
      ⨆ i : Fin 2, (segre3ParamPair segre3Pt1 segre3Pt2 i).tangentSpace := by
  have hgeneric : Module.finrank 𝕜 (LinearMap.ker (segre3Defect).toLinearMap) ≤
      Module.finrank 𝕜 (LinearMap.range (combinedDerivative
        (v := ![segre3 segre3Pt1, segre3 segre3Pt2])
        (segre3ParamPair segre3Pt1 segre3Pt2)).toLinearMap) :=
    le_of_eq (by rw [finrank_ker_segre3Defect, finrank_range_combinedDerivative_segre3])
  exact terraciniLemma ![segre3 segre3Pt1, segre3 segre3Pt2]
    (fun i => by fin_cases i <;> exact ⟨_, rfl⟩)
    (segre3ParamPair segre3Pt1 segre3Pt2)
    (LinearMap.ker (segre3Defect).toLinearMap) hdominant_segre3 hgeneric

/-- The defective secant variety `σ₂(P¹×P¹×P¹)` is a proper (hypersurface)
subvariety of `P⁷`: its tangent space `T` has dimension 6, not 7. -/
theorem segre3_terracini_ne_top :
    LinearMap.ker (segre3Defect).toLinearMap ≠ ⊤ := by
  intro h
  have h7 : Module.finrank 𝕜 (LinearMap.ker (segre3Defect).toLinearMap) = 7 := by
    rw [h, finrank_top, Module.finrank_fin_fun]
  rw [finrank_ker_segre3Defect] at h7
  exact absurd h7 (by norm_num)

/-- Sanity check: the defective Segre threefold example specializes to `ℂ`
for free. -/
example :
    LinearMap.ker ((2 : ℂ) • coordProj 7 6 - coordProj 7 3 - coordProj 7 4 - coordProj 7 5 :
        (Fin 7 → ℂ) →L[ℂ] ℂ).toLinearMap =
      ⨆ i : Fin 2,
        (segre3ParamPair ((0, 0, 0) : ℂ × ℂ × ℂ) ((1, 1, 1) : ℂ × ℂ × ℂ) i).tangentSpace :=
  segre3_terracini (𝕜 := ℂ)

end SegreCubicExample
