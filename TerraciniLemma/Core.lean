module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Terracini's Lemma: core theory

This file contains the general theory shared by the worked examples in
`TerraciniLemma.RationalNormalCurves` and `TerraciniLemma.Segre`.

We work with the *affine cone* over ℙ^N, replacing a projective variety X by
its cone X̂ ⊆ V and σᵣ(X) by σ̂ᵣ(X̂) = closure { v₁ + ⋯ + vᵣ | vᵢ ∈ X̂ }. The
proof divides into two parts of very different difficulty.

**Part A (proved in Lean):** The *addition map*
    Φ : (Fin r → 𝔸) → V,   Φ(u) = ∑ᵢ fᵢ(uᵢ)
where fᵢ are local smooth parametrizations of X̂ near vᵢ, has differential at
the product base point equal to ∑ᵢ (Dfᵢ ∘ πᵢ), whose image is T_{v₁}X̂ + ⋯ + T_{vᵣ}X̂.
This follows from the chain rule and linearity of addition.

**Part B (a hypothesis):** For *general* points, the tangent space to σ̂ᵣ(X̂)
at Σ vᵢ is the image of dΦ. This requires a *generic smoothness* theorem — that
a dominant morphism of smooth irreducible varieties in characteristic zero has
surjective differential at general points — which is not currently in Mathlib.
Only its dimension-count half is assumed: taking T to be the span of Mathlib's
tangent cone `tangentConeAt 𝕜 (secantVariety r X) (∑ vᵢ)`, the containment
Im(dΦ) ⊆ T is proved (`range_combinedDerivative_le_span_tangentConeAt`), since
each chart lands in X̂ near its base point (`LocalParam.chart_mem`).

The file is organized into five sections:

* §1 — differentiating the combined parametrization (`combinedDerivative`,
  `range_combinedParam_eq_iSup`)
* §2 — secant varieties (`secantSet`, `secantVariety`)
* §3 — smooth local parametrizations and their tangent spaces (`LocalParam`)
* §4 — the statement and proof of `terraciniLemma`
* §5 — a sketch of the projective formulation
-/

@[expose] public section

noncomputable section

open Set Filter Topology

/-!
## §1  Differentiating the combined parametrization

Given smooth maps fᵢ : 𝔸 → E (local parametrizations of X̂ near vᵢ), the
combined parametrization Φ(u) = ∑ᵢ fᵢ(uᵢ) has derivative

    dΦᵤ(w) = ∑ᵢ (Dfᵢ)(wᵢ)

at any point u. Equivalently, as a continuous linear map:  dΦᵤ = ∑ᵢ Dfᵢ ∘ πᵢ,
where πᵢ : (Fin r → 𝔸) →L[𝕜] 𝔸 is the i-th coordinate projection.

The image of dΦᵤ is then T_{v₁}X̂ + ⋯ + T_{vᵣ}X̂.  This is the core of
Terracini's Lemma: the computation of the derivative of the addition map.
-/

section TerraciniDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝔸 E : Type*}
  [NormedAddCommGroup 𝔸] [NormedSpace 𝕜 𝔸]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The i-th coordinate projection `(Fin r → 𝔸) →L[𝕜] 𝔸`, given an explicit
    codomain type so that `𝕜` is not left as a metavariable during elaboration. -/
def coordProj (r : ℕ) (i : Fin r) : (Fin r → 𝔸) →L[𝕜] 𝔸 :=
  ContinuousLinearMap.proj i

@[simp]
theorem coordProj_apply (r : ℕ) (i : Fin r) (u : Fin r → 𝔸) :
    coordProj (𝕜 := 𝕜) r i u = u i := rfl

/-- The coordinate projection `coordProj r i` is its own Fréchet derivative
    for the function `u ↦ u i`. -/
theorem hasFDerivAt_coordProj (r : ℕ) (i : Fin r) (u : Fin r → 𝔸) :
    HasFDerivAt (fun u : Fin r → 𝔸 => u i) (coordProj (𝕜 := 𝕜) r i) u := by
  have heq : (fun u : Fin r → 𝔸 => u i) = ⇑(coordProj (𝕜 := 𝕜) r i) := rfl
  rw [heq]
  exact (coordProj (𝕜 := 𝕜) r i : (Fin r → 𝔸) →L[𝕜] 𝔸).hasFDerivAt

/-- **Terracini derivative computation.**

    For smooth maps fᵢ : 𝔸 → E with derivatives Dfᵢ at uᵢ, the combined
    parametrization Φ(u) = ∑ᵢ fᵢ(uᵢ) has derivative dΦᵤ = ∑ᵢ Dfᵢ ∘ πᵢ. -/
theorem hasFDerivAt_combinedParam {r : ℕ}
    (f  : Fin r → 𝔸 → E)
    (Df : Fin r → 𝔸 →L[𝕜] E)
    (u  : Fin r → 𝔸)
    (hf : ∀ i, HasFDerivAt (f i) (Df i) (u i)) :
    HasFDerivAt
      (fun u : Fin r → 𝔸 => ∑ i, f i (u i))
      (∑ i : Fin r, (Df i).comp (coordProj r i))
      u := by
  -- Step 1: for each i, differentiate fᵢ ∘ πᵢ by the chain rule.
  have hcomp : ∀ i : Fin r,
      HasFDerivAt (fun u : Fin r → 𝔸 => f i (u i))
                  ((Df i).comp (coordProj r i)) u := fun i =>
    (hf i).comp u (hasFDerivAt_coordProj r i u)
  -- Step 2: sum over all i using the Fréchet derivative sum rule.
  have hsum : HasFDerivAt (∑ i : Fin r, fun u : Fin r → 𝔸 => f i (u i))
      (∑ i : Fin r, (Df i).comp (coordProj r i)) u :=
    HasFDerivAt.sum (fun i _ => hcomp i)
  -- Rewrite the pointwise sum of functions as a function of a sum.
  have heq : (∑ i : Fin r, fun u : Fin r → 𝔸 => f i (u i)) =
      fun u : Fin r → 𝔸 => ∑ i, f i (u i) := by
    funext u
    simp
  rwa [heq] at hsum

/-!
### Range of the combined derivative

The image of ∑ᵢ Dfᵢ ∘ πᵢ, as a submodule of E, equals the join ⊔ᵢ Im(Dfᵢ).
This expresses that varying uᵢ independently lets us reach any element of the
sum of the individual tangent spaces.
-/

/-- The range of ∑ᵢ Dfᵢ ∘ πᵢ equals the join of the individual ranges. -/
theorem range_combinedParam_eq_iSup {r : ℕ}
    (Df : Fin r → 𝔸 →L[𝕜] E) :
    LinearMap.range
        (∑ i : Fin r, (Df i).comp (coordProj r i) :
         (Fin r → 𝔸) →L[𝕜] E).toLinearMap =
    ⨆ i : Fin r, LinearMap.range (Df i).toLinearMap := by
  apply le_antisymm
  · -- (≤) range(dΦ) ≤ ⨆ Im(Dfᵢ).
    -- Any y in the range satisfies y = ∑ᵢ Dfᵢ(uᵢ) for some u : Fin r → 𝔸.
    -- Each term Dfᵢ(uᵢ) lies in Im(Dfᵢ) ≤ ⨆ Im(Dfᵢ), so their sum is too.
    rintro y ⟨u, rfl⟩
    -- Switch from LinearMap.toLinearMap to the underlying CLM coercion
    change (∑ i : Fin r, (Df i).comp (coordProj r i)) u ∈
           ⨆ i : Fin r, LinearMap.range (Df i).toLinearMap
    simp only [sum_apply, ContinuousLinearMap.comp_apply,
               coordProj_apply]
    -- Goal: ∑ i, Df i (u i) ∈ ⨆ i, Im(Df i)
    apply Submodule.sum_mem
    intro i _
    exact le_iSup (f := fun i => LinearMap.range (Df i).toLinearMap) i
      ⟨u i, rfl⟩
  · -- (≥) ⨆ Im(Dfᵢ) ≤ range(dΦ).
    -- For each i, Im(Dfᵢ) ≤ range(dΦ): given y = Dfᵢ(a), take u = Pi.single i a,
    -- so that all other coordinates contribute 0 and dΦ(u) = Dfᵢ(a) = y.
    apply iSup_le
    intro i
    rintro y ⟨a, rfl⟩
    refine ⟨Pi.single i a, ?_⟩
    change (∑ j : Fin r, (Df j).comp (coordProj r j)) (Pi.single i a) = Df i a
    simp only [sum_apply, ContinuousLinearMap.comp_apply, coordProj_apply]
    rw [Finset.sum_eq_single i
        (fun j _ hji => by rw [Pi.single_eq_of_ne hji, map_zero])
        (fun h => absurd (Finset.mem_univ i) h),
      Pi.single_eq_same]

end TerraciniDerivative

/-!
## §2  Secant varieties

The r-th secant variety of X ⊆ E is the closure of all r-fold sums of points
from X. For a projective variety X ⊂ ℙ(E) this should be interpreted via
the affine cone.
-/

section SecantVariety

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The r-th secant set: all r-fold sums of points from X. -/
def secantSet (r : ℕ) (X : Set E) : Set E :=
  (fun v : Fin r → E => ∑ i, v i) '' (Set.pi Set.univ fun _ => X)

theorem mem_secantSet_iff {r : ℕ} {X : Set E} {y : E} :
    y ∈ secantSet r X ↔ ∃ v : Fin r → E, (∀ i, v i ∈ X) ∧ ∑ i, v i = y := by
  simp only [secantSet, Set.mem_image, Set.mem_pi, Set.mem_univ, forall_const]

theorem secantSet_one_eq (X : Set E) : secantSet 1 X = X := by
  ext y
  simp only [mem_secantSet_iff, Fin.sum_univ_one]
  exact ⟨fun ⟨v, hv, h⟩ => h ▸ hv 0, fun hy => ⟨fun _ => y, fun _ => hy, rfl⟩⟩

/-- The r-th secant variety: closure of the secant set. -/
def secantVariety (r : ℕ) (X : Set E) : Set E :=
  closure (secantSet r X)

theorem secantSet_subset_secantVariety (r : ℕ) (X : Set E) :
    secantSet r X ⊆ secantVariety r X :=
  subset_closure

theorem secantVariety_one_eq (X : Set E) (hX : IsClosed X) :
    secantVariety 1 X = X := by
  rw [secantVariety, secantSet_one_eq, hX.closure_eq]

/-- σᵣ(X) ⊆ σᵣ₊₁(X) whenever 0 ∈ X. -/
theorem secantVariety_mono {r : ℕ} {X : Set E} (h0 : (0 : E) ∈ X) :
    secantVariety r X ⊆ secantVariety (r + 1) X := by
  apply closure_mono
  intro y hy
  rw [mem_secantSet_iff] at hy ⊢
  obtain ⟨v, hv, rfl⟩ := hy
  refine ⟨Fin.snoc v 0, fun i => ?_, by simp [Fin.sum_univ_castSucc]⟩
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using h0
  · simpa using hv j

end SecantVariety

/-!
## §3  Smooth varieties and their tangent spaces

We model a smooth subvariety of E by a collection of local parametrizations.
At each point x ∈ X, a parametrization f : 𝔸 → E with f(u₀) = x, landing in X
near u₀, with derivative Df at u₀ gives the embedded tangent space Im(Df) ⊆ E.
-/

section SmoothVariety

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝔸 E : Type*}
  [NormedAddCommGroup 𝔸] [NormedSpace 𝕜 𝔸]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A smooth local parametrization of X ⊆ E at a point x. -/
structure LocalParam (X : Set E) (x : E) where
  /-- Base point in the parameter space. -/
  basePoint : 𝔸
  /-- The parametrization map. -/
  chart : 𝔸 → E
  chart_eval : chart basePoint = x
  /-- Near the base point, the chart lands in `X`. -/
  chart_mem : ∀ᶠ u in 𝓝 basePoint, chart u ∈ X
  /-- Derivative of the chart at the base point. -/
  tangent : 𝔸 →L[𝕜] E
  hasFDerivAt : HasFDerivAt chart tangent basePoint

/-- The embedded tangent space to X at x, given a local parametrization. -/
def LocalParam.tangentSpace {X : Set E} {x : E} (p : LocalParam (𝕜 := 𝕜) (𝔸 := 𝔸) X x) :
    Submodule 𝕜 E :=
  LinearMap.range p.tangent.toLinearMap

end SmoothVariety

/-!
## §4  Terracini's Lemma

We now state and prove Terracini's Lemma. The theorem has two parts:

**(A) The derivative computation** (fully proved): The derivative of the
combined parametrization Φ(u) = ∑ᵢ chartᵢ(uᵢ) at the product base point
has image ∑ᵢ Im(tangentᵢ) = ∑ᵢ T_{vᵢ}X̂.

**(B) Generic smoothness** (assumed as a hypothesis): The image of dΦ is
contained in the tangent space T to σᵣ(X̂) at ∑ᵢ vᵢ (`hdominant`, easy), and
dim T ≤ dim Im(dΦ) (`hgeneric`). For T the span of the tangent cone to σᵣ(X̂),
`hdominant` is a theorem (`range_combinedDerivative_le_span_tangentConeAt`), and
`terraciniLemma_tangentCone` needs only `hgeneric`. The latter is a dimension count — in
practice obtained from a Jacobian-rank computation — and is the precise
content of generic smoothness in characteristic zero: at a general point,
the differential of a dominant map has rank equal to the dimension of the
target.

Together, `Im(dΦ) ≤ T` and `dim T ≤ dim Im(dΦ)` force `Im(dΦ) = T`, so the
combination gives T_{∑vᵢ} σᵣ(X̂) = ∑ᵢ T_{vᵢ}X̂.
-/

section TerraciniLemma

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝔸 E : Type*}
  [NormedAddCommGroup 𝔸] [NormedSpace 𝕜 𝔸]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
The key missing ingredient is **generic smoothness**: a dominant morphism of
smooth irreducible varieties in characteristic zero has surjective differential
at general points. We incorporate this as an explicit hypothesis `hgeneric` in
the main theorem, making the logical dependency transparent.
-/

/-- Shorthand for the combined derivative of the parametrizations. -/
def combinedDerivative {r : ℕ} {X : Set E} {v : Fin r → E}
    (param : ∀ i : Fin r, LocalParam (𝕜 := 𝕜) (𝔸 := 𝔸) X (v i)) :
    (Fin r → 𝔸) →L[𝕜] E :=
  ∑ i : Fin r, ((param i).tangent).comp (coordProj r i)

/-- **Terracini's Lemma** (modulo generic smoothness).

    Let X̂ ⊆ E be the affine cone of a projective variety, and let
    `T` be the Zariski tangent space to σᵣ(X̂) at ∑ vᵢ.

    The proof combines:
    - **Dominance** (`hdominant`): Im(dΦ) ≤ T              [because Φ maps into σᵣ(X̂)]
    - **Generic smoothness** (`hgeneric`): dim T ≤ dim Im(dΦ)  [Jacobian-rank count]
    - **Terracini computation** (proved): Im(dΦ) = ⨆ Im(Dfᵢ)

    Together these give T = Im(dΦ) = ⨆ Im(Dfᵢ) = T_{v₁}X̂ + ⋯ + T_{vᵣ}X̂. -/
theorem terraciniLemma {r : ℕ} {X : Set E} [FiniteDimensional 𝕜 E]
    (v     : Fin r → E)
    (param : ∀ i, LocalParam (𝕜 := 𝕜) (𝔸 := 𝔸) X (v i))
    -- T is the Zariski tangent space to σᵣ(X̂) at ∑ vᵢ
    (T : Submodule 𝕜 E)
    -- Dominance: the combined derivative maps into the tangent space of σᵣ(X̂),
    -- because Φ itself maps into σᵣ(X̂) (as a sum of r points from X̂).
    (hdominant : LinearMap.range (combinedDerivative (v := v) param).toLinearMap ≤ T)
    -- Generic smoothness, as a dimension count: dim T ≤ dim Im(dΦ). Together
    -- with hdominant (which gives dim Im(dΦ) ≤ dim T automatically), the two
    -- dimensions must agree, forcing the submodules to coincide.
    (hgeneric : Module.finrank 𝕜 T ≤
        Module.finrank 𝕜 (LinearMap.range (combinedDerivative (v := v) param).toLinearMap)) :
    -- Conclusion: T equals the sum of the individual tangent spaces.
    T = ⨆ i : Fin r, (param i).tangentSpace := by
  -- Since Im(dΦ) ≤ T and dim T ≤ dim Im(dΦ), the two submodules are equal.
  have heq : T = LinearMap.range (combinedDerivative (v := v) param).toLinearMap :=
    (Submodule.eq_of_le_of_finrank_le hdominant hgeneric).symm
  -- And Im(dΦ) = ⨆ Im(Dfᵢ) by the Terracini computation.
  rw [heq]
  exact range_combinedParam_eq_iSup (fun i => (param i).tangent)

/-- **Terracini's Lemma, derivative form.**

    The derivative of the combined parametrization Φ(u) = ∑ᵢ chartᵢ(uᵢ) at the
    product base point equals `combinedDerivative param`.

    This is the core computation of Terracini's Lemma, fully proved from the chain rule. -/
theorem terraciniLemma_derivative {r : ℕ} {X : Set E}
    (v     : Fin r → E)
    (param : ∀ i, LocalParam (𝕜 := 𝕜) (𝔸 := 𝔸) X (v i)) :
    HasFDerivAt
      (fun u : Fin r → 𝔸 => ∑ i, (param i).chart (u i))
      (combinedDerivative (v := v) param)
      (fun i => (param i).basePoint) :=
  hasFDerivAt_combinedParam
    (fun i => (param i).chart)
    (fun i => (param i).tangent)
    _
    (fun i => (param i).hasFDerivAt)

/-- **Dominance, derived.** Every vector in `Im(dΦ)` is tangent to σᵣ(X̂) at `∑ vᵢ`: it lies
in Mathlib's tangent cone `tangentConeAt 𝕜 (secantVariety r X) (∑ vᵢ)`, because Φ maps a
neighbourhood of the base point into `secantSet r X ⊆ secantVariety r X`. So `hdominant` holds
for `T = span (tangentConeAt 𝕜 (secantVariety r X) (∑ vᵢ))`. -/
theorem range_combinedDerivative_le_span_tangentConeAt {r : ℕ} {X : Set E}
    {v : Fin r → E} (param : ∀ i, LocalParam (𝕜 := 𝕜) (𝔸 := 𝔸) X (v i)) :
    LinearMap.range (combinedDerivative (v := v) param).toLinearMap ≤
      Submodule.span 𝕜 (tangentConeAt 𝕜 (secantVariety r X) (∑ i, v i)) := by
  rintro _ ⟨w, rfl⟩
  apply Submodule.subset_span
  set Φ : (Fin r → 𝔸) → E := fun u => ∑ i, (param i).chart (u i)
  set u₀ : Fin r → 𝔸 := fun i => (param i).basePoint
  -- The parameters `u` near `u₀` for which every chart lands in `X`.
  set U : Set (Fin r → 𝔸) := {u | ∀ i, (param i).chart (u i) ∈ X}
  have hU : U ∈ 𝓝 u₀ := Filter.eventually_all.mpr fun i =>
    ((continuous_apply i).tendsto u₀).eventually (param i).chart_mem
  have hΦ : HasFDerivAt Φ (combinedDerivative (v := v) param) u₀ :=
    hasFDerivAt_combinedParam _ _ _ fun i => (param i).hasFDerivAt
  have hw : w ∈ tangentConeAt 𝕜 U u₀ := by
    rw [tangentConeAt_of_mem_nhds hU]; trivial
  have hsub : Φ '' U ⊆ secantVariety r X := by
    rintro _ ⟨u, hu, rfl⟩
    exact secantSet_subset_secantVariety r X
      (mem_secantSet_iff.mpr ⟨fun i => (param i).chart (u i), hu, rfl⟩)
  have hΦu₀ : Φ u₀ = ∑ i, v i := Finset.sum_congr rfl fun i _ => (param i).chart_eval
  rw [← hΦu₀]
  exact tangentConeAt_mono hsub (hΦ.hasFDerivWithinAt.mapsTo_tangent_cone hw)

/-- **Terracini's Lemma, tangent-cone form.** With `T` the linear span of the tangent cone to
σᵣ(X̂) at `∑ vᵢ`, the dominance hypothesis of `terraciniLemma` is a theorem
(`range_combinedDerivative_le_span_tangentConeAt`), leaving only the generic-smoothness
dimension count `hgeneric`. -/
theorem terraciniLemma_tangentCone {r : ℕ} {X : Set E} [FiniteDimensional 𝕜 E]
    (v : Fin r → E)
    (param : ∀ i, LocalParam (𝕜 := 𝕜) (𝔸 := 𝔸) X (v i))
    (hgeneric : Module.finrank 𝕜
        (Submodule.span 𝕜 (tangentConeAt 𝕜 (secantVariety r X) (∑ i, v i))) ≤
      Module.finrank 𝕜 (LinearMap.range (combinedDerivative (v := v) param).toLinearMap)) :
    Submodule.span 𝕜 (tangentConeAt 𝕜 (secantVariety r X) (∑ i, v i)) =
      ⨆ i : Fin r, (param i).tangentSpace :=
  terraciniLemma v param _
    (range_combinedDerivative_le_span_tangentConeAt param) hgeneric

/-- **Unconditional corollary.** If the tangent spaces `T_{vᵢ}X̂` already span `E`, the
tangent cone to σᵣ(X̂) at `∑ vᵢ` spans `E` too, with no generic-smoothness input: `hgeneric`
is automatic because `Im(dΦ) = E` has maximal dimension. -/
theorem span_tangentConeAt_secantVariety_eq_top {r : ℕ} {X : Set E} [FiniteDimensional 𝕜 E]
    (v : Fin r → E)
    (param : ∀ i, LocalParam (𝕜 := 𝕜) (𝔸 := 𝔸) X (v i))
    (htop : ⨆ i : Fin r, (param i).tangentSpace = ⊤) :
    Submodule.span 𝕜 (tangentConeAt 𝕜 (secantVariety r X) (∑ i, v i)) = ⊤ := by
  have hrange : LinearMap.range (combinedDerivative (v := v) param).toLinearMap = ⊤ :=
    (range_combinedParam_eq_iSup (fun i => (param i).tangent)).trans htop
  rw [← hrange]
  exact le_antisymm (hrange ▸ le_top) (range_combinedDerivative_le_span_tangentConeAt param)

end TerraciniLemma

/-!
## §5  The projective formulation

In the projective setting, X ⊂ ℙ(E) and its secant variety σᵣ(X) ⊂ ℙ(E) are
projectivizations of the affine cones X̂ ⊆ E and σ̂ᵣ(X̂) ⊆ E. The embedded
tangent space T_p X ⊂ ℙ(E) at a smooth point p corresponds to the projectivization
of the linear subspace Tᵥ X̂ ⊆ E (where v is a lift of p).

Terracini's Lemma in projective coordinates then says:

    ℙ(T_{∑vᵢ} σ̂ᵣ(X̂)) = span{ ℙ(T_{v₁}X̂), …, ℙ(T_{vᵣ}X̂) }

which is exactly the statement T_p σᵣ(X) = ⟨T_{p₁}X, …, T_{pᵣ}X⟩.

This descent is carried out in `TerraciniLemma.Projective`, using the order
isomorphism `Submodule.projectivization : Submodule 𝕜 E ≃o
Projectivization.Subspace 𝕜 E` from `Mathlib.LinearAlgebra.Projectivization`:
applying it to both sides of `T = ⨆ i, (param i).tangentSpace` (and using that
order isomorphisms of complete lattices preserve `iSup`) immediately gives the
projective statement above. See that file for the precise statement,
including the caveat that `E` must itself be the affine cone over `X` for the
result to carry its intended geometric meaning (true for the Veronese
varieties, not for the affine-chart examples).
-/

end
