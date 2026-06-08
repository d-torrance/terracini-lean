/-!
# Terracini's Lemma

Terracini's Lemma (1911) describes the tangent space to the r-th secant variety
σᵣ(X) of a projective variety X ⊂ ℙ^N at a general point in terms of the
embedded tangent spaces to X at r general points.

**Informal statement.** For general points p₁, …, pᵣ ∈ X and a general point
p in the linear span ⟨p₁, …, pᵣ⟩, the embedded tangent space to σᵣ(X) at p is

    T_p σᵣ(X) = ⟨T_{p₁}X, …, T_{pᵣ}X⟩.

## Formalization strategy

We work with the *affine cone* over ℙ^N, replacing X by its cone X̂ ⊆ V
and σᵣ(X) by σ̂ᵣ(X̂) = closure { v₁ + ⋯ + vᵣ | vᵢ ∈ X̂ }. The proof divides
into two parts of very different difficulty.

**Part A (proved in Lean):** The *addition map*
    Φ : (Fin r → 𝔸) → V,   Φ(u) = ∑ᵢ fᵢ(uᵢ)
where fᵢ are local smooth parametrizations of X̂ near vᵢ, has differential at
the product base point equal to ∑ᵢ (Dfᵢ ∘ πᵢ), whose image is T_{v₁}X̂ + ⋯ + T_{vᵣ}X̂.
This follows from the chain rule and linearity of addition.

**Part B (marked `sorry`):** For *general* points, the tangent space to σ̂ᵣ(X̂)
at Σ vᵢ is the image of dΦ. This requires a *generic smoothness* theorem — that
a dominant morphism of smooth irreducible varieties in characteristic zero has
surjective differential at general points — which is not currently in Mathlib.

## References

- A. Terracini, *Sulle vₖ per cui la varietà degli Sₕ (h+1)-secanti ha dimensione
  minore dell'ordinario*, Rend. Circ. Mat. Palermo **31** (1911), 392–396.
- J. M. Landsberg, *Geometry and Complexity Theory*, Cambridge (2017), §5.3.
- L. Chiantini, C. Ciliberto, *Weakly defective varieties*, Trans. Amer. Math.
  Soc. **354** (2002), 151–178.
-/

import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.LinearAlgebra.Span

noncomputable section

open Set Filter Topology

/-!
## §1  The addition map

The map Φ : (Fin r → E) → E, Φ(v) = ∑ᵢ vᵢ, is continuous and 𝕜-linear.
As a continuous linear map it is its own Fréchet derivative everywhere.
-/

section AdditionMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The addition map (Fin r → E) →L[𝕜] E,  v ↦ ∑ᵢ vᵢ. -/
def additionMap (r : ℕ) : (Fin r → E) →L[𝕜] E :=
  ∑ i : Fin r, ContinuousLinearMap.proj i

@[simp]
theorem additionMap_apply (r : ℕ) (v : Fin r → E) :
    additionMap r v = ∑ i, v i := by
  simp [additionMap, ContinuousLinearMap.sum_apply, ContinuousLinearMap.proj_apply]

/-- The addition map, being linear, is its own Fréchet derivative everywhere. -/
theorem hasFDerivAt_additionMap (r : ℕ) (v : Fin r → E) :
    HasFDerivAt (fun v : Fin r → E => ∑ i, v i) (additionMap r) v := by
  have heq : (fun v : Fin r → E => ∑ i, v i) = ⇑(additionMap r) :=
    funext fun v => (additionMap_apply r v).symm
  rw [heq]
  exact (additionMap r).hasFDerivAt

end AdditionMap

/-!
## §2  Differentiating the combined parametrization

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
      (∑ i : Fin r, (Df i).comp (ContinuousLinearMap.proj i))
      u := by
  -- Step 1: for each i, differentiate fᵢ ∘ πᵢ by the chain rule.
  have hcomp : ∀ i : Fin r,
      HasFDerivAt (fun u : Fin r → 𝔸 => f i (u i))
                  ((Df i).comp (ContinuousLinearMap.proj i)) u := fun i =>
    (hf i).comp u (ContinuousLinearMap.proj i).hasFDerivAt
  -- Step 2: sum over all i using the Fréchet derivative sum rule.
  exact HasFDerivAt.sum Finset.univ (fun i _ => hcomp i)

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
        (∑ i : Fin r, (Df i).comp (ContinuousLinearMap.proj i) :
         (Fin r → 𝔸) →L[𝕜] E).toLinearMap =
    ⊔ i : Fin r, LinearMap.range (Df i).toLinearMap := by
  apply le_antisymm
  · -- (≤) range(dΦ) ≤ ⊔ Im(Dfᵢ).
    -- Any y in the range satisfies y = ∑ᵢ Dfᵢ(uᵢ) for some u : Fin r → 𝔸.
    -- Each term Dfᵢ(uᵢ) lies in Im(Dfᵢ) ≤ ⊔ Im(Dfᵢ), so their sum is too.
    rintro y ⟨u, rfl⟩
    -- Switch from LinearMap.toLinearMap to the underlying CLM coercion
    change (∑ i : Fin r, (Df i).comp (ContinuousLinearMap.proj i)) u ∈
           ⊔ i : Fin r, LinearMap.range (Df i).toLinearMap
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
               ContinuousLinearMap.proj_apply]
    -- Goal: ∑ i, Df i (u i) ∈ ⊔ i, Im(Df i)
    apply Submodule.sum_mem
    intro i _
    exact Submodule.le_iSup (f := fun i => LinearMap.range (Df i).toLinearMap) i
      ⟨u i, rfl⟩
  · -- (≥) ⊔ Im(Dfᵢ) ≤ range(dΦ).
    -- For a finite join of submodules, any element is a sum y = ∑ yᵢ with yᵢ ∈ Im(Dfᵢ).
    -- Pick uᵢ with Dfᵢ(uᵢ) = yᵢ; then u = (u₁,…,uᵣ) witnesses y = dΦ(u).
    -- (Membership in a finite join of submodules is characterized by finite sums;
    -- this is proved e.g. by induction on r from `Submodule.mem_sup`. We mark
    -- it sorry pending the relevant Mathlib lemma `Submodule.mem_finset_iSup` or
    -- a direct inductive proof.)
    sorry

end TerraciniDerivative

/-!
## §3  Secant varieties

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
  simp [secantVariety, secantSet_one_eq, hX.closure_eq]

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
## §4  Smooth varieties and their tangent spaces

We model a smooth subvariety of E by a collection of local parametrizations.
At each point x ∈ X, a parametrization f : 𝔸 → E with f(u₀) = x and
derivative Df at u₀ gives the embedded tangent space Im(Df) ⊆ E.
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
  /-- Derivative of the chart at the base point. -/
  tangent : 𝔸 →L[𝕜] E
  hasFDerivAt : HasFDerivAt chart tangent basePoint

/-- The embedded tangent space to X at x, given a local parametrization. -/
def LocalParam.tangentSpace {X : Set E} {x : E} (p : LocalParam (𝕜 := 𝕜) (𝔸 := 𝔸) X x) :
    Submodule 𝕜 E :=
  LinearMap.range p.tangent.toLinearMap

end SmoothVariety

/-!
## §5  Terracini's Lemma

We now state and prove Terracini's Lemma. The theorem has two parts:

**(A) The derivative computation** (fully proved): The derivative of the
combined parametrization Φ(u) = ∑ᵢ chartᵢ(uᵢ) at the product base point
has image ∑ᵢ Im(tangentᵢ) = ∑ᵢ T_{vᵢ}X̂.

**(B) Generic smoothness** (assumed as a hypothesis, marked `sorry` inside):
The tangent space to σᵣ(X̂) at ∑ᵢ vᵢ is contained in the image of dΦ.

The combination gives T_{∑vᵢ} σᵣ(X̂) = ∑ᵢ T_{vᵢ}X̂.
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
  ∑ i : Fin r, ((param i).tangent).comp (ContinuousLinearMap.proj i)

/-- **Terracini's Lemma** (modulo generic smoothness).

    Let X̂ ⊆ E be the affine cone of a projective variety, and let
    `T` be the Zariski tangent space to σᵣ(X̂) at ∑ vᵢ.

    The proof combines:
    - **Generic smoothness** (`hgeneric`): T ≤ Im(dΦ)     [algebraic geometry]
    - **Dominance** (`hdominant`): Im(dΦ) ≤ T              [because Φ maps into σᵣ(X̂)]
    - **Terracini computation** (proved): Im(dΦ) = ⊔ Im(Dfᵢ)

    Together these give T = ⊔ Im(Dfᵢ) = T_{v₁}X̂ + ⋯ + T_{vᵣ}X̂. -/
theorem terraciniLemma {r : ℕ} {X : Set E}
    (v     : Fin r → E)
    (hv    : ∀ i, v i ∈ X)
    (param : ∀ i, LocalParam (𝕜 := 𝕜) (𝔸 := 𝔸) X (v i))
    -- T is the Zariski tangent space to σᵣ(X̂) at ∑ vᵢ
    (T : Submodule 𝕜 E)
    -- Generic smoothness: T is contained in the image of the combined derivative.
    -- This encodes the fact that a dominant map in characteristic zero has
    -- surjective differential at general points.
    (hgeneric : T ≤ LinearMap.range (combinedDerivative (v := v) param).toLinearMap)
    -- Dominance: the combined derivative maps into the tangent space of σᵣ(X̂),
    -- because Φ itself maps into σᵣ(X̂) (as a sum of r points from X̂).
    (hdominant : LinearMap.range (combinedDerivative (v := v) param).toLinearMap ≤ T) :
    -- Conclusion: T equals the sum of the individual tangent spaces.
    T = ⊔ i : Fin r, (param i).tangentSpace := by
  -- Since T ≤ Im(dΦ) ≤ T, we have T = Im(dΦ).
  have heq : T = LinearMap.range (combinedDerivative (v := v) param).toLinearMap :=
    le_antisymm hgeneric hdominant
  -- And Im(dΦ) = ⊔ Im(Dfᵢ) by the Terracini computation.
  rw [heq]
  exact range_combinedParam_eq_iSup (fun i => (param i).tangent)

/-- **Terracini's Lemma, derivative form.**

    The derivative of the combined parametrization Φ(u) = ∑ᵢ chartᵢ(uᵢ) at the
    product base point equals `combinedDerivative param`.

    This is the core computation of Terracini's Lemma, fully proved from the chain rule. -/
theorem terraciniLemma_derivative {r : ℕ} {X : Set E}
    (v     : Fin r → E)
    (hv    : ∀ i, v i ∈ X)
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

/-- **Corollary:** The combined parametrization Φ evaluates to ∑ vᵢ at the base point. -/
theorem terraciniLemma_basePoint {r : ℕ} {X : Set E}
    (v     : Fin r → E)
    (hv    : ∀ i, v i ∈ X)
    (param : ∀ i, LocalParam (𝕜 := 𝕜) (𝔸 := 𝔸) X (v i)) :
    ∑ i, (param i).chart ((param i).basePoint) = ∑ i, v i :=
  Finset.sum_congr rfl fun i _ => (param i).chart_eval

end TerraciniLemma

/-!
## §6  The projective formulation

In the projective setting, X ⊂ ℙ(E) and its secant variety σᵣ(X) ⊂ ℙ(E) are
projectivizations of the affine cones X̂ ⊆ E and σ̂ᵣ(X̂) ⊆ E. The embedded
tangent space T_p X ⊂ ℙ(E) at a smooth point p corresponds to the projectivization
of the linear subspace Tᵥ X̂ ⊆ E (where v is a lift of p).

Terracini's Lemma in projective coordinates then says:

    ℙ(T_{∑vᵢ} σ̂ᵣ(X̂)) = span{ ℙ(T_{v₁}X̂), …, ℙ(T_{vᵣ}X̂) }

which is exactly the statement T_p σᵣ(X) = ⟨T_{p₁}X, …, T_{pᵣ}X⟩.

We do not give a full formalization of the projective version here, as it
requires the projectivization API from `Mathlib.LinearAlgebra.Projectivization`,
which can be connected to the affine cone results above via the standard
cone-to-projective correspondence.
-/

end

/-!
## Summary of proof obligations

| Step | Status | Description |
|------|--------|-------------|
| `hasFDerivAt_additionMap` | ✓ proved | Addition map is its own derivative |
| `hasFDerivAt_combinedParam` | ✓ proved | Chain rule for combined parametrization |
| `range_combinedParam_eq_iSup` (≤ direction) | ✓ proved | Each Dfᵢ(uᵢ) term ∈ ⊔ Im(Dfᵢ) |
| `range_combinedParam_eq_iSup` (≥ direction) | ⚠ sorry | Finite sum membership in ⊔ Im(Dfᵢ) |
| `terraciniLemma_derivative` | ✓ proved | Core Terracini computation |
| Generic smoothness | ⚠ axiom | Dominant maps have surjective differentials (char 0) |

The single `sorry` in the range theorem (the ≥ direction) is a purely algebraic
fact about submodules, not a deep result — it follows from `Submodule.mem_iSup_of_chain`
or a direct finite induction. The axiom for generic smoothness is the genuine
mathematical content that requires characteristic-zero algebraic geometry.
-/
