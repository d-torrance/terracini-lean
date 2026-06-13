import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

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
  ∑ i : Fin r, (ContinuousLinearMap.proj i : (Fin r → E) →L[𝕜] E)

@[simp]
theorem additionMap_apply (r : ℕ) (v : Fin r → E) :
    additionMap (𝕜 := 𝕜) r v = ∑ i, v i := by
  simp [additionMap, ContinuousLinearMap.sum_apply, ContinuousLinearMap.proj_apply]

/-- The addition map, being linear, is its own Fréchet derivative everywhere. -/
theorem hasFDerivAt_additionMap (r : ℕ) (v : Fin r → E) :
    HasFDerivAt (fun v : Fin r → E => ∑ i, v i) (additionMap (𝕜 := 𝕜) r) v := by
  have heq : (fun v : Fin r → E => ∑ i, v i) = ⇑(additionMap (𝕜 := 𝕜) r) :=
    funext fun v => (additionMap_apply r v).symm
  rw [heq]
  exact (additionMap (𝕜 := 𝕜) r : (Fin r → E) →L[𝕜] E).hasFDerivAt

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
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
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
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply, coordProj_apply]
    rw [Finset.sum_eq_single i
        (fun j _ hji => by rw [Pi.single_eq_of_ne hji, map_zero])
        (fun h => absurd (Finset.mem_univ i) h),
      Pi.single_eq_same]

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

**(B) Generic smoothness** (assumed as a hypothesis): The image of dΦ is
contained in the tangent space T to σᵣ(X̂) at ∑ᵢ vᵢ (`hdominant`, easy), and
dim T ≤ dim Im(dΦ) (`hgeneric`). The latter is a dimension count — in
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
    (_hv   : ∀ i, v i ∈ X)
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
    (_hv   : ∀ i, v i ∈ X)
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
    (_hv   : ∀ i, v i ∈ X)
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
## Summary of proof obligations

| Step | Status | Description |
|------|--------|-------------|
| `hasFDerivAt_additionMap` | ✓ proved | Addition map is its own derivative |
| `hasFDerivAt_combinedParam` | ✓ proved | Chain rule for combined parametrization |
| `range_combinedParam_eq_iSup` | ✓ proved | Im(dΦ) = ⨆ Im(Dfᵢ), both directions |
| `terraciniLemma_derivative` | ✓ proved | Core Terracini computation |
| `terraciniLemma` | ✓ proved | From `hdominant` + `hgeneric` (finrank count) |
| `parabola_terracini` | ✓ proved | Worked example: plane conic, σ₂ = ℝ² |
| `segre_terracini` | ✓ proved | Worked example: Segre quadric P¹×P¹ ⊂ P³, σ₂ = ℝ³ |
| Generic smoothness | ⚠ hypothesis | `hdominant`/`hgeneric` in `terraciniLemma` |

There are no `sorry`s remaining in this file. The only gap is mathematical,
not formal: `terraciniLemma` takes `hdominant : Im(dΦ) ≤ T` (easy, since Φ
maps into σᵣ(X̂)) and `hgeneric : finrank T ≤ finrank Im(dΦ)` (a dimension
count, the actual content of generic smoothness in characteristic zero) as
hypotheses, rather than deriving them from a general theory of dominant
morphisms — which is not yet in Mathlib. The worked examples above discharge
both hypotheses concretely for the plane conic and the Segre quadric.
-/
