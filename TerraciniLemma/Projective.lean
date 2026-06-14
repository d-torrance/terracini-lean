import TerraciniLemma.VeroneseSurface
import Mathlib.LinearAlgebra.Projectivization.Subspace

/-!
# §6 (continued) — The projective formulation

`TerraciniLemma/Core.lean` works entirely with affine cones `X̂ ⊆ E`: secant
varieties, tangent spaces, and `terraciniLemma` itself are all subsets/submodules
of a normed vector space `E`. This file descends that result to the projective
statement

    T_{[p]} σᵣ(X) = ⟨T_{[p₁]}X, …, T_{[pᵣ]}X⟩    in ℙ(E),

for `X = ℙ(X̂) ⊂ ℙ(E)`.

## The order isomorphism

`Mathlib.LinearAlgebra.Projectivization.Subspace` provides an order
isomorphism

    Submodule.projectivization : Submodule 𝕜 E ≃o Projectivization.Subspace 𝕜 E

between linear subspaces of `E` and projective subspaces of `ℙ(E)` (a submodule
`S` corresponds to the projective subspace of all lines through `0` contained in
`S`). Order isomorphisms between complete lattices preserve arbitrary `iSup`s
(`OrderIso.map_iSup`) and `⊤` (`OrderIso.map_top`), so applying
`Submodule.projectivization` to both sides of

    T = ⨆ i, (param i).tangentSpace

immediately gives the projective statement

    Submodule.projectivization T = ⨆ i, Submodule.projectivization (param i).tangentSpace.

This is `terraciniLemma_projective` below — a direct corollary of `terraciniLemma`,
with no new mathematical content.

## Caveat: cone vs. chart

The descent above is only the *intended* statement
`T_{[p]} σᵣ(X) = ⟨T_{[p₁]}X, …⟩` when `E` is literally the affine cone over the
projective variety `X` (so that `ℙ(E)` is the ambient projective space containing
`X`). This holds for `TerraciniLemma.VeroneseSurface` (`E = Fin 6 → 𝕜 = Sym²(𝕜³)`
is the cone over `v₂(ℙ²) ⊂ ℙ⁵`), and we instantiate the corollary for that
example below. It does *not* hold for the affine-*chart* examples
(`TerraciniLemma.RationalNormalCurves`'s parabola/twisted cubic,
`TerraciniLemma.Segre`, `TerraciniLemma.EllipticCurve`), whose ambient spaces
are affine charts of a projective space rather than cones over it —
`Submodule.projectivization` still applies formally to those `T = ⨆ ...`
equations, but the resulting statement is
about `ℙ(E)` for the *wrong* `E`, not the projective secant variety of the
intended `X`.
-/

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {𝔸 E : Type*}
  [NormedAddCommGroup 𝔸] [NormedSpace 𝕜 𝔸]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- The projective tangent space to `X` at `x`, as a `Projectivization.Subspace 𝕜 E`:
the projectivization of the affine tangent space `p.tangentSpace ≤ E`. -/
def LocalParam.projectiveTangentSpace {X : Set E} {x : E}
    (p : LocalParam (𝕜 := 𝕜) (𝔸 := 𝔸) X x) : Projectivization.Subspace 𝕜 E :=
  Submodule.projectivization p.tangentSpace

/-- `Submodule.projectivization` commutes with `iSup`: a special case of
`OrderIso.map_iSup` for the order isomorphism between submodules of `E` and
projective subspaces of `ℙ(E)`. -/
theorem projectivization_iSup {ι : Type*} (S : ι → Submodule 𝕜 E) :
    Submodule.projectivization (⨆ i, S i) = ⨆ i, Submodule.projectivization (S i) :=
  OrderIso.map_iSup Submodule.projectivization S

/-- **Terracini's Lemma, projective form.** A direct corollary of `terraciniLemma`:
applying the order isomorphism `Submodule.projectivization` to both sides of
`T = ⨆ i, (param i).tangentSpace` gives the projective statement
`ℙ(T) = ⨆ i, ℙ((param i).tangentSpace)`. See the module docstring for the
caveat about when this is the *geometrically intended* projective Terracini
statement (`E` must be the affine cone over `X`). -/
theorem terraciniLemma_projective {r : ℕ} {X : Set E} [FiniteDimensional 𝕜 E]
    (v     : Fin r → E)
    (hv    : ∀ i, v i ∈ X)
    (param : ∀ i, LocalParam (𝕜 := 𝕜) (𝔸 := 𝔸) X (v i))
    (T : Submodule 𝕜 E)
    (hdominant : LinearMap.range (combinedDerivative (v := v) param).toLinearMap ≤ T)
    (hgeneric : Module.finrank 𝕜 T ≤
        Module.finrank 𝕜 (LinearMap.range (combinedDerivative (v := v) param).toLinearMap)) :
    Submodule.projectivization T = ⨆ i : Fin r, (param i).projectiveTangentSpace := by
  rw [terraciniLemma v hv param T hdominant hgeneric]
  exact projectivization_iSup _

end

/-!
## Worked example: the quadric Veronese surface

`TerraciniLemma.VeroneseSurface`'s ambient space `Fin 6 → 𝕜` *is* the affine
cone over `v₂(ℙ²) ⊂ ℙ⁵` (the symmetric `3×3` matrices `Sym²(𝕜³)`), so the
projective form of `veroneseSurface_terracini` is the genuine projective
Terracini statement for this example: the projective secant variety
`ℙ(σ₂(v₂(ℙ²)))` (a hyperplane `ℙ⁴ ⊂ ℙ⁵`) equals the span of the two projective
tangent planes at `[e₁], [e₂]`.
-/

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

theorem veroneseSurface_terracini_projective :
    Submodule.projectivization (LinearMap.ker (coordProj (𝕜 := 𝕜) (𝔸 := 𝕜) 6 2).toLinearMap) =
      ⨆ i : Fin 2, LocalParam.projectiveTangentSpace
        (veroneseSurfaceParamPair (![1, 0, 0] : Fin 3 → 𝕜) (![0, 1, 0] : Fin 3 → 𝕜) i) := by
  rw [veroneseSurface_terracini]
  exact projectivization_iSup _

/-- The projective secant variety `ℙ(σ₂(v₂(ℙ²)))` is a *proper* projective subspace of `ℙ⁵`
(a hyperplane `ℙ⁴`), not all of `ℙ⁵` — the projective shadow of the Alexander–Hirschowitz
defect. -/
theorem veroneseSurface_terracini_projective_ne_top :
    Submodule.projectivization (LinearMap.ker (coordProj (𝕜 := 𝕜) (𝔸 := 𝕜) 6 2).toLinearMap) ≠
      (⊤ : Projectivization.Subspace 𝕜 (Fin 6 → 𝕜)) := by
  rw [← OrderIso.map_top Submodule.projectivization]
  exact fun h => veroneseSurface_terracini_ne_top (Submodule.projectivization.injective h)

end
