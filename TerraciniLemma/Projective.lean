module

public import TerraciniLemma.Core
public import Mathlib.LinearAlgebra.Projectivization.Subspace

/-!
# §5 (continued) — The projective formulation

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
`X`). This holds for the Veronese varieties (e.g. `TerraciniLemma.VeroneseGeneral`, where
`E = Sym2 (Fin (n+1)) → 𝕜` is the cone over `v₂(ℙⁿ)`). It does *not* hold for the
affine-*chart* examples
(`TerraciniLemma.RationalNormalCurves`'s parabola/twisted cubic,
`TerraciniLemma.Segre`, `TerraciniLemma.EllipticCurve`), whose ambient spaces
are affine charts of a projective space rather than cones over it —
`Submodule.projectivization` still applies formally to those `T = ⨆ ...`
equations, but the resulting statement is
about `ℙ(E)` for the *wrong* `E`, not the projective secant variety of the
intended `X`.
-/

@[expose] public section

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
    (param : ∀ i, LocalParam (𝕜 := 𝕜) (𝔸 := 𝔸) X (v i))
    (T : Submodule 𝕜 E)
    (hdominant : LinearMap.range (combinedDerivative (v := v) param).toLinearMap ≤ T)
    (hgeneric : Module.finrank 𝕜 T ≤
        Module.finrank 𝕜 (LinearMap.range (combinedDerivative (v := v) param).toLinearMap)) :
    Submodule.projectivization T = ⨆ i : Fin r, (param i).projectiveTangentSpace := by
  rw [terraciniLemma v param T hdominant hgeneric]
  exact projectivization_iSup _

end
