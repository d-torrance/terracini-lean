import TerraciniLemma.Core
import TerraciniLemma.PolynomialCalculus
import TerraciniLemma.RationalNormalCurves
import TerraciniLemma.VeroneseSurface
import TerraciniLemma.Segre
import TerraciniLemma.EllipticCurve
import TerraciniLemma.Projective

/-!
# Terracini's Lemma

Terracini's Lemma (1911) describes the tangent space to the r-th secant variety
σᵣ(X) of a projective variety X ⊂ ℙ^N at a general point in terms of the
embedded tangent spaces to X at r general points.

**Informal statement.** For general points p₁, …, pᵣ ∈ X and a general point
p in the linear span ⟨p₁, …, pᵣ⟩, the embedded tangent space to σᵣ(X) at p is

    T_p σᵣ(X) = ⟨T_{p₁}X, …, T_{pᵣ}X⟩.

## File organization

* `TerraciniLemma.Core` — the general theory (§1-6): the addition map,
  the Terracini derivative computation, secant varieties, smooth local
  parametrizations (`LocalParam`), and the statement/proof of
  `terraciniLemma` itself.
* `TerraciniLemma.PolynomialCalculus` — a "middle ground" between hand-rolled
  calculus and the Implicit Function Theorem: a generic bridge between
  `MvPolynomial.pderiv` and `HasFDerivAt`/`ContDiff`, used by
  `TerraciniLemma.RationalNormalCurves` and `TerraciniLemma.EllipticCurve` to
  compute the calculus of polynomial maps for free.
* `TerraciniLemma.RationalNormalCurves` — worked examples for rational normal
  curves `v_r(ℙ¹) ⊂ ℙʳ`: the plane conic `v₂(ℙ¹) ⊂ ℙ²` and the twisted cubic
  `v₃(ℙ¹) ⊂ ℙ³`.
* `TerraciniLemma.VeroneseSurface` — the quadric Veronese surface
  `v₂(ℙ²) ⊂ ℙ⁵`, worked in the *affine cone* model. Unlike the rational normal
  curve examples above, this is a genuinely **defective** case in the sense of
  the Alexander–Hirschowitz theorem: `σ₂(v₂(ℙ²))` falls one dimension short of
  the expected dimension.
* `TerraciniLemma.Segre` — worked examples for Segre varieties: the
  non-defective Segre quadric `ℙ¹ × ℙ¹ ⊂ ℙ³` and the defective Segre
  threefold `ℙ¹ × ℙ¹ × ℙ¹ ⊂ ℙ⁷`.
* `TerraciniLemma.EllipticCurve` — a worked example for the elliptic curve
  `y² = x³ + 1`, which (unlike the Veronese/Segre examples) has no global
  rational parametrization. Local charts are instead built from Mathlib's
  Implicit Function Theorem, demonstrating that `LocalParam` only needs a
  *local* smooth chart at each point.
* `TerraciniLemma.Projective` — descends `terraciniLemma` to the projective
  statement `T_{[p]} σᵣ(X) = ⟨T_{[p₁]}X, …, T_{[pᵣ]}X⟩` in `ℙ(E)`, via the
  order isomorphism `Submodule.projectivization` between linear subspaces of
  `E` and projective subspaces of `ℙ(E)`. Instantiated for the quadric
  Veronese surface: `ℙ(σ₂(v₂(ℙ²)))` is a proper hyperplane `ℙ⁴ ⊊ ℙ⁵`.

## References

- A. Terracini, *Sulle vₖ per cui la varietà degli Sₕ (h+1)-secanti ha dimensione
  minore dell'ordinario*, Rend. Circ. Mat. Palermo **31** (1911), 392–396.
- J. M. Landsberg, *Geometry and Complexity Theory*, Cambridge (2017), §5.3.
- L. Chiantini, C. Ciliberto, *Weakly defective varieties*, Trans. Amer. Math.
  Soc. **354** (2002), 151–178.
-/

/-!
## Summary of proof obligations

| Step | Status | Description |
|------|--------|-------------|
| `hasFDerivAt_additionMap` | ✓ proved | Addition map is its own derivative |
| `hasFDerivAt_combinedParam` | ✓ proved | Chain rule for combined parametrization |
| `range_combinedParam_eq_iSup` | ✓ proved | Im(dΦ) = ⨆ Im(Dfᵢ), both directions |
| `terraciniLemma_derivative` | ✓ proved | Core Terracini computation |
| `terraciniLemma` | ✓ proved | From `hdominant` + `hgeneric` (finrank count) |
| `parabola_terracini` | ✓ proved | Worked example: plane conic, σ₂ = 𝕜² |
| `twistedCubic_terracini` | ✓ proved | Worked example: twisted cubic, combined tangent directions span a hyperplane ⊊ 𝕜³ |
| `veroneseSurface_terracini` | ✓ proved | Worked example: quadric Veronese surface v₂(ℙ²) ⊂ ℙ⁵ (cone model), σ₂ ⊊ 𝕜⁶ (genuine Alexander–Hirschowitz defect) |
| `segre_terracini` | ✓ proved | Worked example: Segre quadric P¹×P¹ ⊂ P³, σ₂ = 𝕜³ |
| `segre3_terracini` | ✓ proved | Worked example: Segre threefold P¹×P¹×P¹ ⊂ P⁷, σ₂ ⊊ 𝕜⁷ (defective) |
| `elliptic_terracini` | ✓ proved | Worked example: elliptic curve y²=x³+1 via the Implicit Function Theorem, σ₂ = 𝕜² |
| `terraciniLemma_projective` | ✓ proved | Projective form of `terraciniLemma`, via `Submodule.projectivization` |
| `veroneseSurface_terracini_projective` | ✓ proved | Projective form for v₂(ℙ²) ⊂ ℙ⁵: ℙ(σ₂) is the span of the two projective tangent planes |
| `veroneseSurface_terracini_projective_ne_top` | ✓ proved | ℙ(σ₂(v₂(ℙ²))) ⊊ ℙ⁵ (a hyperplane ℙ⁴) |
| Generic smoothness | ⚠ hypothesis | `hdominant`/`hgeneric` in `terraciniLemma` |

There are no `sorry`s remaining in this file. The only gap is mathematical,
not formal: `terraciniLemma` takes `hdominant : Im(dΦ) ≤ T` (easy, since Φ
maps into σᵣ(X̂)) and `hgeneric : finrank T ≤ finrank Im(dΦ)` (a dimension
count, the actual content of generic smoothness in characteristic zero) as
hypotheses, rather than deriving them from a general theory of dominant
morphisms — which is not yet in Mathlib. The worked examples above discharge
both hypotheses concretely for the plane conic, the (defective) quadric
Veronese surface, the Segre quadric, the (defective) Segre threefold, and the
elliptic curve.
-/
