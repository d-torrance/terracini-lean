import TerraciniLemma.Core
import TerraciniLemma.PolynomialCalculus
import TerraciniLemma.RationalNormalCurves
import TerraciniLemma.VeroneseSurface
import TerraciniLemma.VeroneseGeneral
import TerraciniLemma.VeroneseDegree
import TerraciniLemma.VeroneseAH437
import TerraciniLemma.VeroneseAH245
import TerraciniLemma.Segre
import TerraciniLemma.EllipticCurve
import TerraciniLemma.Projective
import TerraciniLemma.Defect

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
* `TerraciniLemma.VeroneseGeneral` — the general quadric Veronese variety
  `v₂(ℙⁿ) ⊂ ℙ^N` (`N = binom(n+2,2) - 1`), worked in the affine cone model for
  arbitrary `n` and arbitrary `r` general points (`1 ≤ r ≤ n+1`), subsuming
  `TerraciniLemma.VeroneseSurface`'s `n = 2, r = 2` instance.
  `isDefective_veroneseGeneral_iff` shows `σᵣ(v₂(ℙⁿ))` is
  Alexander–Hirschowitz defective iff `2 ≤ r ≤ n`; `veroneseGeneral_sup_eq_top`
  and `veroneseGeneral_not_isDefective_of_succ_le` handle the non-defective
  superabundant regime `r ≥ n+1`.
* `TerraciniLemma.VeroneseDegree` — the degree-`d` Veronese variety
  `v_d(ℙⁿ) ⊂ ℙ^N` (`N = binom(n+d,d) - 1`), with ambient space indexed by
  `Sym (Fin (n+1)) d` (general `d ≥ 1`), generalizing the `d = 2`-only
  `Sym2 (Fin (n+1))`-indexed construction of `TerraciniLemma.VeroneseGeneral`.
  For `d ≥ 3` and `r ≤ n+1` coordinate points, `veroneseDeg_not_isDefective`
  shows `σ_r(v_d(ℙⁿ))` is *not* Alexander–Hirschowitz defective: the per-point
  tangent space supports are pairwise disjoint (unlike the `d = 2` case, where
  they pairwise overlap in one element), so the combined tangent space is an
  honest direct sum of dimension `r(n+1)`.
* `TerraciniLemma.VeroneseAH437` — the `(n,d,r) = (4,3,7)` exceptional case of
  the Alexander–Hirschowitz theorem: `ah437_isDefective` shows
  `σ₇(v₃(ℙ⁴)) ⊂ ℙ^{34}` is defective, using 5 coordinate points `e₀,…,e₄` plus
  two general points `p₆ = (1,1,1,1,1)`, `p₇ = (1,2,3,4,5)`. The certificate is
  a "dual cubic" linear functional `dualCubicφ'` that vanishes on all 7
  tangent spaces but not on the whole ambient space; geometrically (following
  Brambilla–Ottaviani) it is the Hankel-determinant cubic of the unique
  rational normal curve through the 7 points, whose secant variety is singular
  along that curve.
* `TerraciniLemma.VeroneseAH245` — the `(n,d,r) = (2,4,5)` exceptional case of
  the Alexander–Hirschowitz theorem: `ah245_isDefective` shows
  `σ₅(v₄(ℙ²)) ⊂ ℙ^{14}` is defective, using 3 coordinate points `e₀,e₁,e₂` plus
  two general points `p₃ = (1,1,1)`, `p₄ = (1,2,3)`. The certificate is a "dual
  quartic" linear functional `dualQuarticφ` given by the coefficients of
  `F = Q²`, where `Q = 3x₀x₁ - 4x₀x₂ + x₁x₂` is the unique conic through the 5
  points: since `∇F = 2Q∇Q` vanishes on `{Q = 0}` and all 5 points lie on this
  conic, `dualQuarticφ` vanishes on all 5 tangent spaces but not on the whole
  ambient space.
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
* `TerraciniLemma.Defect` (§7) — packages the dimension count from
  `terraciniLemma` into the classical Alexander–Hirschowitz language of
  *expected dimension* and *defect*: `expectedDim S = min (finrank E)
  (∑ i, finrank (S i))`, `IsDefective S` holds when `finrank (⨆ i, S i) <
  expectedDim S`, and `defect S` is the resulting shortfall. Instantiated for
  the quadric Veronese surface (cone model): `veroneseSurface_isDefective` and
  `defect_veroneseSurface` show the classical defect is exactly `1`. Also
  proves monotonicity of non-defectivity in the number of points `r`:
  `finrank_finsetSup_eq_sum_of_not_isDefective_subabundant` (subabundant case,
  non-defectivity for `r` points propagates down to any sub-collection) and
  `not_isDefective_of_finsetSup_eq_top` (superabundant case, propagates up to
  any super-collection). The two-point specialization
  `not_isDefective_of_sup_eq_top` then extends the `σ₂ = E` examples
  (`parabola_terracini`, `segre_terracini`, `elliptic_terracini`) to
  non-defectivity of `σ_r` for every `r ≥ 2`.

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
| `finrank_iSup_le_expectedDim` | ✓ proved | `finrank (⨆ i, S i) ≤ expectedDim S`, always |
| `veroneseSurface_isDefective` | ✓ proved | `v₂(ℙ²) ⊂ ℙ⁵` is Alexander–Hirschowitz defective |
| `defect_veroneseSurface` | ✓ proved | the defect of `σ₂(v₂(ℙ²))` is exactly `1` |
| `isDefective_veroneseGeneral_iff` | ✓ proved | `σᵣ(v₂(ℙⁿ)) ⊂ ℙ^N` is Alexander–Hirschowitz defective iff `2 ≤ r ≤ n` |
| `veroneseGeneral_sup_eq_top` | ✓ proved | `σ_{n+1}(v₂(ℙⁿ))` fills the ambient space (superabundant, non-defective) |
| `veroneseGeneral_not_isDefective_of_succ_le` | ✓ proved | `σ_r(v₂(ℙⁿ))` is non-defective for every `r ≥ n+1` |
| `finrank_ambient_veroneseDeg` | ✓ proved | ambient space of `v_d(ℙⁿ)` has dimension `binom(n+d,d)` |
| `finrank_tangentSpace_veroneseDegFamily` | ✓ proved | each coordinate-point tangent space of `v_d(ℙⁿ)` has dimension `n+1` |
| `finrank_iSup_veroneseDeg` | ✓ proved | for `d ≥ 3`, `r ≤ n+1` coordinate points, the combined tangent space has dimension exactly `r(n+1)` (direct sum, disjoint supports) |
| `veroneseDeg_not_isDefective` | ✓ proved | `σ_r(v_d(ℙⁿ))` is non-defective for `d ≥ 3`, `r ≤ n+1` coordinate points |
| `dualCubicφ'_ne_zero` | ✓ proved | the dual cubic functional (Hankel-determinant cubic) on `v₃(ℙ⁴)`'s ambient space is nonzero |
| `range_combinedDerivative_ah437_le_ker` | ✓ proved | the dual cubic vanishes on the combined tangent space of the 7 points of `(4,3,7)` |
| `finrank_ker_dualCubicφ'` | ✓ proved | `ker dualCubicφ'` has dimension `34 = 35 - 1` |
| `finrank_tangentSpace_ah437` | ✓ proved | each of the 7 tangent spaces of `(4,3,7)` has dimension `5` |
| `ah437_isDefective` | ✓ proved | `σ₇(v₃(ℙ⁴))` is Alexander–Hirschowitz defective (the `(4,3,7)` exceptional case) |
| `dualQuarticφ_ne_zero` | ✓ proved | the dual quartic functional (`F = Q²` for the conic `Q` through the 5 points) on `v₄(ℙ²)`'s ambient space is nonzero |
| `range_combinedDerivative_ah245_le_ker` | ✓ proved | the dual quartic vanishes on the combined tangent space of the 5 points of `(2,4,5)` |
| `finrank_ker_dualQuarticφ` | ✓ proved | `ker dualQuarticφ` has dimension `14 = 15 - 1` |
| `finrank_tangentSpace_ah245` | ✓ proved | each of the 5 tangent spaces of `(2,4,5)` has dimension `3` |
| `ah245_isDefective` | ✓ proved | `σ₅(v₄(ℙ²))` is Alexander–Hirschowitz defective (the `(2,4,5)` exceptional case) |
| `finrank_finsetSup_eq_sum_of_not_isDefective_subabundant` | ✓ proved | subabundant non-defectivity for `r` points implies it for any sub-collection |
| `not_isDefective_of_finsetSup_eq_top` | ✓ proved | superabundant non-defectivity for `r` points implies it for any super-collection |
| `not_isDefective_of_sup_eq_top` | ✓ proved | two-point specialization of the above |
| `parabola_not_isDefective` | ✓ proved | `σ_r(v₂(ℙ¹))` is non-defective for every `r ≥ 2` |
| `segre_not_isDefective` | ✓ proved | `σ_r(ℙ¹×ℙ¹⊂ℙ³)` is non-defective for every `r ≥ 2` |
| `elliptic_not_isDefective` | ✓ proved | `σ_r(y²=x³+1)` is non-defective for every `r ≥ 2` |
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
