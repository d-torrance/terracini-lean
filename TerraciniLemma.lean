module

public import TerraciniLemma.Core
public import TerraciniLemma.PolynomialCalculus
public import TerraciniLemma.RationalNormalCurves
public import TerraciniLemma.VeroneseGeneral
public import TerraciniLemma.VeroneseDegree
public import TerraciniLemma.Semicontinuity
public import TerraciniLemma.RankCertificate
public import TerraciniLemma.CubicLattice
public import TerraciniLemma.CubicInduction
public import TerraciniLemma.CubicBaseCases
public import TerraciniLemma.CubicInductionMain
public import TerraciniLemma.VeroneseForms
public import TerraciniLemma.AlexanderHirschowitzCubic
public import TerraciniLemma.AlexanderHirschowitz
public import TerraciniLemma.AlexanderHirschowitzCubicGeneral
public import TerraciniLemma.Segre
public import TerraciniLemma.EllipticCurve
public import TerraciniLemma.Projective
public import TerraciniLemma.Defect

/-!
# Terracini's Lemma

Terracini's Lemma (1911) describes the tangent space to the r-th secant variety
σᵣ(X) of a projective variety X ⊂ ℙ^N at a general point in terms of the
embedded tangent spaces to X at r general points.

**Informal statement.** For general points p₁, …, pᵣ ∈ X and a general point
p in the linear span ⟨p₁, …, pᵣ⟩, the embedded tangent space to σᵣ(X) at p is

    T_p σᵣ(X) = ⟨T_{p₁}X, …, T_{pᵣ}X⟩.

## File organization

* `TerraciniLemma.Core` — the general theory (§1-5):
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
* `TerraciniLemma.VeroneseGeneral` — the general quadric Veronese variety
  `v₂(ℙⁿ) ⊂ ℙ^N` (`N = binom(n+2,2) - 1`), worked in the affine cone model for
  arbitrary `n` and arbitrary `r` general points (`1 ≤ r ≤ n+1`).
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
  honest direct sum of dimension `r(n+1)`. §E identifies the tangent span with
  the column space of a polynomial matrix, so non-defectivity at one
  configuration spreads to general points (`forGeneralPoints_not_isDefective`,
  giving `veroneseDeg_not_isDefective_general`) and defectivity at general
  points spreads to every configuration of nonzero points
  (`isDefective_of_forGeneralPoints`).
* `TerraciniLemma.Semicontinuity` — `HoldsGenerically`/`ForGeneralPoints`
  (off the zero locus of a nonzero polynomial in the coordinates) and the
  semicontinuity of the rank of a matrix of polynomials: a rank lower bound at
  one point holds generically (`HoldsGenerically.le_rank`), and a generic rank
  upper bound holds everywhere (`HoldsGenerically.rank_le`), via
  `Matrix.le_rank_iff_exists_submatrix_det_ne_zero`.
* `TerraciniLemma.VeroneseForms` — degree-`d` forms as pullbacks `χ ∘ v_d` of
  functionals on the ambient space (closed under products, containing the
  linear forms; `veroneseFormOf_injective`: the Veronese variety is
  nondegenerate), the **singular-form bound**
  `finrank_iSup_tangentSpace_le_of_singular` (a nonzero form singular at the
  points puts all their tangent spaces in a hyperplane).
* `TerraciniLemma.AlexanderHirschowitzCubic` — the `(4,3,7)` case at general
  points, following Brambilla–Ottaviani: an explicit change of coordinates
  sends seven general points of `ℙ⁴` onto the moment curve, where the Hankel
  cubic (the secant variety of the curve) is singular
  (`ah437_isDefective_general`).
* `TerraciniLemma.AlexanderHirschowitz` — every Alexander–Hirschowitz
  exceptional case is defective at every configuration of nonzero points
  (`alexanderHirschowitz_exceptions_isDefective`): quartics `(2,4,5)`,
  `(3,4,9)`, `(4,4,14)` via the square of a quadric through the points,
  quadrics via `TerraciniLemma.VeroneseGeneral`, and `(4,3,7)` as above. Also
  the full theorem for quadrics (`alexanderHirschowitz_quadric`): at `r ≥ 1`
  general points, `σ_r(v₂(ℙⁿ))` is defective iff `2 ≤ r ≤ n`.
* `TerraciniLemma.RankCertificate` — kernel-checkable certificates that an
  integer matrix has rank `≥ k` over any field of characteristic zero
  (`le_rank_of_check`), computed by Macaulay2 via Macaulean (`m2/`,
  `Generator/`, `lake exe certificates`).
* `TerraciniLemma.CubicLattice`, `TerraciniLemma.CubicInduction`,
  `TerraciniLemma.CubicBaseCases`, `TerraciniLemma.CubicInductionMain` — the
  Brambilla–Ottaviani three-level induction for cubics, in the linear-algebra
  form of Torrance–Vannieuwenhoven: points specialized to a lattice of
  coordinate subspaces, the specialization and trace steps, base cases from
  rank certificates (`TerraciniLemma.CubicCertificates`), and the
  superabundant (`super₀`) and subabundant (`sub₀`) chains.
* `TerraciniLemma.AlexanderHirschowitzCubicGeneral` — **the
  Alexander–Hirschowitz theorem for cubics** (`alexanderHirschowitz_cubic`): at
  `r` general points, `σ_r(v₃(ℙⁿ))` is defective iff `(n, r) = (4, 7)`.
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
  `E` and projective subspaces of `ℙ(E)`.
* `TerraciniLemma.Defect` (§6) — packages the dimension count from
  `terraciniLemma` into the classical Alexander–Hirschowitz language of
  *expected dimension* and *defect*: `expectedDim S = min (finrank E)
  (∑ i, finrank (S i))`, `IsDefective S` holds when `finrank (⨆ i, S i) <
  expectedDim S`, and `defect S` is the resulting shortfall. Also proves monotonicity of non-defectivity in the number of points `r`:
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

@[expose] public section

/-!
## Summary of proof obligations

| Step | Status | Description |
|------|--------|-------------|
| `hasFDerivAt_combinedParam` | ✓ proved | Chain rule for combined parametrization |
| `range_combinedParam_eq_iSup` | ✓ proved | Im(dΦ) = ⨆ Im(Dfᵢ), both directions |
| `terraciniLemma_derivative` | ✓ proved | Core Terracini computation |
| `terraciniLemma` | ✓ proved | From `hdominant` + `hgeneric` (finrank count), for an abstract `T` |
| `range_combinedDerivative_le_span_tangentConeAt` | ✓ proved | `hdominant` for `T` = span of the tangent cone to `σᵣ(X̂)` at `∑ vᵢ` |
| `terraciniLemma_tangentCone` | ✓ proved | Terracini's Lemma for the tangent cone, from `hgeneric` alone |
| `span_tangentConeAt_secantVariety_eq_top` | ✓ proved | if the `T_{vᵢ}X̂` span `E`, so does the tangent cone to `σᵣ(X̂)` (no hypotheses) |
| `parabola_terracini` | ✓ proved | Worked example: plane conic, σ₂ = 𝕜² |
| `twistedCubic_terracini` | ✓ proved | Worked example: twisted cubic, combined tangent directions span a hyperplane ⊊ 𝕜³ |
| `segre_terracini` | ✓ proved | Worked example: Segre quadric P¹×P¹ ⊂ P³, σ₂ = 𝕜³ |
| `segre3_terracini` | ✓ proved | Worked example: Segre threefold P¹×P¹×P¹ ⊂ P⁷, σ₂ ⊊ 𝕜⁷ (defective) |
| `elliptic_terracini` | ✓ proved | Worked example: elliptic curve y²=x³+1 via the Implicit Function Theorem, σ₂ = 𝕜² |
| `terraciniLemma_projective` | ✓ proved | Projective form of `terraciniLemma`, via `Submodule.projectivization` |
| `finrank_iSup_le_expectedDim` | ✓ proved | `finrank (⨆ i, S i) ≤ expectedDim S`, always |
| `isDefective_veroneseGeneral_iff` | ✓ proved | `σᵣ(v₂(ℙⁿ)) ⊂ ℙ^N` is Alexander–Hirschowitz defective iff `2 ≤ r ≤ n` |
| `veroneseGeneral_sup_eq_top` | ✓ proved | `σ_{n+1}(v₂(ℙⁿ))` fills the ambient space (superabundant, non-defective) |
| `veroneseGeneral_span_tangentConeAt_eq_top` | ✓ proved | the tangent cone to `σ_{n+1}(v₂(ℙⁿ))` spans the ambient space (no hypotheses) |
| `veroneseGeneral_not_isDefective_of_succ_le` | ✓ proved | `σ_r(v₂(ℙⁿ))` is non-defective for every `r ≥ n+1` |
| `finrank_range_combinedDerivative_veroneseGeneral_le` | ✓ proved | for any linearly independent `p₀,…,p_{r-1}`, the combined tangent space of `v₂(ℙⁿ)` has dimension `≤ r(n+1) − binom(r,2)` |
| `isDefective_veroneseGeneral_of_linearIndependent` | ✓ proved | `σᵣ(v₂(ℙⁿ))` is defective at **any** linearly independent `r`-point family with `2 ≤ r ≤ n`, not just coordinate points |
| `finrank_ambient_veroneseDeg` | ✓ proved | ambient space of `v_d(ℙⁿ)` has dimension `binom(n+d,d)` |
| `finrank_tangentSpace_veroneseDegFamily` | ✓ proved | each coordinate-point tangent space of `v_d(ℙⁿ)` has dimension `n+1` |
| `finrank_iSup_veroneseDeg` | ✓ proved | for `d ≥ 3`, `r ≤ n+1` coordinate points, the combined tangent space has dimension exactly `r(n+1)` (direct sum, disjoint supports) |
| `veroneseDeg_not_isDefective` | ✓ proved | `σ_r(v_d(ℙⁿ))` is non-defective for `d ≥ 3`, `r ≤ n+1` coordinate points |
| `finrank_iSup_tangentSpace_le_of_singular` | ✓ proved | a nonzero degree-`d` form singular at the points bounds their tangent span by `binom(n+d,d) - 1` |
| `veroneseFormOf_injective` | ✓ proved | the Veronese variety is nondegenerate (a nonzero form is a nonzero function) |
| `finrank_iSup_tangentSpace_quartic_le` | ✓ proved | for any `r < binom(n+2,2)` points, the tangent spaces of `v₄(ℙⁿ)` lie in a hyperplane (dual to `Q²`) |
| `isDefective_quadric` | ✓ proved | `σ_r(v₂(ℙⁿ))` (degree-`d` model) is defective at any linearly independent points, `2 ≤ r ≤ n` |
| `ah437_isDefective_general` | ✓ proved | `σ₇(v₃(ℙ⁴))` is defective at general points (Hankel cubic of the rational normal quartic) |
| `HoldsGenerically.le_rank` | ✓ proved | a rank lower bound for a polynomial matrix at one point holds at general points |
| `HoldsGenerically.rank_le` | ✓ proved | a rank upper bound for a polynomial matrix at general points holds everywhere |
| `forGeneralPoints_not_isDefective` | ✓ proved | non-defectivity of `v_d(ℙⁿ)` at one nonzero configuration implies it at general points |
| `isDefective_of_forGeneralPoints` | ✓ proved | defectivity of `v_d(ℙⁿ)` at general points implies it at every nonzero configuration |
| `veroneseDeg_not_isDefective_general` | ✓ proved | `σ_r(v_d(ℙⁿ))` is non-defective at general points for `d ≥ 3`, `r ≤ n+1` |
| `alexanderHirschowitz_quadric` | ✓ proved | AH for quadrics: at `r ≥ 1` general points, `σ_r(v₂(ℙⁿ))` is defective iff `2 ≤ r ≤ n` |
| `alexanderHirschowitz_cubic` | ✓ proved | AH for cubics: at `r` general points, `σ_r(v₃(ℙⁿ))` is defective iff `(n, r) = (4, 7)` (Brambilla–Ottaviani induction + kernel-checked rank certificates) |
| `alexanderHirschowitz_exceptions_isDefective` | ✓ proved | every Alexander–Hirschowitz exceptional case is defective at every configuration of nonzero points |
| `finrank_finsetSup_eq_sum_of_not_isDefective_subabundant` | ✓ proved | subabundant non-defectivity for `r` points implies it for any sub-collection |
| `not_isDefective_of_finsetSup_eq_top` | ✓ proved | superabundant non-defectivity for `r` points implies it for any super-collection |
| `not_isDefective_of_sup_eq_top` | ✓ proved | two-point specialization of the above |
| `parabola_not_isDefective` | ✓ proved | `σ_r(v₂(ℙ¹))` is non-defective for every `r ≥ 2` |
| `segre_not_isDefective` | ✓ proved | `σ_r(ℙ¹×ℙ¹⊂ℙ³)` is non-defective for every `r ≥ 2` |
| `elliptic_not_isDefective` | ✓ proved | `σ_r(y²=x³+1)` is non-defective for every `r ≥ 2` |
| Generic smoothness | ⚠ hypothesis | `hgeneric` in `terraciniLemma_tangentCone` (and `hdominant` too in the abstract-`T` form `terraciniLemma`) |

There are no `sorry`s remaining in the project. The only gap is mathematical,
not formal: `hgeneric : finrank T ≤ finrank Im(dΦ)` (a dimension count, the
actual content of generic smoothness in characteristic zero) is a hypothesis,
rather than being derived from a general theory of dominant morphisms — which
is not yet in Mathlib. The other half, `hdominant : Im(dΦ) ≤ T`, is proved for
`T` the span of the tangent cone to σᵣ(X̂) (`terraciniLemma_tangentCone`); the
abstract-`T` form `terraciniLemma` still takes it as a hypothesis. The worked examples above discharge
both hypotheses concretely for the plane conic, the Segre quadric, the (defective) Segre threefold, and the
elliptic curve.
-/
