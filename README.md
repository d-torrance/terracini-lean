# Terracini's Lemma in Lean 4

A formalization of Terracini's Lemma in [Lean 4](https://leanprover.github.io/) using [Mathlib4](https://leanprover-community.github.io/mathlib4_docs/).

## The Theorem

**Terracini's Lemma** (1911) is a fundamental result in the theory of secant varieties. Given an irreducible projective variety $X \subset \mathbb{P}^N$, its *$r$-th secant variety* $\sigma_r(X)$ is the Zariski closure of the union of all $(r-1)$-planes spanned by $r$ points of $X$. Terracini's Lemma computes the tangent space to $\sigma_r(X)$ at a general point:

> **Theorem.** For general points $p_1, \ldots, p_r \in X$ and a general point $p \in \langle p_1, \ldots, p_r \rangle$,
> $$T_p\,\sigma_r(X) = \langle T_{p_1}X,\, \ldots,\, T_{p_r}X \rangle.$$

Here $T_{p_i}X$ denotes the embedded tangent space to $X$ at $p_i$ inside $\mathbb{P}^N$, and the right-hand side is their linear span.

This lemma is the primary tool for computing dimensions of secant varieties. For example, the expected dimension of $\sigma_r(X)$ is $\min(N, r(\dim X + 1) - 1)$; a variety is *defective* when $\sigma_r(X)$ falls short of this, and Terracini's Lemma localizes that deficiency to the tangent geometry.

## Strategy

We work with the **affine cone** $\hat X \subseteq V$ over $\mathbb{P}(V)$. The $r$-th secant variety of $\hat X$ is

$$\hat\sigma_r(\hat X) = \overline{\{v_1 + \cdots + v_r \mid v_i \in \hat X\}}.$$

The key player is the **combined parametrization**

$$\Phi : \mathbb{A}^r \to V, \qquad \Phi(u_1,\ldots,u_r) = \sum_{i=1}^r f_i(u_i),$$

where each $f_i : \mathbb{A} \to V$ is a local smooth parametrization of $\hat X$ near $v_i = f_i(u_i^0)$.

The proof has two parts of very different character:

| Part | Content | Status |
|------|---------|--------|
| **A** | $d\Phi_{u^0} = \sum_i Df_i \circ \pi_i$, so $\operatorname{Im}(d\Phi) = T_{v_1}\hat X + \cdots + T_{v_r}\hat X$ | **Proved** (chain rule) |
| **B** | $T_{\sum v_i}\,\hat\sigma_r(\hat X) = \operatorname{Im}(d\Phi)$ for general points | $\subseteq$ **proved** (tangent cone); $\dim$ count **assumed** (generic smoothness) |

Part A is a straightforward chain-rule calculation. Part B requires the *generic smoothness theorem*: a dominant morphism of smooth irreducible varieties in characteristic zero has surjective differential at general points. This theorem is not yet in Mathlib, so it is split into two hypotheses:

- $\operatorname{Im}(d\Phi) \subseteq T$ (`hdominant`), which holds simply because $\Phi$ maps into $\hat\sigma_r(\hat X)$. This is **proved** when $T$ is the span of Mathlib's tangent cone `tangentConeAt 𝕜 (secantVariety r X) (∑ i, v i)` (`range_combinedDerivative_le_span_tangentConeAt`), because each chart lands in $\hat X$ near its base point;
- $\dim T \le \dim \operatorname{Im}(d\Phi)$ (`hgeneric`), a dimension count (in practice obtained from a Jacobian-rank computation), which is the actual content of generic smoothness in characteristic zero.

Together these force $\operatorname{Im}(d\Phi) = T$ by a finite-dimensional submodule-equality lemma (`Submodule.eq_of_le_of_finrank_le`) — no containment in the "hard" direction needs to be assumed directly.

## File Overview

The mathematics is organized into the following files:

- [`TerraciniLemma.lean`](TerraciniLemma.lean) — top-level module: imports the
  files below and gives the overall statement, file organization, and a
  summary table of proof obligations.
- [`TerraciniLemma/Core.lean`](TerraciniLemma/Core.lean) — the general theory
  (§1–§5 below): the Terracini derivative computation,
  secant varieties, smooth local parametrizations (`LocalParam`), and
  `terraciniLemma` itself.
- [`TerraciniLemma/PolynomialCalculus.lean`](TerraciniLemma/PolynomialCalculus.lean)
  — a "middle ground" between hand-rolled calculus and the Implicit Function
  Theorem: a generic bridge from `MvPolynomial.pderiv` to `HasFDerivAt` and
  `ContDiff`, used by the rational normal curve and elliptic curve examples
  to get the calculus of polynomial maps for free.
- [`TerraciniLemma/RationalNormalCurves.lean`](TerraciniLemma/RationalNormalCurves.lean)
  — worked examples for rational normal curves: the plane conic `v₂(ℙ¹) ⊂ ℙ²`
  (σ₂ fills the plane) and the twisted cubic `v₃(ℙ¹) ⊂ ℙ³` (the two tangent
  directions span a hyperplane, the expected outcome since `2 · dim X < dim ℙ³`).
- [`TerraciniLemma/VeroneseGeneral.lean`](TerraciniLemma/VeroneseGeneral.lean)
  — the general quadric Veronese variety `v₂(ℙⁿ) ⊂ ℙ^N`
  (`N = binom(n+2,2) - 1`), worked in the affine cone model (ambient
  `Sym2 (Fin (n+1)) → 𝕜`, of dimension `binom(n+2,2)`, representing symmetric
  `(n+1)×(n+1)` matrices) for arbitrary `n` and arbitrary `r` general points
  (`1 ≤ r ≤ n+1`). The main theorem
  `isDefective_veroneseGeneral_iff` shows `σᵣ(v₂(ℙⁿ))` is
  Alexander–Hirschowitz defective **iff `2 ≤ r ≤ n`**; `veroneseGeneral_sup_eq_top`
  and `veroneseGeneral_not_isDefective_of_succ_le` show the boundary case
  `r = n+1` fills the ambient space and every `r ≥ n+1` is non-defective.
  `isDefective_veroneseGeneral_of_linearIndependent` extends the defective
  direction from coordinate points to *any* `r` linearly independent points: the
  `binom(r,2)` velocity families `wᵏˡ` (`p_l` in slot `k`, `-p_k` in slot `l`)
  are independent elements of the kernel of `dΦ`.
- [`TerraciniLemma/VeroneseDegree.lean`](TerraciniLemma/VeroneseDegree.lean)
  — the degree-`d` Veronese variety `v_d(ℙⁿ) ⊂ ℙ^N`
  (`N = binom(n+d,d) - 1`), worked in the affine cone model (ambient
  `Sym (Fin (n+1)) d → 𝕜`, of dimension `binom(n+d,d)`, representing degree-`d`
  forms in `n+1` variables) for general `d ≥ 1`, generalizing
  `TerraciniLemma/VeroneseGeneral.lean`'s `d = 2`-only `Sym2 (Fin (n+1))`
  indexing. The main theorem `veroneseDeg_not_isDefective` shows that for
  `d ≥ 3` and `r ≤ n+1` coordinate points, `σ_r(v_d(ℙⁿ))` is **not**
  Alexander–Hirschowitz defective: the `n+1`-element tangent-space supports at
  each of the `r` points are pairwise *disjoint* (in contrast to `d = 2`,
  where they pairwise overlap in exactly one element), so the combined tangent
  space is a direct sum of dimension `r(n+1)`. The tangent span is the column
  space of a matrix of polynomials in the points' coordinates, so by
  semicontinuity this lifts to general points
  (`veroneseDeg_not_isDefective_general`). In the other direction, defectivity
  at general points implies defectivity at every configuration of nonzero
  points (`isDefective_of_forGeneralPoints`).
- [`TerraciniLemma/Semicontinuity.lean`](TerraciniLemma/Semicontinuity.lean)
  — "for general points" (`HoldsGenerically`, `ForGeneralPoints`: off the zero
  locus of a nonzero polynomial in the coordinates) and the semicontinuity of
  rank for matrices of polynomials. A rank lower bound at one point holds at
  general points (`HoldsGenerically.le_rank`), and a rank upper bound at general
  points holds everywhere (`HoldsGenerically.rank_le`). The key linear algebra
  is `Matrix.le_rank_iff_exists_submatrix_det_ne_zero`: over a field,
  `k ≤ rank A` iff some `k × k` minor of `A` is nonzero.
- [`TerraciniLemma/VeroneseForms.lean`](TerraciniLemma/VeroneseForms.lean) —
  degree-`d` forms on `𝕜^{n+1}` as pullbacks `χ ∘ v_d` of functionals on the
  ambient space, and the **singular-form bound**
  `finrank_iSup_tangentSpace_le_of_singular`. If a nonzero form is singular at
  the points, all their tangent spaces lie in the hyperplane dual to it.
- [`TerraciniLemma/AlexanderHirschowitzCubic.lean`](TerraciniLemma/AlexanderHirschowitzCubic.lean)
  — the `(4,3,7)` case at **general** points, following Brambilla–Ottaviani.
  An explicit change of coordinates `ahL p = Vᵀ·diag(w)·diag(U)⁻¹·adj(M)`
  (Vandermonde matrix of the nodes, Lagrange weights) sends seven general
  points of `ℙ⁴` onto the moment curve and its point at infinity. The Hankel
  cubic, whose zero set is the secant variety of the curve, is singular there.
  "General" is witnessed by an explicit nonzero polynomial `ahGenericPoly`.
- [`TerraciniLemma/AlexanderHirschowitz.lean`](TerraciniLemma/AlexanderHirschowitz.lean)
  — `alexanderHirschowitz_exceptions_isDefective`: **every**
  Alexander–Hirschowitz exceptional case is defective at every configuration
  of nonzero points (by semicontinuity from general points).
  - Quartics `(2,4,5)`, `(3,4,9)`, `(4,4,14)`: the square of a quadric through
    the `r < binom(n+2,2)` points is a singular quartic. This works for *any*
    nonzero points.
  - Quadrics: transferred from `VeroneseGeneral` along `Sym2 α ≃ Sym α 2`.
  - `(4,3,7)`: proved in the file above.

  For quadrics the full theorem is proved: `alexanderHirschowitz_quadric`
  says that at `r ≥ 1` general points, `σ_r(v₂(ℙⁿ))` is defective iff
  `2 ≤ r ≤ n`. For cubics the full theorem is proved too
  (`alexanderHirschowitz_cubic`, below). For `d ≥ 4`, non-defectivity is
  proved only for `r ≤ n+1`.
- [`TerraciniLemma/RankCertificate.lean`](TerraciniLemma/RankCertificate.lean)
  — rank certificates: row and column indices of a `k × k` minor of an
  integer matrix `A`, a prime `p` and a matrix `B` with
  `B · A[rows, cols] ≡ 1 (mod p)`. `le_rank_of_check` proves `k ≤ rank A` over
  any field of characteristic zero; `check` is computable, so a certificate is
  verified by `decide +kernel`.
- [`TerraciniLemma/DifferentialHorace.lean`](TerraciniLemma/DifferentialHorace.lean)
  — the differential Horace lemma in linear-algebra form
  (`differentialHorace`): if vectors `b_j(t)` move along a polynomial path,
  then for general `t`, `dim (W + span b(t)) ≥ dim (W + span b(0) + D)`, where
  `D = {∑ c_j b_j'(0) : ∑ c_j b_j(0) ∈ W}`. No schemes or limits are needed;
  the limit is lower semicontinuity of rank in `t`.
- [`TerraciniLemma/VeroneseLinear.lean`](TerraciniLemma/VeroneseLinear.lean)
  — linear changes of coordinates on the Veronese cone: they map tangent
  spaces to tangent spaces, so up to `n` points can be moved into a hyperplane
  without lowering the dimension of their tangent span.
- [`TerraciniLemma/AHStep.lean`](TerraciniLemma/AHStep.lean) — **the
  inductive step of the Alexander–Hirschowitz theorem** (Brambilla–Ottaviani,
  Theorem 6.4), `AHHolds.step`: `AH_{n,d+2}(u)`, `AH_{n+1,d+1}(k-u)` and
  `AH_{n+1,d}(k-u-ε)` give `AH_{n+1,d+2}(k)`. The proof splits along the
  hyperplane `x₀ = 0` with the residual map `resid` (`G ↦ x₀ G` on
  conditions), and `horace_step` combines the split with the differential
  Horace lemma; no case split on `k` is needed.
- The cubic induction —
  [`CubicLattice`](TerraciniLemma/CubicLattice.lean),
  [`CubicInduction`](TerraciniLemma/CubicInduction.lean),
  [`CubicBaseCases`](TerraciniLemma/CubicBaseCases.lean),
  [`CubicInductionMain`](TerraciniLemma/CubicInductionMain.lean): the
  Brambilla–Ottaviani three-level induction, in the linear-algebra form of
  Torrance–Vannieuwenhoven (Trans. AMS **374** (2021), Example 4.9). Points of
  `ℙ^{t+4}` are specialized to a lattice of coordinate subspaces `U₀, U₁, U₂`.
  A specialization step (Pascal's rule plus semicontinuity) and a trace step
  (Grassmann's formula along the embedding missing a block) give the
  superabundant chain (`super₀`: `⌈N/(n+1)⌉` points fill) and the subabundant
  chain (`sub₀`: for `t ≡ 1 mod 3`, `⌊N/(n+1)⌋` points are independent).
- [`TerraciniLemma/CubicCertificates/`](TerraciniLemma/CubicCertificates) —
  the base cases: integer points and rank certificates, **generated** by
  `lake exe certificates` (Macaulay2 via
  [Macaulean](https://github.com/Macaulean/Macaulean), with the extension in
  [`m2/terracini.m2`](m2/terracini.m2)) and checked by the kernel. Building
  the project does not need Macaulay2. Kernel checks are memory-hungry, so
  each certificate is checked in chunks of rows (one declaration each), and
  each file imports the previous one so that Lake checks them one at a time;
  the peak is a few gigabytes.
- [`TerraciniLemma/AlexanderHirschowitzCubicGeneral.lean`](TerraciniLemma/AlexanderHirschowitzCubicGeneral.lean)
  — **the Alexander–Hirschowitz theorem for cubics**,
  `alexanderHirschowitz_cubic`: at `r` general points, `σ_r(v₃(ℙⁿ))` is
  defective iff `(n, r) = (4, 7)`. For `n ≥ 5` it uses the two chains; for
  `n ≤ 4` it uses certificates directly.
- [`TerraciniLemma/Segre.lean`](TerraciniLemma/Segre.lean) — worked examples
  for Segre varieties: the non-defective Segre quadric `ℙ¹ × ℙ¹ ⊂ ℙ³` and the
  defective Segre threefold `ℙ¹ × ℙ¹ × ℙ¹ ⊂ ℙ⁷`.
- [`TerraciniLemma/EllipticCurve.lean`](TerraciniLemma/EllipticCurve.lean) —
  a worked example for the elliptic curve `y² = x³ + 1`. Unlike the
  RationalNormalCurves/Segre examples, this curve has no global rational
  parametrization, so the local charts at each point are instead built from
  Mathlib's Implicit Function Theorem.
- [`TerraciniLemma/Projective.lean`](TerraciniLemma/Projective.lean) —
  descends `terraciniLemma` to the projective statement
  `T_{[p]} σᵣ(X) = ⟨T_{[p₁]}X, …, T_{[pᵣ]}X⟩` in `ℙ(E)`, via the order
  isomorphism `Submodule.projectivization` between linear subspaces of `E`
  and projective subspaces of `ℙ(E)`.
- [`TerraciniLemma/Defect.lean`](TerraciniLemma/Defect.lean) (§6) — packages
  the dimension count from `terraciniLemma` into the classical
  Alexander–Hirschowitz language of *expected dimension* and *defect*:
  `expectedDim S = min(N, ∑ᵢ dim Tᵢ)`, `IsDefective S ↔ dim ⨆ᵢ Tᵢ <
  expectedDim S`, and `defect S` is the resulting shortfall. Also proves monotonicity of non-defectivity in
  the number of points `r`, in both the subabundant and superabundant
  regimes.

The sections below (§1–§6) live in `TerraciniLemma/Core.lean` and
`TerraciniLemma/Defect.lean`.

### §1 — The Terracini computation
```
hasFDerivAt_combinedParam   -- dΦ = ∑ Dfᵢ ∘ πᵢ  (chain rule)
range_combinedParam_eq_iSup -- Im(dΦ) = ⨆ Im(Dfᵢ)  (submodule algebra)
```
The core result: the image of the derivative of $\Phi$ is exactly the sum of the individual tangent spaces. Both directions of the equality are fully proved.

### §2 — Secant varieties
```
secantSet r X      -- { v₁ + ⋯ + vᵣ | vᵢ ∈ X }
secantVariety r X  -- closure of the above
```
Basic lemmas: `secantVariety 1 X = X` (for closed `X`), monotonicity in `r`.

### §3 — Smooth parametrizations
```
structure LocalParam (X : Set E) (x : E) where
  basePoint : 𝔸
  chart     : 𝔸 → E
  chart_eval : chart basePoint = x
  chart_mem : ∀ᶠ u in 𝓝 basePoint, chart u ∈ X
  tangent   : 𝔸 →L[𝕜] E
  hasFDerivAt : HasFDerivAt chart tangent basePoint
```
Models a smooth local parametrization of `X` at a point `x` (landing in `X` near the base point), together with its derivative (= embedded tangent space generator).

### §4 — Terracini's Lemma
```
terraciniLemma             -- T = ⨆ tangentSpace (param i),  given hgeneric + hdominant
terraciniLemma_tangentCone -- same for T = span (tangent cone of σᵣ(X̂)),  given only hgeneric
terraciniLemma_derivative  -- HasFDerivAt of combined parametrization
span_tangentConeAt_secantVariety_eq_top  -- if the T_{vᵢ}X̂ span E, so does the tangent cone
```
The main theorem (in finite dimension) takes two hypotheses that together encode generic smoothness:
- `hdominant : Im(dΦ) ≤ T` — the image of $d\Phi$ lands in the tangent space (because $\Phi$ maps into $\hat\sigma_r(\hat X)$);
- `hgeneric : finrank T ≤ finrank Im(dΦ)` — a dimension count (characteristic-zero, Jacobian-rank input).

From these, `Submodule.eq_of_le_of_finrank_le` gives $T = \operatorname{Im}(d\Phi)$, and Part A then gives $T = \bigsqcup_i T_{v_i}\hat X$.

`terraciniLemma_tangentCone` fixes $T$ to be the span of the tangent cone to $\hat\sigma_r(\hat X)$ at $\sum v_i$ and proves `hdominant`, leaving only `hgeneric`. When the tangent spaces already span $E$, `hgeneric` is automatic, so `span_tangentConeAt_secantVariety_eq_top` holds with no hypotheses. For example, `veroneseGeneral_span_tangentConeAt_eq_top` shows that $\sigma_{n+1}(v_2(\mathbb{P}^n))$ fills its ambient space.

### §5 — The projective formulation
The affine cone result descends to the projective statement
`T_{[p]} σᵣ(X) = ⟨T_{[p₁]}X, …, T_{[pᵣ]}X⟩` in `ℙ(E)` via the order isomorphism
`Submodule.projectivization : Submodule 𝕜 E ≃o Projectivization.Subspace 𝕜 E`
from `Mathlib.LinearAlgebra.Projectivization`. This is formalized in
[`TerraciniLemma/Projective.lean`](TerraciniLemma/Projective.lean).

### §6 — Expected dimension and defect
```
expectedDim S          -- min (finrank E) (∑ i, finrank (S i))
IsDefective S          -- finrank (⨆ i, S i) < expectedDim S
defect S                -- expectedDim S - finrank (⨆ i, S i)
```
This packages the dimension count from `terraciniLemma` into the classical
**Alexander–Hirschowitz** language: `expectedDim S` is the naive
("non-defective") prediction for `finrank (⨆ i, S i)`, always an upper bound
(`finrank_iSup_le_expectedDim`), and `IsDefective S ↔ 0 < defect S`. This is
formalized in [`TerraciniLemma/Defect.lean`](TerraciniLemma/Defect.lean).

`IsDefective`/`defect` have their *intended* meaning — genuine
Alexander–Hirschowitz defectivity of `X = ℙ(X̂)` — only when `E` is the affine
**cone** over `X`, as for the Veronese varieties. (For the affine-**chart** examples — rational normal
curves, Segre varieties, the elliptic curve — tangent spaces have dimension
`dim X` rather than `dim X + 1`, so `expectedDim` there is a systematically
different quantity; `IsDefective`/`defect` are deliberately not instantiated
for those.)

**Monotonicity of non-defectivity in `r`.** Two general lemmas about a finite
family `S : ι → Submodule 𝕜 E`:

- `finrank_finsetSup_eq_sum_of_not_isDefective_subabundant`: if `S` is
  non-defective and *subabundant* (`∑ i, finrank (S i) ≤ finrank E`), then for
  every `T : Finset ι`, the sub-family `{S i | i ∈ T}` is non-defective too —
  its combined span already has dimension `∑ i ∈ T, finrank (S i)`.
  Geometrically: if `σ_r(X)` is non-defective and subabundant, then `σ_s(X)`
  is non-defective for every `s < r`.
- `not_isDefective_of_finsetSup_eq_top`: if the combined span of some
  sub-family `{S i | i ∈ T}` already fills `E`, then `S` itself is
  non-defective. Geometrically: if `σ_r(X)` is non-defective and
  superabundant (fills the ambient space), then `σ_s(X)` is non-defective for
  every `s > r`.

**Extending `σ₂` to `σ_r`.** `parabola_terracini`, `segre_terracini`, and
`elliptic_terracini` each show `σ₂ = E` (the superabundant case). The
two-point specialization `not_isDefective_of_sup_eq_top` (via the helper
`iSup_fin_two : ⨆ i : Fin 2, f i = f 0 ⊔ f 1`) turns each of these into a
statement about *every* `σ_r`, `r ≥ 2`:
`parabola_not_isDefective`, `segre_not_isDefective`, and
`elliptic_not_isDefective` show that any family of tangent spaces containing
those two tangent spaces among its members is non-defective, regardless of
the remaining members.

## Sorry Inventory

There is exactly one gap in the formalization.

**Generic smoothness.**  
Assumed as the explicit hypothesis `hgeneric` in `terraciniLemma_tangentCone` (the abstract-`T` form `terraciniLemma` also takes `hdominant`, which is proved for the tangent cone). Formalizing this would require either:
- A general generic smoothness theorem in Mathlib (not yet present), or
- A case-by-case argument for specific varieties of interest.

(The range theorem `range_combinedParam_eq_iSup` is fully proved in both directions: the ≥ direction follows by taking, for $y = Df_i(a) \in \operatorname{Im}(Df_i)$, the input $u = \text{Pi.single } i\ a$, whose other coordinates vanish so that $d\Phi(u) = Df_i(a) = y$.)

## Building

```bash
# Install the Lean toolchain (elan downloads it automatically if needed)
elan toolchain install leanprover/lean4:v4.35.0

# Fetch prebuilt Mathlib compiled objects (~1 GB)
lake exe cache get

# Check the file
lake build TerraciniLemma
```

The project uses Mathlib at tag `v4.35.0`. The `lake exe cache get` step is strongly recommended — building Mathlib from source takes several hours.

## References

- A. Terracini, *Sulle $v_k$ per cui la varietà degli $S_h$ $(h+1)$-secanti ha dimensione minore dell'ordinario*, Rend. Circ. Mat. Palermo **31** (1911), 392–396.
- J. M. Landsberg, *Geometry and Complexity Theory*, Cambridge University Press, 2017. §5.3.
- L. Chiantini and C. Ciliberto, *Weakly defective varieties*, Trans. Amer. Math. Soc. **354** (2002), 151–178.
- L. Ein and R. Lazarsfeld, *Singularities of theta divisors and the birational geometry of irregular varieties*, J. Amer. Math. Soc. **10** (1997), 243–258.
