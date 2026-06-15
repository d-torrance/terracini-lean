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
| **B** | $T_{\sum v_i}\,\hat\sigma_r(\hat X) = \operatorname{Im}(d\Phi)$ for general points | **Assumed** (generic smoothness) |

Part A is a straightforward chain-rule calculation. Part B requires the *generic smoothness theorem*: a dominant morphism of smooth irreducible varieties in characteristic zero has surjective differential at general points. This theorem is not yet in Mathlib, so it is split into two hypotheses:

- $\operatorname{Im}(d\Phi) \subseteq T$ (`hdominant`), which holds simply because $\Phi$ maps into $\hat\sigma_r(\hat X)$ — easy in any setting;
- $\dim T \le \dim \operatorname{Im}(d\Phi)$ (`hgeneric`), a dimension count (in practice obtained from a Jacobian-rank computation), which is the actual content of generic smoothness in characteristic zero.

Together these force $\operatorname{Im}(d\Phi) = T$ by a finite-dimensional submodule-equality lemma (`Submodule.eq_of_le_of_finrank_le`) — no containment in the "hard" direction needs to be assumed directly.

## File Overview

The mathematics is organized into six files:

- [`TerraciniLemma.lean`](TerraciniLemma.lean) — top-level module: imports the
  files below and gives the overall statement, file organization, and a
  summary table of proof obligations.
- [`TerraciniLemma/Core.lean`](TerraciniLemma/Core.lean) — the general theory
  (§1–§6 below): the addition map, the Terracini derivative computation,
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
- [`TerraciniLemma/VeroneseSurface.lean`](TerraciniLemma/VeroneseSurface.lean)
  — the quadric Veronese surface `v₂(ℙ²) ⊂ ℙ⁵`, worked directly in the
  *affine cone* model (ambient `𝕜⁶`, tangent spaces of dimension `3`). This
  is a genuinely **defective** case: the combined tangent space of two
  general points is a `5`-dimensional hyperplane `⊊ 𝕜⁶`, even though
  `min(6, 2·3) = 6` would be the non-defective expectation — the classical
  Alexander–Hirschowitz defect of `σ₂(v₂(ℙ²))` (the determinantal cubic
  hypersurface).
- [`TerraciniLemma/VeroneseGeneral.lean`](TerraciniLemma/VeroneseGeneral.lean)
  — the general quadric Veronese variety `v₂(ℙⁿ) ⊂ ℙ^N`
  (`N = binom(n+2,2) - 1`), worked in the affine cone model (ambient
  `Sym2 (Fin (n+1)) → 𝕜`, of dimension `binom(n+2,2)`, representing symmetric
  `(n+1)×(n+1)` matrices) for arbitrary `n` and arbitrary `r` general points
  (`1 ≤ r ≤ n+1`). This subsumes `TerraciniLemma/VeroneseSurface.lean`'s
  `n = 2, r = 2` instance. The main theorem
  `isDefective_veroneseGeneral_iff` shows `σᵣ(v₂(ℙⁿ))` is
  Alexander–Hirschowitz defective **iff `2 ≤ r ≤ n`**; `veroneseGeneral_sup_eq_top`
  and `veroneseGeneral_not_isDefective_of_succ_le` show the boundary case
  `r = n+1` fills the ambient space and every `r ≥ n+1` is non-defective.
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
  and projective subspaces of `ℙ(E)`. Instantiated for the quadric Veronese
  surface, showing `ℙ(σ₂(v₂(ℙ²)))` is a proper hyperplane `ℙ⁴ ⊊ ℙ⁵`.
- [`TerraciniLemma/Defect.lean`](TerraciniLemma/Defect.lean) (§7) — packages
  the dimension count from `terraciniLemma` into the classical
  Alexander–Hirschowitz language of *expected dimension* and *defect*:
  `expectedDim S = min(N, ∑ᵢ dim Tᵢ)`, `IsDefective S ↔ dim ⨆ᵢ Tᵢ <
  expectedDim S`, and `defect S` is the resulting shortfall. Instantiated for
  the quadric Veronese surface (cone model): the classical defect of
  `σ₂(v₂(ℙ²))` is exactly `1`. Also proves monotonicity of non-defectivity in
  the number of points `r`, in both the subabundant and superabundant
  regimes.

The sections below (§1–§7) live in `TerraciniLemma/Core.lean` and
`TerraciniLemma/Defect.lean`.

### §1 — The addition map
```
additionMap r : (Fin r → E) →L[𝕜] E
```
The map $v \mapsto \sum_i v_i$ is continuous and $\mathbb{k}$-linear, hence its own Fréchet derivative everywhere.

### §2 — The Terracini computation
```
hasFDerivAt_combinedParam   -- dΦ = ∑ Dfᵢ ∘ πᵢ  (chain rule)
range_combinedParam_eq_iSup -- Im(dΦ) = ⨆ Im(Dfᵢ)  (submodule algebra)
```
The core result: the image of the derivative of $\Phi$ is exactly the sum of the individual tangent spaces. Both directions of the equality are fully proved.

### §3 — Secant varieties
```
secantSet r X      -- { v₁ + ⋯ + vᵣ | vᵢ ∈ X }
secantVariety r X  -- closure of the above
```
Basic lemmas: `secantVariety 1 X = X` (for closed `X`), monotonicity in `r`.

### §4 — Smooth parametrizations
```
structure LocalParam (X : Set E) (x : E) where
  basePoint : 𝔸
  chart     : 𝔸 → E
  chart_eval : chart basePoint = x
  tangent   : 𝔸 →L[𝕜] E
  hasFDerivAt : HasFDerivAt chart tangent basePoint
```
Models a smooth local parametrization of `X` at a point `x`, together with its derivative (= embedded tangent space generator).

### §5 — Terracini's Lemma
```
terraciniLemma          -- T = ⨆ tangentSpace (param i),  given hgeneric + hdominant
terraciniLemma_derivative  -- HasFDerivAt of combined parametrization
```
The main theorem (in finite dimension) takes two hypotheses that together encode generic smoothness:
- `hdominant : Im(dΦ) ≤ T` — the image of $d\Phi$ lands in the tangent space (because $\Phi$ maps into $\hat\sigma_r(\hat X)$);
- `hgeneric : finrank T ≤ finrank Im(dΦ)` — a dimension count (characteristic-zero, Jacobian-rank input).

From these, `Submodule.eq_of_le_of_finrank_le` gives $T = \operatorname{Im}(d\Phi)$, and Part A then gives $T = \bigsqcup_i T_{v_i}\hat X$.

### §6 — The projective formulation
The affine cone result descends to the projective statement
`T_{[p]} σᵣ(X) = ⟨T_{[p₁]}X, …, T_{[pᵣ]}X⟩` in `ℙ(E)` via the order isomorphism
`Submodule.projectivization : Submodule 𝕜 E ≃o Projectivization.Subspace 𝕜 E`
from `Mathlib.LinearAlgebra.Projectivization`. This is formalized in
[`TerraciniLemma/Projective.lean`](TerraciniLemma/Projective.lean), with the
quadric Veronese surface as a worked example: `ℙ(σ₂(v₂(ℙ²)))` is a proper
hyperplane `ℙ⁴ ⊊ ℙ⁵`.

### §7 — Expected dimension and defect
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
**cone** over `X`, as for the quadric Veronese surface: `veroneseSurface_isDefective`
and `defect_veroneseSurface` show `σ₂(v₂(ℙ²))` has defect exactly `1`, matching
the classical result. (For the affine-**chart** examples — rational normal
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
Assumed as explicit hypotheses `hgeneric` and `hdominant` in `terraciniLemma`. Formalizing this would require either:
- A general generic smoothness theorem in Mathlib (not yet present), or
- A case-by-case argument for specific varieties of interest.

(The range theorem `range_combinedParam_eq_iSup` is fully proved in both directions: the ≥ direction follows by taking, for $y = Df_i(a) \in \operatorname{Im}(Df_i)$, the input $u = \text{Pi.single } i\ a$, whose other coordinates vanish so that $d\Phi(u) = Df_i(a) = y$.)

## Building

```bash
# Install the Lean toolchain (elan downloads it automatically if needed)
elan toolchain install leanprover/lean4:v4.30.0-rc2

# Fetch prebuilt Mathlib compiled objects (~1 GB)
lake exe cache get

# Check the file
lake build TerraciniLemma
```

The project uses Mathlib at tag `v4.30.0-rc2`. The `lake exe cache get` step is strongly recommended — building Mathlib from source takes several hours.

## References

- A. Terracini, *Sulle $v_k$ per cui la varietà degli $S_h$ $(h+1)$-secanti ha dimensione minore dell'ordinario*, Rend. Circ. Mat. Palermo **31** (1911), 392–396.
- J. M. Landsberg, *Geometry and Complexity Theory*, Cambridge University Press, 2017. §5.3.
- L. Chiantini and C. Ciliberto, *Weakly defective varieties*, Trans. Amer. Math. Soc. **354** (2002), 151–178.
- L. Ein and R. Lazarsfeld, *Singularities of theta divisors and the birational geometry of irregular varieties*, J. Amer. Math. Soc. **10** (1997), 243–258.
