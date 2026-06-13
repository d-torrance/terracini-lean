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

The mathematics is organized into four files:

- [`TerraciniLemma.lean`](TerraciniLemma.lean) — top-level module: imports the
  files below and gives the overall statement, file organization, and a
  summary table of proof obligations.
- [`TerraciniLemma/Core.lean`](TerraciniLemma/Core.lean) — the general theory
  (§1–§6 below): the addition map, the Terracini derivative computation,
  secant varieties, smooth local parametrizations (`LocalParam`), and
  `terraciniLemma` itself.
- [`TerraciniLemma/Veronese.lean`](TerraciniLemma/Veronese.lean) — worked
  examples for Veronese varieties (currently the plane conic `v₂(ℙ¹) ⊂ ℙ²`).
- [`TerraciniLemma/Segre.lean`](TerraciniLemma/Segre.lean) — worked examples
  for Segre varieties: the non-defective Segre quadric `ℙ¹ × ℙ¹ ⊂ ℙ³` and the
  defective Segre threefold `ℙ¹ × ℙ¹ × ℙ¹ ⊂ ℙ⁷`.

The sections below (§1–§6) all live in `TerraciniLemma/Core.lean`.

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
Sketch of how the affine cone result descends to the projective statement via `Mathlib.LinearAlgebra.Projectivization`. Not yet formalized.

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
