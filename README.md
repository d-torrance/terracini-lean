# terracini-lean

A Lean 4 / Mathlib formalization of the **Alexander–Hirschowitz theorem**, the
classification of defective secant varieties of Veronese varieties, together
with **Terracini's Lemma**, which turns the dimension of a secant variety into
the dimension of a span of tangent spaces.

The Alexander–Hirschowitz theorem is proved in full, in every degree and
dimension. The proof follows Brambilla–Ottaviani, with:

- the differential Horace method recast as a statement about spans of moving
  vectors, so that no schemes or limits are needed;
- the finitely many base cases certified by integer rank certificates that are
  computed by Macaulay2 (through [Macaulean](https://github.com/Macaulean/Macaulean))
  and checked by the Lean kernel.

## The main theorem

```lean
theorem alexanderHirschowitz (n d r : ℕ) (hd : 1 ≤ d) :
    ForGeneralPoints (𝕜 := 𝕜) r (n + 1) (fun p =>
      IsDefective (fun k => (veroneseDegParam n d (p k)).tangentSpace) ↔
        IsAHException n d r)
```

Here `𝕜` is any nontrivially normed field of characteristic zero (for example
`ℝ` or `ℂ`). In words: for `r` general points of `𝕜^{n+1}`, the tangent spaces
to the cone over the Veronese variety `v_d(ℙⁿ)` at those points span a space of
the expected dimension `min(binom(n+d, d), r(n+1))` unless `(n, d, r)` is one of
the exceptions

- `d = 2` and `2 ≤ r ≤ n` (quadrics),
- `(n, d, r) = (2, 4, 5), (3, 4, 9), (4, 4, 14)` (quartics),
- `(n, d, r) = (4, 3, 7)` (cubics),

and in the exceptions the span is smaller.

- **Ambient space.** The ambient space of `v_d(ℙⁿ)` is
  `Sym (Fin (n+1)) d → 𝕜`, one coordinate per monomial of degree `d`.
- **The points.** `veroneseDegParam n d p` is the cone parametrization at `p`,
  and its `tangentSpace` is the image of the derivative.
- **`IsDefective`** says that the span falls short of the expected dimension
  (`TerraciniLemma.Defect`).
- **`ForGeneralPoints r m P`** says that `P` holds for every `r`-tuple of points
  of `𝕜^m` off the zero locus of some nonzero polynomial in their coordinates
  (`TerraciniLemma.Semicontinuity`).

By Terracini's Lemma, this span is the tangent space to the secant variety
`σ_r(v_d(ℙⁿ))` at a general point. So the theorem says that `σ_r(v_d(ℙⁿ))` has
the expected dimension exactly outside the exceptions. Equivalently, `r` general
double points impose independent conditions on forms of degree `d`. In this
project's coordinates a tangent vector at `p` *is* such a condition,
`F ↦ ∂_v F(p)`.

The exceptions are also proved defective at *every* configuration of nonzero
points, not just general ones (`alexanderHirschowitz_exceptions_isDefective`).

`#print axioms alexanderHirschowitz` reports only `propext`,
`Classical.choice` and `Quot.sound`. There are no `sorry`s in the project.

## How the proof goes

**The exceptions** (`AlexanderHirschowitz`, `AlexanderHirschowitzCubic`,
`VeroneseForms`, `VeroneseGeneral`). The singular-form bound: if a nonzero form
of degree `d` is singular at the points, the tangent spaces lie in a
hyperplane.

- *Quartics:* the square of a quadric through the points is such a form.
- *Quadrics:* the tangent spaces at linearly independent points are computed
  directly.
- *`(4, 3, 7)`:* seven general points of `ℙ⁴` lie on a rational normal quartic,
  whose secant variety is a cubic hypersurface (a Hankel determinant) singular
  along it. An explicit change of coordinates sends the curve to the moment
  curve.

**Semicontinuity** (`Semicontinuity`, `VeroneseDegree`). Ranks of matrices of
polynomials are lower semicontinuous, so a lower bound at one explicit
configuration holds at general points. Upper bounds at general points hold
everywhere.

**Cubics** (`CubicLattice`, `CubicInduction`, `CubicBaseCases`,
`CubicInductionMain`, `AlexanderHirschowitzCubicGeneral`). This is the
Brambilla–Ottaviani three-level induction, in the linear-algebra form of
Torrance–Vannieuwenhoven (Example 4.9).

- Points are specialized to a lattice of coordinate subspaces.
- A specialization step (Pascal's rule) and a trace step (Grassmann's formula
  along an embedding that skips a block of coordinates) give two chains of lower
  bounds.
- The chains start from base cases proved by rank certificates
  (`CubicCertificates/`). Projective spaces of dimension `n ≤ 4` are certified
  directly.

**Degree `d ≥ 4`.** These cases are proved by induction on `(n, d)`, starting
from `ℙ⁰`, `ℙ¹`, quadrics and cubics.

- *The differential Horace lemma* (`DifferentialHorace`). For vectors
  `b_j(t)` moving along a polynomial path, consider the first-order terms of the
  relations between the `b_j(0)` and a fixed subspace `W`:
  `D = {∑ c_j b_j'(0) : ∑ c_j b_j(0) ∈ W}`. Then for general `t`,
  `dim (W + span b(t)) ≥ dim (W + span b(0) + D)`. The limit is taken by
  semicontinuity of rank in `t`. This replaces the curvilinear lemma and the
  limits of curvilinear schemes in Chandler's version of the method.
- *The Horace step* (`AHStep`). Split the ambient space along the hyperplane
  `H = {x₀ = 0}` with the residual map (`φ ↦ φ(x₀ · _)`, which divides a form
  by `x₀`). Then move `ε` points of `H` off it along `γᵢ + t e₀`.
  - `horace_step`: for general `t`, the span is at least the trace on `H` plus
    the residual one degree lower.
  - `AHHolds.horace` and `AHHolds.step`: Brambilla–Ottaviani's Theorems 4.1
    and 6.4. `AH_{n,d+2}(u)`, `AH_{n+1,d+1}(k-u)` and `AH_{n+1,d}(k-u-ε)` give
    `AH_{n+1,d+2}(k)`, with no case split on `k`.
  - Moving points onto `H` uses that linear changes of coordinates act on the
    Veronese cone (`VeroneseLinear`).
- *The arithmetic* (`AHArith`, Brambilla–Ottaviani's Lemma 6.3). The step's
  hypotheses hold for the standard choice of `u` and `ε`, and none of its inputs
  is exceptional. This is proved symbolically for `n ≥ 9` or `d ≥ 9`, and checked
  by the kernel for smaller `(n, d)`.
- *The induction* (`AlexanderHirschowitzGeneral`). Only two numbers of points
  need proving for each `(n, d)`: `⌊N/(n+1)⌋` and `⌈N/(n+1)⌉`. The remaining
  cases are:
  - the neighbours of the three quartic exceptions;
  - quartics in `ℙ⁷`, with `u = 30`, as in Brambilla–Ottaviani;
  - sextics in `ℙ²`.

  These use explicit Horace steps. Quartics in `ℙ⁵` need the exceptional case
  `(4, 4, 14)` along every route, so `AH_{5,4}(21)` is a rank certificate
  (`AHCertificates/`, via `DegreeCertificate`).

## Terracini's Lemma

`TerraciniLemma.Core` works with the affine cone `X̂ ⊆ E` over a variety
`X ⊂ ℙ(E)`, its secant variety `σ̂_r(X̂)`, and local smooth parametrizations
(`LocalParam`). The derivative of the addition map `Φ(u) = ∑ fᵢ(uᵢ)` has image
`T_{v₁}X̂ + ⋯ + T_{vᵣ}X̂`, and this image lies in the span of Mathlib's tangent
cone to `σ̂_r(X̂)` at `∑ vᵢ`.

The lemma itself (`terraciniLemma_tangentCone`) takes one hypothesis: the
dimension count from generic smoothness of `Φ`, which is not in Mathlib. When
the tangent spaces span `E`, it holds automatically
(`span_tangentConeAt_secantVariety_eq_top`). `TerraciniLemma.Projective`
descends the statement to `ℙ(E)`.

The Alexander–Hirschowitz theorem above is stated directly about spans of
tangent spaces. It does not depend on this hypothesis.

Worked examples:
- **`RationalNormalCurves`:** the parabola and the twisted cubic.
- **`Segre`:** the Segre quadric `ℙ¹ × ℙ¹ ⊂ ℙ³` and the defective threefold
  `ℙ¹ × ℙ¹ × ℙ¹ ⊂ ℙ⁷`.
- **`EllipticCurve`:** the curve `y² = x³ + 1`, with charts from the implicit
  function theorem.
- **`PolynomialCalculus`:** the bridge between formal and Fréchet derivatives of
  polynomials that these examples use.

The curve and Segre examples work in affine charts rather than cones. Their
module docstrings explain what that changes.

## Rank certificates

The base cases need lower bounds on the ranks of explicit integer matrices,
some of size `166 × 166`.

- **Certificate format.** A certificate consists of a square minor, given by
  row and column indices, a prime `p = 2³¹ - 1`, and a matrix `B` with
  `B · minor ≡ 1 (mod p)`. Then the minor's determinant is nonzero, so the
  matrix has full rank over every field of characteristic zero
  (`RankCertificate.le_rank_of_check`).
- **Computing them.** Macaulay2 computes the certificates. `m2/terracini.m2`
  extends the Macaulean server with MRDI serialization of integer matrices and a
  `rankCertificate` JSON-RPC method, and `Generator/` is the Lean client. The
  certificates are written to `TerraciniLemma/CubicCertificates/` and
  `TerraciniLemma/AHCertificates/`.
- **Trust.** Neither Macaulay2 nor its output is trusted: each certificate is
  checked by `decide +kernel`. Building the project does not need Macaulay2.
- **Memory.** The kernel keeps every intermediate term of a declaration, so each
  check is split into chunks of rows of `B`, one declaration each. Each
  certificate file also imports the previous one, so that Lake checks them one
  at a time. A full build peaks at about 5 GB of memory.

To regenerate the certificates, with Macaulay2 installed:

```sh
lake exe certificates            # every job
lake exe certificates cubicB1t6  # one job, by name
```

## Building

```sh
lake exe cache get   # Mathlib's prebuilt oleans
lake build
```

The toolchain is Lean `v4.35.0` with Mathlib `v4.35.0` (see `lean-toolchain` and
`lakefile.lean`). A cold build of the project, excluding Mathlib, takes about
40 minutes, most of it in the kernel checks of the certificates. GitHub Actions
builds every push and pull request (`.github/workflows/build.yml`).

## Files

`TerraciniLemma.lean` imports everything and lists the main results.

| Files | Contents |
|---|---|
| `Core`, `Projective`, `Defect` | Terracini's Lemma; the projective form; expected dimension and `IsDefective` |
| `PolynomialCalculus`, `RationalNormalCurves`, `Segre`, `EllipticCurve` | worked examples of Terracini's Lemma |
| `VeroneseGeneral`, `VeroneseDegree`, `VeroneseForms`, `VeroneseLinear` | the Veronese cone in degree 2 and degree `d`; forms and the singular-form bound; linear changes of coordinates |
| `Semicontinuity` | `HoldsGenerically`, `ForGeneralPoints`, semicontinuity of rank |
| `AlexanderHirschowitz`, `AlexanderHirschowitzCubic` | the exceptions are defective; the full theorem for quadrics |
| `CubicLattice`, `CubicInduction`, `CubicBaseCases`, `CubicInductionMain`, `AlexanderHirschowitzCubicGeneral` | the theorem for cubics |
| `DifferentialHorace`, `AHStep`, `AHArith`, `AlexanderHirschowitzGeneral` | the theorem in every degree |
| `RankCertificate`, `DegreeCertificate`, `CubicCertificates/`, `AHCertificates/` | rank certificates and the generated base cases |
| `Generator/`, `m2/` | the certificate generator (Lean client and Macaulay2 extension) |

## References

- J. Alexander and A. Hirschowitz, *Polynomial interpolation in several
  variables*, J. Algebraic Geom. **4** (1995), no. 2, 201–222.
- M. C. Brambilla and G. Ottaviani, *On the Alexander–Hirschowitz theorem*,
  J. Pure Appl. Algebra **212** (2008), 1229–1251.
  [arXiv:math/0701409](https://arxiv.org/abs/math/0701409)
- K. Chandler, *A brief proof of a maximal rank theorem for generic double
  points in projective space*, Trans. Amer. Math. Soc. **353** (2001), no. 5,
  1907–1920.
- D. A. Torrance and N. Vannieuwenhoven, *All secant varieties of the Chow
  variety are nondefective for cubics and quaternary forms*, Trans. Amer. Math.
  Soc. **374** (2021), no. 7, 4815–4838.
  [arXiv:2005.12436](https://arxiv.org/abs/2005.12436)
- A. Terracini, *Sulle V_k per cui la varietà degli S_h (h+1)-seganti ha
  dimensione minore dell'ordinario*, Rend. Circ. Mat. Palermo **31** (1911),
  392–396.
