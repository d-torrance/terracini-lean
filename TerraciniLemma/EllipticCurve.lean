import TerraciniLemma.PolynomialCalculus
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Worked example: an elliptic curve via the Implicit Function Theorem

All previous worked examples (`TerraciniLemma.Veronese`, `TerraciniLemma.Segre`) build their
`LocalParam`s from an explicit *rational parametrization* of the variety. An elliptic curve
cannot be rationally parametrized, so we instead build the required local charts directly from
Mathlib's **implicit function theorem** (`HasStrictFDerivAt.implicitFunction` and friends, in
`Mathlib.Analysis.Calculus.Implicit`).

This illustrates that `LocalParam` does not require a global parametrization of `X`: all that is
needed is a chart defined near the base point, together with its derivative there
(`chart_eval` and `hasFDerivAt`).

We work with the curve `E : y² = x³ + 1` over `Fin 2 → 𝕜` (variable `0` = x, `1` = y), cut out by
the polynomial `ellipticPoly = Y² - X³ - 1 ∈ MvPolynomial (Fin 2) 𝕜`, i.e.
`ellipticF p = p 1 ^ 2 - p 0 ^ 3 - 1 = 0`, which is smooth (its discriminant `-27 ≠ 0`). At the
two rational points `p₁ = (0,1)` and `p₂ = (2,3)`, the tangent lines are spanned by `(1,0)` and
`(1,2)` respectively, which are independent in characteristic ≠ 2. So over `ℝ` or `ℂ` (or any
`RCLike` field), the combined derivative of the two-point parametrization is surjective onto
`𝕜²`, and Terracini's Lemma gives `σ₂(E) = 𝕜²`.

The calculus of `ellipticF` (its derivative and smoothness) is obtained for free from
`TerraciniLemma.PolynomialCalculus`'s generic `MvPolynomial.pderiv` ↔ `HasFDerivAt` bridge,
since `ellipticF` is literally evaluation of `ellipticPoly`.

**Affine chart vs. cone.** `Fin 2 → 𝕜` here is the affine chart `{[1:x:y]}` of
`ℙ²` (the curve `E` minus its point at infinity), not the 3-dimensional cone
over `E`. So `elliptic_terracini` is a chart-level computation and does not
directly feed into `TerraciniLemma.Projective`'s `Submodule.projectivization`
descent.
-/

noncomputable section EllipticCurveExample

variable {𝕜 : Type*} [RCLike 𝕜]

open MvPolynomial

/-- `Y² - X³ - 1`, defining the elliptic curve `y² = x³ + 1` (variable `0` = x, `1` = y). -/
def ellipticPoly : MvPolynomial (Fin 2) 𝕜 := X 1 ^ 2 - X 0 ^ 3 - 1

/-- The defining polynomial of the elliptic curve `y² = x³ + 1`, evaluated at `p`. -/
def ellipticF (p : Fin 2 → 𝕜) : 𝕜 := eval p ellipticPoly

/-- The elliptic curve `{p : p 1 ² = p 0 ³ + 1}`. -/
def ellipticCurve : Set (Fin 2 → 𝕜) := {p | ellipticF p = 0}

/-- The derivative of `ellipticF` at `p`, as the formal derivative of `ellipticPoly`
evaluated at `p` (see `TerraciniLemma.PolynomialCalculus`). -/
def ellipticFDeriv (p : Fin 2 → 𝕜) : (Fin 2 → 𝕜) →L[𝕜] 𝕜 := mvPolynomialDeriv ellipticPoly p

@[simp]
theorem ellipticFDeriv_apply (p q : Fin 2 → 𝕜) :
    ellipticFDeriv p q = -(3 * p 0 ^ 2) * q 0 + 2 * p 1 * q 1 := by
  have h0 : pderiv 0 ellipticPoly = -(3 * X 0 ^ 2 : MvPolynomial (Fin 2) 𝕜) := by
    simp [ellipticPoly, map_sub]
  have h1 : pderiv 1 ellipticPoly = (2 * X 1 : MvPolynomial (Fin 2) 𝕜) := by
    simp [ellipticPoly, map_sub]
  simp [ellipticFDeriv, mvPolynomialDeriv, Fin.sum_univ_two, coordProj_apply, h0, h1,
    eval_neg, eval_mul, eval_pow, eval_X]

/-- `ellipticFDeriv p` is the Fréchet derivative of `ellipticF` at `p`. -/
theorem hasFDerivAt_ellipticF (p : Fin 2 → 𝕜) : HasFDerivAt ellipticF (ellipticFDeriv p) p :=
  hasFDerivAt_eval_mvPolynomial ellipticPoly p

/-- `ellipticF` is a polynomial, hence `C^∞`. -/
theorem contDiff_ellipticF : ContDiff 𝕜 (⊤ : WithTop ℕ∞) (ellipticF (𝕜 := 𝕜)) := by
  show ContDiff 𝕜 (⊤ : WithTop ℕ∞) (fun p : Fin 2 → 𝕜 => eval p ellipticPoly)
  exact contDiff_eval_mvPolynomial (𝕜 := 𝕜) (n := 2) ellipticPoly

/-- `ellipticFDeriv p` is also a *strict* Fréchet derivative, since `ellipticF` is `C^∞`. -/
theorem hasStrictFDerivAt_ellipticF (p : Fin 2 → 𝕜) :
    HasStrictFDerivAt ellipticF (ellipticFDeriv p) p :=
  ContDiffAt.hasStrictFDerivAt' contDiff_ellipticF.contDiffAt (hasFDerivAt_ellipticF p) (by simp)

/-- The implicit-function-theorem chart at `p`, parametrized by `t : 𝕜` along the direction
`w` of a chosen nonzero kernel vector of `ellipticFDeriv p`. -/
def ellipticChart (p w : Fin 2 → 𝕜) (hw : w ∈ (ellipticFDeriv p).ker)
    (hp' : (ellipticFDeriv p).range = ⊤) : 𝕜 → Fin 2 → 𝕜 :=
  fun t => (hasStrictFDerivAt_ellipticF p).implicitFunction ellipticF (ellipticFDeriv p) hp'
    (ellipticF p) (t • (⟨w, hw⟩ : (ellipticFDeriv p).ker))

@[simp]
theorem ellipticChart_zero (p w : Fin 2 → 𝕜) (hw : w ∈ (ellipticFDeriv p).ker)
    (hp' : (ellipticFDeriv p).range = ⊤) : ellipticChart p w hw hp' 0 = p := by
  simp [ellipticChart]

/-- The derivative of `ellipticChart p w hw hp'` at `0` is `t ↦ t • w`. -/
theorem hasFDerivAt_ellipticChart (p w : Fin 2 → 𝕜) (hw : w ∈ (ellipticFDeriv p).ker)
    (hp' : (ellipticFDeriv p).range = ⊤) :
    HasFDerivAt (ellipticChart p w hw hp') ((ContinuousLinearMap.id 𝕜 𝕜).smulRight w) 0 := by
  set c : (ellipticFDeriv p).ker := ⟨w, hw⟩ with hc
  have hsmul : HasFDerivAt (fun t : 𝕜 => t • c)
      ((ContinuousLinearMap.id 𝕜 𝕜).smulRight c) 0 :=
    ((ContinuousLinearMap.id 𝕜 𝕜).smulRight c).hasFDerivAt
  have hg : HasFDerivAt
      ((hasStrictFDerivAt_ellipticF p).implicitFunction ellipticF (ellipticFDeriv p) hp'
        (ellipticF p))
      ((ellipticFDeriv p).ker.subtypeL) ((0 : 𝕜) • c) := by
    rw [zero_smul]
    exact ((hasStrictFDerivAt_ellipticF p).to_implicitFunction hp').hasFDerivAt
  have hcomp := hg.comp 0 hsmul
  have heq : ((ellipticFDeriv p).ker.subtypeL).comp
      ((ContinuousLinearMap.id 𝕜 𝕜).smulRight c) = (ContinuousLinearMap.id 𝕜 𝕜).smulRight w := by
    refine ContinuousLinearMap.ext fun t => ?_
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.id_apply, hc]
  rwa [heq] at hcomp

/-- The local parametrization of the elliptic curve at `p`, built from the implicit function
theorem using a chosen nonzero kernel vector `w` of `ellipticFDeriv p`. -/
def ellipticParam (p w : Fin 2 → 𝕜) (hw : w ∈ (ellipticFDeriv p).ker)
    (hp' : (ellipticFDeriv p).range = ⊤) :
    LocalParam (𝕜 := 𝕜) (𝔸 := 𝕜) ellipticCurve p where
  basePoint := 0
  chart := ellipticChart p w hw hp'
  chart_eval := ellipticChart_zero p w hw hp'
  tangent := (ContinuousLinearMap.id 𝕜 𝕜).smulRight w
  hasFDerivAt := hasFDerivAt_ellipticChart p w hw hp'

/-- The pair of local parametrizations at `p₁ = (0,1)` and `p₂ = (2,3)`, using the kernel
vectors `(1,0)` (tangent line `y = 1`) and `(1,2)` (tangent line through `(2,3)` with slope `2`)
respectively. -/
def ellipticParamPair :
    ∀ i : Fin 2, LocalParam (𝕜 := 𝕜) (𝔸 := 𝕜)
      ellipticCurve (![![(0 : 𝕜), 1], ![2, 3]] i)
  | 0 => ellipticParam ![(0 : 𝕜), 1] ![1, 0]
      (by simp)
      (Module.Dual.range_eq_top_of_ne_zero (fun h =>
        by simpa using congrFun (congrArg DFunLike.coe h) ![(0 : 𝕜), 1]))
  | 1 => ellipticParam ![(2 : 𝕜), 3] ![1, 2]
      (by simp; ring)
      (Module.Dual.range_eq_top_of_ne_zero (fun h =>
        by simpa using congrFun (congrArg DFunLike.coe h) ![(1 : 𝕜), 0]))

/-- For `v : Fin 2 → 𝕜`, the combined derivative of the two-point parametrization at `(0,1)`
and `(2,3)` is surjective onto `𝕜²`: solve `s • (1,0) + t • (1,2) = v` by
`t = v 1 / 2`, `s = v 0 - t`. This requires `2 ≠ 0`, i.e. characteristic zero. -/
theorem combinedDerivative_elliptic_surjective :
    Function.Surjective
      (combinedDerivative (v := ![![(0 : 𝕜), 1], ![2, 3]]) ellipticParamPair) := by
  intro v
  set t : 𝕜 := v 1 / 2 with ht
  refine ⟨![v 0 - t, t], ?_⟩
  funext i
  fin_cases i <;>
    simp only [combinedDerivative, ellipticParamPair, ellipticParam, Fin.sum_univ_two,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, coordProj_apply,
      Fin.isValue, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · ring
  · rw [ht]; ring

/-- **Terracini's Lemma for the elliptic curve `y² = x³ + 1`.** The tangent lines at
`(0,1)` and `(2,3)` together span all of `𝕜²` — matching the fact that the second secant
variety of (the affine cone over) a smooth plane cubic is the whole plane, over `ℝ`, `ℂ`, or
any other `RCLike` field. -/
theorem elliptic_terracini :
    (⊤ : Submodule 𝕜 (Fin 2 → 𝕜)) =
      ⨆ i : Fin 2, (ellipticParamPair (𝕜 := 𝕜) i).tangentSpace := by
  have hrange : LinearMap.range
      (combinedDerivative (v := ![![(0 : 𝕜), 1], ![2, 3]])
        ellipticParamPair).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr combinedDerivative_elliptic_surjective
  have hgeneric : Module.finrank 𝕜 (⊤ : Submodule 𝕜 (Fin 2 → 𝕜)) ≤
      Module.finrank 𝕜 (LinearMap.range
        (combinedDerivative (v := ![![(0 : 𝕜), 1], ![2, 3]])
          ellipticParamPair).toLinearMap) :=
    le_of_eq (by rw [hrange])
  exact terraciniLemma ![![(0 : 𝕜), 1], ![2, 3]]
    (fun i => by
      fin_cases i <;>
        simp [ellipticCurve, ellipticF, ellipticPoly, Fin.isValue,
          Matrix.cons_val_zero, Matrix.cons_val_one, eval_sub, eval_pow, eval_X, map_one]
      all_goals ring)
    ellipticParamPair ⊤ le_top hgeneric

/-- Sanity check: the elliptic curve example specializes to `ℂ` for free. -/
example :
    (⊤ : Submodule ℂ (Fin 2 → ℂ)) =
      ⨆ i : Fin 2, (ellipticParamPair (𝕜 := ℂ) i).tangentSpace :=
  elliptic_terracini

end EllipticCurveExample
