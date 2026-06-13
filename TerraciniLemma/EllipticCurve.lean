import TerraciniLemma.Core
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
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

We work with the curve `E : y² = x³ + 1`, i.e. `ellipticF (x,y) = y² - x³ - 1 = 0`, which is
smooth (its discriminant `-27 ≠ 0`). At the two rational points `p₁ = (0,1)` and `p₂ = (2,3)`,
the tangent lines are spanned by `(1,0)` and `(1,2)` respectively, which are independent in
characteristic ≠ 2. So over `ℝ` or `ℂ` (or any `RCLike` field), the combined derivative of the
two-point parametrization is surjective onto `𝕜²`, and Terracini's Lemma gives `σ₂(E) = 𝕜²`.
-/

noncomputable section EllipticCurveExample

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The defining polynomial of the elliptic curve `y² = x³ + 1`. -/
def ellipticF (p : 𝕜 × 𝕜) : 𝕜 := p.2 ^ 2 - p.1 ^ 3 - 1

/-- The elliptic curve `{(x,y) : y² = x³ + 1}`. -/
def ellipticCurve : Set (𝕜 × 𝕜) := {p | ellipticF p = 0}

/-- The derivative of `ellipticF` at `p`: `(dx, dy) ↦ -3p.1² dx + 2p.2 dy`. -/
def ellipticFDeriv (p : 𝕜 × 𝕜) : (𝕜 × 𝕜) →L[𝕜] 𝕜 :=
  (-(3 * p.1 ^ 2)) • ContinuousLinearMap.fst 𝕜 𝕜 𝕜 + (2 * p.2) • ContinuousLinearMap.snd 𝕜 𝕜 𝕜

@[simp]
theorem ellipticFDeriv_apply (p q : 𝕜 × 𝕜) :
    ellipticFDeriv p q = -(3 * p.1 ^ 2) * q.1 + 2 * p.2 * q.2 := by
  simp [ellipticFDeriv, smul_eq_mul]

/-- `ellipticF` is a polynomial, hence `C^∞`. -/
theorem contDiff_ellipticF : ContDiff 𝕜 (⊤ : WithTop ℕ∞) (ellipticF (𝕜 := 𝕜)) :=
  ((ContDiff.pow contDiff_snd 2).sub (ContDiff.pow contDiff_fst 3)).sub contDiff_const

/-- `ellipticFDeriv p` is the Fréchet derivative of `ellipticF` at `p`. -/
theorem hasFDerivAt_ellipticF (p : 𝕜 × 𝕜) : HasFDerivAt ellipticF (ellipticFDeriv p) p := by
  have h1 : HasFDerivAt (fun q : 𝕜 × 𝕜 => q.1) (ContinuousLinearMap.fst 𝕜 𝕜 𝕜) p :=
    (ContinuousLinearMap.fst 𝕜 𝕜 𝕜).hasFDerivAt
  have h2 : HasFDerivAt (fun q : 𝕜 × 𝕜 => q.2) (ContinuousLinearMap.snd 𝕜 𝕜 𝕜) p :=
    (ContinuousLinearMap.snd 𝕜 𝕜 𝕜).hasFDerivAt
  have h1' : HasFDerivAt (fun q : 𝕜 × 𝕜 => q.1 ^ 3)
      ((3 * p.1 ^ 2) • ContinuousLinearMap.fst 𝕜 𝕜 𝕜) p := by
    simpa [nsmul_eq_mul, mul_comm] using (hasFDerivAt_pow 3 (x := p.1)).comp p h1
  have h2' : HasFDerivAt (fun q : 𝕜 × 𝕜 => q.2 ^ 2)
      ((2 * p.2) • ContinuousLinearMap.snd 𝕜 𝕜 𝕜) p := by
    simpa [nsmul_eq_mul, mul_comm] using (hasFDerivAt_pow 2 (x := p.2)).comp p h2
  have h := (h2'.sub h1').sub (hasFDerivAt_const (1 : 𝕜) p)
  have heq : (2 * p.2) • ContinuousLinearMap.snd 𝕜 𝕜 𝕜
      - (3 * p.1 ^ 2) • ContinuousLinearMap.fst 𝕜 𝕜 𝕜 - 0 = ellipticFDeriv p := by
    refine ContinuousLinearMap.ext fun q => ?_
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, sub_zero, ellipticFDeriv_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
    ring
  rwa [heq] at h

/-- `ellipticFDeriv p` is also a *strict* Fréchet derivative, since `ellipticF` is `C^∞`. -/
theorem hasStrictFDerivAt_ellipticF (p : 𝕜 × 𝕜) :
    HasStrictFDerivAt ellipticF (ellipticFDeriv p) p :=
  (contDiff_ellipticF.contDiffAt).hasStrictFDerivAt' (hasFDerivAt_ellipticF p) (by simp)

/-- The implicit-function-theorem chart at `p`, parametrized by `t : 𝕜` along the direction
`w` of a chosen nonzero kernel vector of `ellipticFDeriv p`. -/
def ellipticChart (p w : 𝕜 × 𝕜) (hw : w ∈ (ellipticFDeriv p).ker)
    (hp' : (ellipticFDeriv p).range = ⊤) : 𝕜 → 𝕜 × 𝕜 :=
  fun t => (hasStrictFDerivAt_ellipticF p).implicitFunction ellipticF (ellipticFDeriv p) hp'
    (ellipticF p) (t • (⟨w, hw⟩ : (ellipticFDeriv p).ker))

@[simp]
theorem ellipticChart_zero (p w : 𝕜 × 𝕜) (hw : w ∈ (ellipticFDeriv p).ker)
    (hp' : (ellipticFDeriv p).range = ⊤) : ellipticChart p w hw hp' 0 = p := by
  simp [ellipticChart]

/-- The derivative of `ellipticChart p w hw hp'` at `0` is `t ↦ t • w`. -/
theorem hasFDerivAt_ellipticChart (p w : 𝕜 × 𝕜) (hw : w ∈ (ellipticFDeriv p).ker)
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
def ellipticParam (p w : 𝕜 × 𝕜) (hw : w ∈ (ellipticFDeriv p).ker)
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
      ellipticCurve (![((0 : 𝕜), (1 : 𝕜)), ((2 : 𝕜), (3 : 𝕜))] i)
  | 0 => ellipticParam ((0 : 𝕜), (1 : 𝕜)) ((1 : 𝕜), (0 : 𝕜))
      (by simp)
      (Module.Dual.range_eq_top_of_ne_zero (fun h =>
        by simpa using congrFun (congrArg DFunLike.coe h) ((0 : 𝕜), (1 : 𝕜))))
  | 1 => ellipticParam ((2 : 𝕜), (3 : 𝕜)) ((1 : 𝕜), (2 : 𝕜))
      (by simp; ring)
      (Module.Dual.range_eq_top_of_ne_zero (fun h =>
        by simpa using congrFun (congrArg DFunLike.coe h) ((1 : 𝕜), (0 : 𝕜))))

/-- For `(a,b) : 𝕜 × 𝕜`, the combined derivative of the two-point parametrization at `(0,1)`
and `(2,3)` is surjective onto `𝕜²`: solve `s • (1,0) + t • (1,2) = (a,b)` by
`t = b/2`, `s = a - b/2`. This requires `2 ≠ 0`, i.e. characteristic zero. -/
theorem combinedDerivative_elliptic_surjective :
    Function.Surjective
      (combinedDerivative (v := ![((0 : 𝕜), (1 : 𝕜)), ((2 : 𝕜), (3 : 𝕜))]) ellipticParamPair) := by
  rintro ⟨a, b⟩
  set t : 𝕜 := b / 2 with ht
  refine ⟨![a - t, t], ?_⟩
  simp only [combinedDerivative, ellipticParamPair, ellipticParam, Fin.sum_univ_two,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, coordProj_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply, Prod.smul_mk, smul_eq_mul, mul_zero, mul_one,
    Prod.mk_add_mk, zero_add]
  rw [Prod.mk.injEq]
  refine ⟨by ring, ?_⟩
  rw [ht]
  field_simp

/-- **Terracini's Lemma for the elliptic curve `y² = x³ + 1`.** The tangent lines at
`(0,1)` and `(2,3)` together span all of `𝕜²` — matching the fact that the second secant
variety of (the affine cone over) a smooth plane cubic is the whole plane, over `ℝ`, `ℂ`, or
any other `RCLike` field. -/
theorem elliptic_terracini :
    (⊤ : Submodule 𝕜 (𝕜 × 𝕜)) =
      ⨆ i : Fin 2, (ellipticParamPair (𝕜 := 𝕜) i).tangentSpace := by
  have hrange : LinearMap.range
      (combinedDerivative (v := ![((0 : 𝕜), (1 : 𝕜)), ((2 : 𝕜), (3 : 𝕜))])
        ellipticParamPair).toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr combinedDerivative_elliptic_surjective
  have hgeneric : Module.finrank 𝕜 (⊤ : Submodule 𝕜 (𝕜 × 𝕜)) ≤
      Module.finrank 𝕜 (LinearMap.range
        (combinedDerivative (v := ![((0 : 𝕜), (1 : 𝕜)), ((2 : 𝕜), (3 : 𝕜))])
          ellipticParamPair).toLinearMap) :=
    le_of_eq (by rw [hrange])
  exact terraciniLemma ![((0 : 𝕜), (1 : 𝕜)), ((2 : 𝕜), (3 : 𝕜))]
    (fun i => by fin_cases i <;> simp [ellipticCurve, ellipticF]; ring)
    ellipticParamPair ⊤ le_top hgeneric

/-- Sanity check: the elliptic curve example specializes to `ℂ` for free. -/
example :
    (⊤ : Submodule ℂ (ℂ × ℂ)) =
      ⨆ i : Fin 2, (ellipticParamPair (𝕜 := ℂ) i).tangentSpace :=
  elliptic_terracini

end EllipticCurveExample
