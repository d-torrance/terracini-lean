import TerraciniLemma.Core
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Calculus of multivariate polynomials

A "middle ground" between hand-rolled calculus (as in `TerraciniLemma.RationalNormalCurves`
and `TerraciniLemma.Segre`) and the Implicit Function Theorem (as in
`TerraciniLemma.EllipticCurve`): every variety in this project is cut out by, or
parametrized by, polynomials, so Mathlib's *formal* derivative
(`MvPolynomial.pderiv`) already computes the Fréchet derivative of evaluation. This
file proves that bridging lemma once, generically.
-/

noncomputable section PolynomialCalculus

open MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : ℕ}

/-- The Fréchet derivative of `y ↦ MvPolynomial.eval y p` at `x`, as a continuous linear
map `(Fin n → 𝕜) →L[𝕜] 𝕜`: `∑ i, (∂p/∂xᵢ)(x) • coordProj n i`. -/
def mvPolynomialDeriv (p : MvPolynomial (Fin n) 𝕜) (x : Fin n → 𝕜) : (Fin n → 𝕜) →L[𝕜] 𝕜 :=
  ∑ i, eval x (pderiv i p) • coordProj n i

/-- `mvPolynomialDeriv p x` is the Fréchet derivative at `x` of evaluation at `p`. -/
theorem hasFDerivAt_eval_mvPolynomial (p : MvPolynomial (Fin n) 𝕜) (x : Fin n → 𝕜) :
    HasFDerivAt (fun y : Fin n → 𝕜 => eval y p) (mvPolynomialDeriv p x) x := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa [mvPolynomialDeriv, pderiv_C] using hasFDerivAt_const a x
  | add p q hp hq =>
      simpa [mvPolynomialDeriv, eval_add, map_add, add_smul, Finset.sum_add_distrib]
        using hp.add hq
  | mul_X p i hp =>
      have hproj : HasFDerivAt (fun y : Fin n → 𝕜 => y i) (coordProj (𝕜 := 𝕜) n i) x :=
        hasFDerivAt_coordProj n i x
      have hmul := hp.mul hproj
      convert hmul using 1
      · funext y
        simp [eval_mul, eval_X]
      · have hkey : ∀ j : Fin n, eval x (pderiv j (p * X i)) • coordProj (𝕜 := 𝕜) (𝔸 := 𝕜) n j
            = x i • (eval x (pderiv j p) • coordProj (𝕜 := 𝕜) (𝔸 := 𝕜) n j)
                + eval x p • (if i = j then coordProj (𝕜 := 𝕜) (𝔸 := 𝕜) n j else 0) := by
          intro j
          rw [pderiv_mul, map_add, map_mul, map_mul, eval_X]
          by_cases h : i = j
          · subst h
            rw [pderiv_X_self, map_one, mul_one, if_pos rfl]
            module
          · rw [pderiv_X_of_ne h, map_zero, mul_zero, if_neg h]
            module
        calc mvPolynomialDeriv (p * X i) x
            = ∑ j, (x i • (eval x (pderiv j p) • coordProj (𝕜 := 𝕜) (𝔸 := 𝕜) n j)
                + eval x p • (if i = j then coordProj (𝕜 := 𝕜) (𝔸 := 𝕜) n j else 0)) :=
              Finset.sum_congr rfl fun j _ => hkey j
          _ = ∑ j, x i • (eval x (pderiv j p) • coordProj (𝕜 := 𝕜) (𝔸 := 𝕜) n j)
                + ∑ j, eval x p • (if i = j then coordProj (𝕜 := 𝕜) (𝔸 := 𝕜) n j else 0) :=
              Finset.sum_add_distrib
          _ = x i • mvPolynomialDeriv p x + eval x p • coordProj (𝕜 := 𝕜) (𝔸 := 𝕜) n i := by
              rw [← Finset.smul_sum, ← Finset.smul_sum, Finset.sum_ite_eq]
              simp [mvPolynomialDeriv]
          _ = eval x p • coordProj (𝕜 := 𝕜) (𝔸 := 𝕜) n i + x i • mvPolynomialDeriv p x :=
              add_comm _ _

/-- `MvPolynomial.eval · p` is `C^m` for every `m`, since it is analytic. -/
theorem contDiff_eval_mvPolynomial [CompleteSpace 𝕜] (p : MvPolynomial (Fin n) 𝕜)
    {m : WithTop ℕ∞} :
    ContDiff 𝕜 m (fun y : Fin n → 𝕜 => eval y p) :=
  contDiffOn_univ.mp (AnalyticOnNhd.eval_mvPolynomial p).contDiffOn_of_completeSpace

end PolynomialCalculus
