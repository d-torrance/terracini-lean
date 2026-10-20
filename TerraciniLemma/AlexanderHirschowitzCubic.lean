module

public import TerraciniLemma.VeroneseForms
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Vandermonde

/-!
# The `(4,3,7)` Alexander–Hirschowitz case at general points

`σ₇(v₃(ℙ⁴))` is defective: the tangent spaces to the cone over `v₃(ℙ⁴)` at `7` general points
span only `34` of the `35` ambient dimensions. We follow Brambilla–Ottaviani, *On the
Alexander–Hirschowitz theorem*, J. Pure Appl. Algebra **212** (2008), §2: seven general points
of `ℙ⁴` lie on a rational normal quartic `C`, and the secant variety `σ₂(C)` is a cubic
hypersurface singular along `C`, hence singular at the seven points. The singular-form bound
(`isDefective_of_singular`) then gives the defect.

Concretely, in coordinates `y` in which `C` is the moment curve `t ↦ (1, t, t², t³, t⁴)`,
`σ₂(C)` is the Hankel determinant
`hankelCubic y = det !![y₀, y₁, y₂; y₁, y₂, y₃; y₂, y₃, y₄]`, whose gradient vanishes on the cone
over `C` (including its point at infinity `(0,0,0,0,1)`). For seven points `p₀, …, p₆` we build
an invertible linear change of coordinates `ahL p` sending

* `p₀, …, p₄` to multiples of moment vectors `(1, λᵢ, …, λᵢ⁴)`,
* `p₅` to the point at infinity `(0,0,0,0,1)`,
* `p₆` to a multiple of the moment vector at `t = 0`,

namely `ahL p = Vᵀ · diag(w) · diag(U)⁻¹ · adj(M)`, where `M` has columns `p₀, …, p₄`,
`U = adj(M) p₅`, `W = adj(M) p₆`, the nodes are `λᵢ = Uᵢ / Wᵢ`, `V` is their Vandermonde matrix
and `wᵢ = 1 / ∏_{j ≠ i} (λᵢ - λⱼ)` are the Lagrange weights. (Since `∑ᵢ wᵢ λᵢᵏ = [k = 4]` for
`k ≤ 4`, the point `p₅` goes to `(0,0,0,0,1)`.) The form `hankelCubic ∘ ahL p` is then a nonzero
cubic singular at all seven points. The construction needs `det M ≠ 0`, `Uᵢ, Wᵢ ≠ 0` and
distinct nodes (`AHGeneric`), which holds off the zero locus of an explicit polynomial in the
coordinates of the points (`forGeneralPoints_ahGeneric`).
-/

@[expose] public section

noncomputable section AlexanderHirschowitzCubic

open Finset
open scoped Matrix

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-! ### §A — Lagrange weights -/

omit [CharZero 𝕜] in
/-- The Lagrange weight `1 / ∏_{j ≠ i} (lᵢ - lⱼ)` of the node `lᵢ`. -/
def lagrangeWeight {m : ℕ} (l : Fin (m + 1) → 𝕜) (i : Fin (m + 1)) : 𝕜 :=
  (∏ j ∈ univ.erase i, (l i - l j))⁻¹

omit [CharZero 𝕜] in
theorem lagrangeWeight_ne_zero {m : ℕ} {l : Fin (m + 1) → 𝕜} (hl : Function.Injective l)
    (i : Fin (m + 1)) : lagrangeWeight l i ≠ 0 :=
  inv_ne_zero (prod_ne_zero_iff.mpr fun _ hj =>
    sub_ne_zero.mpr (hl.ne (ne_of_mem_erase hj).symm))

omit [CharZero 𝕜] in
/-- `∑ᵢ wᵢ lᵢᵏ = [k = m]` for `k ≤ m`: compare the coefficients of `Xᵐ` in the Lagrange
interpolation of `Xᵏ` at the `m + 1` nodes. -/
theorem sum_pow_mul_lagrangeWeight {m : ℕ} {l : Fin (m + 1) → 𝕜} (hl : Function.Injective l)
    {k : ℕ} (hk : k ≤ m) :
    ∑ i, l i ^ k * lagrangeWeight l i = if k = m then 1 else 0 := by
  classical
  have hinj : Set.InjOn l (univ : Finset (Fin (m + 1))) := hl.injOn
  have hf := Lagrange.eq_interpolate (s := univ) (f := (Polynomial.X ^ k : Polynomial 𝕜)) hinj (by
    rw [Polynomial.degree_X_pow, card_univ, Fintype.card_fin]
    exact_mod_cast Nat.lt_succ_of_le hk)
  have h := congrArg (fun P : Polynomial 𝕜 => P.coeff m) hf
  simp only [Polynomial.coeff_X_pow, Lagrange.interpolate_apply, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, Polynomial.eval_X_pow] at h
  rw [show (if k = m then (1 : 𝕜) else 0) = if m = k then 1 else 0 by simp [eq_comm], h]
  refine sum_congr rfl fun i _ => ?_
  congr 1
  rw [lagrangeWeight, ← Lagrange.leadingCoeff_basis hinj (mem_univ i), Polynomial.leadingCoeff,
    Lagrange.natDegree_basis hinj (mem_univ i)]
  simp

/-! ### §B — The Hankel cubic, singular along the moment curve -/

omit [CharZero 𝕜] in
/-- The moment vector `(1, t, t², t³, t⁴)`. -/
def momentVec (t : 𝕜) : Fin 5 → 𝕜 := fun j => t ^ (j : ℕ)

omit [CharZero 𝕜] in
/-- The Hankel determinant `det !![y₀, y₁, y₂; y₁, y₂, y₃; y₂, y₃, y₄]`, the equation of the
secant variety of the moment curve in `ℙ⁴`. -/
def hankelCubic (y : Fin 5 → 𝕜) : 𝕜 :=
  y 0 * y 2 * y 4 + 2 * y 1 * y 2 * y 3 - y 2 ^ 3 - y 0 * y 3 ^ 2 - y 1 ^ 2 * y 4

omit [CharZero 𝕜] in
/-- `hankelCubic` as a polynomial. -/
def hankelPoly : MvPolynomial (Fin 5) 𝕜 :=
  .X 0 * .X 2 * .X 4 + .C 2 * .X 1 * .X 2 * .X 3 - .X 2 ^ 3 - .X 0 * .X 3 ^ 2 - .X 1 ^ 2 * .X 4

omit [CharZero 𝕜] in
theorem hankelCubic_eq_eval (y : Fin 5 → 𝕜) : hankelCubic y = MvPolynomial.eval y hankelPoly := by
  simp [hankelCubic, hankelPoly]

omit [CharZero 𝕜] in
theorem hasFDerivAt_hankelCubic (y : Fin 5 → 𝕜) :
    HasFDerivAt hankelCubic (mvPolynomialDeriv hankelPoly y) y := by
  rw [show (hankelCubic : (Fin 5 → 𝕜) → 𝕜) = fun y => MvPolynomial.eval y hankelPoly from
    funext hankelCubic_eq_eval]
  exact hasFDerivAt_eval_mvPolynomial hankelPoly y

omit [CharZero 𝕜] in
/-- The gradient of the Hankel cubic: its partial derivatives are (twice) the `2 × 2` minors
of the Hankel matrix. -/
theorem mvPolynomialDeriv_hankelPoly_apply (y w : Fin 5 → 𝕜) :
    mvPolynomialDeriv hankelPoly y w
      = (y 2 * y 4 - y 3 ^ 2) * w 0 + (2 * y 2 * y 3 - 2 * y 1 * y 4) * w 1
        + (y 0 * y 4 + 2 * y 1 * y 3 - 3 * y 2 ^ 2) * w 2 + (2 * y 1 * y 2 - 2 * y 0 * y 3) * w 3
        + (y 0 * y 2 - y 1 ^ 2) * w 4 := by
  simp [mvPolynomialDeriv, hankelPoly, Fin.sum_univ_five, coordProj_apply, Pi.single_apply]
  ring

omit [CharZero 𝕜] in
/-- The Hankel cubic is singular along the cone over the moment curve. -/
theorem mvPolynomialDeriv_hankelPoly_momentVec (c t : 𝕜) :
    mvPolynomialDeriv hankelPoly (c • momentVec t) = 0 := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [mvPolynomialDeriv_hankelPoly_apply]
  simp [momentVec]
  ring

omit [CharZero 𝕜] in
/-- The Hankel cubic is singular at the point at infinity `(0,0,0,0,1)` of the moment curve. -/
theorem mvPolynomialDeriv_hankelPoly_single (c : 𝕜) :
    mvPolynomialDeriv hankelPoly (c • Pi.single 4 1 : Fin 5 → 𝕜) = 0 := by
  refine ContinuousLinearMap.ext fun w => ?_
  rw [mvPolynomialDeriv_hankelPoly_apply]
  simp

/-! ### §C — Sending seven points to the moment curve -/

section Normalization

variable (p : Fin 7 → Fin 5 → 𝕜)

omit [CharZero 𝕜] in
/-- The matrix whose columns are the first five points `p₀, …, p₄`. -/
def ahMat : Matrix (Fin 5) (Fin 5) 𝕜 := fun i j => p (Fin.castAdd 2 j) i

omit [CharZero 𝕜] in
/-- `U = adj(M) p₅`, the coordinates of `p₅` in the basis `p₀, …, p₄` (up to the factor
`det M`). -/
def ahU : Fin 5 → 𝕜 := (ahMat p).adjugate *ᵥ p 5

omit [CharZero 𝕜] in
/-- `W = adj(M) p₆`, the coordinates of `p₆` in the basis `p₀, …, p₄` (up to `det M`). -/
def ahW : Fin 5 → 𝕜 := (ahMat p).adjugate *ᵥ p 6

omit [CharZero 𝕜] in
/-- The nodes `λᵢ = Uᵢ / Wᵢ` of the rational normal quartic through the seven points. -/
def ahNode : Fin 5 → 𝕜 := fun i => ahU p i / ahW p i

omit [CharZero 𝕜] in
/-- The change of coordinates `Vᵀ · diag(w) · diag(U)⁻¹ · adj(M)` taking the rational normal
quartic through the seven points to the moment curve. -/
def ahL : Matrix (Fin 5) (Fin 5) 𝕜 :=
  (Matrix.vandermonde (ahNode p))ᵀ * Matrix.diagonal (lagrangeWeight (ahNode p))
    * Matrix.diagonal (fun i => (ahU p i)⁻¹) * (ahMat p).adjugate

omit [CharZero 𝕜] in
/-- The open conditions under which `ahL p` does its job. -/
structure AHGeneric : Prop where
  det_ne_zero : (ahMat p).det ≠ 0
  U_ne_zero : ∀ i, ahU p i ≠ 0
  W_ne_zero : ∀ i, ahW p i ≠ 0
  node_injective : Function.Injective (ahNode p)

omit [CharZero 𝕜] in
theorem ahL_mulVec (x : Fin 5 → 𝕜) (a : Fin 5) :
    (ahL p *ᵥ x) a
      = ∑ i, ahNode p i ^ (a : ℕ) * lagrangeWeight (ahNode p) i * (ahU p i)⁻¹
          * ((ahMat p).adjugate *ᵥ x) i := by
  simp only [ahL, ← Matrix.mulVec_mulVec]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply,
    Matrix.diagonal, Matrix.of_apply]
  refine sum_congr rfl fun i _ => ?_
  simp [mul_assoc]

variable {p}

omit [CharZero 𝕜] in
theorem ahNode_ne_zero (hp : AHGeneric p) (i : Fin 5) : ahNode p i ≠ 0 :=
  div_ne_zero (hp.U_ne_zero i) (hp.W_ne_zero i)

omit [CharZero 𝕜] in
/-- `p₀, …, p₄` go to multiples of the moment vectors at the nodes. -/
theorem ahL_mulVec_castAdd (j : Fin 5) :
    ahL p *ᵥ p (Fin.castAdd 2 j)
      = ((ahMat p).det * lagrangeWeight (ahNode p) j * (ahU p j)⁻¹) • momentVec (ahNode p j) := by
  have hcol : p (Fin.castAdd 2 j) = ahMat p *ᵥ Pi.single j 1 := by
    rw [Matrix.mulVec_single_one]
    rfl
  have hadj : (ahMat p).adjugate *ᵥ p (Fin.castAdd 2 j) = (ahMat p).det • Pi.single j 1 := by
    rw [hcol, Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  funext a
  rw [ahL_mulVec, hadj, sum_eq_single j]
  · simp [momentVec]
    ring
  · intro i _ hij
    simp [hij]
  · simp

omit [CharZero 𝕜] in
/-- `p₅` goes to the point at infinity `(0,0,0,0,1)` of the moment curve. -/
theorem ahL_mulVec_five (hp : AHGeneric p) : ahL p *ᵥ p 5 = Pi.single 4 1 := by
  funext a
  rw [ahL_mulVec]
  have h := sum_pow_mul_lagrangeWeight hp.node_injective (k := (a : ℕ)) (by omega)
  have hU : ∀ i, (ahU p i)⁻¹ * ((ahMat p).adjugate *ᵥ p 5) i = 1 := fun i =>
    inv_mul_cancel₀ (hp.U_ne_zero i)
  simp only [mul_assoc, hU, mul_one] at h ⊢
  rw [h]
  fin_cases a <;> simp

omit [CharZero 𝕜] in
/-- `p₆` goes to a multiple of the moment vector at `t = 0`. -/
theorem ahL_mulVec_six (hp : AHGeneric p) :
    ahL p *ᵥ p 6 = (∑ i, lagrangeWeight (ahNode p) i * (ahNode p i)⁻¹) • momentVec 0 := by
  funext a
  rw [ahL_mulVec]
  -- `Wᵢ / Uᵢ = λᵢ⁻¹`
  have hWU : ∀ i, (ahU p i)⁻¹ * ((ahMat p).adjugate *ᵥ p 6) i = (ahNode p i)⁻¹ := fun i => by
    rw [ahNode, inv_div, div_eq_inv_mul]
    rfl
  simp only [mul_assoc, hWU]
  rcases Nat.eq_zero_or_pos (a : ℕ) with ha | ha
  · simp [ha, momentVec]
  · -- for `a ≥ 1`, `∑ᵢ wᵢ λᵢ^(a-1) = 0` since `a - 1 < 4`
    have h := sum_pow_mul_lagrangeWeight hp.node_injective (k := (a : ℕ) - 1) (by omega)
    rw [ite_eq_right (by omega)] at h
    have hpow : ∀ i, ahNode p i ^ (a : ℕ) * (lagrangeWeight (ahNode p) i * (ahNode p i)⁻¹)
        = ahNode p i ^ ((a : ℕ) - 1) * lagrangeWeight (ahNode p) i := fun i => by
      have hne := ahNode_ne_zero hp i
      obtain ⟨b, hb⟩ : ∃ b, (a : ℕ) = b + 1 := ⟨(a : ℕ) - 1, by omega⟩
      rw [hb, Nat.add_sub_cancel, pow_succ]
      field_simp
    simp only [hpow, h]
    rw [Pi.smul_apply, momentVec, zero_pow (by omega), smul_zero]

omit [CharZero 𝕜] in
theorem det_ahL_ne_zero (hp : AHGeneric p) : (ahL p).det ≠ 0 := by
  simp only [ahL, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, Matrix.det_adjugate]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) (pow_ne_zero _ hp.det_ne_zero)
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr hp.node_injective
  · exact prod_ne_zero_iff.mpr fun i _ => lagrangeWeight_ne_zero hp.node_injective i
  · exact prod_ne_zero_iff.mpr fun i _ => inv_ne_zero (hp.U_ne_zero i)

end Normalization

/-! ### §D — The secant cubic through seven general points -/

omit [CharZero 𝕜] in
/-- A `5 × 5` matrix as a continuous linear map. -/
def matrixCLM (A : Matrix (Fin 5) (Fin 5) 𝕜) : (Fin 5 → 𝕜) →L[𝕜] (Fin 5 → 𝕜) :=
  ContinuousLinearMap.pi fun a => ∑ j, A a j • ContinuousLinearMap.proj j

omit [CharZero 𝕜] in
theorem matrixCLM_apply (A : Matrix (Fin 5) (Fin 5) 𝕜) (x : Fin 5 → 𝕜) :
    matrixCLM A x = A *ᵥ x := by
  funext a
  simp [matrixCLM, Matrix.mulVec, dotProduct]

omit [CharZero 𝕜] in
/-- The secant cubic `σ₂(C)` of the rational normal quartic `C` through the seven points:
the Hankel cubic in the coordinates `ahL p`. -/
def ahCubic (p : Fin 7 → Fin 5 → 𝕜) : (Fin 5 → 𝕜) → 𝕜 := fun x => hankelCubic (ahL p *ᵥ x)

omit [CharZero 𝕜] in
theorem hasFDerivAt_ahCubic (p : Fin 7 → Fin 5 → 𝕜) (x : Fin 5 → 𝕜) :
    HasFDerivAt (ahCubic p)
      ((mvPolynomialDeriv hankelPoly (ahL p *ᵥ x)).comp (matrixCLM (ahL p))) x := by
  have h := (hasFDerivAt_hankelCubic (matrixCLM (ahL p) x)).comp x (matrixCLM (ahL p)).hasFDerivAt
  rwa [show hankelCubic ∘ ⇑(matrixCLM (ahL p)) = ahCubic p from
    funext fun y => by simp [ahCubic, matrixCLM_apply], matrixCLM_apply] at h

variable {p : Fin 7 → Fin 5 → 𝕜}

omit [CharZero 𝕜] in
/-- **The secant cubic is singular at all seven points**: `ahL p` sends each of them to the cone
over the moment curve (or its point at infinity), where the Hankel cubic is singular. -/
theorem ahCubic_singular (hp : AHGeneric p) (k : Fin 7) :
    HasFDerivAt (ahCubic p) (0 : (Fin 5 → 𝕜) →L[𝕜] 𝕜) (p k) := by
  have h := hasFDerivAt_ahCubic p (p k)
  have hz : mvPolynomialDeriv hankelPoly (ahL p *ᵥ p k) = 0 := by
    obtain ⟨k, hk⟩ := k
    rcases (by omega : k < 5 ∨ k = 5 ∨ k = 6) with h5 | rfl | rfl
    · rw [show (⟨k, hk⟩ : Fin 7) = Fin.castAdd 2 ⟨k, h5⟩ from rfl, ahL_mulVec_castAdd]
      exact mvPolynomialDeriv_hankelPoly_momentVec _ _
    · rw [show (⟨5, hk⟩ : Fin 7) = 5 from rfl, ahL_mulVec_five hp]
      simpa using mvPolynomialDeriv_hankelPoly_single (𝕜 := 𝕜) 1
    · rw [show (⟨6, hk⟩ : Fin 7) = 6 from rfl, ahL_mulVec_six hp]
      exact mvPolynomialDeriv_hankelPoly_momentVec _ _
  rwa [hz, ContinuousLinearMap.zero_comp] at h

omit [CharZero 𝕜] in
/-- The secant cubic is nonzero: `ahL p` is invertible and the Hankel cubic is `-1` at
`(0,0,1,0,0)`. -/
theorem ahCubic_ne_zero (hp : AHGeneric p) : ahCubic p ≠ 0 := by
  intro h
  have hx := congrFun h ((ahL p)⁻¹ *ᵥ Pi.single 2 1)
  rw [ahCubic, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (det_ahL_ne_zero hp)),
    Matrix.one_mulVec] at hx
  simp [hankelCubic] at hx

omit [CharZero 𝕜] in
/-- The secant cubic is a cubic form: the Hankel cubic is a sum of products of three
coordinates, each of which is a linear form in `x`. -/
theorem ahCubic_mem_veroneseForms (p : Fin 7 → Fin 5 → 𝕜) : ahCubic p ∈ veroneseForms 4 3 := by
  let ℓ : Fin 5 → Module.Dual 𝕜 (Fin 5 → 𝕜) := fun a =>
    (LinearMap.proj a).comp (Matrix.mulVecLin (ahL p))
  have h3 : ∀ a b c, ⇑(ℓ a) * ⇑(ℓ b) * ⇑(ℓ c) ∈ veroneseForms 4 3 := fun a b c =>
    mul_mem_veroneseForms rfl (mul_mem_veroneseForms rfl (linearMap_mem_veroneseForms 4 (ℓ a))
      (linearMap_mem_veroneseForms 4 (ℓ b))) (linearMap_mem_veroneseForms 4 (ℓ c))
  have heq : ahCubic p = ⇑(ℓ 0) * ⇑(ℓ 2) * ⇑(ℓ 4) + (2 : 𝕜) • (⇑(ℓ 1) * ⇑(ℓ 2) * ⇑(ℓ 3))
      - ⇑(ℓ 2) * ⇑(ℓ 2) * ⇑(ℓ 2) - ⇑(ℓ 0) * ⇑(ℓ 3) * ⇑(ℓ 3) - ⇑(ℓ 1) * ⇑(ℓ 1) * ⇑(ℓ 4) := by
    funext x
    simp [ahCubic, hankelCubic, ℓ]
    ring
  rw [heq]
  exact sub_mem (sub_mem (sub_mem (add_mem (h3 _ _ _) (Submodule.smul_mem _ _ (h3 _ _ _)))
    (h3 _ _ _)) (h3 _ _ _)) (h3 _ _ _)

/-- **`(4,3,7)` defectivity** for seven nonzero points in the open set `AHGeneric`. -/
theorem ah437_isDefective_of_generic (hp : AHGeneric p) (hp0 : ∀ k, p k ≠ 0) :
    IsDefective (fun k => (veroneseDegParam 4 3 (p k)).tangentSpace) :=
  isDefective_of_singular (by norm_num) p hp0 (by decide) (ahCubic_mem_veroneseForms p)
    (ahCubic_ne_zero hp) (ahCubic_singular hp)

/-! ### §E — Seven general points are `AHGeneric` -/

section Genericity

omit [CharZero 𝕜] in
/-- `ahMat` with the coordinates of the points as indeterminates. -/
def ahMatPoly : Matrix (Fin 5) (Fin 5) (MvPolynomial (Fin 7 × Fin 5) 𝕜) :=
  fun i j => MvPolynomial.X (Fin.castAdd 2 j, i)

omit [CharZero 𝕜] in
/-- `ahU` with the coordinates of the points as indeterminates. -/
def ahUPoly : Fin 5 → MvPolynomial (Fin 7 × Fin 5) 𝕜 :=
  (ahMatPoly (𝕜 := 𝕜)).adjugate *ᵥ fun i => MvPolynomial.X (5, i)

omit [CharZero 𝕜] in
/-- `ahW` with the coordinates of the points as indeterminates. -/
def ahWPoly : Fin 5 → MvPolynomial (Fin 7 × Fin 5) 𝕜 :=
  (ahMatPoly (𝕜 := 𝕜)).adjugate *ᵥ fun i => MvPolynomial.X (6, i)

omit [CharZero 𝕜] in
/-- The genericity polynomial: `det M · ∏ Uᵢ · ∏ Wᵢ · ∏_{i<j} (Uᵢ Wⱼ - Uⱼ Wᵢ)`. Off its zero
locus, the seven points are `AHGeneric`. -/
def ahGenericPoly : MvPolynomial (Fin 7 × Fin 5) 𝕜 :=
  (ahMatPoly (𝕜 := 𝕜)).det * (∏ i, ahUPoly i) * (∏ i, ahWPoly i) *
    ∏ ij ∈ (univ : Finset (Fin 5 × Fin 5)).filter (fun ij => ij.1 < ij.2),
      (ahUPoly ij.1 * ahWPoly ij.2 - ahUPoly ij.2 * ahWPoly ij.1)

omit [CharZero 𝕜] in
theorem eval_ahGenericPoly (p : Fin 7 → Fin 5 → 𝕜) :
    MvPolynomial.eval (fun ki => p ki.1 ki.2) ahGenericPoly
      = (ahMat p).det * (∏ i, ahU p i) * (∏ i, ahW p i) *
        ∏ ij ∈ (univ : Finset (Fin 5 × Fin 5)).filter (fun ij => ij.1 < ij.2),
          (ahU p ij.1 * ahW p ij.2 - ahU p ij.2 * ahW p ij.1) := by
  set φ := MvPolynomial.eval (fun ki : Fin 7 × Fin 5 => p ki.1 ki.2)
  have hmat : φ.mapMatrix ahMatPoly = ahMat p := by
    ext i j
    exact MvPolynomial.eval_X (f := fun ki : Fin 7 × Fin 5 => p ki.1 ki.2) (Fin.castAdd 2 j, i)
  have hvec : ∀ (k : Fin 7) (i : Fin 5),
      φ ((ahMatPoly.adjugate *ᵥ fun i => MvPolynomial.X (k, i)) i)
        = ((ahMat p).adjugate *ᵥ p k) i := fun k i => by
    rw [RingHom.map_mulVec, ← RingHom.mapMatrix_apply, RingHom.map_adjugate, hmat]
    congr 1
    funext i
    exact MvPolynomial.eval_X (f := fun ki : Fin 7 × Fin 5 => p ki.1 ki.2) (k, i)
  have hU : ∀ i, φ (ahUPoly i) = ahU p i := hvec 5
  have hW : ∀ i, φ (ahWPoly i) = ahW p i := hvec 6
  simp only [ahGenericPoly, map_mul, map_prod, map_sub, RingHom.map_det, hmat, hU, hW]

omit [CharZero 𝕜] in
/-- Off the zero locus of `ahGenericPoly`, the seven points are `AHGeneric`. -/
theorem ahGeneric_of_eval_ne_zero {p : Fin 7 → Fin 5 → 𝕜}
    (h : MvPolynomial.eval (fun ki => p ki.1 ki.2) ahGenericPoly ≠ 0) : AHGeneric p := by
  rw [eval_ahGenericPoly] at h
  obtain ⟨⟨⟨hdet, hU⟩, hW⟩, hUW⟩ := by simpa only [mul_ne_zero_iff] using h
  rw [prod_ne_zero_iff] at hU hW hUW
  refine ⟨hdet, fun i => hU i (mem_univ i), fun i => hW i (mem_univ i), fun i j hij => ?_⟩
  by_contra hne
  have hcross : ahU p i * ahW p j = ahU p j * ahW p i := by
    have := (div_eq_div_iff (hW i (mem_univ i)) (hW j (mem_univ j))).mp hij
    linear_combination this
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hUW (i, j) (by simp [hlt]) (sub_eq_zero.mpr hcross)
  · exact hUW (j, i) (by simp [hlt]) (sub_eq_zero.mpr hcross.symm)

/-- A witness configuration: the coordinate points `e₀, …, e₄`, the point `(1,1,1,1,1)` and
the point `(1,2,3,4,5)`. -/
def ahWitness : Fin 7 → Fin 5 → 𝕜 := fun k =>
  if h : (k : ℕ) < 5 then Pi.single ⟨k, h⟩ 1 else if (k : ℕ) = 5 then fun _ => 1
  else fun i => ((i : ℕ) : 𝕜) + 1

/-- The genericity polynomial is nonzero: it does not vanish at `ahWitness`. -/
theorem ahGenericPoly_ne_zero : (ahGenericPoly (𝕜 := 𝕜)) ≠ 0 := by
  intro h
  have h0 := congrArg (MvPolynomial.eval fun ki : Fin 7 × Fin 5 => ahWitness (𝕜 := 𝕜) ki.1 ki.2) h
  rw [eval_ahGenericPoly, map_zero] at h0
  have hmat : ahMat (ahWitness (𝕜 := 𝕜)) = 1 := by
    ext i j
    simp [ahMat, ahWitness, Matrix.one_apply, Pi.single_apply]
  have hU : ahU (ahWitness (𝕜 := 𝕜)) = fun _ => 1 := by
    rw [ahU, hmat, Matrix.adjugate_one, Matrix.one_mulVec]
    funext i
    simp [ahWitness]
  have hW : ahW (ahWitness (𝕜 := 𝕜)) = fun i : Fin 5 => ((i : ℕ) : 𝕜) + 1 := by
    rw [ahW, hmat, Matrix.adjugate_one, Matrix.one_mulVec]
    funext i
    simp [ahWitness]
  rw [hmat, hU, hW] at h0
  simp only [Matrix.det_one, prod_const_one, one_mul, mul_eq_zero, prod_eq_zero_iff,
    mem_filter, mem_univ, true_and] at h0
  rcases h0 with ⟨i, hi⟩ | ⟨ij, hij, hz⟩
  · exact Nat.cast_add_one_ne_zero (i : ℕ) hi
  · have : ((ij.2 : ℕ) : 𝕜) = (ij.1 : ℕ) := by linear_combination hz
    exact absurd (Fin.ext (Nat.cast_injective this)) (ne_of_gt hij)

/-- Seven general points of `𝕜⁵` are `AHGeneric`. -/
theorem forGeneralPoints_ahGeneric :
    ForGeneralPoints (𝕜 := 𝕜) 7 5 (fun p => AHGeneric p) :=
  ⟨ahGenericPoly, ahGenericPoly_ne_zero, fun _ hp => ahGeneric_of_eval_ne_zero hp⟩

end Genericity

/-- **`σ₇(v₃(ℙ⁴))` is defective at general points** (the `(4,3,7)` case). -/
theorem ah437_isDefective_general :
    ForGeneralPoints (𝕜 := 𝕜) 7 5
      (fun p => IsDefective (fun k => (veroneseDegParam 4 3 (p k)).tangentSpace)) :=
  (ForGeneralPoints.ne_zero.and forGeneralPoints_ahGeneric).mono fun _ h =>
    ah437_isDefective_of_generic h.2 h.1

end AlexanderHirschowitzCubic
