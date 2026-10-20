module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Generic properties and semicontinuity of rank

A property of points `x : σ → 𝕜` *holds generically* (`HoldsGenerically`) if it holds off the
zero locus of a nonzero polynomial in the coordinates. Over an infinite field such a locus is a
proper Zariski-closed set, so this is the classical meaning of "for general `x`".

For a matrix `M` whose entries are polynomials in `x`, the rank of `M(x)` is **lower
semicontinuous**: `rank M(x) ≥ k` is the non-vanishing of some `k × k` minor, an open condition.
Hence:

* `HoldsGenerically.le_rank`: if `rank M(x₀) ≥ k` at a *single* point `x₀`, then
  `rank M(x) ≥ k` for general `x`;
* `HoldsGenerically.rank_le`: if `rank M(x) ≤ k` for general `x`, then it holds for *every* `x`
  (a closed condition holding on a dense set holds everywhere).

These are the two halves of the specialization principle used throughout the
Alexander–Hirschowitz theorem: non-defectivity can be checked at one (special) configuration,
and defectivity at general points propagates to all configurations.

The linear-algebra input is `Matrix.le_rank_iff_exists_submatrix_det_ne_zero`: over a field,
`k ≤ rank A` iff some `k × k` minor of `A` is nonzero.

`ForGeneralPoints r m P` specializes `HoldsGenerically` to `r`-tuples of points of `𝕜^m`.
-/

@[expose] public section

noncomputable section Semicontinuity

open MvPolynomial

/-! ### §A — Rank and minors -/

section Minors

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- From a finite family spanning a subspace of dimension `≥ k`, one can extract `k` linearly
independent members. -/
theorem exists_linearIndependent_fin_of_le_finrank_span {ι : Type*} [Finite ι] (v : ι → V)
    {k : ℕ} (hk : k ≤ Module.finrank K (Submodule.span K (Set.range v))) :
    ∃ g : Fin k → ι, LinearIndependent K (v ∘ g) := by
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K v
  have : Finite κ := Finite.of_injective a ha
  have := Fintype.ofFinite κ
  rw [← hspan, finrank_span_eq_card hli] at hk
  let e : Fin k ↪ κ := (Fin.castLEEmb hk).trans (Fintype.equivFin κ).symm.toEmbedding
  exact ⟨a ∘ e, hli.comp e e.injective⟩

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- If `A` has rank `≥ k`, some `k × k` minor of `A` is nonzero. -/
theorem Matrix.exists_submatrix_det_ne_zero {A : Matrix ι κ K} {k : ℕ} (hk : k ≤ A.rank) :
    ∃ (f : Fin k → ι) (g : Fin k → κ), (A.submatrix f g).det ≠ 0 := by
  classical
  rw [Matrix.rank_eq_finrank_span_cols] at hk
  obtain ⟨g, hg⟩ := exists_linearIndependent_fin_of_le_finrank_span A.col hk
  -- the `k` independent columns form a matrix of rank `k`, which has `k` independent rows
  have hB : k ≤ (A.submatrix id g).rank := by
    rw [Matrix.rank_eq_finrank_span_cols]
    exact (finrank_span_eq_card (b := (A.submatrix id g).col) hg).trans (Fintype.card_fin k)
      |>.ge
  rw [Matrix.rank_eq_finrank_span_row] at hB
  obtain ⟨f, hf⟩ := exists_linearIndependent_fin_of_le_finrank_span (A.submatrix id g).row hB
  refine ⟨f, g, ?_⟩
  exact ((Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.linearIndependent_row_iff_isUnit.mp hf)).ne_zero

omit [Fintype ι] in
/-- A nonzero `k × k` minor forces rank `≥ k`. -/
theorem Matrix.le_rank_of_submatrix_det_ne_zero {A : Matrix ι κ K} {k : ℕ} (f : Fin k → ι)
    (g : Fin k → κ) (h : (A.submatrix f g).det ≠ 0) : k ≤ A.rank := by
  classical
  have := Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr h.isUnit)
  rw [Fintype.card_fin] at this
  exact this ▸ Matrix.rank_submatrix_le A f g

/-- Over a field, `k ≤ rank A` iff some `k × k` minor of `A` is nonzero. -/
theorem Matrix.le_rank_iff_exists_submatrix_det_ne_zero {A : Matrix ι κ K} {k : ℕ} :
    k ≤ A.rank ↔ ∃ (f : Fin k → ι) (g : Fin k → κ), (A.submatrix f g).det ≠ 0 :=
  ⟨Matrix.exists_submatrix_det_ne_zero, fun ⟨f, g, h⟩ => Matrix.le_rank_of_submatrix_det_ne_zero f g h⟩

end Minors

/-! ### §B — Generic properties -/

section Generic

variable {𝕜 : Type*} [Field 𝕜] {σ : Type*}

/-- `P` **holds generically**: there is a nonzero polynomial `G` in the coordinates such that
`P x` holds whenever `G(x) ≠ 0`. -/
def HoldsGenerically (σ : Type*) (P : (σ → 𝕜) → Prop) : Prop :=
  ∃ G : MvPolynomial σ 𝕜, G ≠ 0 ∧ ∀ x, eval x G ≠ 0 → P x

namespace HoldsGenerically

variable {P Q : (σ → 𝕜) → Prop}

theorem mono (h : HoldsGenerically σ P) (hPQ : ∀ x, P x → Q x) : HoldsGenerically σ Q :=
  let ⟨G, hG, hP⟩ := h
  ⟨G, hG, fun x hx => hPQ x (hP x hx)⟩

theorem of_forall (h : ∀ x, P x) : HoldsGenerically σ P :=
  ⟨1, one_ne_zero, fun x _ => h x⟩

theorem and (hP : HoldsGenerically σ P) (hQ : HoldsGenerically σ Q) :
    HoldsGenerically σ (fun x => P x ∧ Q x) := by
  obtain ⟨G, hG, hGP⟩ := hP
  obtain ⟨H, hH, hHQ⟩ := hQ
  refine ⟨G * H, mul_ne_zero hG hH, fun x hx => ?_⟩
  rw [map_mul] at hx
  exact ⟨hGP x (left_ne_zero_of_mul hx), hHQ x (right_ne_zero_of_mul hx)⟩

variable [Infinite 𝕜]

/-- A generic property holds somewhere (over an infinite field): the notion is never
vacuous. -/
theorem exists_point (h : HoldsGenerically σ P) : ∃ x, P x := by
  obtain ⟨G, hG, hP⟩ := h
  by_contra! hno
  exact hG (MvPolynomial.funext fun x => by_contra fun hx => hno x (hP x (by simpa using hx)))

/-- A polynomial vanishing generically vanishes identically. -/
theorem eq_zero {Q : MvPolynomial σ 𝕜} (h : HoldsGenerically σ fun x => eval x Q = 0) : Q = 0 := by
  obtain ⟨G, hG, hQ⟩ := h
  have hGQ : G * Q = 0 := MvPolynomial.funext fun x => by
    rw [map_mul, map_zero]
    by_cases hx : eval x G = 0
    · rw [hx, zero_mul]
    · rw [hQ x hx, mul_zero]
  exact (mul_eq_zero.mp hGQ).resolve_left hG

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Infinite 𝕜] [Fintype ι] [Fintype κ] in
theorem eval_det_submatrix (M : Matrix ι κ (MvPolynomial σ 𝕜)) {k : ℕ} (f : Fin k → ι)
    (g : Fin k → κ) (x : σ → 𝕜) :
    eval x (M.submatrix f g).det = ((M.map (eval x)).submatrix f g).det := by
  rw [RingHom.map_det]
  rfl

omit [Infinite 𝕜] in
/-- **Lower semicontinuity of rank.** If a matrix of polynomials has rank `≥ k` at one point,
it has rank `≥ k` at general points: some `k × k` minor is nonzero at `x₀`, hence a nonzero
polynomial, and wherever it does not vanish the rank is `≥ k`. -/
theorem le_rank (M : Matrix ι κ (MvPolynomial σ 𝕜)) {k : ℕ} (x₀ : σ → 𝕜)
    (hk : k ≤ (M.map (eval x₀)).rank) :
    HoldsGenerically σ fun x => k ≤ (M.map (eval x)).rank := by
  obtain ⟨f, g, hfg⟩ := Matrix.exists_submatrix_det_ne_zero hk
  refine ⟨(M.submatrix f g).det, fun h => hfg ?_, fun x hx => ?_⟩
  · rw [← eval_det_submatrix, h, map_zero]
  · rw [eval_det_submatrix] at hx
    exact Matrix.le_rank_of_submatrix_det_ne_zero f g hx

/-- **Rank bounds propagate from general points to all points.** If a matrix of polynomials
has rank `≤ k` at general points, it has rank `≤ k` everywhere: every `(k+1) × (k+1)` minor
vanishes generically, hence identically. -/
theorem rank_le (M : Matrix ι κ (MvPolynomial σ 𝕜)) {k : ℕ}
    (h : HoldsGenerically σ fun x => (M.map (eval x)).rank ≤ k) (x : σ → 𝕜) :
    (M.map (eval x)).rank ≤ k := by
  by_contra! hlt
  obtain ⟨f, g, hfg⟩ := Matrix.exists_submatrix_det_ne_zero (Nat.succ_le_of_lt hlt)
  have hzero : (M.submatrix f g).det = 0 := eq_zero <| h.mono fun y hy => by
    by_contra hne
    rw [eval_det_submatrix] at hne
    exact absurd (Matrix.le_rank_of_submatrix_det_ne_zero f g hne) (by omega)
  rw [← eval_det_submatrix, hzero, map_zero] at hfg
  exact hfg rfl

end HoldsGenerically

end Generic

/-! ### §C — General points -/

section GeneralPoints

variable {𝕜 : Type*} [Field 𝕜]

/-- `P` holds **for general `r`-tuples of points of `𝕜^m`**: there is a nonzero polynomial `G`
in the `r·m` coordinates such that `P p` holds whenever `G(p) ≠ 0`. This is `HoldsGenerically`
for the coordinates `Fin r × Fin m` (`forGeneralPoints_iff_holdsGenerically`). -/
def ForGeneralPoints (r m : ℕ) (P : (Fin r → Fin m → 𝕜) → Prop) : Prop :=
  ∃ G : MvPolynomial (Fin r × Fin m) 𝕜, G ≠ 0 ∧
    ∀ p : Fin r → Fin m → 𝕜, eval (fun ki => p ki.1 ki.2) G ≠ 0 → P p

theorem forGeneralPoints_iff_holdsGenerically {r m : ℕ} {P : (Fin r → Fin m → 𝕜) → Prop} :
    ForGeneralPoints r m P ↔
      HoldsGenerically (Fin r × Fin m) (fun x => P fun k i => x (k, i)) :=
  ⟨fun ⟨G, hG, hP⟩ => ⟨G, hG, fun _ hx => hP _ hx⟩,
    fun ⟨G, hG, hP⟩ => ⟨G, hG, fun p hp => hP (fun ki => p ki.1 ki.2) hp⟩⟩

namespace ForGeneralPoints

variable {r m : ℕ} {P Q : (Fin r → Fin m → 𝕜) → Prop}

theorem mono (h : ForGeneralPoints r m P) (hPQ : ∀ p, P p → Q p) : ForGeneralPoints r m Q :=
  let ⟨G, hG, hP⟩ := h
  ⟨G, hG, fun p hp => hPQ p (hP p hp)⟩

theorem of_forall (h : ∀ p, P p) : ForGeneralPoints r m P :=
  ⟨1, one_ne_zero, fun p _ => h p⟩

theorem and (hP : ForGeneralPoints r m P) (hQ : ForGeneralPoints r m Q) :
    ForGeneralPoints r m (fun p => P p ∧ Q p) := by
  obtain ⟨G, hG, hGP⟩ := hP
  obtain ⟨H, hH, hHQ⟩ := hQ
  refine ⟨G * H, mul_ne_zero hG hH, fun p hp => ?_⟩
  rw [map_mul] at hp
  exact ⟨hGP p (left_ne_zero_of_mul hp), hHQ p (right_ne_zero_of_mul hp)⟩

/-- A property of general points holds for *some* points (over an infinite field). -/
theorem exists_point [Infinite 𝕜] (h : ForGeneralPoints r m P) : ∃ p, P p :=
  let ⟨_, hx⟩ := (forGeneralPoints_iff_holdsGenerically.mp h).exists_point
  ⟨_, hx⟩

/-- General points are nonzero (here: have nonzero first coordinate). -/
theorem ne_zero {m : ℕ} : ForGeneralPoints (𝕜 := 𝕜) r (m + 1) (fun p => ∀ k, p k ≠ 0) := by
  classical
  refine ⟨∏ k, X (k, 0), ?_, fun p hp k hk => ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    exact fun k _ => X_ne_zero _
  · rw [map_prod, Finset.prod_ne_zero_iff] at hp
    simpa [hk] using hp k (Finset.mem_univ _)

end ForGeneralPoints

end GeneralPoints

end Semicontinuity
