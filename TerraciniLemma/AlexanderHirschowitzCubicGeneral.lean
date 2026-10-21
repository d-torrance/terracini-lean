module

public import TerraciniLemma.CubicInductionMain
public import TerraciniLemma.AlexanderHirschowitzCubic
public import TerraciniLemma.CubicCertificates.cubicB0t1
public import TerraciniLemma.CubicCertificates.cubicB0t2
public import TerraciniLemma.CubicCertificates.cubicB0t3
public import TerraciniLemma.CubicCertificates.cubicB1t4
public import TerraciniLemma.CubicCertificates.cubicB1t5
public import TerraciniLemma.CubicCertificates.cubicB1t6
public import TerraciniLemma.CubicCertificates.cubicB2t7
public import TerraciniLemma.CubicCertificates.cubicB2t8
public import TerraciniLemma.CubicCertificates.cubicB2t9
public import TerraciniLemma.CubicCertificates.cubicB3
public import TerraciniLemma.CubicCertificates.cubicB0t1Sub
public import TerraciniLemma.CubicCertificates.cubicB1t4Sub
public import TerraciniLemma.CubicCertificates.cubicN4Fill
public import TerraciniLemma.CubicCertificates.cubicN4Indep
public import TerraciniLemma.CubicCertificates.cubicN3
public import TerraciniLemma.CubicCertificates.cubicN2Fill
public import TerraciniLemma.CubicCertificates.cubicN2Indep
public import TerraciniLemma.CubicCertificates.cubicN1
public import TerraciniLemma.CubicCertificates.cubicN0

/-!
# The Alexander–Hirschowitz theorem for cubics

`σ_r(v₃(ℙⁿ))` is nondefective for general points, except for `(n, r) = (4, 7)`
(`alexanderHirschowitz_cubic`).

For `n ≥ 5` we write `n = t + 4` and use the two chains of `TerraciniLemma.CubicInductionMain`:

* `s₂(t) = ⌈N/(n+1)⌉` general points fill the ambient space (the superabundant chain), hence so
  do more points;
* fewer points have independent tangent spaces: for `t ≢ 1 (mod 3)` because `n + 1` divides
  `N` and `s₂(t)` points fill, and for `t ≡ 1 (mod 3)` by the subabundant chain for
  `s₁(t) = ⌊N/(n+1)⌋` points.

The base cases of the chains, and the cases `n ≤ 4`, are rank certificates computed by
Macaulay2 and checked by the kernel (`TerraciniLemma.CubicCertificates`).
-/

@[expose] public section

noncomputable section AlexanderHirschowitzCubicGeneral

open CubicCertificates

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-! ### §A — Spans of the first `r` points of a sequence -/

section Spans

variable {n : ℕ} (q : ℕ → Fin (n + 1) → 𝕜)

/-- The span of the tangent spaces to `v₃` at the first `r` points of a sequence. -/
def tanSpan (r : ℕ) : Submodule 𝕜 (Sym (Fin (n + 1)) 3 → 𝕜) :=
  ⨆ k : Fin r, (veroneseDegParam n 3 (q k)).tangentSpace

omit [CharZero 𝕜] in
theorem tanSpan_mono {r r' : ℕ} (h : r ≤ r') : tanSpan q r ≤ tanSpan q r' :=
  iSup_le fun k => le_iSup_of_le (Fin.castLE h k) le_rfl

omit [CharZero 𝕜] in
theorem tanSpan_succ (r : ℕ) :
    tanSpan q (r + 1) = tanSpan q r ⊔ (veroneseDegParam n 3 (q r)).tangentSpace := by
  refine le_antisymm (iSup_le fun k => ?_)
    (sup_le (tanSpan_mono q (Nat.le_succ r)) (le_iSup_of_le (Fin.last r) le_rfl))
  induction k using Fin.lastCases with
  | last => exact le_sup_of_le_right le_rfl
  | cast k => exact le_sup_of_le_left (le_iSup_of_le k le_rfl)

omit [CharZero 𝕜] in
/-- Each further point adds at most `n + 1` dimensions. -/
theorem finrank_tanSpan_le {r r' : ℕ} (h : r ≤ r') :
    Module.finrank 𝕜 (tanSpan q r') ≤ Module.finrank 𝕜 (tanSpan q r) + (r' - r) * (n + 1) := by
  induction r', h using Nat.le_induction with
  | base => simp
  | succ r' h ih =>
    have hT : Module.finrank 𝕜 (veroneseDegParam n 3 (q r')).tangentSpace ≤ n + 1 :=
      (LinearMap.finrank_range_le (veroneseDegDeriv (𝕜 := 𝕜) n 3 (q r')).toLinearMap).trans
        (by simp)
    rw [tanSpan_succ, Nat.succ_sub h, Nat.succ_mul]
    have := Submodule.finrank_add_le_finrank_add_finrank (tanSpan q r')
      (veroneseDegParam n 3 (q r')).tangentSpace
    omega

omit [CharZero 𝕜] in
/-- If `r₀` points fill the ambient space, so do `r ≥ r₀` points. -/
theorem min_le_finrank_tanSpan_of_fill {r₀ r : ℕ}
    (hq : (n + 3).choose 3 ≤ Module.finrank 𝕜 (tanSpan q r₀)) (hr : r₀ ≤ r) :
    min ((n + 3).choose 3) (r * (n + 1)) ≤ Module.finrank 𝕜 (tanSpan q r) :=
  (min_le_left _ _).trans (hq.trans (Submodule.finrank_mono (tanSpan_mono q hr)))

omit [CharZero 𝕜] in
/-- If `r₀` points have independent tangent spaces, so do `r ≤ r₀` points. -/
theorem min_le_finrank_tanSpan_of_indep {r₀ r : ℕ}
    (hq : r₀ * (n + 1) ≤ Module.finrank 𝕜 (tanSpan q r₀)) (hr : r ≤ r₀) :
    min ((n + 3).choose 3) (r * (n + 1)) ≤ Module.finrank 𝕜 (tanSpan q r) := by
  refine (min_le_right _ _).trans ?_
  have h := finrank_tanSpan_le q hr
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [Nat.add_sub_cancel_left] at h
  rw [add_mul] at hq
  omega

end Spans

/-! ### §B — From configurations to sequences of points -/

/-- A lower bound for `A_{0,0}(t)` gives `s(t)` points with that lower bound. -/
theorem exists_seq_of_good {s : ℕ → ℕ} {t m : ℕ} (h : Good 𝕜 s t 0 0 m) :
    ∃ q : ℕ → Fin (t + 4 + 1) → 𝕜, m ≤ Module.finrank 𝕜 (tanSpan q (s t)) := by
  have := CharZero.infinite 𝕜
  obtain ⟨x, hx⟩ := HoldsGenerically.exists_point h
  have hcard : Fintype.card (Slot s t 0) = s t := by
    rw [Fintype.card_sigma]
    simp only [countAt, countFor, Nat.zero_sub, Fintype.card_fin]
    rw [Finset.sum_coe_sort (Finset.range 0).powerset (fun I => s (t - 3 * I.card))]
    simp
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨fun k => if hk : k < s t then configPoint x (e.symm ⟨k, hk⟩) else 0,
    hx.trans (Submodule.finrank_mono (sup_le ?_ (iSup_le fun σ => ?_)))⟩
  · intro f hf
    have : f = 0 := funext fun m => hf m (by simp [latticeSet])
    exact this ▸ zero_mem _
  · refine le_iSup_of_le (e σ) (le_of_eq ?_)
    beta_reduce
    rw [dite_eq_left (e σ).isLt, Fin.eta, Equiv.symm_apply_apply]

/-! ### §C — The base cases -/

omit [CharZero 𝕜] in
theorem Good.mono_target {s : ℕ → ℕ} {t K i m m' : ℕ} (h : Good 𝕜 s t K i m) (hm : m' ≤ m) :
    Good 𝕜 s t K i m' :=
  HoldsGenerically.mono h fun _ hx => hm.trans hx

/-- The nine points of the uniform case. -/
def cubicB3Points : Fin 3 → Fin 3 → List ℤ := fun j c => (cubicB3Data.getD j default).2.getD c []

theorem uniformData_cubicB3Points : uniformData cubicB3Points = cubicB3Data := by decide +kernel

theorem cubic_B₃ {s : ℕ → ℕ} : ∀ t, 10 ≤ t → Good 𝕜 s t 3 3 (Ncube t) := fun t ht =>
  good_three cubicB3Points (by rw [uniformData_cubicB3Points]; decide +kernel)
    (by rw [uniformData_cubicB3Points]; exact cubicB3Check)
    (by decide +kernel) (by omega)

theorem cubic_B₂ (s : ℕ → ℕ)
    (h7 : validPoints s 7 2 cubicB2t7Data = true) (h8 : validPoints s 8 2 cubicB2t8Data = true)
    (h9 : validPoints s 9 2 cubicB2t9Data = true) :
    ∀ t, 7 ≤ t → t ≤ 9 → Good 𝕜 s t 2 2 (Ncube t) := by
  intro t h₁ h₂
  interval_cases t
  · exact good_top_of_check h7 cubicB2t7Check (by decide +kernel)
  · exact good_top_of_check h8 cubicB2t8Check (by decide +kernel)
  · exact good_top_of_check h9 cubicB2t9Check (by decide +kernel)

theorem cubic_B₁ : ∀ t, 4 ≤ t → t ≤ 6 → Good 𝕜 s₂ t 1 1 (Ncube t) := by
  intro t h₁ h₂
  interval_cases t
  · exact good_top_of_check (by decide +kernel) cubicB1t4Check
      (by decide +kernel)
  · exact good_top_of_check (by decide +kernel) cubicB1t5Check
      (by decide +kernel)
  · exact good_top_of_check (by decide +kernel) cubicB1t6Check
      (by decide +kernel)

theorem cubic_B₀ : ∀ t, 1 ≤ t → t ≤ 3 → Good 𝕜 s₂ t 0 0 (Ncube t) := by
  intro t h₁ h₂
  interval_cases t
  · exact good_top_of_check (by decide +kernel) cubicB0t1Check
      (by decide +kernel)
  · exact good_top_of_check (by decide +kernel) cubicB0t2Check
      (by decide +kernel)
  · exact good_top_of_check (by decide +kernel) cubicB0t3Check
      (by decide +kernel)

theorem cubic_B₁_sub : Good 𝕜 s₁ 4 1 1 (Ncube 4 - 1) :=
  (good_of_check (by decide +kernel) cubicB1t4SubCheck).mono_target
    (by decide +kernel)

theorem cubic_B₀_sub : Good 𝕜 s₁ 1 0 0 (6 * s₁ 1) :=
  (good_zero_of_check (by decide +kernel) cubicB0t1SubCheck).mono_target
    (by decide +kernel)

/-! ### §D — Points for every `n` -/

/-- The superabundant chain, as points: `s₂(t)` points of `𝕜^{t+5}` filling the ambient
space. -/
theorem exists_seq_fill (t : ℕ) (ht : 1 ≤ t) :
    ∃ q : ℕ → Fin (t + 4 + 1) → 𝕜, Ncube t ≤ Module.finrank 𝕜 (tanSpan q (s₂ t)) :=
  exists_seq_of_good (super₀ s₂_add_three cubic_B₃
    (cubic_B₂ s₂ (by decide +kernel) (by decide +kernel) (by decide +kernel))
    cubic_B₁ cubic_B₀ t ht)

/-- The subabundant chain, as points: for `t ≡ 1 (mod 3)`, `s₁(t)` points of `𝕜^{t+5}` with
independent tangent spaces. -/
theorem exists_seq_indep (u : ℕ) :
    ∃ q : ℕ → Fin (3 * u + 1 + 4 + 1) → 𝕜,
      (3 * u + 1 + 5) * s₁ (3 * u + 1) ≤ Module.finrank 𝕜 (tanSpan q (s₁ (3 * u + 1))) :=
  exists_seq_of_good (sub₀ cubic_B₃
    (cubic_B₂ s₁ (by decide +kernel) (by decide +kernel) (by decide +kernel))
    cubic_B₁_sub cubic_B₀_sub u)

/-- For `t ≢ 1 (mod 3)`, `n + 1 = t + 5` divides `N(t)`: `6 ∣ (t+7)(t+6)`. -/
theorem six_mul_s₂ {t : ℕ} (ht : t % 3 ≠ 1) : 6 * s₂ t = (t + 7) * (t + 6) := by
  unfold s₂
  have h6 : (t + 7) * (t + 6) % 6 = 0 := by
    rcases (by omega : t % 6 = 0 ∨ t % 6 = 2 ∨ t % 6 = 3 ∨ t % 6 = 5) with h | h | h | h <;>
      simp [Nat.mul_mod, Nat.add_mod, h]
  omega

/-- The listed points of a certificate, as a sequence. -/
def listedSeq (n : ℕ) (data : LocatedPoints) : ℕ → Fin (n + 1) → 𝕜 :=
  fun k x => (((allPoints data).getD k []).getD x 0 : ℤ)

omit [CharZero 𝕜] in
theorem listedSpan_eq_tanSpan (n : ℕ) (data : LocatedPoints) :
    listedSpan (𝕜 := 𝕜) n data = tanSpan (listedSeq n data) (allPoints data).length := by
  refine iSup_congr fun k => congrArg (fun p => (veroneseDegParam n 3 p).tangentSpace) ?_
  funext x
  simp [listedSeq, List.getD_eq_getElem?_getD, Fin.getElem_fin]

/-- A small case: a certificate for `r` points of `𝕜^{n+1}` gives a sequence. -/
theorem exists_seq_of_check {n m : ℕ} {data : LocatedPoints} {c : RankCertificate.Cert}
    (hc : RankCertificate.check (baseMatrix (n + 1) 0 data) (baseRows (n + 1) 0).length
      ((allPoints data).length * (n + 1)) c = true) (hm : m ≤ c.rows.length) :
    ∃ q : ℕ → Fin (n + 1) → 𝕜, m ≤ Module.finrank 𝕜 (tanSpan q (allPoints data).length) :=
  ⟨listedSeq n data, hm.trans ((listedSpan_eq_tanSpan (𝕜 := 𝕜) n data) ▸
    le_finrank_listedSpan_of_check hc)⟩

/-- **Nondefective configurations exist** for every `(n, r) ≠ (4, 7)`: some `r` points of
`𝕜^{n+1}` have tangent spaces spanning a space of the expected dimension. -/
theorem exists_seq_nondefective (n r : ℕ) (h : ¬ (n = 4 ∧ r = 7)) :
    ∃ q : ℕ → Fin (n + 1) → 𝕜,
      min ((n + 3).choose 3) (r * (n + 1)) ≤ Module.finrank 𝕜 (tanSpan q r) := by
  -- the small cases, from certificates `(fill, indep)` with `fill` points filling and `indep`
  -- points independent
  have small : ∀ {n : ℕ} (fill indep : ℕ) {d₁ d₂ : LocatedPoints} {c₁ c₂ : RankCertificate.Cert},
      RankCertificate.check (baseMatrix (n + 1) 0 d₁) (baseRows (n + 1) 0).length
        ((allPoints d₁).length * (n + 1)) c₁ = true →
      RankCertificate.check (baseMatrix (n + 1) 0 d₂) (baseRows (n + 1) 0).length
        ((allPoints d₂).length * (n + 1)) c₂ = true →
      (allPoints d₁).length = fill → (allPoints d₂).length = indep →
      (n + 3).choose 3 ≤ c₁.rows.length → indep * (n + 1) ≤ c₂.rows.length →
      ∀ r, (fill ≤ r ∨ r ≤ indep) → ∃ q : ℕ → Fin (n + 1) → 𝕜,
        min ((n + 3).choose 3) (r * (n + 1)) ≤ Module.finrank 𝕜 (tanSpan q r) := by
    intro n fill indep d₁ d₂ c₁ c₂ hc₁ hc₂ hl₁ hl₂ hr₁ hr₂ r hr
    rcases hr with hr | hr
    · obtain ⟨q, hq⟩ := exists_seq_of_check (𝕜 := 𝕜) hc₁ hr₁
      exact ⟨q, min_le_finrank_tanSpan_of_fill q (hl₁ ▸ hq) hr⟩
    · obtain ⟨q, hq⟩ := exists_seq_of_check (𝕜 := 𝕜) hc₂ hr₂
      exact ⟨q, min_le_finrank_tanSpan_of_indep q (hl₂ ▸ hq) hr⟩
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n) with
    rfl | rfl | rfl | rfl | rfl | hn
  · exact small 1 1 cubicN0Check cubicN0Check (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) r (by omega)
  · exact small 2 2 cubicN1Check cubicN1Check (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) r (by omega)
  · exact small 4 3 cubicN2FillCheck cubicN2IndepCheck (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) r (by omega)
  · exact small 5 5 cubicN3Check cubicN3Check (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) r (by omega)
  · exact small 8 6 cubicN4FillCheck cubicN4IndepCheck (by decide) (by decide)
      (by decide +kernel) (by decide +kernel) r (by omega)
  -- `n = t + 4` with `t ≥ 1`
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 4 := ⟨n - 4, by omega⟩
  obtain ⟨q, hq⟩ := exists_seq_fill (𝕜 := 𝕜) t (by omega)
  by_cases hr : s₂ t ≤ r
  · exact ⟨q, min_le_finrank_tanSpan_of_fill q hq hr⟩
  by_cases ht : t % 3 = 1
  · -- `r ≤ s₁(t)` points: the subabundant chain
    obtain ⟨u, rfl⟩ : ∃ u, t = 3 * u + 1 := ⟨t / 3, by omega⟩
    obtain ⟨q', hq'⟩ := exists_seq_indep (𝕜 := 𝕜) u
    have hk := six_mul_s₁ u
    have hs : s₂ (3 * u + 1) = s₁ (3 * u + 1) + 1 := by unfold s₂; omega
    exact ⟨q', min_le_finrank_tanSpan_of_indep q' (by rw [mul_comm]; exact hq') (by omega)⟩
  · -- `r < s₂(t)` points, where `s₂(t)(t+5) = N(t)`
    have h6 := six_mul_s₂ ht
    have hN := six_mul_Ncube t
    have hfill : s₂ t * (t + 4 + 1) ≤ Module.finrank 𝕜 (tanSpan q (s₂ t)) := by
      refine le_trans (le_of_eq ?_) hq
      have : 6 * (s₂ t * (t + 5)) = 6 * Ncube t := by rw [hN, ← h6]; ring
      rw [show t + 4 + 1 = t + 5 by ring]
      omega
    exact ⟨q, min_le_finrank_tanSpan_of_indep q hfill (by omega)⟩

/-! ### §E — The theorem -/

/-- **The Alexander–Hirschowitz theorem for cubics**: for `r` general points, `σ_r(v₃(ℙⁿ))`
is defective if and only if `(n, r) = (4, 7)`. -/
theorem alexanderHirschowitz_cubic (n r : ℕ) :
    ForGeneralPoints (𝕜 := 𝕜) r (n + 1) (fun p =>
      IsDefective (fun k => (veroneseDegParam n 3 (p k)).tangentSpace) ↔ n = 4 ∧ r = 7) := by
  by_cases h : n = 4 ∧ r = 7
  · obtain ⟨rfl, rfl⟩ := h
    exact ah437_isDefective_general.mono fun _ hp => iff_of_true hp ⟨rfl, rfl⟩
  obtain ⟨q, hq⟩ := exists_seq_nondefective (𝕜 := 𝕜) n r h
  refine (forGeneralPoints_le_finrank_iSup (fun k : Fin r => q k) hq).mono fun p hp =>
    iff_of_false ?_ h
  unfold IsDefective
  exact not_lt.mpr ((expectedDim_veroneseDegParam_le p).trans hp)

end AlexanderHirschowitzCubicGeneral
