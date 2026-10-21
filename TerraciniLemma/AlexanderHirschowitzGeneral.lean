module

public import TerraciniLemma.AHStep
public import TerraciniLemma.AlexanderHirschowitz
public import TerraciniLemma.AlexanderHirschowitzCubicGeneral
public import TerraciniLemma.AHArith
public import TerraciniLemma.AHCertificates.ahN5D4

/-!
# The Alexander–Hirschowitz theorem

`AH_{n,d}(k)` (`AHHolds 𝕜 n d k`): some `k` points of `𝕜^{n+1}` have tangent spaces to `v_d`
spanning a space of the expected dimension `min (N, k(n+1))`, `N = binom(n+d, d)`.

* §A — basic facts: monotonicity in `k` (`AHHolds.of_fill`, `AHHolds.of_indep`), so the two
  critical values `⌊N/(n+1)⌋` and `⌈N/(n+1)⌉` suffice (`AHHolds.of_critical`); `ℙ⁰`, degree
  `1`, quadrics and cubics from the earlier files; the rational normal curves `ℙ¹`, by the
  Horace step (`AHHolds.horace`).
-/

@[expose] public section

noncomputable section AlexanderHirschowitzGeneral

open CubicCertificates AHArith

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-! ### §A — Basic facts -/

section Basic

variable {n d k : ℕ}

omit [CharZero 𝕜] in
theorem AHHolds.of_seq {q : ℕ → Fin (n + 1) → 𝕜}
    (h : min ((n + d).choose d) (k * (n + 1)) ≤ Module.finrank 𝕜 (tanSpan q k d)) :
    AHHolds 𝕜 n d k :=
  ⟨fun i => q i, h⟩

omit [CharZero 𝕜] in
theorem AHHolds.exists_seq (h : AHHolds 𝕜 n d k) : ∃ q : ℕ → Fin (n + 1) → 𝕜,
    min ((n + d).choose d) (k * (n + 1)) ≤ Module.finrank 𝕜 (tanSpan q k d) := by
  obtain ⟨p, hp⟩ := h
  refine ⟨fun i => if hi : i < k then p ⟨i, hi⟩ else 0, ?_⟩
  have : tanSpan (fun i => if hi : i < k then p ⟨i, hi⟩ else 0) k d
      = ⨆ i, (veroneseDegParam n d (p i)).tangentSpace := by
    unfold tanSpan
    exact iSup_congr fun i => by beta_reduce; rw [dite_eq_left i.isLt]
  rw [this]
  exact hp

omit [CharZero 𝕜] in
/-- If `k₀` points fill the ambient space, so do `k ≥ k₀` points. -/
theorem AHHolds.of_fill {k₀ : ℕ} (h : AHHolds 𝕜 n d k₀) (hk₀ : (n + d).choose d ≤ k₀ * (n + 1))
    (hk : k₀ ≤ k) : AHHolds 𝕜 n d k := by
  obtain ⟨q, hq⟩ := h.exists_seq
  exact AHHolds.of_seq (min_le_finrank_tanSpan_of_fill q ((min_eq_left hk₀).symm ▸ hq) hk)

omit [CharZero 𝕜] in
/-- If `k₀` points have independent tangent spaces, so do `k ≤ k₀` points. -/
theorem AHHolds.of_indep {k₀ : ℕ} (h : AHHolds 𝕜 n d k₀)
    (hk₀ : k₀ * (n + 1) ≤ (n + d).choose d) (hk : k ≤ k₀) : AHHolds 𝕜 n d k := by
  obtain ⟨q, hq⟩ := h.exists_seq
  exact AHHolds.of_seq (min_le_finrank_tanSpan_of_indep q ((min_eq_right hk₀).symm ▸ hq) hk)

omit [CharZero 𝕜] in
/-- **The critical values suffice.** `AH` at `⌊N/(n+1)⌋` and `⌈N/(n+1)⌉` points gives it for
every number of points. -/
theorem AHHolds.of_critical
    (h₁ : AHHolds 𝕜 n d ((n + d).choose d / (n + 1)))
    (h₂ : AHHolds 𝕜 n d (((n + d).choose d + n) / (n + 1))) (k : ℕ) : AHHolds 𝕜 n d k := by
  set N := (n + d).choose d
  have hle₁ : N / (n + 1) * (n + 1) ≤ N := Nat.div_mul_le_self N (n + 1)
  have hle₂ : N ≤ (N + n) / (n + 1) * (n + 1) := by
    have h1 := Nat.div_add_mod (N + n) (n + 1)
    have h2 := Nat.mod_lt (N + n) (by omega : 0 < n + 1)
    rw [mul_comm] at h1
    omega
  have hK : (N + n) / (n + 1) ≤ N / (n + 1) + 1 := by
    rw [← Nat.add_div_right N (Nat.succ_pos n)]
    exact Nat.div_le_div_right (by omega)
  by_cases hk : k ≤ N / (n + 1)
  · exact h₁.of_indep hle₁ hk
  · exact h₂.of_fill hle₂ (by omega)

omit [CharZero 𝕜] in
theorem AHHolds.zero (n d : ℕ) : AHHolds 𝕜 n d 0 :=
  ⟨Fin.elim0, by simp⟩

/-- A single nonzero point gives tangent space of dimension `n + 1`. -/
theorem AHHolds.of_tangent_top {n d : ℕ} (hd : 1 ≤ d) (hN : (n + d).choose d ≤ n + 1)
    (k : ℕ) : AHHolds 𝕜 n d k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact AHHolds.zero n d
  refine ⟨fun _ => Pi.single 0 1, le_trans (min_le_left _ _) (hN.trans ?_)⟩
  have h1 := finrank_tangentSpace_veroneseDegParam (𝕜 := 𝕜) n d hd (v := Pi.single 0 1)
    (by simp [funext_iff, Pi.single_apply])
  refine (le_of_eq h1.symm).trans ?_
  exact Submodule.finrank_mono (le_iSup (fun i : Fin k =>
    (veroneseDegParam n d ((fun _ => Pi.single 0 1) i)).tangentSpace) ⟨0, hk⟩)

/-- `ℙ⁰`: the ambient space has dimension `1`. -/
theorem AHHolds.dim_zero {d : ℕ} (hd : 1 ≤ d) (k : ℕ) : AHHolds 𝕜 0 d k :=
  AHHolds.of_tangent_top hd (by simp) k

/-- Degree `1`: a tangent space is the whole space. -/
theorem AHHolds.deg_one (n k : ℕ) : AHHolds 𝕜 n 1 k :=
  AHHolds.of_tangent_top le_rfl (by simp) k

/-- **Quadrics**: `AH_{n,2}(k)` unless `2 ≤ k ≤ n`. -/
theorem AHHolds.quadric {n k : ℕ} (hk : ¬ (2 ≤ k ∧ k ≤ n)) : AHHolds 𝕜 n 2 k := by
  have : Infinite 𝕜 := CharZero.infinite 𝕜
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact AHHolds.zero n 2
  obtain ⟨p, hp, hne⟩ := ((alexanderHirschowitz_quadric (𝕜 := 𝕜) (n := n) hk1).and
    ForGeneralPoints.ne_zero).exists_point
  refine ⟨p, ?_⟩
  have hnd : ¬ IsDefective (fun i => (veroneseDegParam n 2 (p i)).tangentSpace) :=
    fun h => hk (hp.mp h)
  unfold IsDefective at hnd
  rw [expectedDim_veroneseDegParam (by norm_num) p hne] at hnd
  exact not_lt.mp hnd

/-- **Cubics**: `AH_{n,3}(k)` unless `(n, k) = (4, 7)`. -/
theorem AHHolds.cubic {n k : ℕ} (hk : ¬ (n = 4 ∧ k = 7)) : AHHolds 𝕜 n 3 k := by
  obtain ⟨q, hq⟩ := exists_seq_nondefective (𝕜 := 𝕜) n k hk
  exact AHHolds.of_seq hq

/-- **Rational normal curves**: `AH_{1,d}(k)` for all `d ≥ 1` and `k`, by the Horace step with
the trace in `ℙ⁰`. -/
theorem AHHolds.line : ∀ d, 1 ≤ d → ∀ k, AHHolds 𝕜 1 d k := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro hd k
  rcases (by omega : d = 1 ∨ d = 2 ∨ 3 ≤ d) with rfl | rfl | hd3
  · exact AHHolds.deg_one 1 k
  · exact AHHolds.quadric (by omega)
  obtain ⟨D, rfl⟩ : ∃ D, d = D + 2 := ⟨d - 2, by omega⟩
  have hc1 : (0 + (D + 2)).choose (D + 2) = 1 := by simp
  have hc2 : (0 + 1 + (D + 1)).choose (D + 1) = D + 2 := by
    rw [show 0 + 1 + (D + 1) = (D + 1) + 1 by ring, Nat.choose_succ_self_right]
  have hc3 : (0 + 1 + D).choose D = D + 1 := by
    rw [show 0 + 1 + D = D + 1 by ring, Nat.choose_succ_self_right]
  have key : ∀ k, D + 1 ≤ 2 * k → 2 * k ≤ D + 4 → AHHolds 𝕜 1 (D + 2) k := by
    intro k hk1 hk2
    by_cases hk : 2 * k ≤ D + 2
    · refine AHHolds.horace (n := 0) (d := D) (u := 0) (ε := 0) (by omega) le_rfl le_rfl
        (by omega) ?_ ?_ (AHHolds.dim_zero (by omega) 0) (ih _ (by omega) (by omega) _)
        (ih _ (by omega) (by omega) _)
      · rw [hc1, hc2]; left; omega
      · rw [hc3]; omega
    · refine AHHolds.horace (n := 0) (d := D) (u := 1) (ε := 0) (by omega) le_rfl (by omega)
        (by omega) ?_ ?_ (AHHolds.dim_zero (by omega) 1) (ih _ (by omega) (by omega) _)
        (ih _ (by omega) (by omega) _)
      · rw [hc1, hc2]
        by_cases h3 : 2 * k = D + 3
        · left; omega
        · right; omega
      · rw [hc3]; omega
  have hN : (1 + (D + 2)).choose (D + 2) = D + 3 := by
    rw [show 1 + (D + 2) = (D + 2) + 1 by ring, Nat.choose_succ_self_right]
  refine AHHolds.of_critical ?_ ?_ k
  · rw [hN]; exact key _ (by omega) (by omega)
  · rw [hN]; exact key _ (by omega) (by omega)

end Basic

/-! ### §B — The induction -/

section Induction

/-- The Horace step for the standard choice of `u` and `ε` (`AHArith.StepOK`). -/
theorem AHHolds.of_stepOK {n d k : ℕ} (hd : 1 ≤ d) (h : StepOK n d k)
    (htr : ∀ u, ¬ IsAHException n (d + 2) u → AHHolds 𝕜 n (d + 2) u)
    (hres : ∀ j, ¬ IsAHException (n + 1) (d + 1) j → AHHolds 𝕜 (n + 1) (d + 1) j)
    (hres₂ : ∀ j, ¬ IsAHException (n + 1) d j → AHHolds 𝕜 (n + 1) d j) :
    AHHolds 𝕜 (n + 1) (d + 2) k := by
  simp only [StepOK, StepOKv] at h
  obtain ⟨hA, hεu, hC, hD, -, h1, h2, h3⟩ := h
  have hεn : (k * (n + 2) - (n + 1 + (d + 1)).choose (d + 1)) % (n + 1) ≤ n :=
    Nat.le_of_lt_succ (Nat.mod_lt _ (by omega))
  refine AHHolds.step hd hεn hεu hC ?_ hD (htr _ h1) (hres _ h2) (hres₂ _ h3)
  have := Nat.div_add_mod (k * (n + 2) - (n + 1 + (d + 1)).choose (d + 1)) (n + 1)
  omega

/-- `AH_{5,4}(21)`, from a rank certificate. -/
theorem AHHolds.n5d4 : AHHolds 𝕜 5 4 21 := by
  have hv : DegreeCertificate.validRows 6 4 (DegreeCertificate.allMonos 6 4) = true := by
    decide +kernel
  have hc := DegreeCertificate.le_finrank_of_check (𝕜 := 𝕜) hv
    AHCertificates.ahN5D4Check
  have hlen : AHCertificates.ahN5D4Data.length = 21 := by decide +kernel
  have hrows : AHCertificates.ahN5D4Cert.rows.length = 126 := by decide +kernel
  refine ⟨fun i => fun x => ((AHCertificates.ahN5D4Data[Fin.cast hlen.symm i].getD x 0 : ℤ) : 𝕜),
    ?_⟩
  rw [hrows] at hc
  have hS := ((finCongr hlen).symm.iSup_comp (g := fun k : Fin AHCertificates.ahN5D4Data.length =>
    (veroneseDegParam 5 4 (fun x => ((AHCertificates.ahN5D4Data[k].getD x 0 : ℤ) : 𝕜))).tangentSpace))
  rw [← hS] at hc
  exact le_trans (by decide) hc

/-- **The Alexander–Hirschowitz theorem**, in the form `AH_{n,d}(k)`: outside the exceptions,
some `k` points of `𝕜^{n+1}` have tangent spaces to `v_d` spanning `min(N, k(n+1))`
dimensions. -/
theorem ahHolds_of_not_exception : ∀ n d k, 1 ≤ d → ¬ IsAHException n d k →
    AHHolds 𝕜 n d k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ihd =>
  intro k hd hexc
  rw [isAHException_iff] at hexc
  rcases (by omega : n = 0 ∨ n = 1 ∨ 2 ≤ n) with rfl | rfl | hn
  · exact AHHolds.dim_zero hd k
  · exact AHHolds.line d hd k
  rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3 ∨ 4 ≤ d) with rfl | rfl | rfl | hd4
  · exact AHHolds.deg_one n k
  · exact AHHolds.quadric (by omega)
  · exact AHHolds.cubic (by omega)
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
  -- the inputs of the step, by induction
  have htr : ∀ u, ¬ IsAHException n' (d' + 2) u → AHHolds 𝕜 n' (d' + 2) u :=
    fun u h => ihn n' (by omega) (d' + 2) u (by omega) h
  have hres : ∀ j, ¬ IsAHException (n' + 1) (d' + 1) j → AHHolds 𝕜 (n' + 1) (d' + 1) j :=
    fun j h => ihd (d' + 1) (by omega) j (by omega) h
  have hres₂ : ∀ j, ¬ IsAHException (n' + 1) d' j → AHHolds 𝕜 (n' + 1) d' j :=
    fun j h => ihd d' (by omega) j (by omega) h
  -- the Horace step with explicit `u` and `ε`
  have H : ∀ {k u ε : ℕ}, 1 ≤ d' → ε ≤ n' → ε ≤ u → u + ε ≤ k →
      (((n' + 1) * u + ε ≤ (n' + (d' + 2)).choose (d' + 2) ∧
          (k - u) * (n' + 2) + u ≤ (n' + 1 + (d' + 1)).choose (d' + 1) + ε) ∨
        ((n' + (d' + 2)).choose (d' + 2) ≤ (n' + 1) * u + ε ∧
          (n' + 1 + (d' + 1)).choose (d' + 1) + ε ≤ (k - u) * (n' + 2) + u)) →
      (n' + 1 + d').choose d' ≤ (k - u - ε) * (n' + 2) →
      ¬ IsAHException n' (d' + 2) u → ¬ IsAHException (n' + 1) (d' + 1) (k - u) →
      ¬ IsAHException (n' + 1) d' (k - u - ε) → AHHolds 𝕜 (n' + 1) (d' + 2) k :=
    fun h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
      AHHolds.horace h1 h2 h3 h4 h5 h6 (htr _ h7) (hres _ h8) (hres₂ _ h9)
  by_cases hs : Special n' d'
  · unfold Special at hs
    rcases hs with ⟨rfl, rfl | rfl | rfl | rfl | rfl⟩ | ⟨rfl, rfl⟩
    · -- `ℙ²`, quartics: around the exception `k = 5`
      rcases (by omega : k ≤ 4 ∨ 6 ≤ k) with hk | hk
      · exact (H (k := 4) (u := 1) (ε := 0) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).of_indep (by decide) hk
      · exact (H (k := 6) (u := 3) (ε := 0) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).of_fill (by decide) hk
    · -- `ℙ³`, quartics: around `k = 9`
      rcases (by omega : k ≤ 8 ∨ 10 ≤ k) with hk | hk
      · exact (H (k := 8) (u := 4) (ε := 0) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).of_indep (by decide) hk
      · exact (H (k := 10) (u := 6) (ε := 0) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).of_fill (by decide) hk
    · -- `ℙ⁴`, quartics: around `k = 14`
      rcases (by omega : k ≤ 13 ∨ 15 ≤ k) with hk | hk
      · exact (H (k := 13) (u := 8) (ε := 0) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).of_indep (by decide) hk
      · exact (H (k := 15) (u := 10) (ε := 0) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)).of_fill (by decide) hk
    · -- `ℙ⁵`, quartics: the certificate
      refine AHHolds.of_critical ?_ ?_ k <;>
        rw [show (4 + 1 + (2 + 2) : ℕ).choose (2 + 2) = 126 by decide] <;> exact AHHolds.n5d4
    · -- `ℙ⁷`, quartics: Theorem 4.1 with `u = 30`
      refine AHHolds.of_critical ?_ ?_ k <;>
        rw [show (6 + 1 + (2 + 2) : ℕ).choose (2 + 2) = 330 by decide]
      · exact H (k := 41) (u := 30) (ε := 0) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact H (k := 42) (u := 30) (ε := 0) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)
    · -- `ℙ²`, sextics
      refine AHHolds.of_critical ?_ ?_ k <;>
        rw [show (1 + 1 + (4 + 2) : ℕ).choose (4 + 2) = 28 by decide]
      · exact H (k := 9) (u := 3) (ε := 0) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact H (k := 10) (u := 4) (ε := 0) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide)
  · -- the general case: the standard choice of `u` and `ε`
    have hk : StepOK n' d' (kLow n' d') ∧ StepOK n' d' (kHigh n' d') := by
      by_cases hbox : n' < 9 ∧ d' < 9
      · exact stepOK_box (by omega) hbox.1 (by omega) hbox.2 hs
      · exact stepOK_of_big (by omega) (by omega) (by omega)
    exact AHHolds.of_critical (AHHolds.of_stepOK (by omega) hk.1 htr hres hres₂)
      (AHHolds.of_stepOK (by omega) hk.2 htr hres hres₂) k

/-- **The Alexander–Hirschowitz theorem.** For `r` general points, `σ_r(v_d(ℙⁿ))` is defective if
and only if `(n, d, r)` is one of the exceptions: `d = 2` and `2 ≤ r ≤ n`, or
`(n, d, r) ∈ {(2,4,5), (3,4,9), (4,4,14), (4,3,7)}`. -/
theorem alexanderHirschowitz (n d r : ℕ) (hd : 1 ≤ d) :
    ForGeneralPoints (𝕜 := 𝕜) r (n + 1) (fun p =>
      IsDefective (fun k => (veroneseDegParam n d (p k)).tangentSpace) ↔
        IsAHException n d r) := by
  by_cases h : IsAHException n d r
  · exact (alexanderHirschowitz_exceptions_isDefective_general h).mono fun _ hp =>
      iff_of_true hp h
  obtain ⟨p₀, hp₀⟩ := ahHolds_of_not_exception (𝕜 := 𝕜) n d r hd h
  refine (forGeneralPoints_le_finrank_iSup p₀ hp₀).mono fun p hp => iff_of_false ?_ h
  unfold IsDefective
  exact not_lt.mpr ((expectedDim_veroneseDegParam_le p).trans hp)

end Induction

end AlexanderHirschowitzGeneral
