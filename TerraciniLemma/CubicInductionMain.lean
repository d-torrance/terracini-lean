module

public import TerraciniLemma.CubicBaseCases
public import Mathlib.Data.Nat.Choose.Basic

/-!
# The induction for cubics

The three-level induction of the Brambilla–Ottaviani method for cubics, assembled from the
specialization and trace steps (`TerraciniLemma.CubicInduction`):

* `A_{3,3}(t)` is everything for `t ≥ 10` (the uniform case, `good_three`);
* `A_{2,2}(t)` for `t ≥ 7`, from `A_{2,2}(t-3)` and `A_{3,3}(t)`;
* `A_{1,1}(t)` for `t ≥ 4`, from `A_{1,1}(t-3)` and `A_{2,2}(t)`;
* `A_{0,0}(t)` for `t ≥ 1`, from `A_{0,0}(t-3)` and `A_{1,1}(t)`;

each step being `Good.trace` followed by `Good.of_succ`. The base cases (`A_{i,i}(t)` for
`3i < t ≤ 3i + 3`) are hypotheses here and are proved by certificates.

There are two chains. For `s₂(t) = ⌈N(t)/(t+5)⌉` points everything is *superabundant*: every
statement says that the configuration space is everything. For `s₁(t) = ⌊N(t)/(t+5)⌋` points
and `t ≡ 1 (mod 3)`, where `s₁(t)(t+5) < N(t)`, the statements `A_{0,0}` and `A_{1,1}` are
*subabundant* and their targets are `(t+5) s₁(t)` and `N(t) - 1`.
-/

@[expose] public section

noncomputable section CubicInductionMain

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-- The number of points that fill the ambient space of `v₃(ℙ^{t+4})`:
`⌈N(t)/(t+5)⌉ = ⌈(t+7)(t+6)/6⌉`. -/
def s₂ (t : ℕ) : ℕ := ((t + 7) * (t + 6) + 5) / 6

/-- The largest number of points whose tangent spaces can be independent:
`⌊N(t)/(t+5)⌋ = ⌊(t+7)(t+6)/6⌋`. -/
def s₁ (t : ℕ) : ℕ := (t + 7) * (t + 6) / 6

theorem s₂_add_three (u : ℕ) : s₂ (u + 3) = s₂ u + u + 8 := by
  unfold s₂
  rw [show (u + 3 + 7) * (u + 3 + 6) + 5 = (u + 7) * (u + 6) + 5 + (u + 8) * 6 by ring,
    Nat.add_mul_div_right _ _ (by norm_num)]
  ring

theorem s₁_add_three (u : ℕ) : s₁ (u + 3) = s₁ u + u + 8 := by
  unfold s₁
  rw [show (u + 3 + 7) * (u + 3 + 6) = (u + 7) * (u + 6) + (u + 8) * 6 by ring,
    Nat.add_mul_div_right _ _ (by norm_num)]
  ring

/-- The ambient dimension `N(t) = binom(t+7, 3)`. -/
abbrev Ncube (t : ℕ) : ℕ := (t + 7).choose 3

/-! ### Steps -/

section Steps

variable {s : ℕ → ℕ} (hs : ∀ u, s (u + 3) = s u + u + 8) {t m₁ m₂ : ℕ}
include hs

theorem step₂ (ht : 6 ≤ t) (h₁ : Good 𝕜 s t 2 2 m₁) (h₂ : Good 𝕜 s (t + 3) 3 3 m₂) :
    Good 𝕜 s (t + 3) 2 2 (m₂ + m₁ - Ncube t) :=
  (Good.trace (by norm_num) (by omega) h₁ h₂).of_succ hs (by omega)

theorem step₁ (ht : 3 ≤ t) (h₁ : Good 𝕜 s t 1 1 m₁) (h₂ : Good 𝕜 s (t + 3) 2 2 m₂) :
    Good 𝕜 s (t + 3) 1 1 (m₂ + m₁ - Ncube t) :=
  (Good.trace (by norm_num) (by omega) h₁ h₂).of_succ hs (by omega)

theorem step₀ (h₁ : Good 𝕜 s t 0 0 m₁) (h₂ : Good 𝕜 s (t + 3) 1 1 m₂) :
    Good 𝕜 s (t + 3) 0 0 (m₂ + m₁ - Ncube t) :=
  (Good.trace (by norm_num) (by omega) h₁ h₂).of_succ hs (by omega)

end Steps

/-- Induction with step `3` from three consecutive base cases. -/
theorem induction_three {P : ℕ → Prop} {a : ℕ} (h₀ : P a) (h₁ : P (a + 1)) (h₂ : P (a + 2))
    (step : ∀ t, a ≤ t → P t → P (t + 3)) : ∀ t, a ≤ t → P t := by
  intro t ht
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rcases (by omega : t = a ∨ t = a + 1 ∨ t = a + 2 ∨ a + 3 ≤ t) with rfl | rfl | rfl | h
    · exact h₀
    · exact h₁
    · exact h₂
    · obtain ⟨u, rfl⟩ : ∃ u, t = u + 3 := ⟨t - 3, by omega⟩
      exact step u (by omega) (ih u (by omega) (by omega))

theorem Ncube_le (t : ℕ) : Ncube t + 1 ≤ Ncube (t + 3) := by
  unfold Ncube
  have h1 : (t + 7).choose 3 + 1 ≤ (t + 7 + 1).choose 3 := by
    have e : (t + 7 + 1).choose 3 = (t + 7).choose 2 + (t + 7).choose 3 :=
      Nat.choose_succ_succ (t + 7) 2
    have := Nat.choose_pos (show 2 ≤ t + 7 by omega)
    omega
  have h2 := Nat.choose_le_choose 3 (show t + 7 + 1 ≤ t + 3 + 7 by omega)
  omega

/-! ### The superabundant chain -/

section Super

variable {s : ℕ → ℕ} (hs : ∀ u, s (u + 3) = s u + u + 8)
  (B₃ : ∀ t, 10 ≤ t → Good 𝕜 s t 3 3 (Ncube t))
include hs B₃

theorem super₂ (B₂ : ∀ t, 7 ≤ t → t ≤ 9 → Good 𝕜 s t 2 2 (Ncube t)) :
    ∀ t, 7 ≤ t → Good 𝕜 s t 2 2 (Ncube t) :=
  induction_three (B₂ 7 le_rfl (by norm_num)) (B₂ 8 (by norm_num) (by norm_num))
    (B₂ 9 (by norm_num) le_rfl) fun t ht h => by
      simpa using step₂ hs (by omega) h (B₃ (t + 3) (by omega))

theorem super₁ (B₂ : ∀ t, 7 ≤ t → t ≤ 9 → Good 𝕜 s t 2 2 (Ncube t))
    (B₁ : ∀ t, 4 ≤ t → t ≤ 6 → Good 𝕜 s t 1 1 (Ncube t)) :
    ∀ t, 4 ≤ t → Good 𝕜 s t 1 1 (Ncube t) :=
  induction_three (B₁ 4 le_rfl (by norm_num)) (B₁ 5 (by norm_num) (by norm_num))
    (B₁ 6 (by norm_num) le_rfl) fun t ht h => by
      simpa using step₁ hs (by omega) h (super₂ hs B₃ B₂ (t + 3) (by omega))

/-- **The superabundant chain**: `s(t)` general points fill the ambient space, for all
`t ≥ 1`. -/
theorem super₀ (B₂ : ∀ t, 7 ≤ t → t ≤ 9 → Good 𝕜 s t 2 2 (Ncube t))
    (B₁ : ∀ t, 4 ≤ t → t ≤ 6 → Good 𝕜 s t 1 1 (Ncube t))
    (B₀ : ∀ t, 1 ≤ t → t ≤ 3 → Good 𝕜 s t 0 0 (Ncube t)) :
    ∀ t, 1 ≤ t → Good 𝕜 s t 0 0 (Ncube t) :=
  induction_three (B₀ 1 le_rfl (by norm_num)) (B₀ 2 (by norm_num) (by norm_num))
    (B₀ 3 (by norm_num) le_rfl) fun t ht h => by
      simpa using step₀ hs h (super₁ hs B₃ B₂ B₁ (t + 3) (by omega))

end Super

theorem six_mul_Ncube (t : ℕ) : 6 * Ncube t = (t + 7) * (t + 6) * (t + 5) := by
  unfold Ncube
  have h1 := Nat.add_one_mul_choose_eq (t + 6) 2
  have h2 := Nat.add_one_mul_choose_eq (t + 5) 1
  simp only [Nat.choose_one_right] at h1 h2
  nlinarith [h1, h2]

/-- For `t ≡ 1 (mod 3)`, `(t+7)(t+6) ≡ 2 (mod 6)`. -/
theorem six_mul_s₁ (u : ℕ) : 6 * s₁ (3 * u + 1) + 2 = (3 * u + 1 + 7) * (3 * u + 1 + 6) := by
  unfold s₁
  obtain ⟨w, rfl | rfl⟩ : ∃ w, u = 2 * w ∨ u = 2 * w + 1 := ⟨u / 2, by omega⟩
  · rw [show (3 * (2 * w) + 1 + 7) * (3 * (2 * w) + 1 + 6) = 2 + (6 * w * w + 15 * w + 9) * 6 by
      ring, Nat.add_mul_div_right _ _ (by norm_num)]
    ring
  · rw [show (3 * (2 * w + 1) + 1 + 7) * (3 * (2 * w + 1) + 1 + 6) = 2 + (6 * w * w + 21 * w + 18) * 6 by
      ring, Nat.add_mul_div_right _ _ (by norm_num)]
    ring

/-- The arithmetic of the subabundant step: `a₁(t+3) + a₀(t) - N(t) = a₀(t+3)`. -/
theorem sub_identity (u : ℕ) :
    Ncube (3 * u + 1 + 3) + (3 * u + 1 + 5) * s₁ (3 * u + 1)
      = (3 * u + 1 + 3 + 5) * s₁ (3 * u + 1 + 3) + Ncube (3 * u + 1) + 1 := by
  have hA := six_mul_Ncube (3 * u + 1 + 3)
  have hB := six_mul_Ncube (3 * u + 1)
  have hk := six_mul_s₁ u
  rw [s₁_add_three]
  have : ((Ncube (3 * u + 1 + 3) + (3 * u + 1 + 5) * s₁ (3 * u + 1) : ℕ) : ℚ)
      = (((3 * u + 1 + 3 + 5) * (s₁ (3 * u + 1) + (3 * u + 1) + 8) + Ncube (3 * u + 1) + 1 : ℕ) : ℚ) := by
    push_cast
    have hA' : (6 : ℚ) * Ncube (3 * u + 1 + 3)
        = (3 * u + 1 + 3 + 7) * (3 * u + 1 + 3 + 6) * (3 * u + 1 + 3 + 5) := by exact_mod_cast hA
    have hB' : (6 : ℚ) * Ncube (3 * u + 1) = (3 * u + 1 + 7) * (3 * u + 1 + 6) * (3 * u + 1 + 5) := by
      exact_mod_cast hB
    have hk' : (6 : ℚ) * s₁ (3 * u + 1) + 2 = (3 * u + 1 + 7) * (3 * u + 1 + 6) := by
      exact_mod_cast hk
    linear_combination (1 / 6 : ℚ) * hA' - (1 / 6 : ℚ) * hB' - (1 / 2 : ℚ) * hk'
  exact_mod_cast this

/-! ### The subabundant chain -/

section Sub

variable (B₃ : ∀ t, 10 ≤ t → Good 𝕜 s₁ t 3 3 (Ncube t))
  (B₂ : ∀ t, 7 ≤ t → t ≤ 9 → Good 𝕜 s₁ t 2 2 (Ncube t))
include B₃ B₂

theorem sub₁ (B₁ : Good 𝕜 s₁ 4 1 1 (Ncube 4 - 1)) :
    ∀ u, Good 𝕜 s₁ (3 * u + 4) 1 1 (Ncube (3 * u + 4) - 1) := by
  intro u
  induction u with
  | zero => exact B₁
  | succ u ih =>
    have h := step₁ s₁_add_three (by omega) ih
      (super₂ s₁_add_three B₃ B₂ (3 * u + 4 + 3) (by omega))
    have hN := Ncube_le (3 * u + 4)
    rw [show 3 * (u + 1) + 4 = 3 * u + 4 + 3 by ring]
    have hpos : 0 < Ncube (3 * u + 4) := Nat.choose_pos (by omega)
    convert h using 1
    omega

/-- **The subabundant chain**: for `t ≡ 1 (mod 3)`, the tangent spaces at `s₁(t)` general
points are independent. -/
theorem sub₀ (B₁ : Good 𝕜 s₁ 4 1 1 (Ncube 4 - 1)) (B₀ : Good 𝕜 s₁ 1 0 0 (6 * s₁ 1)) :
    ∀ u, Good 𝕜 s₁ (3 * u + 1) 0 0 ((3 * u + 1 + 5) * s₁ (3 * u + 1)) := by
  intro u
  induction u with
  | zero => exact B₀
  | succ u ih =>
    have h := step₀ s₁_add_three ih (by
      simpa only [show 3 * u + 4 = 3 * u + 1 + 3 by ring] using sub₁ B₃ B₂ B₁ u)
    have hN := Ncube_le (3 * u + 1)
    have hid := sub_identity u
    rw [show 3 * (u + 1) + 1 = 3 * u + 1 + 3 by ring]
    convert h using 1
    omega

end Sub

end CubicInductionMain
