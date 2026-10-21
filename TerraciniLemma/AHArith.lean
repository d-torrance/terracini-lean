module

public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# The arithmetic of the Alexander–Hirschowitz induction

In `ℙ^{n+1}` and degree `d + 2`, with `N_e = binom(n+1+e, e)` and `N^H = binom(n+d+2, d+2)`,
the Horace step (`AHHolds.step`) for `k` points uses
`u = ⌊(k(n+2) - N_{d+1}) / (n+1)⌋` points on `H` and `ε` = the remainder. `StepOK n d k` collects
its numerical hypotheses, and that none of its three inputs is an exceptional case
(`IsAHException`). This is Brambilla–Ottaviani's Lemma 6.3.

* `stepOK_of_big`: `StepOK` holds at the two critical values of `k` when `n ≥ 9` or `d ≥ 9`;
* `stepOK_box`: and for `n, d ≤ 8` except at six `(n, d)`, by computation.
-/

@[expose] public section

/-- The exceptional cases of the Alexander–Hirschowitz theorem: `σ_r(v_d(ℙⁿ))` with
`d = 2, 2 ≤ r ≤ n`, or `(n, d, r) ∈ {(2,4,5), (3,4,9), (4,4,14), (4,3,7)}`. -/
def IsAHException (n d r : ℕ) : Prop :=
  (d = 2 ∧ 2 ≤ r ∧ r ≤ n) ∨ (n, d, r) = (2, 4, 5) ∨ (n, d, r) = (3, 4, 9) ∨
    (n, d, r) = (4, 4, 14) ∨ (n, d, r) = (4, 3, 7)

instance (n d r : ℕ) : Decidable (IsAHException n d r) := by
  unfold IsAHException; infer_instance

theorem isAHException_iff {n d r : ℕ} : IsAHException n d r ↔
    (d = 2 ∧ 2 ≤ r ∧ r ≤ n) ∨ (n = 2 ∧ d = 4 ∧ r = 5) ∨ (n = 3 ∧ d = 4 ∧ r = 9) ∨
      (n = 4 ∧ d = 4 ∧ r = 14) ∨ (n = 4 ∧ d = 3 ∧ r = 7) := by
  simp [IsAHException]

namespace AHArith

/-- The numerical hypotheses of the Horace step, for given values `NH = N^H`, `N1 = N_{d+1}`
and `Nd = N_d`. -/
def StepOKv (NH N1 Nd n d k : ℕ) : Prop :=
  let r := k * (n + 2) - N1
  let u := r / (n + 1)
  let ε := r % (n + 1)
  N1 ≤ k * (n + 2) ∧ ε ≤ u ∧ u + ε ≤ k ∧ Nd ≤ (k - u - ε) * (n + 2) ∧
    (u * (n + 1) ≤ NH ∨ NH ≤ u * (n + 1)) ∧
    ¬ IsAHException n (d + 2) u ∧ ¬ IsAHException (n + 1) (d + 1) (k - u) ∧
    ¬ IsAHException (n + 1) d (k - u - ε)

instance (NH N1 Nd n d k : ℕ) : Decidable (StepOKv NH N1 Nd n d k) := by
  unfold StepOKv; infer_instance

/-- The numerical hypotheses of the Horace step in `ℙ^{n+1}`, degree `d + 2`, for `k` points. -/
def StepOK (n d k : ℕ) : Prop :=
  StepOKv ((n + (d + 2)).choose (d + 2)) ((n + 1 + (d + 1)).choose (d + 1))
    ((n + 1 + d).choose d) n d k

/-- A fast binomial coefficient for computation. -/
def fchoose (n k : ℕ) : ℕ := n.descFactorial k / k.factorial

theorem fchoose_eq (n k : ℕ) : fchoose n k = n.choose k :=
  (Nat.choose_eq_descFactorial_div_factorial n k).symm

/-- The cases handled by other means: `(n + 1, d + 2) = (2, 4), (3, 4), (4, 4)` (the quartic
exceptions), `(5, 4)`, `(7, 4)` and `(2, 6)`. -/
def Special (n d : ℕ) : Prop :=
  (d = 2 ∧ (n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 6)) ∨ (d = 4 ∧ n = 1)

instance (n d : ℕ) : Decidable (Special n d) := by unfold Special; infer_instance

/-- The two critical values of `k` in `ℙ^{n+1}`, degree `d + 2`. -/
def kLow (n d : ℕ) : ℕ := (n + 1 + (d + 2)).choose (d + 2) / (n + 2)
def kHigh (n d : ℕ) : ℕ := ((n + 1 + (d + 2)).choose (d + 2) + (n + 1)) / (n + 2)

/-- The computable form of the box statement. -/
def BoxProp (n d : ℕ) : Prop := 1 ≤ n → 2 ≤ d → ¬ Special n d →
    StepOKv (fchoose (n + (d + 2)) (d + 2)) (fchoose (n + 1 + (d + 1)) (d + 1))
      (fchoose (n + 1 + d) d) n d (fchoose (n + 1 + (d + 2)) (d + 2) / (n + 2)) ∧
    StepOKv (fchoose (n + (d + 2)) (d + 2)) (fchoose (n + 1 + (d + 1)) (d + 1))
      (fchoose (n + 1 + d) d) n d ((fchoose (n + 1 + (d + 2)) (d + 2) + (n + 1)) / (n + 2))

instance (n d : ℕ) : Decidable (BoxProp n d) := by unfold BoxProp; infer_instance

theorem stepOK_box_aux : ∀ n < 9, ∀ d < 9, BoxProp n d := by
  decide +kernel

/-- **The box.** `StepOK` at both critical values for `1 ≤ n ≤ 8`, `2 ≤ d ≤ 8`, except at the
special `(n, d)`. -/
theorem stepOK_box {n d : ℕ} (hn : 1 ≤ n) (hn' : n < 9) (hd : 2 ≤ d) (hd' : d < 9)
    (hs : ¬ Special n d) : StepOK n d (kLow n d) ∧ StepOK n d (kHigh n d) := by
  have := stepOK_box_aux n hn' d hd' hn hd hs
  simp only [fchoose_eq] at this
  exact this

/-! ### Large `n` or `d` -/

section Big

theorem choose_three_mul (m : ℕ) : m.choose 3 * 6 = m * (m - 1) * (m - 2) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose m 3
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.factorial, Nat.succ_eq_add_one,
    Nat.sub_zero, mul_one] at h
  rw [mul_comm, ← h]
  ring

/-- Unimodality: `binom(m, 3) ≤ binom(m, j)` for `3 ≤ j ≤ m - 3`. -/
theorem choose_three_le {m j : ℕ} (h3 : 3 ≤ j) (hj : j + 3 ≤ m) : m.choose 3 ≤ m.choose j := by
  have up : ∀ t, 3 + t ≤ m / 2 → m.choose 3 ≤ m.choose (3 + t) := by
    intro t
    induction t with
    | zero => intro _; rfl
    | succ t ih =>
      intro ht
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  rcases le_or_gt j (m / 2) with hjm | hjm
  · simpa [Nat.add_sub_cancel' h3] using up (j - 3) (by omega)
  · rw [← Nat.choose_symm (by omega : j ≤ m)]
    simpa [show 3 + (m - j - 3) = m - j by omega] using up (m - j - 3) (by omega)

theorem polyB {n d : ℕ} (hn : 2 ≤ n) (hd : 2 ≤ d) :
    6 * ((n ^ 2 + 3 * n + 1) * (d + 2)) ≤ (n + 1) * ((n + d + 2) * (n + d + 1) * (n + d)) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hn
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hd
  ring_nf; omega

theorem polyC {n d : ℕ} (h : (9 ≤ n ∧ 2 ≤ d) ∨ (2 ≤ n ∧ 9 ≤ d)) :
    6 * ((d + 2) * (n + 1) * (n + 3)) ≤ (d + 1) * ((n + d + 2) * (n + d + 1) * (n + d)) := by
  rcases h with ⟨hn, hd⟩ | ⟨hn, hd⟩ <;>
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hn
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hd
    ring_nf; omega

theorem polyD {n d : ℕ} (h : (9 ≤ n ∧ 2 ≤ d) ∨ (2 ≤ n ∧ 9 ≤ d)) :
    6 * ((n ^ 2 + n + 1) * (d + 2) * (n + d + 2))
      ≤ n * (d + 1) * ((n + d + 2) * (n + d + 1) * (n + d)) := by
  rcases h with ⟨hn, hd⟩ | ⟨hn, hd⟩ <;>
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hn
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hd
    ring_nf; omega

theorem polyE {n : ℕ} (hn : 9 ≤ n) : 8 * (2 * n ^ 2 + 5 * n + 5) ≤ (n + 4) * (n + 3) * (n + 2) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hn
  ring_nf; omega

/-- The lower bound for `N_{d+1} = binom(n+d+2, d+1)` used for large `n` or `d`, in the form of
the four inequalities the step needs. -/
theorem big_bounds {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) (hbig : 9 ≤ n ∨ 9 ≤ d) :
    let x := (n + 1 + (d + 1)).choose (d + 1)
    (n ^ 2 + 3 * n + 1) * (d + 2) ≤ x * (n + 1) ∧
    (d + 2) * (n + 1) * (n + 3) ≤ (d + 1) * x ∧
    (n ^ 2 + n + 1) * (d + 2) * (n + d + 2) ≤ x * n * (d + 1) ∧
    (d = 2 → 4 * (2 * n ^ 2 + 5 * n + 5) ≤ 3 * x) := by
  intro x
  rcases (by omega : n = 1 ∨ 2 ≤ n) with rfl | hn2
  · -- `ℙ²`: `x = binom(d+3, 2)`, and `d ≥ 9`
    have hd9 : 9 ≤ d := by omega
    have hx : x * 2 = (d + 3) * (d + 2) := by
      show (1 + 1 + (d + 1)).choose (d + 1) * 2 = _
      rw [show 1 + 1 + (d + 1) = d + 3 by ring, show d + 1 = d + 3 - 2 by omega,
        Nat.choose_symm (by omega), Nat.choose_two_right]
      have : 2 ∣ (d + 3) * (d + 3 - 1) := (Nat.even_mul_pred_self (d + 3)).two_dvd
      rw [Nat.div_mul_cancel this, show d + 3 - 1 = d + 2 by omega]
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hd9
    refine ⟨?_, ?_, ?_, by omega⟩ <;> nlinarith
  · have hx : (n + d + 2) * (n + d + 1) * (n + d) ≤ 6 * x := by
      have h3 := choose_three_mul (n + d + 2)
      have hle : (n + d + 2).choose 3 ≤ x := by
        show (n + d + 2).choose 3 ≤ (n + 1 + (d + 1)).choose (d + 1)
        rw [show n + 1 + (d + 1) = n + d + 2 by ring]
        exact choose_three_le (by omega) (by omega)
      rw [show n + d + 2 - 1 = n + d + 1 by omega, show n + d + 2 - 2 = n + d by omega] at h3
      omega
    have hreg : (9 ≤ n ∧ 2 ≤ d) ∨ (2 ≤ n ∧ 9 ≤ d) := by omega
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := polyB hn2 hd
      have := Nat.mul_le_mul_left (n + 1) hx
      nlinarith
    · have := polyC hreg
      have := Nat.mul_le_mul_left (d + 1) hx
      nlinarith
    · have := polyD hreg
      have := Nat.mul_le_mul_left (n * (d + 1)) hx
      nlinarith
    · rintro rfl
      have hn9 : 9 ≤ n := by omega
      have := polyE hn9
      have hx' : x * 6 = (n + 4) * (n + 3) * (n + 2) := by
        have h3 := choose_three_mul (n + 4)
        have : x = (n + 4).choose 3 := by
          show (n + 1 + (2 + 1)).choose (2 + 1) = _
          rw [show n + 1 + (2 + 1) = n + 4 by ring]
        rw [this, h3, show n + 4 - 1 = n + 3 by omega, show n + 4 - 2 = n + 2 by omega]
      nlinarith

/-- **Brambilla–Ottaviani, Lemma 6.3**, for `n ≥ 9` or `d ≥ 9`: the hypotheses of the Horace step
hold for every `k` with `k(n+2)` within `n + 1` of `N_{d+2}`. -/
theorem stepOK_of_bounds {n d k : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) (hbig : 9 ≤ n ∨ 9 ≤ d)
    (hk1 : (n + 1 + (d + 2)).choose (d + 2) ≤ k * (n + 2) + (n + 1))
    (hk2 : k * (n + 2) ≤ (n + 1 + (d + 2)).choose (d + 2) + (n + 1)) : StepOK n d k := by
  obtain ⟨hQB, hQC, hQD, hQE⟩ := big_bounds hn hd hbig
  set NH := (n + (d + 2)).choose (d + 2) with hNH
  set x := (n + 1 + (d + 1)).choose (d + 1) with hx
  set Nd := (n + 1 + d).choose d with hNd
  set M := (n + d + 1).choose (d + 1) with hM
  -- binomial identities
  have h1 : NH * (d + 2) = x * (n + 1) := by
    have := Nat.choose_succ_right_eq (n + d + 2) (d + 1)
    rw [show n + d + 2 - (d + 1) = n + 1 by omega] at this
    rw [hNH, hx, show n + (d + 2) = n + d + 2 by ring, show n + 1 + (d + 1) = n + d + 2 by ring]
    exact this
  have h2 : (n + 1 + (d + 2)).choose (d + 2) = NH + x := by
    rw [hNH, hx, show n + 1 + (d + 2) = (n + d + 2) + 1 by ring, Nat.choose_succ_succ',
      show n + (d + 2) = n + d + 2 by ring, show n + 1 + (d + 1) = n + d + 2 by ring, add_comm]
  have h3 : x = Nd + M := by
    rw [hx, hNd, hM, show n + 1 + (d + 1) = (n + d + 1) + 1 by ring, Nat.choose_succ_succ',
      show n + 1 + d = n + d + 1 by ring]
  have h4 : M * (n + d + 2) = x * (n + 1) := by
    have := Nat.choose_mul_succ_eq (n + d + 1) (d + 1)
    rw [show n + d + 1 + 1 - (d + 1) = n + 1 by omega] at this
    rw [hM, hx, show n + 1 + (d + 1) = n + d + 1 + 1 by ring]
    exact this
  rw [h2] at hk1 hk2
  -- the trace dimension is large
  have hNHB : n ^ 2 + 3 * n + 1 ≤ NH :=
    Nat.le_of_mul_le_mul_right (by rw [h1]; exact hQB) (by omega : 0 < d + 2)
  unfold StepOK StepOKv
  simp only []
  rw [← hNH, ← hx, ← hNd]
  set K := k * (n + 2) with hK
  have hA : x ≤ K := by omega
  set r := K - x with hr
  set u := r / (n + 1) with hu
  set ε := r % (n + 1) with hε
  have hdm : (n + 1) * u + ε = r := Nat.div_add_mod r (n + 1)
  have hεn : ε < n + 1 := Nat.mod_lt r (by omega)
  -- `ε ≤ n ≤ u`
  have hnu : n ≤ u := by
    by_contra! h
    have : (n + 1) * u ≤ (n + 1) * (n - 1) := Nat.mul_le_mul_left _ (by omega)
    have : (n + 1) * (n - 1) + 1 = n ^ 2 := by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn; simp; ring
    omega
  -- `u + (n+1)ε ≤ M`
  have hu1 : (n + 1) * u ≤ NH + (n + 1) := by omega
  have hε1 : (n + 1) * ((n + 1) * ε) ≤ (n + 1) * ((n + 1) * n) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  have hDM : u + (n + 1) * ε ≤ M := by
    have key : NH + (n + 1) + (n + 1) * ((n + 1) * n) ≤ (n + 1) * M := by
      have e1 : (NH + (n + 1) + (n + 1) * ((n + 1) * n)) * ((d + 2) * (n + d + 2))
          = (NH * (d + 2)) * (n + d + 2) + (n + 1) * ((n ^ 2 + n + 1) * (d + 2) * (n + d + 2)) := by
        ring
      have e2 : ((n + 1) * M) * ((d + 2) * (n + d + 2)) = (n + 1) * (d + 2) * (M * (n + d + 2)) := by
        ring
      have e3 : (n + 1) * (d + 2) * (x * (n + 1))
          = x * (n + 1) * (n + d + 2) + (n + 1) * (x * n * (d + 1)) := by ring
      have A := Nat.mul_le_mul_left (n + 1) hQD
      have : (NH + (n + 1) + (n + 1) * ((n + 1) * n)) * ((d + 2) * (n + d + 2))
          ≤ ((n + 1) * M) * ((d + 2) * (n + d + 2)) := by
        rw [e1, e2, h1, h4, e3]
        omega
      exact Nat.le_of_mul_le_mul_right this (by positivity)
    have : (n + 1) * (u + (n + 1) * ε) ≤ (n + 1) * M := by
      rw [mul_add]; omega
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hMx : M ≤ x := by omega
  -- `u + ε ≤ k`
  have hC : u + ε ≤ k := by
    have e : (n + 2) * (u + ε) = (n + 1) * u + ε + (u + (n + 1) * ε) := by ring
    have : (n + 2) * (u + ε) ≤ (n + 2) * k := by
      rw [e, mul_comm (n + 2) k]; omega
    exact Nat.le_of_mul_le_mul_left this (by omega)
  have hsub : (k - u - ε) * (n + 2) + u + (n + 1) * ε = x := by
    have : (k - u - ε) * (n + 2) = K - (u + ε) * (n + 2) := by
      rw [Nat.sub_sub, Nat.sub_mul]
    have : (u + ε) * (n + 2) = (n + 1) * u + u + (n + 1) * ε + ε := by ring
    omega
  refine ⟨hA, by omega, hC, by omega, by omega, ?_, ?_, ?_⟩
  · rw [isAHException_iff]; omega
  · rw [isAHException_iff]; omega
  · rw [isAHException_iff]
    rcases (by omega : d = 2 ∨ 3 ≤ d) with rfl | hd3
    · -- quadrics: `k - u - ε ≥ n + 2`
      have hn9 : 9 ≤ n := by omega
      have hE := hQE rfl
      have h14 : NH * 4 = x * (n + 1) := h1
      have key : (n + 1) * (u + (n + 1) * ε + (n + 2) * (n + 2)) ≤ (n + 1) * x := by
        have e1 : 4 * (NH + (n + 1) + (n + 1) * ((n + 1) * n) + (n + 1) * ((n + 2) * (n + 2)))
            = NH * 4 + (n + 1) * (4 * (2 * n ^ 2 + 5 * n + 5)) := by ring
        have e2 : 4 * ((n + 1) * x) = x * (n + 1) + (n + 1) * (3 * x) := by ring
        have A := Nat.mul_le_mul_left (n + 1) hE
        have : NH + (n + 1) + (n + 1) * ((n + 1) * n) + (n + 1) * ((n + 2) * (n + 2))
            ≤ (n + 1) * x := by
          have : 4 * (NH + (n + 1) + (n + 1) * ((n + 1) * n) + (n + 1) * ((n + 2) * (n + 2)))
              ≤ 4 * ((n + 1) * x) := by rw [e1, e2, h14]; omega
          omega
        rw [mul_add, mul_add]; omega
      have : u + (n + 1) * ε + (n + 2) * (n + 2) ≤ x :=
        Nat.le_of_mul_le_mul_left key (by omega)
      have : (n + 2) * (n + 2) ≤ (k - u - ε) * (n + 2) := by omega
      have : n + 2 ≤ k - u - ε := Nat.le_of_mul_le_mul_right this (by omega)
      omega
    · omega

/-- `StepOK` at both critical values, for `n ≥ 9` or `d ≥ 9`. -/
theorem stepOK_of_big {n d : ℕ} (hn : 1 ≤ n) (hd : 2 ≤ d) (hbig : 9 ≤ n ∨ 9 ≤ d) :
    StepOK n d (kLow n d) ∧ StepOK n d (kHigh n d) := by
  have h1 := Nat.div_add_mod' ((n + 1 + (d + 2)).choose (d + 2)) (n + 2)
  have h2 := Nat.mod_lt ((n + 1 + (d + 2)).choose (d + 2)) (by omega : 0 < n + 2)
  have h3 := Nat.div_add_mod' ((n + 1 + (d + 2)).choose (d + 2) + (n + 1)) (n + 2)
  have h4 := Nat.mod_lt ((n + 1 + (d + 2)).choose (d + 2) + (n + 1)) (by omega : 0 < n + 2)
  refine ⟨stepOK_of_bounds hn hd hbig ?_ ?_, stepOK_of_bounds hn hd hbig ?_ ?_⟩ <;>
    simp only [kLow, kHigh] <;> omega

end Big

end AHArith
