module

public import TerraciniLemma.Semicontinuity

/-!
# The differential Horace lemma

A linear-algebra form of the differential Horace method of Alexander–Hirschowitz, for spans
of vectors moving along a polynomial path. Let `W` be a subspace and let `b_j(t)` be vectors
depending polynomially on a parameter `t`,
`b_j(t) = β_{j,0} + t β_{j,1} + t² β_{j,2} + ⋯`. Put
`D = {∑ c_j β_{j,1} : ∑ c_j β_{j,0} ∈ W}`. Then for general `t`,

  `dim (W + span b(t)) ≥ dim (W + span β_{·,0} + D)` (`differentialHorace`).

So the limit at `t = 0` keeps, besides the limit vectors `β_{j,0}`, the first-order terms of the
relations between them and `W`: if `∑ c_j β_{j,0} = w ∈ W`, then
`(∑ c_j b_j(t) - w) / t ∈ W + span b(t)` tends to `∑ c_j β_{j,1}`.

This replaces the curvilinear lemma and the limits of curvilinear schemes in Chandler's
version of the method (Brambilla–Ottaviani, *On the Alexander–Hirschowitz theorem*, §6): the
statement is about spans, and the limit is lower semicontinuity of rank in `t`
(`HoldsGenerically.le_rank`).

* §A — polynomial paths of vectors and semicontinuity of the dimension of their span;
* §B — the differential Horace lemma.
-/

@[expose] public section

noncomputable section DifferentialHorace

open MvPolynomial

variable {𝕜 : Type*} [Field 𝕜] {κ : Type*} [Fintype κ]

/-! ### §A — Polynomial paths -/

section Paths

/-- The polynomial path `t ↦ ∑_{i ≤ m} tⁱ • a i`. -/
def polyPath (m : ℕ) (a : ℕ → κ → 𝕜) (t : 𝕜) : κ → 𝕜 :=
  ∑ i ∈ Finset.range (m + 1), t ^ i • a i

omit [Fintype κ] in
theorem polyPath_zero (m : ℕ) (a : ℕ → κ → 𝕜) : polyPath m a 0 = a 0 := by
  rw [polyPath, Finset.sum_range_succ']
  simp

/-- The matrix of polynomials in `t` whose columns are the paths `polyPath m (a k)`. -/
def pathMatrix {K : Type*} (m : ℕ) (a : K → ℕ → κ → 𝕜) : Matrix κ K (MvPolynomial Unit 𝕜) :=
  Matrix.of fun x k => ∑ i ∈ Finset.range (m + 1), C (a k i x) * X () ^ i

omit [Fintype κ] in
theorem pathMatrix_map_col {K : Type*} (m : ℕ) (a : K → ℕ → κ → 𝕜) (t : Unit → 𝕜) :
    ((pathMatrix m a).map (eval t)).col = fun k => polyPath m (a k) (t ()) := by
  ext k x
  simp [Matrix.col, pathMatrix, polyPath, Finset.sum_apply, mul_comm]

/-- **Semicontinuity along a path.** If the vectors `a k 0` span a space of dimension `≥ r`,
then so do the vectors `polyPath m (a k) t`, for general `t`. -/
theorem holdsGenerically_le_finrank_span {K : Type*} [Fintype K] (m : ℕ) (a : K → ℕ → κ → 𝕜)
    {r : ℕ} (h : r ≤ Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range fun k => a k 0))) :
    HoldsGenerically Unit fun t =>
      r ≤ Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range fun k => polyPath m (a k) (t ()))) := by
  have key : ∀ t : Unit → 𝕜, ((pathMatrix m a).map (eval t)).rank
      = Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range fun k => polyPath m (a k) (t ()))) := by
    intro t
    rw [Matrix.rank_eq_finrank_span_cols, pathMatrix_map_col]
  refine (HoldsGenerically.le_rank (k := r) (pathMatrix m a) (fun _ => 0) ?_).mono fun t ht => ?_
  · have h0 : (fun k => polyPath m (a k) 0) = fun k => a k 0 :=
      funext fun k => polyPath_zero m (a k)
    rw [key]
    exact h0 ▸ h
  · rwa [key] at ht

end Paths

/-! ### §B — The differential Horace lemma -/

section Horace

variable (W : Submodule 𝕜 (κ → 𝕜)) {ι : Type*} [Fintype ι] (β : ι → ℕ → κ → 𝕜)

/-- The first-order terms of the relations between the limit vectors `β j 0` and `W`:
`D = {∑ c_j β_{j,1} : ∑ c_j β_{j,0} ∈ W}`. -/
def horaceD : Submodule 𝕜 (κ → 𝕜) :=
  (W.comap (Fintype.linearCombination 𝕜 fun j => β j 0)).map
    (Fintype.linearCombination 𝕜 fun j => β j 1)

/-- The coefficients of `(∑ c_j b_j(t) - ∑ c_j β_{j,0}) / t`. -/
def relPath (m : ℕ) (c : ι → 𝕜) (i : ℕ) : κ → 𝕜 :=
  if i < m then ∑ j, c j • β j (i + 1) else 0

omit [Fintype κ] in
theorem smul_polyPath_relPath (m : ℕ) (c : ι → 𝕜) (t : 𝕜) :
    t • polyPath m (relPath β m c) t
      = ∑ j, c j • polyPath m (β j) t - ∑ j, c j • β j 0 := by
  simp only [polyPath, relPath]
  rw [Finset.sum_range_succ, ite_eq_right (lt_irrefl m), smul_zero, add_zero]
  simp only [Finset.sum_range_succ', pow_zero, one_smul, smul_add, Finset.sum_add_distrib,
    add_sub_cancel_right, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [ite_eq_left (Finset.mem_range.mp hi), Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, smul_smul, smul_smul, pow_succ]
  ring_nf

/-- **The differential Horace lemma.** Let `b_j(t) = ∑_{i ≤ m} tⁱ β_{j,i}` with `m ≥ 1`. For
general `t`, `W + span b(t)` has dimension at least that of `W + span β_{·,0} + D`, where `D`
holds the first-order terms of the relations between the `β_{j,0}` and `W` (`horaceD`). -/
theorem differentialHorace {m : ℕ} (hm : 0 < m) :
    HoldsGenerically Unit fun t =>
      Module.finrank 𝕜 ((W ⊔ Submodule.span 𝕜 (Set.range fun j => β j 0) ⊔ horaceD W β :
          Submodule 𝕜 (κ → 𝕜)))
        ≤ Module.finrank 𝕜 ((W ⊔ Submodule.span 𝕜 (Set.range fun j => polyPath m (β j) (t ())) :
          Submodule 𝕜 (κ → 𝕜))) := by
  classical
  -- finite spanning sets of `W` and of the relations `R = {c : ∑ c_j β_{j,0} ∈ W}`
  set L₀ := Fintype.linearCombination 𝕜 fun j => β j 0
  set L₁ := Fintype.linearCombination 𝕜 fun j => β j 1
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian W
  obtain ⟨T, hT⟩ := IsNoetherian.noetherian (W.comap L₀)
  -- the paths: constant vectors spanning `W`, the `b_j`, and the rescaled relations
  let a : (↥S ⊕ ι ⊕ ↥T) → ℕ → κ → 𝕜
    | .inl s => fun i => if i = 0 then (s : κ → 𝕜) else 0
    | .inr (.inl j) => β j
    | .inr (.inr c) => relPath β m c
  -- at `t = 0` they span `W + span β_{·,0} + D`
  have h0 : (W ⊔ Submodule.span 𝕜 (Set.range fun j => β j 0) ⊔ horaceD W β :
      Submodule 𝕜 (κ → 𝕜)) ≤ Submodule.span 𝕜 (Set.range fun k => a k 0) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [← hS, Submodule.span_le]
      intro s hs
      exact Submodule.subset_span ⟨.inl ⟨s, hs⟩, by simp [a]⟩
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact Submodule.subset_span ⟨.inr (.inl j), rfl⟩
    · rw [horaceD, ← hT, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨c, hc, rfl⟩
      refine Submodule.subset_span ⟨.inr (.inr ⟨c, hc⟩), ?_⟩
      simp [a, relPath, hm, Fintype.linearCombination_apply]
  -- for `t ≠ 0` they lie in `W + span b(t)`
  have ht : ∀ t : 𝕜, t ≠ 0 → Submodule.span 𝕜 (Set.range fun k => polyPath m (a k) t)
      ≤ W ⊔ Submodule.span 𝕜 (Set.range fun j => polyPath m (β j) t) := by
    intro t ht
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rcases k with ⟨s, hs⟩ | j | ⟨c, hc⟩
    · refine Submodule.mem_sup_left ?_
      show polyPath m (a (.inl ⟨s, hs⟩)) t ∈ W
      have : polyPath m (a (.inl ⟨s, hs⟩)) t = s := by
        rw [polyPath, Finset.sum_eq_single 0 (fun i _ hi => by simp [a, hi]) (by simp)]
        simp [a]
      rw [this, ← hS]
      exact Submodule.subset_span hs
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨j, rfl⟩)
    · show polyPath m (relPath β m c) t ∈ W ⊔ _
      rw [← Submodule.smul_mem_iff _ ht]
      rw [smul_polyPath_relPath]
      refine Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.sum_mem _ fun j _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))) (Submodule.mem_sup_left ?_)
      have hc' : c ∈ W.comap L₀ := hT ▸ Submodule.subset_span hc
      simpa [L₀, Fintype.linearCombination_apply] using hc'
  -- semicontinuity in `t`, avoiding `t = 0`
  have hX : HoldsGenerically (𝕜 := 𝕜) Unit fun t => t () ≠ 0 :=
    ⟨X (), X_ne_zero (), fun t h => by simpa using h⟩
  refine ((holdsGenerically_le_finrank_span m a (Submodule.finrank_mono h0)).and hX).mono
    fun t ⟨hle, hne⟩ => hle.trans (Submodule.finrank_mono (ht _ hne))

end Horace

end DifferentialHorace
