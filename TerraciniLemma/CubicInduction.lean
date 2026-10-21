module

public import TerraciniLemma.CubicLattice
public import Mathlib.Algebra.CharZero.Infinite

/-!
# The Brambilla–Ottaviani induction for cubics

We follow Torrance–Vannieuwenhoven (*All secant varieties of the Chow variety are nondefective
for cubics and quaternary forms*, Trans. AMS **374** (2021), §4, Example 4.9), with only the
lower bounds needed.

Fix `n = t + 4` (so `ℙⁿ` with `n ≥ 5` for `t ≥ 1`), the ambient space of `v₃(ℙⁿ)` of dimension
`N(t) = binom(t+7, 3)`, and the coordinate lattice `U₀, U₁, U₂` of `TerraciniLemma.CubicLattice`
(`U_b` kills block `b`), with `P̂_b = S³U_b`. A number of points `s(t)` is distributed on the
first `K ≤ 3` lattice spaces by the Newton (Pascal) rule: at each location `I ⊆ {0, …, K-1}`
(a point of `⋂_{b ∈ I} U_b`) we put `∇^{K-|I|} s(t - 3|I|)` points, where `∇f(t) = f(t) - f(t-3)`.
For the `s` we use, `∇s(t) = t + 5`, `∇²s = 3` and `∇³s = 0`, so these counts are `s(t')`,
`t' + 5`, `3` and `0` (`countAt`), with `t' = t - 3|I|`.

The configuration space `A_{i,K}(t)` (`configSpace`) is `P̂₀ + ⋯ + P̂_{i-1}` plus the tangent
spaces at the points, and `Good s t K i m` says that it has dimension `≥ m` for general points.
The induction has three ingredients:

* **specialization** (`Good.of_succ`): a configuration on `K + 1` lattice spaces is a
  configuration on `K` of them with some points pushed into `U_K` (Pascal's rule), so a lower
  bound for `K + 1` gives one for `K`;
* **the trace step** (`Good.trace`): the points of `A_{i,K+1}(t+3)` on `U_i` form, via the
  embedding skipping block `i`, the configuration of `A_{i,K}(t)`, so Grassmann's formula
  bounds `A_{i,K+1}(t+3)` below by `A_{i+1,K+1}(t+3)` and `A_{i,K}(t)`;
* the base cases, proved with rank certificates.
-/

@[expose] public section

noncomputable section CubicInduction

open MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]

/-! ### §A — Configurations -/

/-- `∇^e s(t')` for our `s`: `s(t')`, `t' + 5`, `3`, `0`, … -/
def countFor (s : ℕ → ℕ) (t' e : ℕ) : ℕ :=
  match e with
  | 0 => s t'
  | 1 => t' + 5
  | 2 => 3
  | _ => 0

/-- The number of points at location `I` in the configuration on `K` lattice spaces at level
`t`: `∇^{K-|I|} s(t - 3|I|)`, which for our `s` is `s(t')`, `t' + 5`, `3` or `0`. -/
def countAt (s : ℕ → ℕ) (t K : ℕ) (I : Finset ℕ) : ℕ :=
  countFor s (t - 3 * I.card) (K - I.card)

/-- Locations: subsets of the first `K` lattice indices. -/
abbrev Loc (K : ℕ) := ↥(Finset.range K).powerset

/-- Point slots of the configuration on `K` lattice spaces at level `t`. -/
abbrev Slot (s : ℕ → ℕ) (t K : ℕ) := Σ I : Loc K, Fin (countAt s t K I)

/-- Parameters: a free point of `𝕜^{t+5}` for each slot. -/
abbrev Param (s : ℕ → ℕ) (t K : ℕ) := Slot s t K × Fin (t + 4 + 1)

variable {s : ℕ → ℕ} {t K : ℕ}

/-- The point in a slot at location `I`: the free point with the blocks of `I` zeroed. -/
def configPoint (x : Param s t K → 𝕜) (σ : Slot s t K) : Fin (t + 4 + 1) → 𝕜 :=
  zeroBlocks (σ.1 : Finset ℕ) (fun j => x (σ, j))

/-- The monomials avoiding one of the blocks `b < i`: `P̂₀ + ⋯ + P̂_{i-1}` is their span. -/
def latticeSet (t i : ℕ) : Set (Sym (Fin (t + 4 + 1)) 3) := {m | ∃ b < i, AvoidsBlock b m}

/-- The configuration space `A_{i,K}(t) = P̂₀ + ⋯ + P̂_{i-1} + ∑ T_p`. -/
def configSpace (s : ℕ → ℕ) (t K i : ℕ) (x : Param s t K → 𝕜) :
    Submodule 𝕜 (Sym (Fin (t + 4 + 1)) 3 → 𝕜) :=
  monoSpan (t + 4) 3 (latticeSet t i) ⊔
    ⨆ σ, (veroneseDegParam (t + 4) 3 (configPoint x σ)).tangentSpace

/-- `Good s t K i m`: for general points, `A_{i,K}(t)` has dimension `≥ m`. -/
def Good (𝕜 : Type*) [NontriviallyNormedField 𝕜] (s : ℕ → ℕ) (t K i m : ℕ) : Prop :=
  HoldsGenerically (Param s t K) fun x : Param s t K → 𝕜 =>
    m ≤ Module.finrank 𝕜 (configSpace s t K i x)

omit [CharZero 𝕜] in
/-- Configuration points depend polynomially on the parameters. -/
theorem configPoint_eq_polyPoint (x : Param s t K → 𝕜) (σ : Slot s t K) :
    configPoint x σ = polyPoint (fun j =>
      if ∃ b ∈ (σ.1 : Finset ℕ), InBlock b j then 0 else X (σ, j)) x := by
  funext j
  simp only [configPoint, zeroBlocks, polyPoint]
  split_ifs
  · exact (map_zero _).symm
  · exact (eval_X (f := x) _).symm

omit [CharZero 𝕜] in
/-- **Semicontinuity**: a lower bound at one choice of points gives `Good`. -/
theorem Good.of_point {i m : ℕ} (x₀ : Param s t K → 𝕜)
    (h : m ≤ Module.finrank 𝕜 (configSpace s t K i x₀)) : Good 𝕜 s t K i m := by
  let P : Slot s t K → Fin (t + 4 + 1) → MvPolynomial (Param s t K) 𝕜 := fun σ j =>
    if ∃ b ∈ (σ.1 : Finset ℕ), InBlock b j then 0 else X (σ, j)
  have hcs : ∀ x, configSpace s t K i x = monoSpan (t + 4) 3 (latticeSet t i) ⊔
      ⨆ σ, (veroneseDegParam (t + 4) 3 (polyPoint (P σ) x)).tangentSpace := fun x =>
    congrArg (monoSpan (t + 4) 3 (latticeSet t i) ⊔ ·) (iSup_congr fun σ =>
      congrArg (fun v => (veroneseDegParam (𝕜 := 𝕜) (t + 4) 3 v).tangentSpace)
        (configPoint_eq_polyPoint x σ))
  rw [hcs] at h
  exact (holdsGenerically_le_finrank _ P x₀ h).mono fun x hx => (hcs x).symm ▸ hx

/-! ### §B — Specialization -/

omit [CharZero 𝕜] in
/-- Pascal's rule for the point counts: the points at location `J` of the configuration on `K`
lattice spaces split into those at `J` and at `J ∪ {K}` of the configuration on `K + 1`. -/
theorem countAt_add_countAt_insert (hs : ∀ u, s (u + 3) = s u + u + 8) {J : Finset ℕ}
    (hJ : J ⊆ Finset.range K) (ht : 3 * (K + 1) ≤ t) :
    countAt s t (K + 1) J + countAt s t (K + 1) (insert K J) = countAt s t K J := by
  have hK : K ∉ J := fun h => by simpa using hJ h
  have hcard : J.card ≤ K := by simpa using Finset.card_le_card hJ
  simp only [countAt, Finset.card_insert_of_notMem hK]
  obtain ⟨e, he⟩ : ∃ e, K = J.card + e := ⟨K - J.card, by omega⟩
  rw [show K + 1 - J.card = e + 1 by omega, show K + 1 - (J.card + 1) = e by omega,
    show K - J.card = e by omega]
  rcases e with _ | _ | _ | e
  · obtain ⟨u, hu⟩ : ∃ u, t - 3 * (J.card + 1) = u := ⟨_, rfl⟩
    simp only [countFor]
    rw [hu, show t - 3 * J.card = u + 3 by omega, hs]
    omega
  · simp only [countFor]; omega
  · simp [countFor]
  · simp [countFor]

omit [CharZero 𝕜] in
theorem zeroBlocks_zeroBlocks {n : ℕ} {B B' : Finset ℕ} (h : B ⊆ B') (z : Fin (n + 1) → 𝕜) :
    zeroBlocks B (zeroBlocks B' z) = zeroBlocks B' z := by
  funext a
  simp only [zeroBlocks]
  split_ifs with h1 h2 <;> try rfl
  exact absurd (let ⟨b, hb, hab⟩ := h1; ⟨b, h hb, hab⟩) h2

/-- **Specialization.** A lower bound for the configuration on `K + 1` lattice spaces gives
the same lower bound for the configuration on `K` of them: the former is the latter with some
points pushed into `U_K`. -/
theorem Good.of_succ {i m : ℕ} (hs : ∀ u, s (u + 3) = s u + u + 8) (ht : 3 * (K + 1) ≤ t)
    (h : Good 𝕜 s t (K + 1) i m) : Good 𝕜 s t K i m := by
  classical
  have := CharZero.infinite 𝕜
  obtain ⟨x₀, hx₀⟩ := h.exists_point
  have hsub : Finset.range K ⊆ Finset.range (K + 1) :=
    Finset.range_subset_range.mpr (Nat.le_succ K)
  let up : Loc K → Loc (K + 1) := fun J =>
    ⟨J.1, Finset.mem_powerset.mpr ((Finset.mem_powerset.mp J.2).trans hsub)⟩
  let upK : Loc K → Loc (K + 1) := fun J =>
    ⟨insert K J.1, Finset.mem_powerset.mpr (Finset.insert_subset (by simp)
      ((Finset.mem_powerset.mp J.2).trans hsub))⟩
  have hpascal : ∀ J : Loc K,
      countAt s t (K + 1) (up J) + countAt s t (K + 1) (upK J) = countAt s t K J :=
    fun J => countAt_add_countAt_insert hs (Finset.mem_powerset.mp J.2) ht
  -- each slot on `K` spaces is a slot on `K + 1` spaces, at `J` or at `J ∪ {K}`
  let pick : Slot s t K → Slot s t (K + 1) := fun σ =>
    if hc : (σ.2 : ℕ) < countAt s t (K + 1) (up σ.1) then ⟨up σ.1, ⟨σ.2, hc⟩⟩
    else ⟨upK σ.1, ⟨σ.2 - countAt s t (K + 1) (up σ.1), by
      have := hpascal σ.1; have := σ.2.2; omega⟩⟩
  have hpick : ∀ σ : Slot s t K, (σ.1 : Finset ℕ) ⊆ ((pick σ).1 : Finset ℕ) := fun σ => by
    by_cases hc : (σ.2 : ℕ) < countAt s t (K + 1) (up σ.1)
    · simp [pick, hc, up]
    · simp only [pick, hc, dite_false, upK]
      exact Finset.subset_insert _ _
  let y₀ : Param s t K → 𝕜 := fun p => configPoint x₀ (pick p.1) p.2
  have hy : ∀ σ, configPoint y₀ σ = configPoint x₀ (pick σ) := fun σ =>
    zeroBlocks_zeroBlocks (hpick σ) _
  -- every slot on `K + 1` spaces is picked
  have hsurj : ∀ σ' : Slot s t (K + 1), ∃ σ, pick σ = σ' := by
    rintro ⟨⟨L, hL⟩, c⟩
    have hL' := Finset.mem_powerset.mp hL
    by_cases hK : K ∈ L
    · have hJ : L.erase K ⊆ Finset.range K := fun b hb => by
        have := hL' (Finset.mem_of_mem_erase hb)
        simp only [Finset.mem_range] at this ⊢
        exact lt_of_le_of_ne (Nat.lt_succ_iff.mp this) (Finset.ne_of_mem_erase hb)
      let J : Loc K := ⟨L.erase K, Finset.mem_powerset.mpr hJ⟩
      have hLJ : upK J = ⟨L, hL⟩ := Subtype.ext (Finset.insert_erase hK)
      have hc : (c : ℕ) < countAt s t (K + 1) (upK J) := by rw [hLJ]; exact c.2
      refine ⟨⟨J, ⟨countAt s t (K + 1) (up J) + c, by have := hpascal J; omega⟩⟩, ?_⟩
      simp only [pick, show ¬ (countAt s t (K + 1) (up J) + (c : ℕ) <
        countAt s t (K + 1) (up J)) by omega, dite_false]
      exact Sigma.ext hLJ ((Fin.heq_ext_iff (congrArg (fun I : Loc (K + 1) =>
        countAt s t (K + 1) I) hLJ)).mpr (by simp))
    · have hJ : L ⊆ Finset.range K := fun b hb => by
        have := hL' hb
        simp only [Finset.mem_range] at this ⊢
        exact lt_of_le_of_ne (Nat.lt_succ_iff.mp this) (fun h => hK (h ▸ hb))
      let J : Loc K := ⟨L, Finset.mem_powerset.mpr hJ⟩
      have h1 : countAt s t (K + 1) ((⟨L, hL⟩ : Loc (K + 1)) : Finset ℕ)
          = countAt s t (K + 1) (up J : Finset ℕ) := rfl
      refine ⟨⟨J, ⟨c, by have := hpascal J; have := c.2; omega⟩⟩, ?_⟩
      simp only [pick, show (c : ℕ) < countAt s t (K + 1) (up J) from c.2, dite_true]
      rfl
  refine Good.of_point y₀ (hx₀.trans (Submodule.finrank_mono ?_))
  refine sup_le_sup_left (iSup_le fun σ' => ?_) _
  obtain ⟨σ, rfl⟩ := hsurj σ'
  refine le_iSup_of_le σ (le_of_eq ?_)
  exact congrArg (fun v => (veroneseDegParam (𝕜 := 𝕜) (t + 4) 3 v).tangentSpace) (hy σ).symm

/-! ### §C — The trace step -/

omit [CharZero 𝕜] in
theorem relabel_ne (i b' : ℕ) : relabel i b' ≠ i := by
  simp only [relabel]; split_ifs <;> omega

omit [CharZero 𝕜] in
theorem relabel_injective (i : ℕ) : Function.Injective (relabel i) := by
  intro a b h
  simp only [relabel] at h
  split_ifs at h <;> omega

omit [CharZero 𝕜] in
theorem unrelabel_relabel (i b' : ℕ) : unrelabel i (relabel i b') = b' := by
  simp only [relabel, unrelabel]; split_ifs <;> omega

/-- The location in the configuration on `K + 1` spaces of a point of the trace on `U_i`. -/
def traceLoc (i : ℕ) (I : Finset ℕ) : Finset ℕ := insert i (I.image (relabel i))

omit [CharZero 𝕜] in
theorem card_traceLoc (i : ℕ) (I : Finset ℕ) : (traceLoc i I).card = I.card + 1 := by
  rw [traceLoc, Finset.card_insert_of_notMem, Finset.card_image_of_injective _
    (relabel_injective i)]
  simp [relabel_ne]

omit [CharZero 𝕜] in
theorem traceLoc_erase (i : ℕ) (I : Finset ℕ) :
    ((traceLoc i I).erase i).image (unrelabel i) = I := by
  rw [traceLoc, Finset.erase_insert (by simp [relabel_ne]), Finset.image_image]
  conv_rhs => rw [← Finset.image_id (s := I)]
  exact Finset.image_congr fun b _ => unrelabel_relabel i b

omit [CharZero 𝕜] in
theorem traceLoc_injective (i : ℕ) : Function.Injective (traceLoc i) := by
  intro I I' h
  rw [← traceLoc_erase i I, ← traceLoc_erase i I', h]

omit [CharZero 𝕜] in
theorem countAt_traceLoc (i : ℕ) (I : Finset ℕ) :
    countAt s (t + 3) (K + 1) (traceLoc i I) = countAt s t K I := by
  simp only [countAt, card_traceLoc]
  congr 1 <;> omega

omit [CharZero 𝕜] in
theorem monoSpan_latticeSet_succ_le (t i : ℕ) :
    (monoSpan (t + 4) 3 (latticeSet t (i + 1)) : Submodule 𝕜 _)
      ≤ monoSpan (t + 4) 3 (latticeSet t i) ⊔ latticeSpace (t + 4) 3 i := by
  rw [latticeSpace, monoSpan_eq_span, monoSpan_eq_span, monoSpan_eq_span,
    ← Submodule.span_union, ← Set.image_union]
  refine Submodule.span_mono (Set.image_mono ?_)
  rintro m ⟨b, hb, hm⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
  · exact Or.inl ⟨b, hb, hm⟩
  · exact Or.inr hm

omit [CharZero 𝕜] in
/-- The trace of `P̂₀ + ⋯ + P̂_{i-1}` on `U_i` is `P̂₀ + ⋯ + P̂_{i-1}` one level down. -/
theorem map_monoSpan_latticeSet_le (t i : ℕ) :
    (monoSpan (t + 4) 3 (latticeSet t i)).map (pushSkip (𝕜 := 𝕜) i).toLinearMap
      ≤ monoSpan (t + 4 + 3) 3 (latticeSet (t + 3) i) := by
  rintro _ ⟨f, hf, rfl⟩ m hm
  by_cases hr : m ∈ Set.range (Sym.map (skip i))
  · obtain ⟨m', rfl⟩ := hr
    simp only [ContinuousLinearMap.coe_coe, pushSkip_map]
    refine hf m' fun ⟨b, hb, hm'⟩ => hm ⟨b, hb, fun a ha => ?_⟩
    obtain ⟨a', ha', rfl⟩ := Sym.mem_map.mp ha
    have := (inBlock_skip_iff i b a').not.mpr (hm' a' ha')
    rwa [relabel, ite_eq_left hb] at this
  · exact pushSkip_of_not_mem i f hr

omit [CharZero 𝕜] in
/-- **The trace step** (Torrance–Vannieuwenhoven, Lemma 4.4). The points of the configuration
`A_{i,K+1}(t+3)` lying on `U_i` form, via the embedding skipping block `i`, the configuration
`A_{i,K}(t)`, whose span lies in `A_{i,K+1}(t+3) ⊓ P̂_i`; and `A_{i,K+1}(t+3) ⊔ P̂_i`
contains `A_{i+1,K+1}(t+3)`. Grassmann's formula then gives
`dim A_{i,K+1}(t+3) ≥ dim A_{i+1,K+1}(t+3) + dim A_{i,K}(t) - N(t)`. -/
theorem Good.trace {i m₁ m₂ : ℕ} (hi : i ≤ K) (hit : 3 * i ≤ t + 4 + 1)
    (hsmall : Good 𝕜 s t K i m₁) (hbig : Good 𝕜 s (t + 3) (K + 1) (i + 1) m₂) :
    Good 𝕜 s (t + 3) (K + 1) i (m₂ + m₁ - (t + 7).choose 3) := by
  classical
  -- small slots correspond to the big slots on `U_i`
  have hloc : ∀ I : Loc K, traceLoc i (I : Finset ℕ) ∈ (Finset.range (K + 1)).powerset :=
    fun I => by
      have hI := Finset.mem_powerset.mp I.2
      refine Finset.mem_powerset.mpr (Finset.insert_subset (by simp; omega) ?_)
      intro b hb
      obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
      have := Finset.mem_range.mp (hI hb')
      simp only [Finset.mem_range, relabel]
      split_ifs <;> omega
  let bigLoc : Loc K → Loc (K + 1) := fun I => ⟨traceLoc i I, hloc I⟩
  let bigSlot : Slot s t K → Slot s (t + 3) (K + 1) := fun σ =>
    ⟨bigLoc σ.1, Fin.cast (countAt_traceLoc i σ.1).symm σ.2⟩
  let φ : Param s t K → Param s (t + 3) (K + 1) := fun p => (bigSlot p.1, skip i p.2)
  have hφ : Function.Injective φ := by
    rintro ⟨⟨I, c⟩, j⟩ ⟨⟨I', c'⟩, j'⟩ h
    simp only [φ, bigSlot, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hI, hc⟩ := Sigma.mk.inj_iff.mp h1
    have hII' : I = I' := Subtype.ext (traceLoc_injective i (congrArg Subtype.val hI))
    subst hII'
    have hcc' : c = c' := by
      have := (Fin.heq_ext_iff rfl).mp hc
      exact Fin.ext (by simpa using this)
    subst hcc'
    rw [skip_injective i h2]
  refine (hbig.and (hsmall.comap hφ)).mono fun x ⟨h₂, h₁⟩ => ?_
  -- the trace configuration space
  have hpoint : ∀ σ : Slot s t K,
      extSkip i (configPoint (x ∘ φ) σ) = configPoint x (bigSlot σ) := by
    intro σ
    have hz : configPoint (x ∘ φ) σ = configPoint x (bigSlot σ) ∘ skip i := by
      simp only [configPoint]
      rw [zeroBlocks_comp_skip]
      congr 1
      exact (traceLoc_erase i σ.1).symm
    rw [hz, extSkip_comp_skip (by omega)]
    intro a ha
    simp only [configPoint, zeroBlocks]
    exact ite_eq_left ⟨i, Finset.mem_insert_self _ _, ha⟩
  have htrace : (configSpace s t K i (x ∘ φ)).map (pushSkip (𝕜 := 𝕜) i).toLinearMap
      ≤ configSpace s (t + 3) (K + 1) i x ⊓ latticeSpace (t + 3 + 4) 3 i := by
    have hP : ∀ V : Submodule 𝕜 (Sym (Fin (t + 4 + 1)) 3 → 𝕜),
        V.map (pushSkip (𝕜 := 𝕜) i).toLinearMap ≤ latticeSpace (t + 3 + 4) 3 i := fun V => by
      show _ ≤ latticeSpace (t + 4 + 3) 3 i
      rw [← range_pushSkip (by omega)]
      exact LinearMap.map_le_range
    refine le_inf ?_ (hP _)
    rw [configSpace, Submodule.map_sup, Submodule.map_iSup]
    refine sup_le_sup (map_monoSpan_latticeSet_le t i) (iSup_le fun σ => ?_)
    refine (map_tangentSpace_pushSkip_le i _).trans (le_iSup_of_le (bigSlot σ) ?_)
    exact le_of_eq (congrArg (fun v => (veroneseDegParam (𝕜 := 𝕜) (t + 3 + 4) 3 v).tangentSpace)
      (hpoint σ))
  have hsup : configSpace s (t + 3) (K + 1) (i + 1) x
      ≤ configSpace s (t + 3) (K + 1) i x ⊔ latticeSpace (t + 3 + 4) 3 i := by
    rw [configSpace, configSpace, sup_right_comm]
    exact sup_le_sup_right (monoSpan_latticeSet_succ_le (t + 3) i) _
  -- dimensions
  have hfP : Module.finrank 𝕜 (latticeSpace (𝕜 := 𝕜) (t + 3 + 4) 3 i) = (t + 7).choose 3 := by
    show Module.finrank 𝕜 (latticeSpace (𝕜 := 𝕜) (t + 4 + 3) 3 i) = _
    rw [← range_pushSkip (by omega), LinearMap.finrank_range_of_inj (pushSkip_injective i),
      finrank_ambient_veroneseDeg]
  have hfmap : Module.finrank 𝕜 ((configSpace s t K i (x ∘ φ)).map
      (pushSkip (𝕜 := 𝕜) i).toLinearMap) = Module.finrank 𝕜 (configSpace s t K i (x ∘ φ)) :=
    (Submodule.equivMapOfInjective _ (pushSkip_injective i) _).finrank_eq.symm
  have hgrass := Submodule.finrank_sup_add_finrank_inf_eq (configSpace s (t + 3) (K + 1) i x)
    (latticeSpace (t + 3 + 4) 3 i)
  have h3 : Module.finrank 𝕜 (configSpace s (t + 3) (K + 1) (i + 1) x)
      ≤ Module.finrank 𝕜 (configSpace s (t + 3) (K + 1) i x ⊔ latticeSpace (t + 3 + 4) 3 i :
        Submodule 𝕜 _) := Submodule.finrank_mono hsup
  have h4 : Module.finrank 𝕜 ((configSpace s t K i (x ∘ φ)).map
      (pushSkip (𝕜 := 𝕜) i).toLinearMap)
      ≤ Module.finrank 𝕜 (configSpace s (t + 3) (K + 1) i x ⊓ latticeSpace (t + 3 + 4) 3 i :
        Submodule 𝕜 _) := Submodule.finrank_mono htrace
  omega

end CubicInduction
