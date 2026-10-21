module

public import TerraciniLemma.VeroneseDegree
public import TerraciniLemma.Semicontinuity
public import Mathlib.Algebra.MvPolynomial.Monad

/-!
# Coordinate lattices for the Brambilla–Ottaviani induction

The Brambilla–Ottaviani induction for cubics, in the linear-algebra form of
Torrance–Vannieuwenhoven (*All secant varieties of the Chow variety are nondefective for cubics
and quaternary forms*, Trans. AMS **374** (2021), §4), specializes points of `ℙⁿ` to a lattice of
codimension-`3` linear subspaces `U₀, U₁, U₂` and compares tangent spaces with the subspaces
`P̂ⱼ = S³Uⱼ` of the ambient space. We take the `Uⱼ` to be *coordinate* subspaces:
`Uⱼ = {x | x_a = 0 for a in block j}`, block `j` being the coordinates `3j, 3j+1, 3j+2`. Then
each `P̂ⱼ` is a *monomial* subspace (`latticeSpace`): spanned by the monomials avoiding block
`j`.

This file provides:

* §A — monomial subspaces `monoSpan S` of the ambient space `Sym (Fin (n+1)) d → 𝕜` and the
  dimension formula `finrank (monoSpan S ⊔ W) = finrank (monoSpan S) + finrank (W restricted
  to the coordinates outside S)` (`finrank_monoSpan_sup`);
* §B — blocks, the lattice spaces `latticeSpace n d b`, and the block-zeroing maps
  `zeroBlocks` that place points on intersections of the `Uⱼ`;
* §C — for an injective coordinate map `ι`, extension by zero `extAlong ι` of points and the
  induced pushforward `pushAlong ι` of ambient spaces; they intertwine the Veronese maps
  (`veroneseDeg_extAlong`) and their derivatives (`veroneseDegDeriv_extAlong`), so tangent
  spaces push forward to tangent spaces (`map_tangentSpace_pushAlong_le`);
* §D — the embedding `skip b : Fin (n+1) → Fin (n+3+1)` missing block `b`, which identifies
  `𝕜^{n+1}` with `U_b ⊆ 𝕜^{n+4}`. The pushforward `pushSkip b` is injective with image
  `latticeSpace (n+3) d b` (`range_pushSkip`) and sends lattice spaces to lattice spaces
  (`map_latticeSpace_pushSkip_le`). This is what identifies the *trace* of a configuration on
  `P̂_b` with a configuration one level down;
* §E — polynomial dependence on the points: lower bounds for `monoSpan S ⊔ ∑ T_p` at one
  choice of polynomially parametrized points hold generically (`holdsGenerically_le_finrank`).
-/

@[expose] public section

noncomputable section CubicLattice

open MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-! ### §A — Monomial subspaces -/

section MonoSpan

variable {n d : ℕ}

/-- The coordinate subspace of the ambient space spanned by the monomials in `S`: the
functions vanishing outside `S`. -/
def monoSpan (n d : ℕ) (S : Set (Sym (Fin (n + 1)) d)) :
    Submodule 𝕜 (Sym (Fin (n + 1)) d → 𝕜) where
  carrier := {f | ∀ s, s ∉ S → f s = 0}
  add_mem' {f g} hf hg s hs := by simp [hf s hs, hg s hs]
  zero_mem' _ _ := rfl
  smul_mem' c f hf s hs := by simp [hf s hs]

theorem mem_monoSpan {S : Set (Sym (Fin (n + 1)) d)} {f : Sym (Fin (n + 1)) d → 𝕜} :
    f ∈ monoSpan n d S ↔ ∀ s, s ∉ S → f s = 0 := Iff.rfl

theorem monoSpan_mono {S S' : Set (Sym (Fin (n + 1)) d)} (h : S ⊆ S') :
    (monoSpan n d S : Submodule 𝕜 _) ≤ monoSpan n d S' :=
  fun _ hf s hs => hf s (fun h' => hs (h h'))

/-- Restriction of an ambient vector to the coordinates in `T`. -/
def coordRestrict (n d : ℕ) (T : Set (Sym (Fin (n + 1)) d)) :
    (Sym (Fin (n + 1)) d → 𝕜) →ₗ[𝕜] (T → 𝕜) :=
  LinearMap.funLeft 𝕜 𝕜 Subtype.val

theorem ker_coordRestrict_compl (S : Set (Sym (Fin (n + 1)) d)) :
    LinearMap.ker (coordRestrict (𝕜 := 𝕜) n d Sᶜ) = monoSpan n d S := by
  ext f
  simp only [LinearMap.mem_ker, mem_monoSpan]
  constructor
  · intro h s hs
    exact congrFun h ⟨s, hs⟩
  · intro h
    funext ⟨s, hs⟩
    exact h s hs

/-- **Dimension of a monomial subspace plus a subspace**: the monomial subspace contributes its
own dimension, and `W` contributes the dimension of its restriction to the other
coordinates. -/
theorem finrank_monoSpan_sup (S : Set (Sym (Fin (n + 1)) d))
    (W : Submodule 𝕜 (Sym (Fin (n + 1)) d → 𝕜)) :
    Module.finrank 𝕜 (monoSpan n d S ⊔ W : Submodule 𝕜 _)
      = Module.finrank 𝕜 (monoSpan (𝕜 := 𝕜) n d S)
        + Module.finrank 𝕜 (W.map (coordRestrict n d Sᶜ)) := by
  set X : Submodule 𝕜 _ := monoSpan n d S ⊔ W
  set φ := coordRestrict (𝕜 := 𝕜) n d Sᶜ
  have h1 := LinearMap.finrank_range_add_finrank_ker (φ.domRestrict X)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h1
  have hmap : X.map φ = W.map φ := by
    rw [Submodule.map_sup, (LinearMap.le_ker_iff_map).mp (ker_coordRestrict_compl S).ge,
      bot_sup_eq]
  have hle : LinearMap.ker φ ≤ X := by
    rw [ker_coordRestrict_compl]
    exact le_sup_left
  rw [hmap, LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle),
    ker_coordRestrict_compl] at h1
  omega

/-- A monomial subspace plus `W` is everything iff `W` restricted to the other coordinates is
everything. -/
theorem monoSpan_sup_eq_top_iff (S : Set (Sym (Fin (n + 1)) d))
    (W : Submodule 𝕜 (Sym (Fin (n + 1)) d → 𝕜)) :
    monoSpan n d S ⊔ W = ⊤ ↔ W.map (coordRestrict n d Sᶜ) = ⊤ := by
  set φ := coordRestrict (𝕜 := 𝕜) n d Sᶜ
  have hsurj : Function.Surjective φ :=
    LinearMap.funLeft_surjective_of_injective _ _ _ Subtype.val_injective
  constructor
  · intro h
    rw [eq_top_iff]
    rintro y -
    obtain ⟨f, rfl⟩ := hsurj y
    have hf : f ∈ monoSpan n d S ⊔ W := h ▸ Submodule.mem_top
    obtain ⟨g, hg, w, hw, rfl⟩ := Submodule.mem_sup.mp hf
    have hφg : φ g = 0 := by rwa [← LinearMap.mem_ker, ker_coordRestrict_compl]
    exact ⟨w, hw, by rw [map_add, hφg, zero_add]⟩
  · intro h
    rw [eq_top_iff]
    rintro f -
    obtain ⟨w, hw, hwf⟩ := (h ▸ Submodule.mem_top : φ f ∈ W.map φ)
    have hker : f - w ∈ monoSpan n d S := by
      rw [← ker_coordRestrict_compl, LinearMap.mem_ker, map_sub, hwf, sub_self]
    simpa using Submodule.add_mem_sup hker hw

end MonoSpan

/-! ### §B — Blocks and lattice spaces -/

section Blocks

variable {n d : ℕ}

/-- The coordinate `a` lies in block `b`, i.e. `a ∈ {3b, 3b+1, 3b+2}`. -/
def InBlock (b : ℕ) (a : Fin (n + 1)) : Prop := 3 * b ≤ (a : ℕ) ∧ (a : ℕ) < 3 * b + 3

instance (b : ℕ) (a : Fin (n + 1)) : Decidable (InBlock b a) := by
  unfold InBlock; infer_instance

/-- The monomial `s` avoids block `b`. -/
def AvoidsBlock (b : ℕ) (s : Sym (Fin (n + 1)) d) : Prop := ∀ a ∈ s, ¬ InBlock b a

/-- The lattice space `P̂_b = S^d U_b`, `U_b` the coordinate subspace killing block `b`:
spanned by the monomials avoiding block `b`. -/
def latticeSpace (n d b : ℕ) : Submodule 𝕜 (Sym (Fin (n + 1)) d → 𝕜) :=
  monoSpan n d {s | AvoidsBlock b s}

/-- Zero the coordinates in the blocks `B`: this places a point on `⋂_{b ∈ B} U_b`. -/
def zeroBlocks (B : Finset ℕ) (x : Fin (n + 1) → 𝕜) : Fin (n + 1) → 𝕜 :=
  fun a => if ∃ b ∈ B, InBlock b a then 0 else x a

end Blocks

/-! ### §C — Pushing forward along a coordinate embedding -/

section Along

variable {m n d : ℕ}

/-- A multiset all of whose elements lie in the range of a map is itself in the
range of the induced map on `Sym`. -/
theorem sym_mem_range_map {α β : Type*} [Nonempty α] {f : α → β} {s : Sym β d} (hs : ∀ a ∈ s, a ∈ Set.range f) : s ∈ Set.range (Sym.map (n := d) f) := by
  refine ⟨Sym.map (Function.invFun f) s, ?_⟩
  rw [Sym.map_map]
  conv_rhs => rw [← Sym.map_id s]
  exact Sym.map_congr fun a ha => Function.invFun_eq (hs a ha)

/-- Extension by zero along a map of coordinates `ι : Fin (m+1) → Fin (n+1)`. -/
def extAlong (ι : Fin (m + 1) → Fin (n + 1)) : (Fin (m + 1) → 𝕜) →L[𝕜] (Fin (n + 1) → 𝕜) where
  toFun y a := if ∃ a', ι a' = a then y (Function.invFun ι a) else 0
  map_add' y y' := by
    funext a
    by_cases h : ∃ a', ι a' = a <;> simp [h]
  map_smul' c y := by
    funext a
    by_cases h : ∃ a', ι a' = a <;> simp [h]
  cont := continuous_pi fun a => by
    split_ifs
    · exact continuous_apply _
    · exact continuous_const

/-- Pushforward of ambient vectors along `ι`: `(pushAlong ι f)(s) = f(s')` if `s = ι(s')`,
and `0` otherwise. -/
def pushAlong (ι : Fin (m + 1) → Fin (n + 1)) :
    (Sym (Fin (m + 1)) d → 𝕜) →L[𝕜] (Sym (Fin (n + 1)) d → 𝕜) where
  toFun f s := if ∃ s', Sym.map ι s' = s then f (Function.invFun (Sym.map ι) s) else 0
  map_add' f g := by
    funext s
    by_cases h : ∃ s', Sym.map ι s' = s <;> simp [h]
  map_smul' c f := by
    funext s
    by_cases h : ∃ s', Sym.map ι s' = s <;> simp [h]
  cont := continuous_pi fun s => by
    split_ifs
    · exact continuous_apply _
    · exact continuous_const

variable {ι : Fin (m + 1) → Fin (n + 1)}

theorem extAlong_apply (hι : Function.Injective ι) (y : Fin (m + 1) → 𝕜) (a : Fin (m + 1)) :
    extAlong (𝕜 := 𝕜) ι y (ι a) = y a := by
  simp only [extAlong, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  rw [ite_eq_left ⟨a, rfl⟩, Function.leftInverse_invFun hι a]

theorem extAlong_of_not_mem (y : Fin (m + 1) → 𝕜) {a : Fin (n + 1)} (ha : a ∉ Set.range ι) :
    extAlong (𝕜 := 𝕜) ι y a = 0 := by
  simp only [extAlong, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  exact ite_eq_right ha

theorem pushAlong_map (hι : Function.Injective ι) (f : Sym (Fin (m + 1)) d → 𝕜)
    (s : Sym (Fin (m + 1)) d) : pushAlong (𝕜 := 𝕜) ι f (Sym.map ι s) = f s := by
  simp only [pushAlong, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  rw [ite_eq_left ⟨s, rfl⟩, Function.leftInverse_invFun (Sym.map_injective hι d) s]

theorem pushAlong_of_not_mem (f : Sym (Fin (m + 1)) d → 𝕜) {s : Sym (Fin (n + 1)) d}
    (hs : s ∉ Set.range (Sym.map ι)) : pushAlong (𝕜 := 𝕜) ι f s = 0 := by
  simp only [pushAlong, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk]
  exact ite_eq_right hs

theorem pushAlong_injective (hι : Function.Injective ι) :
    Function.Injective (pushAlong (𝕜 := 𝕜) (d := d) ι) := by
  intro f g h
  funext s
  rw [← pushAlong_map hι f s, ← pushAlong_map hι g s, h]

/-- The Veronese map commutes with `ι`. -/
theorem veroneseDeg_extAlong (hι : Function.Injective ι) (y : Fin (m + 1) → 𝕜) :
    veroneseDeg n d (extAlong ι y) = pushAlong ι (veroneseDeg m d y) := by
  funext s
  by_cases hs : s ∈ Set.range (Sym.map ι)
  · obtain ⟨s', rfl⟩ := hs
    rw [pushAlong_map hι]
    simp only [veroneseDeg, veroneseDegPoly, map_multiset_prod, Multiset.map_map,
      Function.comp_def, eval_X, Sym.val_eq_coe, Sym.coe_map, extAlong_apply hι]
  · rw [pushAlong_of_not_mem _ hs]
    -- some coordinate of `s` is outside the range of `ι`, where `extAlong ι y` vanishes
    obtain ⟨a, ha, hna⟩ : ∃ a ∈ s, a ∉ Set.range ι := by
      by_contra! h
      exact hs (sym_mem_range_map h)
    simp only [veroneseDeg, veroneseDegPoly, map_multiset_prod, Multiset.map_map,
      Function.comp_def, eval_X]
    exact Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨a, ha, extAlong_of_not_mem y hna⟩)

/-- The derivatives of the Veronese maps commute with `ι`. -/
theorem veroneseDegDeriv_extAlong (hι : Function.Injective ι) (y : Fin (m + 1) → 𝕜) :
    (veroneseDegDeriv n d (extAlong ι y)).comp (extAlong ι)
      = (pushAlong ι).comp (veroneseDegDeriv m d y) := by
  have h1 := (hasFDerivAt_veroneseDeg (𝕜 := 𝕜) n d (extAlong ι y)).comp y
    (extAlong (𝕜 := 𝕜) ι).hasFDerivAt
  have h2 := (pushAlong (𝕜 := 𝕜) (d := d) ι).hasFDerivAt.comp y
    (hasFDerivAt_veroneseDeg (𝕜 := 𝕜) m d y)
  rw [show veroneseDeg n d ∘ ⇑(extAlong (𝕜 := 𝕜) ι) = ⇑(pushAlong ι) ∘ veroneseDeg m d from
    funext fun y => veroneseDeg_extAlong hι y] at h1
  exact h1.unique h2

/-- `ι` sends tangent spaces into tangent spaces. -/
theorem map_tangentSpace_pushAlong_le (hι : Function.Injective ι) (y : Fin (m + 1) → 𝕜) :
    (veroneseDegParam m d y).tangentSpace.map (pushAlong (𝕜 := 𝕜) ι).toLinearMap
      ≤ (veroneseDegParam n d (extAlong ι y)).tangentSpace := by
  rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
  refine ⟨extAlong ι w, ?_⟩
  have := congrArg (fun L : (Fin (m + 1) → 𝕜) →L[𝕜] _ => L w)
    (veroneseDegDeriv_extAlong (d := d) hι y)
  simpa [veroneseDegParam] using this

end Along

/-! ### §D — Skipping a block -/

section Skip

variable {n d : ℕ}

/-- The order-preserving embedding `Fin (n+1) → Fin (n+3+1)` missing block `b`. -/
def skip (b : ℕ) (a : Fin (n + 1)) : Fin (n + 3 + 1) :=
  if (a : ℕ) < 3 * b then ⟨a, by omega⟩ else ⟨a + 3, by omega⟩

theorem skip_val (b : ℕ) (a : Fin (n + 1)) :
    (skip b a : ℕ) = if (a : ℕ) < 3 * b then (a : ℕ) else (a : ℕ) + 3 := by
  unfold skip; split_ifs <;> rfl

theorem skip_injective (b : ℕ) : Function.Injective (skip (n := n) b) := by
  intro a a' h
  have := congrArg Fin.val h
  rw [skip_val, skip_val] at this
  ext
  split_ifs at this <;> omega

/-- The image of `skip b` is the complement of block `b` (when block `b` fits). -/
theorem mem_range_skip {b : ℕ} (hb : 3 * b ≤ n + 1) (a : Fin (n + 3 + 1)) :
    a ∈ Set.range (skip (n := n) b) ↔ ¬ InBlock b a := by
  constructor
  · rintro ⟨a', rfl⟩
    rw [InBlock, skip_val]
    split_ifs <;> omega
  · intro h
    simp only [InBlock, not_and_or, not_le, not_lt] at h
    rcases h with h | h
    · exact ⟨⟨a, by omega⟩, Fin.ext (by rw [skip_val]; simp [h])⟩
    · refine ⟨⟨a - 3, by omega⟩, Fin.ext ?_⟩
      rw [skip_val, ite_eq_right (by simp only; omega)]
      simp only
      omega

/-- A monomial is in the range of `Sym.map (skip b)` iff it avoids block `b`. -/
theorem mem_range_symMap_skip {b : ℕ} (hb : 3 * b ≤ n + 1) (s : Sym (Fin (n + 3 + 1)) d) :
    s ∈ Set.range (Sym.map (skip (n := n) b)) ↔ AvoidsBlock b s := by
  constructor
  · rintro ⟨s', rfl⟩ a ha
    obtain ⟨a', -, rfl⟩ := Sym.mem_map.mp ha
    exact (mem_range_skip hb _).mp ⟨a', rfl⟩
  · intro h
    exact sym_mem_range_map fun a ha => (mem_range_skip hb a).mpr (h a ha)

/-- Extension by zero along `skip b`: identifies `𝕜^{n+1}` with `U_b ⊆ 𝕜^{n+4}`. -/
abbrev extSkip (b : ℕ) : (Fin (n + 1) → 𝕜) →L[𝕜] (Fin (n + 3 + 1) → 𝕜) := extAlong (skip b)

/-- Pushforward of ambient vectors along `skip b`. -/
abbrev pushSkip (b : ℕ) : (Sym (Fin (n + 1)) d → 𝕜) →L[𝕜] (Sym (Fin (n + 3 + 1)) d → 𝕜) :=
  pushAlong (skip b)

theorem extSkip_skip (b : ℕ) (y : Fin (n + 1) → 𝕜) (a : Fin (n + 1)) :
    extSkip (𝕜 := 𝕜) b y (skip b a) = y a := extAlong_apply (skip_injective b) y a

theorem extSkip_of_not_mem (b : ℕ) (y : Fin (n + 1) → 𝕜) {a : Fin (n + 3 + 1)}
    (ha : a ∉ Set.range (skip b)) : extSkip (𝕜 := 𝕜) b y a = 0 := extAlong_of_not_mem y ha

theorem pushSkip_map (b : ℕ) (f : Sym (Fin (n + 1)) d → 𝕜) (s : Sym (Fin (n + 1)) d) :
    pushSkip (𝕜 := 𝕜) b f (Sym.map (skip b) s) = f s := pushAlong_map (skip_injective b) f s

theorem pushSkip_of_not_mem (b : ℕ) (f : Sym (Fin (n + 1)) d → 𝕜) {s : Sym (Fin (n + 3 + 1)) d}
    (hs : s ∉ Set.range (Sym.map (skip b))) : pushSkip (𝕜 := 𝕜) b f s = 0 :=
  pushAlong_of_not_mem f hs

theorem pushSkip_injective (b : ℕ) :
    Function.Injective (pushSkip (𝕜 := 𝕜) (n := n) (d := d) b) :=
  pushAlong_injective (skip_injective b)

/-- The pushforward along `skip b` has image the lattice space `P̂_b`. -/
theorem range_pushSkip {b : ℕ} (hb : 3 * b ≤ n + 1) :
    LinearMap.range (pushSkip (𝕜 := 𝕜) (n := n) (d := d) b).toLinearMap
      = latticeSpace (n + 3) d b := by
  ext f
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, latticeSpace, mem_monoSpan,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨g, rfl⟩ s hs
    exact pushSkip_of_not_mem b g (fun h => hs ((mem_range_symMap_skip hb s).mp h))
  · intro h
    refine ⟨fun s' => f (Sym.map (skip b) s'), funext fun s => ?_⟩
    by_cases hs : s ∈ Set.range (Sym.map (skip b))
    · obtain ⟨s', rfl⟩ := hs
      rw [pushSkip_map]
    · rw [pushSkip_of_not_mem b _ hs, h s fun h' => hs ((mem_range_symMap_skip hb s).mpr h')]

/-- `skip b` sends tangent spaces into tangent spaces. -/
theorem map_tangentSpace_pushSkip_le (b : ℕ) (y : Fin (n + 1) → 𝕜) :
    (veroneseDegParam n d y).tangentSpace.map (pushSkip (𝕜 := 𝕜) b).toLinearMap
      ≤ (veroneseDegParam (n + 3) d (extSkip b y)).tangentSpace :=
  map_tangentSpace_pushAlong_le (skip_injective b) y

/-- Relabelling of blocks along `skip b`: block `b'` of `𝕜^{n+1}` becomes block `b'` or
`b' + 1` of `𝕜^{n+4}`, according as it lies before or after the skipped block `b`. -/
def relabel (b b' : ℕ) : ℕ := if b' < b then b' else b' + 1

theorem inBlock_skip_iff (b b' : ℕ) (a : Fin (n + 1)) :
    InBlock (relabel b b') (skip b a) ↔ InBlock b' a := by
  simp only [InBlock, relabel, skip_val]
  split_ifs <;> omega

theorem not_inBlock_skip (b : ℕ) (a : Fin (n + 1)) : ¬ InBlock b (skip b a) := by
  simp only [InBlock, skip_val]
  split_ifs <;> omega

/-- `skip b` sends lattice spaces to lattice spaces. -/
theorem map_latticeSpace_pushSkip_le (b b' : ℕ) :
    (latticeSpace n d b').map (pushSkip (𝕜 := 𝕜) b).toLinearMap
      ≤ latticeSpace (n + 3) d (relabel b b') := by
  rintro _ ⟨f, hf, rfl⟩ s hs
  by_cases hr : s ∈ Set.range (Sym.map (skip b))
  · obtain ⟨s', rfl⟩ := hr
    simp only [ContinuousLinearMap.coe_coe, pushSkip_map]
    refine hf s' fun hs' => hs fun a ha => ?_
    obtain ⟨a', ha', rfl⟩ := Sym.mem_map.mp ha
    exact (inBlock_skip_iff b b' a').not.mpr (hs' a' ha')
  · exact pushSkip_of_not_mem b f hr

/-- Inverse relabelling of the blocks other than `b`. -/
def unrelabel (b b'' : ℕ) : ℕ := if b'' < b then b'' else b'' - 1

theorem relabel_unrelabel {b b'' : ℕ} (h : b'' ≠ b) : relabel b (unrelabel b b'') = b'' := by
  simp only [relabel, unrelabel]
  split_ifs <;> omega

/-- Points with block `b` zeroed are exactly the images of `extSkip b`. -/
theorem extSkip_comp_skip {b : ℕ} (hb : 3 * b ≤ n + 1) {x : Fin (n + 3 + 1) → 𝕜}
    (hx : ∀ a, InBlock b a → x a = 0) : extSkip b (x ∘ skip b) = x := by
  funext a
  by_cases ha : a ∈ Set.range (skip b)
  · obtain ⟨a', rfl⟩ := ha
    rw [extSkip_skip]
    rfl
  · rw [extSkip_of_not_mem b _ ha, hx a ((mem_range_skip hb a).not.mp ha |> not_not.mp)]

/-- Zeroing blocks commutes with `skip b`. -/
theorem zeroBlocks_comp_skip (b : ℕ) (B : Finset ℕ) (x : Fin (n + 3 + 1) → 𝕜) :
    zeroBlocks B x ∘ skip b = zeroBlocks ((B.erase b).image (unrelabel b)) (x ∘ skip b) := by
  funext a
  simp only [Function.comp_apply, zeroBlocks, Finset.mem_image, Finset.mem_erase]
  congr 1
  apply propext
  constructor
  · rintro ⟨b'', hb'', hin⟩
    have hne : b'' ≠ b := fun h => not_inBlock_skip b a (h ▸ hin)
    refine ⟨unrelabel b b'', Finset.mem_image.mpr ⟨b'', Finset.mem_erase.mpr ⟨hne, hb''⟩, rfl⟩,
      ?_⟩
    rwa [← inBlock_skip_iff b, relabel_unrelabel hne]
  · rintro ⟨b', hb', hin⟩
    obtain ⟨b'', hb'', rfl⟩ := Finset.mem_image.mp hb'
    obtain ⟨hne, hb''⟩ := Finset.mem_erase.mp hb''
    refine ⟨b'', hb'', ?_⟩
    rwa [← inBlock_skip_iff b, relabel_unrelabel hne] at hin

end Skip

/-! ### §E — Semicontinuity for monomial subspaces plus tangent spaces -/

section Semicontinuity

variable {n d : ℕ}

theorem monoSpan_eq_span (S : Set (Sym (Fin (n + 1)) d)) :
    (monoSpan n d S : Submodule 𝕜 _) = Submodule.span 𝕜 ((fun s => Pi.single s 1) '' S) := by
  classical
  apply le_antisymm
  · intro f hf
    have hsum : f = ∑ s, f s • (Pi.single s 1 : Sym (Fin (n + 1)) d → 𝕜) := by
      funext s'
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    refine Submodule.sum_mem _ fun s _ => ?_
    by_cases hs : s ∈ S
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, hs, rfl⟩)
    · rw [hf s hs, zero_smul]
      exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩ s' hs'
    show (Pi.single s 1 : Sym (Fin (n + 1)) d → 𝕜) s' = 0
    rw [Pi.single_apply, ite_eq_right]
    rintro rfl
    exact hs' hs

/-- The tangent space at `v` is spanned by the derivatives along the coordinate directions. -/
theorem tangentSpace_eq_span (v : Fin (n + 1) → 𝕜) :
    (veroneseDegParam n d v).tangentSpace
      = Submodule.span 𝕜 (Set.range fun j => veroneseDegDeriv n d v (Pi.single j 1)) := by
  classical
  show LinearMap.range (veroneseDegDeriv n d v).toLinearMap = _
  rw [LinearMap.range_eq_map, ← (Pi.basisFun 𝕜 (Fin (n + 1))).span_eq, Submodule.map_span,
    ← Set.range_comp]
  congr 1
  ext; simp

/-- The derivative of `veroneseDeg` along the coordinate direction `j`, at the monomial `s`,
is the evaluation of the formal partial derivative. -/
theorem veroneseDegDeriv_single (v : Fin (n + 1) → 𝕜) (j : Fin (n + 1))
    (s : Sym (Fin (n + 1)) d) :
    veroneseDegDeriv n d v (Pi.single j 1) s = eval v (pderiv j (veroneseDegPoly n d s)) := by
  classical
  simp [veroneseDegDeriv, mvPolynomialDeriv, coordProj_apply, Pi.single_apply]

/-- A point of `𝕜^{n+1}` whose coordinates are polynomials in parameters `x : σ → 𝕜`. -/
def polyPoint {σ : Type*} (P : Fin (n + 1) → MvPolynomial σ 𝕜) (x : σ → 𝕜) : Fin (n + 1) → 𝕜 :=
  fun j => eval x (P j)

/-- **Semicontinuity for configurations.** Let points `P k` depend polynomially on parameters
`x`. If a monomial subspace together with the tangent spaces at the points has dimension
`≥ m` at one parameter value, it has dimension `≥ m` at general parameter values. -/
theorem holdsGenerically_le_finrank {ι σ : Type*} [Fintype ι] (S : Set (Sym (Fin (n + 1)) d))
    (P : ι → Fin (n + 1) → MvPolynomial σ 𝕜) {m : ℕ} (x₀ : σ → 𝕜)
    (h : m ≤ Module.finrank 𝕜 (monoSpan n d S ⊔
      ⨆ k, (veroneseDegParam n d (polyPoint (P k) x₀)).tangentSpace : Submodule 𝕜 _)) :
    HoldsGenerically σ fun x => m ≤ Module.finrank 𝕜 (monoSpan n d S ⊔
      ⨆ k, (veroneseDegParam n d (polyPoint (P k) x)).tangentSpace : Submodule 𝕜 _) := by
  classical
  -- the matrix whose columns are the monomials of `S` and the coordinate derivatives
  let M : Matrix (Sym (Fin (n + 1)) d) (S ⊕ ι × Fin (n + 1)) (MvPolynomial σ 𝕜) :=
    Matrix.of fun s c => match c with
      | .inl s' => if s = s' then 1 else 0
      | .inr (k, j) => bind₁ (P k) (pderiv j (veroneseDegPoly n d s))
  have hspan : ∀ x : σ → 𝕜, Module.finrank 𝕜 (monoSpan n d S ⊔
      ⨆ k, (veroneseDegParam n d (polyPoint (P k) x)).tangentSpace : Submodule 𝕜 _)
        = (M.map (eval x)).rank := by
    intro x
    have hcol : (M.map (eval x)).col = Sum.elim (fun s' : S => Pi.single (s' : Sym _ d) 1)
        (fun kj => veroneseDegDeriv n d (polyPoint (P kj.1) x) (Pi.single kj.2 1)) := by
      funext c s
      rcases c with s' | ⟨k, j⟩
      · simp only [Matrix.col_apply, Matrix.map_apply, Matrix.of_apply, M, Sum.elim_inl,
          Pi.single_apply]
        split_ifs <;> simp
      · simp only [Matrix.col_apply, Matrix.map_apply, Matrix.of_apply, M, Sum.elim_inr]
        rw [veroneseDegDeriv_single]
        show eval₂Hom (RingHom.id 𝕜) x _ = _
        rw [eval₂Hom_bind₁]
        rfl
    have heq : (monoSpan n d S ⊔
        ⨆ k, (veroneseDegParam n d (polyPoint (P k) x)).tangentSpace : Submodule 𝕜 _)
          = Submodule.span 𝕜 (Set.range (M.map (eval x)).col) := by
      rw [hcol, Set.Sum.elim_range, Submodule.span_union, monoSpan_eq_span,
        Set.image_eq_range]
      congr 1
      simp_rw [tangentSpace_eq_span, Submodule.span_range_eq_iSup]
      exact (iSup_prod (f := fun kj : ι × Fin (n + 1) => Submodule.span 𝕜
        {veroneseDegDeriv n d (polyPoint (P kj.1) x) (Pi.single kj.2 1)})).symm
    rw [Matrix.rank_eq_finrank_span_cols, heq]
  rw [hspan] at h
  exact (HoldsGenerically.le_rank M x₀ h).mono fun x hx => (hspan x).symm ▸ hx

end Semicontinuity

end CubicLattice
