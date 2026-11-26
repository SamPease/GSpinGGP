/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.SpecialK
import GSpinGGP.Sanity.GL2GoodK
import GSpinGGP.Foundations.ValueGroup

/-!
# `GoodK.IsSpecial` at `gl2Data`: satisfiable, and not every `GoodK`

At `gl2Data` (`W = 0`, `V` split of dimension `3`, `q = ac + b²` in the coordinates of
`gl2Basis`; `Sanity/GL2GoodK.lean`) with the torus datum `gl2Levi`:

* `gl2SpecialV`: the lattice `Λ` spanned by `z₋₁, z₀, ½ z₁` is W1-special (Waldspurger 2010,
  §7.1) with `c = 0`: the hyperbolic pair `v = z₋₁`, `v' = ½ z₁` (`polar(v, v') = 1`),
  `V_an = F z₀` with `q(z₀) = 1`, so `R_an = 𝒪_F z₀` and `R = Λ` (`gl2SpecialV_R`).  It is adapted
  to the weight basis of `gl2Levi`.
* `gl2GoodK_isSpecial`: the existing `gl2GoodK` is special (so `IsSpecial` is satisfiable).
* `gl2GoodK'`: the subgroup of `gl2GoodK` where the `GSpin(W) = F^×` component `u` has
  `‖u − 1‖ < ‖ϖ‖`, for some `0 < ‖ϖ‖ < 1`.  It is a `GoodK` (`G = P K'` because the `W`-component
  is central and lies in every parabolic), of finite index in `gl2GoodK`, and it is **not** special
  (`not_isSpecial_gl2GoodK'`): every special stabilizer contains all scalars of norm `1` of
  `GSpin(W)`, and `1 + ϖ` is missing.  So `IsSpecial` is not satisfied by every `GoodK`.  This
  only tests that `K` must *equal* a special stabilizer: `gl2GoodK'` has the same `H_P`.
* `not_exists_specialLattice_R_eq_edge`: the lattice `⟨z₋₁, z₀, ϖ · ½ z₁⟩` (for `ϖ` a uniformizer,
  the lattice of an edge midpoint of the tree of `PGL₂`) is not W1-special for any hyperbolic
  system and `c`.  The proof uses only the shape of `R` (`SpecialLattice.norm_quadForm_le`) and
  the anisotropy of `V_an`; it does not use the condition "`c` is a value of `val_F ∘ q` on
  `V_an`" (`attained`).
* `not_exists_specialLattice_R_eq_iwahori`: the lattice `⟨z₋₁, ϖ z₀, ϖ · ½ z₁⟩` (for `ϖ` a
  uniformizer; its stabilizer is the normalizer of an Iwahori subgroup, maximal compact but not
  special) is not W1-special for any hyperbolic system and `c`.  This tests `attained`: the
  lattice satisfies every other condition of `SpecialLattice` (`gl2_iwahori_data`), and the proof
  rules it out only because `q` takes square values on the orthogonal of every hyperbolic pair,
  so `‖q‖` on `V_an` is never `|ϖ^c| = ‖ϖ‖`.
-/

noncomputable section

open Module GSpinGGP.Sanity

namespace GSpinGGP.GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝔾" => (gl2Data (F := F))

/-! ## `W = 0` -/

local instance : Subsingleton (Fin (𝔾).m → F) := inferInstanceAs (Subsingleton (Fin 0 → F))

/-- The special lattice of `W = 0` (no hyperbolic system, `V_an = 0`, `c = 0`). -/
def gl2SpecialW : SpecialLattice (𝔾).QW where
  n := 0
  v := Fin.elim0
  v' := Fin.elim0
  polar_v_v' i := i.elim0
  polar_v_v i := i.elim0
  polar_v'_v' i := i.elim0
  aniso x _ _ := Subsingleton.elim x 0
  r := 1
  exists_norm_eq := ⟨1, one_ne_zero, norm_one⟩
  attained h := (h (Submodule.eq_bot_of_subsingleton)).elim

theorem gl2SpecialW_R :
    (gl2SpecialW (F := F)).R = {x | ∀ i, ‖(Pi.basisFun F (Fin 0)).repr x i‖ ≤ 1} := by
  ext x
  simp only [Set.mem_ofPred_eq, IsEmpty.forall_iff, iff_true]
  exact ⟨Fin.elim0, Fin.elim0, 0, fun i => i.elim0, fun i => i.elim0, zero_mem _,
    by simp [gl2SpecialW], Subsingleton.elim _ _⟩

theorem gl2SpecialW_isAdapted :
    (gl2SpecialW (F := F)).IsAdapted (gl2Levi (F := F)).bW (gl2Levi (F := F)).wtW :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun x _ => Subsingleton.elim x 0 ▸ zero_mem _⟩

/-! ## `V`: the lattice `Λ = ⟨z₋₁, z₀, ½ z₁⟩` -/

/-- `polar` in the coordinates `(a, b, c)` of `gl2Basis`. -/
theorem gl2_polar (x y : (𝔾).V) : QuadraticMap.polar (𝔾).QV x y =
    gl2Basis.repr x 0 * gl2Basis.repr y 2 + gl2Basis.repr y 0 * gl2Basis.repr x 2 +
      2 * (gl2Basis.repr x 1 * gl2Basis.repr y 1) := by
  simp only [QuadraticMap.polar, gl2_QV_eq, map_add, Finsupp.add_apply]
  ring

theorem gl2Basis_repr_self (i j : Fin 3) :
    (gl2Basis (F := F)).repr (gl2Basis i) j = if i = j then 1 else 0 := by
  rw [Basis.repr_self, Finsupp.single_apply]

theorem gl2_mem_hypOrth {x : (𝔾).V} :
    x ∈ hypOrth (𝔾).QV (fun _ : Fin 1 => gl2Basis 0) (fun _ : Fin 1 => gl2Basis 2) ↔
      gl2Basis.repr x 2 = 0 ∧ gl2Basis.repr x 0 = 0 := by
  rw [mem_hypOrth]
  simp only [gl2_polar, gl2Basis_repr_self]
  simp

/-- **`Λ` is W1-special** with `c = 0`. -/
def gl2SpecialV : SpecialLattice (𝔾).QV where
  n := 1
  v _ := gl2Basis 0
  v' _ := gl2Basis 2
  polar_v_v' i j := by
    obtain rfl := Subsingleton.elim i j
    rw [gl2_polar]; simp
  polar_v_v _ _ := by rw [gl2_polar]; simp
  polar_v'_v' _ _ := by rw [gl2_polar]; simp
  aniso x hx hQ := by
    rw [gl2_mem_hypOrth] at hx
    rw [gl2_QV_eq, hx.1, hx.2, zero_mul, zero_add, sq, mul_self_eq_zero] at hQ
    refine gl2Basis.ext_elem fun i => ?_
    fin_cases i <;> simp [hx.1, hx.2, hQ]
  r := 1
  exists_norm_eq := ⟨1, one_ne_zero, norm_one⟩
  attained _ := ⟨gl2Basis 1, gl2_mem_hypOrth.2 (by simp),
    by rw [gl2_QV_eq]; simp⟩

theorem gl2SpecialV_R :
    (gl2SpecialV (F := F)).R = {x | ∀ i, ‖gl2Basis.repr x i‖ ≤ 1} := by
  ext x
  change (∃ (a b : Fin 1 → F) (y : (𝔾).V), (∀ i, ‖a i‖ ≤ 1) ∧ (∀ i, ‖b i‖ ≤ 1) ∧
    y ∈ hypOrth (𝔾).QV (fun _ : Fin 1 => gl2Basis 0) (fun _ : Fin 1 => gl2Basis 2) ∧
    ‖(𝔾).QV y‖ ≤ 1 ∧ x = ∑ i, a i • gl2Basis 0 + ∑ i, b i • gl2Basis 2 + y) ↔ _
  constructor
  · rintro ⟨a, b, y, ha, hb, hy, hQy, rfl⟩
    rw [gl2_mem_hypOrth] at hy
    rw [gl2_QV_eq, hy.1, mul_zero, zero_add, norm_pow] at hQy
    have h1 : ‖gl2Basis.repr y 1‖ ≤ 1 := (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 hQy
    intro i
    fin_cases i <;> simp [hy.1, hy.2, ha 0, h1, hb 0]
  · intro hx
    refine ⟨fun _ => gl2Basis.repr x 0, fun _ => gl2Basis.repr x 2, gl2Basis.repr x 1 • gl2Basis 1,
      fun _ => hx 0, fun _ => hx 2, ?_, ?_, ?_⟩
    · rw [gl2_mem_hypOrth]; simp
    · rw [gl2_QV_eq]
      simpa [gl2Basis_repr_self, norm_pow] using hx 1
    · refine gl2Basis.ext_elem fun i => ?_
      fin_cases i <;> simp

/-- `gl2Basis i` lies in the weight space of `stdWt (inr i)`. -/
theorem gl2Basis_mem_wtSpan (i : Fin 3) :
    gl2Basis i ∈ wtSpan (gl2Levi (F := F)).bV (gl2Levi (F := F)).wtV ((𝔾).stdWt (Sum.inr i)) := by
  rw [gl2Basis_eq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl, rfl⟩)

theorem gl2SpecialV_isAdapted :
    (gl2SpecialV (F := F)).IsAdapted (gl2Levi (F := F)).bV (gl2Levi (F := F)).wtV := by
  refine ⟨fun _ => ⟨_, gl2Basis_mem_wtSpan 0⟩, fun _ => ⟨_, gl2Basis_mem_wtSpan 2⟩, fun x hx => ?_⟩
  change x ∈ hypOrth (𝔾).QV (fun _ : Fin 1 => gl2Basis 0) (fun _ : Fin 1 => gl2Basis 2) at hx
  rw [gl2_mem_hypOrth] at hx
  have hx1 : x = gl2Basis.repr x 1 • gl2Basis 1 := by
    refine gl2Basis.ext_elem fun i => ?_
    fin_cases i <;> simp [hx.1, hx.2]
  have h0 : (𝔾).stdWt (Sum.inr 1) = 0 := by simp [stdWt]
  rw [hx1, ← h0]
  exact Submodule.smul_mem _ _ (gl2Basis_mem_wtSpan 1)

theorem gl2_not_isHypPlane_W : ¬ IsHypPlane (𝔾).QW := fun h => by
  have := h.1; simp at this

theorem gl2_not_isHypPlane_V : ¬ IsHypPlane (𝔾).QV := fun h => by
  have := h.1; rw [gl2Data_finrank_V] at this; omega

/-! ## (a), (c): `gl2GoodK` is special -/

/-- **`gl2GoodK` is special**: it is `specialStab` of the special lattices `0 ⊆ W` and `Λ ⊆ V`,
which are adapted to `gl2Levi`. -/
theorem gl2GoodK_isSpecial : (gl2GoodK (F := F)).IsSpecial :=
  ⟨gl2SpecialW, gl2SpecialV, gl2SpecialW_isAdapted, gl2SpecialV_isAdapted,
    ((𝔾).specialStab_eq_latticeK _ _ _ _ gl2SpecialW_R gl2SpecialV_R gl2_not_isHypPlane_W
      gl2_not_isHypPlane_V).symm⟩

/-- **`IsSpecial` is satisfiable** for a proper Levi subgroup. -/
theorem exists_isSpecial_gl2 :
    ∃ K : (𝔾).GoodK (gl2Levi (F := F)).toFlagLeviDatum, K.IsSpecial :=
  ⟨gl2GoodK, gl2GoodK_isSpecial⟩

/-! ## (b): a `GoodK` that is not special -/

/-- **`{u ∈ F^× : ‖u − 1‖ < s}`**, a subgroup for `0 < s ≤ 1` (ultrametric). -/
def unitBall (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) : Subgroup Fˣ where
  carrier := {u | ‖(u : F) - 1‖ < s}
  one_mem' := by simpa using hs0
  mul_mem' := fun {u w} hu hw => by
    have hu1 : ‖(u : F)‖ ≤ 1 := by
      have := IsUltrametricDist.norm_add_le_max ((u : F) - 1) 1
      rw [sub_add_cancel, norm_one] at this
      exact this.trans (max_le (le_of_lt (lt_of_lt_of_le hu hs1)) le_rfl)
    change ‖((u : F) * w) - 1‖ < s
    have e : (u : F) * w - 1 = (u : F) * ((w : F) - 1) + ((u : F) - 1) := by ring
    rw [e]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ hu)
    rw [norm_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hu1) hw
  inv_mem' := fun {u} hu => by
    have hu' : ‖(u : F) - 1‖ < 1 := lt_of_lt_of_le hu hs1
    have hu1 : ‖(u : F)‖ = 1 := by
      have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (x := (u : F) - 1) (y := 1) (by rw [norm_one]; exact hu'.ne)
      rw [sub_add_cancel, norm_one, max_eq_right hu'.le] at h
      exact h
    change ‖((u⁻¹ : Fˣ) : F) - 1‖ < s
    have e : ((u⁻¹ : Fˣ) : F) - 1 = ((u⁻¹ : Fˣ) : F) * (1 - (u : F)) := by
      rw [mul_sub, mul_one, Units.inv_mul]
    rw [e, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hu1, inv_one, one_mul, norm_sub_rev]
    exact hu

/-- A fixed element `ϖ` with `0 < ‖ϖ‖ < 1`. -/
def gl2Pi : F := (NormedField.exists_norm_lt_one F).choose

omit [PAdicField F] in
theorem gl2Pi_pos : 0 < ‖(gl2Pi : F)‖ := (NormedField.exists_norm_lt_one F).choose_spec.1

omit [PAdicField F] in
theorem gl2Pi_lt_one : ‖(gl2Pi : F)‖ < 1 := (NormedField.exists_norm_lt_one F).choose_spec.2

/-- **`K'`**: the `g ∈ gl2K` whose `GSpin(W) = F^×`-component `u` has `‖u − 1‖ < ‖ϖ‖`. -/
def gl2K' : Subgroup ↥(𝔾).G :=
  gl2K ⊓ (unitBall ‖(gl2Pi : F)‖ gl2Pi_pos gl2Pi_lt_one.le).comap ((detChar (𝔾).QW).comp (𝔾).fst)

theorem isOpen_gl2K' : IsOpen (gl2K' (F := F) : Set ↥(𝔾).G) := by
  refine (gl2GoodK (F := F)).isOpen.inter ?_
  exact isOpen_lt (((continuous_detChar (𝔾).QW).comp (𝔾).continuous_fst).sub
    continuous_const).norm continuous_const

/-- **`K'` is a `GoodK` for the torus `M`.**  `G = P K'`: write `g = p k` with `k ∈ gl2K`
(`gl2_iwasawa`) and `z = (k_W, 1)`; `z` lies in every flag parabolic (`W = 0`), and
`z⁻¹ k ∈ K'` has `W`-component `1`. -/
def gl2GoodK' : (𝔾).GoodK (gl2Levi (F := F)).toFlagLeviDatum where
  K := gl2K'
  isOpen := isOpen_gl2K'
  isCompact := (gl2GoodK (F := F)).isCompact.of_isClosed_subset
    (Subgroup.isClosed_of_isOpen _ isOpen_gl2K') fun _ h => h.1
  mul_eq P hP g := by
    obtain ⟨FW, FV, rfl, -⟩ := hP
    obtain ⟨p, hp, k, hk, rfl⟩ := gl2_iwasawa FW FV g
    set z := (𝔾).pair ((𝔾).fst k, 1)
    refine ⟨p * z, mul_mem hp ⟨?_, ?_⟩, z⁻¹ * k, ⟨⟨?_, ?_⟩, ?_⟩, by group⟩
    · change (𝔾).fst z ∈ flagStab FW
      rw [gl2_flagStab_W]; trivial
    · change (𝔾).snd z ∈ flagStab FV
      rw [snd_pair]; exact one_mem _
    · change (𝔾).fst (z⁻¹ * k) ∈ latticeSpin _ _
      rw [map_mul, map_inv, fst_pair, inv_mul_cancel]; exact one_mem _
    · change (𝔾).snd (z⁻¹ * k) ∈ latticeSpin _ _
      rw [map_mul, map_inv, snd_pair, inv_one, one_mul]; exact hk.2
    · change ((detChar (𝔾).QW).comp (𝔾).fst) (z⁻¹ * k) ∈ unitBall _ gl2Pi_pos gl2Pi_lt_one.le
      rw [MonoidHom.comp_apply, map_mul, map_inv, fst_pair, inv_mul_cancel, map_one]
      exact one_mem _
  goodPositionW := (gl2GoodK (F := F)).goodPositionW.mono (Set.image_mono fun _ h => h.1)
  goodPositionV := (gl2GoodK (F := F)).goodPositionV.mono (Set.image_mono fun _ h => h.1)

/-- **`gl2GoodK'` is not special**: a special `K` contains the scalar `1 + ϖ` of `GSpin(W)`
(norm `1`), whose `detChar` is `1 + ϖ` (`dim C(W) = 1`), at distance `‖ϖ‖` from `1`. -/
theorem not_isSpecial_gl2GoodK' : ¬ (gl2GoodK' (F := F)).IsSpecial := by
  intro hK
  have hlt := gl2Pi_lt_one (F := F)
  have hne : (1 + gl2Pi : F) ≠ 0 := by
    intro h
    have : ‖(1 : F)‖ = ‖(gl2Pi : F)‖ := by rw [eq_neg_of_add_eq_zero_left h, norm_neg]
    rw [norm_one] at this; linarith
  set u : Fˣ := Units.mk0 _ hne
  have hu : ‖(u : F)‖ = 1 := by
    change ‖1 + (gl2Pi : F)‖ = 1
    have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (x := (1 : F)) (y := gl2Pi) (by rw [norm_one]; exact hlt.ne')
    rw [h, norm_one, max_eq_left hlt.le]
  have hmem := (hK.pair_scalarGSpin_mem hu).2
  change ‖((detChar (𝔾).QW ((𝔾).fst ((𝔾).pair (scalarGSpin (𝔾).QW u, 1))) : Fˣ) : F) - 1‖ <
    ‖(gl2Pi : F)‖ at hmem
  rw [fst_pair, detChar_scalarGSpin, finrank_cliffordAlgebra] at hmem
  simp [u] at hmem

/-! ## A lattice that is not special: `⟨z₋₁, z₀, ϖ · ½ z₁⟩`

The lattice `Λ' = {‖a‖ ≤ 1, ‖b‖ ≤ 1, ‖c‖ ≤ ‖ϖ‖}` (coordinates of `gl2Basis`; for `ϖ` a
uniformizer, the lattice of the midpoint of an edge of the tree of `PGL₂ ≅ SO(V)`) is not
W1-special, for **any** hyperbolic system and `c` (`not_exists_specialLattice_R_eq_edge`), so in
particular not for one adapted to `gl2Levi`.  The proof does not use the condition `attained`
("`c` is a value of `val_F ∘ q` on `V_an`"), only `SpecialLattice.norm_quadForm_le`
(`‖q‖ ≤ |ϖ^c|` on `R`) and the anisotropy of `V_an`: `z₀ ∈ Λ'`
forces `|ϖ^c| ≥ 1`, while two isotropic vectors of `Λ'` pair to norm `< 1`, so `Λ'` contains no
`v_1`, `ϖ^c v_{-1}`. -/

/-- The lattice `Λ' = ⟨z₋₁, z₀, ϖ · ½ z₁⟩`. -/
def gl2EdgeLattice : Set (𝔾).V :=
  {x | ‖gl2Basis.repr x 0‖ ≤ 1 ∧ ‖gl2Basis.repr x 1‖ ≤ 1 ∧ ‖gl2Basis.repr x 2‖ ≤ ‖(gl2Pi : F)‖}

/-- `‖2‖ ≤ 1` (ultrametric). -/
theorem norm_two_le_one : ‖(2 : F)‖ ≤ 1 := by
  have h := IsUltrametricDist.norm_add_le_max (1 : F) 1
  rw [one_add_one_eq_two, norm_one, max_self] at h
  exact h

/-- **Two isotropic vectors of `Λ'` pair to norm `< 1`.** -/
theorem norm_polar_lt_one_of_mem_edge {x y : (𝔾).V} (hx : x ∈ gl2EdgeLattice (F := F))
    (hy : y ∈ gl2EdgeLattice (F := F)) (hQx : (𝔾).QV x = 0) :
    ‖QuadraticMap.polar (𝔾).QV x y‖ < 1 := by
  have hs := gl2Pi_lt_one (F := F)
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨hy0, hy1, hy2⟩ := hy
  rw [gl2_QV_eq] at hQx
  have hb : ‖gl2Basis.repr x 1‖ < 1 := by
    have e : (gl2Basis.repr x 1) ^ 2 = -(gl2Basis.repr x 0 * gl2Basis.repr x 2) := by
      linear_combination hQx
    have h2 : ‖gl2Basis.repr x 1‖ ^ 2 < 1 := by
      rw [← norm_pow, e, norm_neg, norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hx0 |>.trans hx2) hs
    nlinarith [norm_nonneg (gl2Basis.repr x 1)]
  rw [gl2_polar]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
  · refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul]
      exact lt_of_le_of_lt ((mul_le_of_le_one_left (norm_nonneg _) hx0).trans hy2) hs
    · rw [norm_mul]
      exact lt_of_le_of_lt ((mul_le_of_le_one_left (norm_nonneg _) hy0).trans hx2) hs
  · rw [norm_mul, norm_mul]
    calc ‖(2 : F)‖ * (‖gl2Basis.repr x 1‖ * ‖gl2Basis.repr y 1‖)
        ≤ 1 * (‖gl2Basis.repr x 1‖ * 1) := by gcongr; exact norm_two_le_one
      _ < 1 := by rw [one_mul, mul_one]; exact hb

/-- **`⟨z₋₁, z₀, ϖ · ½ z₁⟩` is not a W1-special lattice** (for any hyperbolic system and `c`). -/
theorem not_exists_specialLattice_R_eq_edge :
    ¬ ∃ S : SpecialLattice (𝔾).QV, S.R = gl2EdgeLattice (F := F) := by
  rintro ⟨S, hS⟩
  have hs := gl2Pi_pos (F := F)
  -- `z₀ ∈ Λ'` and `q(z₀) = 1`, so `|ϖ^c| ≥ 1`
  have he1 : gl2Basis 1 ∈ S.R := by
    rw [hS]; refine ⟨?_, ?_, ?_⟩ <;> simp [hs.le]
  have hr : 1 ≤ S.r := by
    have h := S.norm_quadForm_le he1
    have hq : (𝔾).QV (gl2Basis 1) = 1 := by rw [gl2_QV_eq]; simp
    rwa [hq, norm_one] at h
  rcases Nat.eq_zero_or_pos S.n with hn | hn
  · -- no hyperbolic system: `V_an = V` is isotropic
    have hmem : gl2Basis 0 ∈ S.Van := mem_hypOrth.2 fun i => absurd i.2 (by omega)
    have h0 := S.aniso _ hmem (by rw [gl2_QV_eq]; simp)
    exact gl2Basis.ne_zero 0 h0
  · set i : Fin S.n := ⟨0, hn⟩
    obtain ⟨α, -, hα⟩ := S.exists_norm_eq
    have hv : S.v i ∈ S.R := by
      refine ⟨Pi.single i 1, 0, 0, fun j => ?_, fun j => by simpa using S.r_nonneg, zero_mem _,
        by simpa using S.r_nonneg, by simp [Pi.single_apply]⟩
      by_cases h : j = i <;> simp [h]
    have hv' : α • S.v' i ∈ S.R := by
      refine ⟨0, Pi.single i α, 0, fun j => by simp, fun j => ?_, zero_mem _,
        by simpa using S.r_nonneg, by simp [Pi.single_apply]⟩
      by_cases h : j = i <;> simp [h, hα, S.r_nonneg]
    rw [hS] at hv hv'
    have hlt := norm_polar_lt_one_of_mem_edge hv hv' (S.quadForm_v i)
    rw [QuadraticMap.polar_smul_right, S.polar_v_v'] at hlt
    simp only [↓reduceIte, smul_eq_mul, mul_one, hα] at hlt
    linarith

/-! ## A maximal compact subgroup that is not special: the Iwahori lattice

For `ϖ` a uniformizer, the lattice `Λ'' = {‖a‖ ≤ 1, ‖b‖ ≤ ‖ϖ‖, ‖c‖ ≤ ‖ϖ‖}` (coordinates of
`gl2Basis`) has the shape `R` of W1 §7.1 for the hyperbolic pair `v = z₋₁`, `v' = ½ z₁`,
`V_an = F z₀` and `|ϖ^c| = ‖ϖ‖` (`gl2_iwahori_data`): every condition of `SpecialLattice` holds
except `attained`.  Its stabilizer in `SO(V) ≅ PGL₂` is the normalizer of an Iwahori subgroup,
maximal compact but not special.  It is excluded only by `attained`
(`not_exists_specialLattice_R_eq_iwahori`): on the orthogonal of a hyperbolic pair, `q = ac + b²`
takes only square values (the discriminant of `q` is that of a hyperbolic plane plus a line of
square class `1`), so `‖q(y)‖ ∈ ‖F^×‖²` is an even power of `‖ϖ‖`, while `|ϖ^c| = ‖ϖ‖`. -/

/-- The lattice `Λ'' = ⟨z₋₁, ϖ z₀, ϖ · ½ z₁⟩`. -/
def gl2IwahoriLattice (ϖ : F) : Set (𝔾).V :=
  {x | ‖gl2Basis.repr x 0‖ ≤ 1 ∧ ‖gl2Basis.repr x 1‖ ≤ ‖ϖ‖ ∧ ‖gl2Basis.repr x 2‖ ≤ ‖ϖ‖}

/-- The determinant of three vectors in the coordinates of `gl2Basis`. -/
def gl2Det (x y z : (𝔾).V) : F :=
  gl2Basis.repr x 0 *
      (gl2Basis.repr y 1 * gl2Basis.repr z 2 - gl2Basis.repr z 1 * gl2Basis.repr y 2) -
    gl2Basis.repr x 1 *
      (gl2Basis.repr y 0 * gl2Basis.repr z 2 - gl2Basis.repr z 0 * gl2Basis.repr y 2) +
    gl2Basis.repr x 2 *
      (gl2Basis.repr y 0 * gl2Basis.repr z 1 - gl2Basis.repr z 0 * gl2Basis.repr y 1)

theorem gl2Det_add_right (x y z z' : (𝔾).V) :
    gl2Det x y (z + z') = gl2Det x y z + gl2Det x y z' := by
  simp only [gl2Det, map_add, Finsupp.add_apply]; ring

omit [NontriviallyNormedField F] [PAdicField F] in
/-- The Gram-determinant identity behind `gl2_quadForm_eq_sq`, in coordinates. -/
theorem gl2_gram_aux [Field F] (a1 b1 c1 a2 b2 c2 a3 b3 c3 : F) (h1 : a1 * c1 + b1 ^ 2 = 0)
    (h3 : a1 * c2 + a2 * c1 + 2 * (b1 * b2) = 1)
    (h4 : a1 * c3 + a3 * c1 + 2 * (b1 * b3) = 0) :
    a3 * c3 + b3 ^ 2 = (a1 * (b2 * c3 - b3 * c2) - b1 * (a2 * c3 - a3 * c2) +
      c1 * (a2 * b3 - a3 * b2)) ^ 2 := by
  linear_combination (-(a3 * c3 + b3 ^ 2) * ((a1 * c2 + a2 * c1 + 2 * (b1 * b2)) + 1)) * h3 +
    (4 * (a2 * c2 + b2 ^ 2) * (a3 * c3 + b3 ^ 2) - (a2 * c3 + a3 * c2 + 2 * (b2 * b3)) ^ 2) * h1 +
    ((a1 * c2 + a2 * c1 + 2 * (b1 * b2)) * (a2 * c3 + a3 * c2 + 2 * (b2 * b3)) -
      (a2 * c2 + b2 ^ 2) * (a1 * c3 + a3 * c1 + 2 * (b1 * b3))) * h4

/-- **On the orthogonal of a hyperbolic pair, `q` is a square**: if `q(v) = q(v') = 0`,
`polar(v, v') = 1` and `y ⊥ v, v'`, then `q(y) = det(v, v', y)²` (compare Gram determinants in
the bases `(v, v', y)` and `gl2Basis`: `−2 q(y) = −2 det(v, v', y)²`).  This holds for **every**
hyperbolic pair of `V`, not only for `z₋₁, ½ z₁`. -/
theorem gl2_quadForm_eq_sq {v v' y : (𝔾).V} (hv : (𝔾).QV v = 0)
    (hvv' : QuadraticMap.polar (𝔾).QV v v' = 1) (hy : QuadraticMap.polar (𝔾).QV v y = 0) :
    (𝔾).QV y = gl2Det v v' y ^ 2 := by
  rw [gl2_polar] at hvv' hy
  rw [gl2_QV_eq] at hv ⊢
  exact gl2_gram_aux _ _ _ _ _ _ _ _ _ hv hvv' hy

/-- A vector orthogonal to `v` and `v'` (a cross product): with `G` the Gram matrix of `polar` in
`gl2Basis`, the coordinates are `Gv × Gv'`. -/
def gl2Cross (v v' : (𝔾).V) : (𝔾).V :=
  (2 * (gl2Basis.repr v 1 * gl2Basis.repr v' 0 - gl2Basis.repr v 0 * gl2Basis.repr v' 1)) •
      gl2Basis 0 +
    (gl2Basis.repr v 0 * gl2Basis.repr v' 2 - gl2Basis.repr v 2 * gl2Basis.repr v' 0) • gl2Basis 1 +
      (2 * (gl2Basis.repr v 2 * gl2Basis.repr v' 1 - gl2Basis.repr v 1 * gl2Basis.repr v' 2)) •
        gl2Basis 2

theorem gl2Cross_repr (v v' : (𝔾).V) :
    gl2Basis.repr (gl2Cross v v') 0 =
        2 * (gl2Basis.repr v 1 * gl2Basis.repr v' 0 - gl2Basis.repr v 0 * gl2Basis.repr v' 1) ∧
      gl2Basis.repr (gl2Cross v v') 1 =
        gl2Basis.repr v 0 * gl2Basis.repr v' 2 - gl2Basis.repr v 2 * gl2Basis.repr v' 0 ∧
      gl2Basis.repr (gl2Cross v v') 2 =
        2 * (gl2Basis.repr v 2 * gl2Basis.repr v' 1 - gl2Basis.repr v 1 * gl2Basis.repr v' 2) := by
  simp [gl2Cross]

theorem polar_gl2Cross_left (v v' : (𝔾).V) : QuadraticMap.polar (𝔾).QV v (gl2Cross v v') = 0 := by
  obtain ⟨h0, h1, h2⟩ := gl2Cross_repr v v'
  rw [gl2_polar, h0, h1, h2]; ring

theorem polar_gl2Cross_right (v v' : (𝔾).V) :
    QuadraticMap.polar (𝔾).QV v' (gl2Cross v v') = 0 := by
  obtain ⟨h0, h1, h2⟩ := gl2Cross_repr v v'
  rw [gl2_polar, h0, h1, h2]; ring

/-- **The orthogonal of a hyperbolic pair is not zero**: `q(v × v') = 1`. -/
theorem quadForm_gl2Cross {v v' : (𝔾).V} (hv : (𝔾).QV v = 0)
    (hvv' : QuadraticMap.polar (𝔾).QV v v' = 1) : (𝔾).QV (gl2Cross v v') = 1 := by
  obtain ⟨h0, h1, h2⟩ := gl2Cross_repr v v'
  rw [gl2_polar] at hvv'
  rw [gl2_QV_eq] at hv
  rw [gl2_QV_eq, h0, h1, h2]
  linear_combination
    ((gl2Basis.repr v 0 * gl2Basis.repr v' 2 + gl2Basis.repr v' 0 * gl2Basis.repr v 2 +
        2 * (gl2Basis.repr v 1 * gl2Basis.repr v' 1)) + 1) * hvv' -
      4 * (gl2Basis.repr v' 0 * gl2Basis.repr v' 2 + gl2Basis.repr v' 1 ^ 2) * hv

omit [PAdicField F] in
/-- **`‖ϖ‖` is not the norm of a square** when `ϖ` is a uniformizer: norms are the `‖ϖ‖^k`,
`k ∈ ℤ`, and `2k ≠ 1`. -/
theorem norm_sq_ne_of_uniformizer {ϖ : F} (h0 : 0 < ‖ϖ‖) (h1 : ‖ϖ‖ < 1)
    (hmax : ∀ x : F, ‖x‖ < 1 → ‖x‖ ≤ ‖ϖ‖) (t : F) : ‖t‖ ^ 2 ≠ ‖ϖ‖ := by
  intro h
  have ht : t ≠ 0 := by rintro rfl; rw [norm_zero] at h; simp at h; linarith
  obtain ⟨k, hk⟩ := exists_norm_eq_zpow h0 h1 hmax ht
  rw [hk, ← zpow_natCast, ← zpow_mul] at h
  have := (zpow_right_inj₀ h0 h1.ne).1 (h.trans (zpow_one _).symm)
  omega

/-- **`polar` has norm `≤ ‖ϖ‖` on `Λ''`.** -/
theorem norm_polar_le_of_mem_iwahori {ϖ : F} (h1 : ‖ϖ‖ < 1) {x y : (𝔾).V}
    (hx : x ∈ gl2IwahoriLattice ϖ) (hy : y ∈ gl2IwahoriLattice ϖ) :
    ‖QuadraticMap.polar (𝔾).QV x y‖ ≤ ‖ϖ‖ := by
  obtain ⟨hx0, hx1, hx2⟩ := hx
  obtain ⟨hy0, hy1, hy2⟩ := hy
  rw [gl2_polar]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hx0).trans hy2
    · rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hy0).trans hx2
  · rw [norm_mul, norm_mul]
    calc ‖(2 : F)‖ * (‖gl2Basis.repr x 1‖ * ‖gl2Basis.repr y 1‖)
        ≤ 1 * (‖ϖ‖ * 1) := by
          gcongr
          · exact norm_two_le_one
          · exact hy1.trans h1.le
      _ = ‖ϖ‖ := by ring

/-- **`Λ''` is not a W1-special lattice** (for any hyperbolic system and `c`), when `ϖ` is a
uniformizer.  The proof uses `attained`:
1. a system has length `n ≥ 1` (`V` is isotropic) and `n ≤ 1` (two orthogonal hyperbolic pairs
   would give `q(v_2 + v_{−2}) = 1` and, by `gl2_quadForm_eq_sq`, `= det² = 0`);
2. `|ϖ^c| = ‖ϖ‖`: `polar(v_1, ϖ^c v_{−1}) = ϖ^c` with both vectors in `Λ''`
   (`norm_polar_le_of_mem_iwahori`), and `q(z₋₁ + ϖ · ½ z₁) = ϖ` with `z₋₁ + ϖ · ½ z₁ ∈ Λ''`;
3. `V_an ∋ v_1 × v_{−1} ≠ 0` (`quadForm_gl2Cross`), so **`attained`** gives `y ∈ V_an` with
   `‖q(y)‖ = ‖ϖ‖`; but `q(y) = det(v_1, v_{−1}, y)²` (`gl2_quadForm_eq_sq`), and `‖ϖ‖` is not the
   norm of a square (`norm_sq_ne_of_uniformizer`). -/
theorem not_exists_specialLattice_R_eq_iwahori {ϖ : F} (h0 : 0 < ‖ϖ‖) (h1 : ‖ϖ‖ < 1)
    (hmax : ∀ x : F, ‖x‖ < 1 → ‖x‖ ≤ ‖ϖ‖) :
    ¬ ∃ S : SpecialLattice (𝔾).QV, S.R = gl2IwahoriLattice ϖ := by
  rintro ⟨S, hS⟩
  rcases Nat.eq_zero_or_pos S.n with hn | hn
  · -- no hyperbolic system: `V_an = V` is isotropic
    have hmem : gl2Basis 0 ∈ S.Van := mem_hypOrth.2 fun i => absurd i.2 (by omega)
    exact gl2Basis.ne_zero 0 (S.aniso _ hmem (by rw [gl2_QV_eq]; simp))
  set i : Fin S.n := ⟨0, hn⟩
  have hvv' : QuadraticMap.polar (𝔾).QV (S.v i) (S.v' i) = 1 := by simpa using S.polar_v_v' i i
  -- 1. the system has length `1`
  have hj : ∀ j, j = i := by
    intro j
    by_contra hji
    have hd : ∀ y, (𝔾).QV y = 0 → QuadraticMap.polar (𝔾).QV (S.v i) y = 0 →
        gl2Det (S.v i) (S.v' i) y = 0 := fun y hQ hy =>
      pow_eq_zero_iff two_ne_zero |>.1 ((gl2_quadForm_eq_sq (S.quadForm_v i) hvv' hy).symm.trans hQ)
    have hij : i ≠ j := Ne.symm hji
    have h1' := hd _ (S.quadForm_v j) (S.polar_v_v i j)
    have h2' := hd _ (S.quadForm_v' j) (by simpa [hij] using S.polar_v_v' i j)
    have hjj : QuadraticMap.polar (𝔾).QV (S.v j) (S.v' j) = 1 := by simpa using S.polar_v_v' j j
    have hQ := gl2_quadForm_eq_sq (y := S.v j + S.v' j) (S.quadForm_v i) hvv'
      (by rw [QuadraticMap.polar_add_right, S.polar_v_v i j]
          simpa [hij] using S.polar_v_v' i j)
    rw [gl2Det_add_right, h1', h2', QuadraticMap.map_add (⇑(𝔾).QV), S.quadForm_v j, S.quadForm_v' j,
      hjj] at hQ
    norm_num at hQ
  -- 2. `|ϖ^c| = ‖ϖ‖`
  obtain ⟨α, -, hα⟩ := S.exists_norm_eq
  have hv : S.v i ∈ S.R := by
    refine ⟨Pi.single i 1, 0, 0, fun j => ?_, fun j => by simpa using S.r_nonneg, zero_mem _,
      by simpa using S.r_nonneg, by simp [Pi.single_apply]⟩
    by_cases h : j = i <;> simp [h]
  have hv' : α • S.v' i ∈ S.R := by
    refine ⟨0, Pi.single i α, 0, fun j => by simp, fun j => ?_, zero_mem _,
      by simpa using S.r_nonneg, by simp [Pi.single_apply]⟩
    by_cases h : j = i <;> simp [h, hα, S.r_nonneg]
  have hx : gl2Basis 0 + ϖ • gl2Basis 2 ∈ S.R := by
    rw [hS]; refine ⟨?_, ?_, ?_⟩ <;> simp [h0.le]
  have hr : S.r = ‖ϖ‖ := by
    refine le_antisymm ?_ ?_
    · rw [hS] at hv hv'
      have h := norm_polar_le_of_mem_iwahori h1 hv hv'
      rwa [QuadraticMap.polar_smul_right, hvv', smul_eq_mul, mul_one, hα] at h
    · have h := S.norm_quadForm_le hx
      rwa [show (𝔾).QV (gl2Basis 0 + ϖ • gl2Basis 2) = ϖ by rw [gl2_QV_eq]; simp] at h
  -- 3. `V_an ≠ 0`, and `attained`
  have hz : gl2Cross (S.v i) (S.v' i) ∈ S.Van :=
    mem_hypOrth.2 fun j => by
      rw [hj j]; exact ⟨polar_gl2Cross_left _ _, polar_gl2Cross_right _ _⟩
  have hne : S.Van ≠ ⊥ := fun h => by
    have h0z : gl2Cross (S.v i) (S.v' i) = 0 := by rw [h] at hz; exact hz
    have := quadForm_gl2Cross (S.quadForm_v i) hvv'
    rw [h0z, map_zero] at this
    exact zero_ne_one this
  obtain ⟨y, hy, hQy⟩ := S.attained hne
  rw [gl2_quadForm_eq_sq (S.quadForm_v i) hvv' ((mem_hypOrth.1 hy i).1), norm_pow, hr] at hQy
  exact norm_sq_ne_of_uniformizer h0 h1 hmax _ hQy

/-- **The test is not vacuous**: `Λ''` satisfies every condition of `SpecialLattice` except
`attained`, for the hyperbolic pair `v = z₋₁`, `v' = ½ z₁` (`V_an = F z₀`) and `r = ‖ϖ‖`: the
three `polar` relations, anisotropy on `V_an`, `r` a norm of `F^×`, and `Λ''` is the set `R` of
these data; `attained` fails (`‖q‖ ≠ ‖ϖ‖` on `V_an`). -/
theorem gl2_iwahori_data {ϖ : F} (h0 : 0 < ‖ϖ‖) (h1 : ‖ϖ‖ < 1)
    (hmax : ∀ x : F, ‖x‖ < 1 → ‖x‖ ≤ ‖ϖ‖) :
    (∀ i j : Fin 1, QuadraticMap.polar (𝔾).QV (gl2Basis 0) (gl2Basis 2) = if i = j then 1 else 0) ∧
    (∀ _ _ : Fin 1, QuadraticMap.polar (𝔾).QV (gl2Basis 0) (gl2Basis 0) = 0) ∧
    (∀ _ _ : Fin 1, QuadraticMap.polar (𝔾).QV (gl2Basis 2) (gl2Basis 2) = 0) ∧
    (∀ x ∈ hypOrth (𝔾).QV (fun _ : Fin 1 => gl2Basis 0) (fun _ : Fin 1 => gl2Basis 2),
      (𝔾).QV x = 0 → x = 0) ∧
    (∃ a : F, a ≠ 0 ∧ ‖a‖ = ‖ϖ‖) ∧
    gl2IwahoriLattice ϖ = {x | ∃ (a b : Fin 1 → F) (y : (𝔾).V), (∀ i, ‖a i‖ ≤ 1) ∧
      (∀ i, ‖b i‖ ≤ ‖ϖ‖) ∧
      y ∈ hypOrth (𝔾).QV (fun _ : Fin 1 => gl2Basis 0) (fun _ : Fin 1 => gl2Basis 2) ∧
      ‖(𝔾).QV y‖ ≤ ‖ϖ‖ ∧ x = ∑ i, a i • gl2Basis 0 + ∑ i, b i • gl2Basis 2 + y} ∧
    (∀ y ∈ hypOrth (𝔾).QV (fun _ : Fin 1 => gl2Basis 0) (fun _ : Fin 1 => gl2Basis 2),
      ‖(𝔾).QV y‖ ≠ ‖ϖ‖) := by
  refine ⟨gl2SpecialV.polar_v_v', gl2SpecialV.polar_v_v, gl2SpecialV.polar_v'_v',
    gl2SpecialV.aniso, ⟨ϖ, norm_pos_iff.1 h0, rfl⟩, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hx0, hx1, hx2⟩
      refine ⟨fun _ => gl2Basis.repr x 0, fun _ => gl2Basis.repr x 2,
        gl2Basis.repr x 1 • gl2Basis 1, fun _ => hx0, fun _ => hx2, ?_, ?_, ?_⟩
      · rw [gl2_mem_hypOrth]; simp
      · rw [gl2_QV_eq]
        simp only [map_smul, gl2Basis_repr_self, Finsupp.smul_apply]
        simp only [Fin.isValue, Fin.reduceEq, ite_false, ite_true, smul_eq_mul, mul_zero, mul_one,
          zero_add, norm_pow]
        calc ‖gl2Basis.repr x 1‖ ^ 2 ≤ ‖ϖ‖ ^ 2 := by gcongr
          _ ≤ ‖ϖ‖ := by nlinarith
      · refine gl2Basis.ext_elem fun i => ?_
        fin_cases i <;> simp
    · rintro ⟨a, b, y, ha, hb, hy, hQy, rfl⟩
      rw [gl2_mem_hypOrth] at hy
      rw [gl2_QV_eq, hy.1, mul_zero, zero_add, norm_pow] at hQy
      have hy1 : ‖gl2Basis.repr y 1‖ ≤ ‖ϖ‖ := by
        by_contra hlt
        push Not at hlt
        rcases lt_or_ge ‖gl2Basis.repr y 1‖ 1 with h | h
        · exact absurd (hmax _ h) (not_le.2 hlt)
        · nlinarith
      refine ⟨?_, ?_, ?_⟩ <;> simp [hy.1, hy.2, ha 0, hy1, hb 0]
  · intro y hy
    rw [gl2_mem_hypOrth] at hy
    rw [gl2_QV_eq, hy.1, mul_zero, zero_add, norm_pow]
    exact norm_sq_ne_of_uniformizer h0 h1 hmax _

/-- **A uniformizer exists**, so the hypotheses of `not_exists_specialLattice_R_eq_iwahori` can be
met. -/
theorem exists_not_specialLattice_iwahori :
    ∃ ϖ : F, 0 < ‖ϖ‖ ∧ ‖ϖ‖ < 1 ∧ (¬ ∃ S : SpecialLattice (𝔾).QV, S.R = gl2IwahoriLattice ϖ) ∧
      ∀ y ∈ hypOrth (𝔾).QV (fun _ : Fin 1 => gl2Basis 0) (fun _ : Fin 1 => gl2Basis 2),
        ‖(𝔾).QV y‖ ≠ ‖ϖ‖ := by
  obtain ⟨ϖ, h0, h1, hmax⟩ := exists_norm_lt_one_isGreatest (F := F)
  exact ⟨ϖ, h0, h1, not_exists_specialLattice_R_eq_iwahori h0 h1 hmax,
    (gl2_iwahori_data h0 h1 hmax).2.2.2.2.2.2⟩

end GSpinGGP.GGPData
