/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.SpecialK
import GSpinGGP.Sanity.GL2GoodK

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
  `GSpin(W)`, and `1 + ϖ` is missing.  So `IsSpecial` is not satisfied by every `GoodK`.
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

end GSpinGGP.GGPData
