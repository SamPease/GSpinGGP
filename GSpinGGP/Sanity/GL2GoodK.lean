/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.LatticeK
import GSpinGGP.Sanity.WeightAudit

/-!
# A good compact subgroup for a proper Levi subgroup: `GSpin₃ ≅ GL₂`

At `gl2Data` (`W = 0`, `V = Z` split of dimension `3` with `q(x) = 2x₀x₂ + x₁²`, so
`G = GL₁ × GSpin₃`) take the flag `⟨z₁⟩` with its standard splitting basis; its Levi subgroup `M`
is a maximal torus, and `a_M^G ≠ 0`.  In the coordinates `a = x₀`, `b = x₁`, `c = 2x₂` the form
is `ac + b²` (`gl2_QV_eq`), and the lattice `Λ = {‖a‖, ‖b‖, ‖c‖ ≤ 1}`, spanned by `z₋₁`, `z₀`,
`½ z₁`, is split by the weight spaces.  The factor `½` makes `q` integral on `Λ` with unit
half-discriminant, so its reduction mod `𝔭` is smooth and the stabilizer of `Λ` is hyperspecial.
In residue characteristic `2` the plain lattice `𝒪³` (on which `polar` takes values in `2𝒪`)
gives an Iwahori-type stabilizer when `2` is a uniformizer, and a deeper level when `2` is
ramified, and `G = B K` fails for it.  (`Λ` is not self-dual for `polar` when `‖2‖ < 1`: its dual
is `𝒪 ⊕ 2⁻¹𝒪 ⊕ 𝒪` in the coordinates `(a, b, c)`.)

* `gl2_iwasawa`: `G = P K` for **every** flag parabolic `P = P_{F_W} × P_{F_V}`, with
  `K = latticeK` the stabilizer of `Λ` with `‖detChar‖ = 1`: `K` is transitive on the isotropic
  lines of `V` (`exists_mem_latticeSpin_apply_eq_smul`), and every proper flag of `V` is one
  isotropic line.  So the description of `𝒫(M)` is not needed.
* `gl2GoodK`: the resulting `GoodK` for the reduced Levi datum `gl2Levi` of the torus
  (`Sanity/WeightAudit.lean`, where `gl2_aMG_nontrivial` shows `a_M^G ≠ 0`).
-/

noncomputable section

open Module GSpinGGP.Sanity

namespace GSpinGGP.GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝔾" => (gl2Data (F := F))

/-! ## Coordinates -/

/-- The coordinates `(a, b, c) = (x₀, x₁, 2x₂)` of `V = 0 × F³`. -/
def gl2CoordEquiv : (𝔾).V ≃ₗ[F] (Fin 3 → F) where
  toFun v := ![v.2 0, v.2 1, 2 * v.2 2]
  invFun x := (0, ![x 0, x 1, 2⁻¹ * x 2])
  map_add' v w := by
    ext i; fin_cases i <;> simp [mul_add]
  map_smul' s v := by
    ext i; fin_cases i <;> simp [mul_left_comm]
  left_inv v := by
    refine Prod.ext (Subsingleton.elim _ _) ?_
    ext i; fin_cases i <;> simp
  right_inv x := by
    ext i; fin_cases i <;> simp

/-- The basis `z₋₁, z₀, ½ z₁` of `V`: the lattice `Λ` it spans is `{‖a‖, ‖b‖, ‖c‖ ≤ 1}`. -/
def gl2Basis : Basis (Fin 3) F (𝔾).V := Basis.ofEquivFun gl2CoordEquiv

theorem gl2Basis_repr (v : (𝔾).V) (i : Fin 3) :
    (gl2Basis (F := F)).repr v i = ![v.2 0, v.2 1, 2 * v.2 2] i := rfl

/-- **The form in these coordinates is `ac + b²`.** -/
theorem gl2_QV_eq (v : (𝔾).V) : (𝔾).QV v =
    (gl2Basis (F := F)).repr v 0 * (gl2Basis (F := F)).repr v 2 +
      (gl2Basis (F := F)).repr v 1 ^ 2 := by
  change (0 : QuadraticForm F (Fin 0 → F)) v.1 + splitOddForm 1 ((1 : Fˣ) : F) v.2 = _
  rw [LeviAux.splitOddForm_apply]
  change _ + (1 : F) * ∑ i : Fin 3, v.2 i * v.2 i.rev = _
  simp only [gl2Basis_repr, Fin.sum_univ_three]
  simp [Fin.rev]
  ring

/-- The basis vectors in terms of the standard basis. -/
theorem gl2Basis_eq (i : Fin 3) : (gl2Basis (F := F)) i =
    (![1, 1, 2⁻¹] : Fin 3 → F) i • (𝔾).stdBasis (Sum.inr i) := by
  classical
  rw [gl2Basis, Basis.coe_ofEquivFun]
  refine Prod.ext (Subsingleton.elim _ _) ?_
  rw [Prod.smul_snd, stdBasis, Basis.prod_apply_inr_snd, Pi.basisFun_apply]
  ext j
  fin_cases i <;> fin_cases j <;> simp [gl2CoordEquiv]

/-! ## The compact open subgroup and the Iwasawa decomposition -/

/-- **`K`**: the stabilizer of `Λ` with `‖detChar‖ = 1` (on `W = 0` there is no condition beyond
`‖detChar‖ = 1`). -/
abbrev gl2K : Subgroup ↥(𝔾).G := (𝔾).latticeK (Pi.basisFun F (Fin 0)) gl2Basis


/-- On `W = 0` every flag stabilizer is everything. -/
theorem gl2_flagStab_W (FW : IsotropicFlag (𝔾).QW) : flagStab FW = ⊤ := by
  ext g
  simp only [Subgroup.mem_top, iff_true]
  intro i
  rw [(Submodule.eq_bot_of_subsingleton : FW.sub i = ⊥)]
  exact Submodule.map_bot _

/-- A totally isotropic subspace of `V` has dimension `≤ 1` (`U ⊆ U^⊥`, `dim U^⊥ = 3 - dim U`). -/
theorem gl2_finrank_le_one {U : Submodule F (𝔾).V} (hU : IsTotallyIsotropic (𝔾).QV U) :
    finrank F U ≤ 1 := by
  have hle : U ≤ (bform (𝔾).QV).orthogonal U := fun u hu w hw =>
    bform_eq_zero_of_isTotallyIsotropic hU hw hu
  have h1 := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal (𝔾).nondeg_QV, gl2Data_finrank_V] at h1
  omega

/-- An isotropic flag of `V` has length `≤ 1`. -/
theorem gl2_flag_len_le_one (FV : IsotropicFlag (𝔾).QV) : FV.len ≤ 1 := by
  by_contra hne
  have h2 : 2 ≤ FV.len := by omega
  have hlt1 : FV.sub ⟨0, by omega⟩ < FV.sub ⟨1, by omega⟩ :=
    FV.strictMono (Fin.mk_lt_mk.2 (by omega))
  have hlt2 : FV.sub ⟨1, by omega⟩ < FV.sub ⟨2, by omega⟩ :=
    FV.strictMono (Fin.mk_lt_mk.2 (by omega))
  have f1 := Submodule.finrank_lt_finrank_of_lt hlt1
  have f2 := Submodule.finrank_lt_finrank_of_lt hlt2
  have := gl2_finrank_le_one (FV.isotropic ⟨2, by omega⟩)
  omega

/-- **The Iwasawa decomposition `G = P K` for every flag parabolic `P`.** -/
theorem gl2_iwasawa (FW : IsotropicFlag (𝔾).QW) (FV : IsotropicFlag (𝔾).QV) (g : ↥(𝔾).G) :
    ∃ p ∈ (𝔾).whittB FW FV, ∃ k ∈ gl2K (F := F), g = p * k := by
  classical
  rcases Nat.eq_zero_or_pos FV.len with h0 | hpos
  · refine ⟨g, ⟨?_, ?_⟩, 1, Subgroup.one_mem _, (mul_one g).symm⟩
    · change (𝔾).fst g ∈ flagStab FW
      rw [gl2_flagStab_W]; trivial
    · change _ ∈ flagStab FV
      rw [flagStab_eq_top_of_len_eq_zero FV h0]; trivial
  · -- the flag is one isotropic line `ℓ = F v₁`
    have hlen : FV.len = 1 := le_antisymm (gl2_flag_len_le_one FV) hpos
    set ℓ := FV.sub ⟨1, by omega⟩
    have hℓ : ⊥ < ℓ := by
      have h := FV.strictMono (show (⟨0, by omega⟩ : Fin (FV.len + 1)) < ⟨1, by omega⟩ from
        Fin.mk_lt_mk.2 (by omega))
      rwa [show (⟨0, by omega⟩ : Fin (FV.len + 1)) = 0 from Fin.ext (by simp), FV.sub_zero] at h
    obtain ⟨v₁, hv₁, hv₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hℓ.ne'
    have hℓeq : ℓ = Submodule.span F {v₁} := by
      refine (Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).2 hv₁)
        ?_).symm
      rw [finrank_span_singleton hv₁0]
      exact gl2_finrank_le_one (FV.isotropic _)
    have hQ₁ : (𝔾).QV v₁ = 0 := FV.isotropic _ v₁ hv₁
    set y := (𝔾).snd g
    set v₂ := specP (𝔾).QV y⁻¹ v₁
    have hQ₂ : (𝔾).QV v₂ = 0 := by rw [specP_isometry]; exact hQ₁
    have hv₂0 : v₂ ≠ 0 := fun h => hv₁0 ((specP (𝔾).QV y⁻¹).map_eq_zero_iff.1 h)
    obtain ⟨k₁, hk₁, t₁, ht₁, he₁⟩ :=
      exists_mem_latticeSpin_apply_eq_smul (𝔾).QV gl2Basis gl2_QV_eq hv₁0 hQ₁
    obtain ⟨k₂, hk₂, t₂, ht₂, he₂⟩ :=
      exists_mem_latticeSpin_apply_eq_smul (𝔾).QV gl2Basis gl2_QV_eq hv₂0 hQ₂
    set κ := (𝔾).inr (k₁ * k₂⁻¹)
    have hκ : κ ∈ gl2K (F := F) := (𝔾).inr_mem_latticeK _ _ (mul_mem hk₁ (inv_mem hk₂))
    refine ⟨g * κ⁻¹, ⟨?_, ?_⟩, κ, hκ, by rw [inv_mul_cancel_right]⟩
    · change (𝔾).fst (g * κ⁻¹) ∈ flagStab FW
      rw [gl2_flagStab_W]; trivial
    · change (𝔾).snd (g * κ⁻¹) ∈ flagStab FV
      have hk₁inv : specP (𝔾).QV k₁⁻¹ v₁ = t₁⁻¹ • gl2Basis 2 := by
        apply (specP (𝔾).QV k₁).injective
        rw [← specP_mul_apply, mul_inv_cancel, map_one, map_smul, he₁, smul_smul,
          inv_mul_cancel₀ ht₁, one_smul]; rfl
      have hy : specP (𝔾).QV y v₂ = v₁ := by
        rw [← specP_mul_apply, mul_inv_cancel, map_one]; rfl
      have key : specP (𝔾).QV ((𝔾).snd (g * κ⁻¹)) v₁ = (t₁⁻¹ * t₂) • v₁ := by
        rw [map_mul, map_inv, snd_inr, mul_inv_rev, inv_inv, ← mul_assoc]
        change specP (𝔾).QV (y * k₂ * k₁⁻¹) v₁ = _
        rw [specP_mul_apply, hk₁inv, map_smul, specP_mul_apply, he₂, map_smul, hy, smul_smul]
      rw [mem_flagStab_iff]
      intro i v hv
      rcases Nat.lt_or_ge (i : ℕ) 1 with hi | hi
      · have : i = 0 := Fin.ext (by rw [Fin.val_zero]; omega)
        rw [this, FV.sub_zero, Submodule.mem_bot] at hv ⊢
        rw [hv, map_zero]
      · have : i = ⟨1, by omega⟩ := Fin.ext (by have := i.isLt; simp; omega)
        rw [this] at hv ⊢
        change v ∈ ℓ at hv
        change _ ∈ ℓ
        rw [hℓeq] at hv ⊢
        obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hv
        rw [map_smul, key, smul_smul]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-! ## The torus `M` and its good compact subgroup -/

/-- **A good compact subgroup for the torus `M`** (a proper Levi subgroup): `K = gl2K`, compact
open (`isCompact_latticeK`, `isOpen_latticeK`), with `G = P K` for every `P ∈ 𝒫(M)`
(`gl2_iwasawa`, which holds for all flag parabolics), and in good position: it stabilizes the
lattice spanned by `z₋₁, z₀, ½ z₁`, whose basis vectors lie in the weight spaces of `M`. -/
def gl2GoodK : (𝔾).GoodK (gl2Levi (F := F)).toFlagLeviDatum where
  K := gl2K
  isOpen := (𝔾).isOpen_latticeK _ _
  isCompact := (𝔾).isCompact_latticeK _ _
  mul_eq P hP g := by
    obtain ⟨FW, FV, rfl, -⟩ := hP
    exact gl2_iwasawa FW FV g
  goodPositionW := ⟨Fin 0, inferInstance, Pi.basisFun F (Fin 0), fun i => i.elim0,
    fun _ _ _ _ i => i.elim0⟩
  goodPositionV := ⟨Fin 3, inferInstance, gl2Basis, fun i => ⟨(𝔾).stdWt (Sum.inr i), by
      rw [gl2Basis_eq]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr i, rfl, rfl⟩)⟩,
    by rintro _ ⟨k, hk, rfl⟩; exact hk.2.1⟩

end GSpinGGP.GGPData
