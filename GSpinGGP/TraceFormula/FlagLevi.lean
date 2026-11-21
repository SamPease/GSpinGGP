/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Basic
import GSpinGGP.GGP.Cocharacter

/-!
# The Levi subgroups of flag stabilizers

For an isotropic flag `F` of a quadratic space `V` and a splitting `(b, wt)` of its weight
filtration (`IsFlagSplitting`, `GGP/Cocharacter.lean`), the Levi subgroup `M_F` of the flag
stabilizer `P_F = flagStab F ⊆ GSpin(V)` (Thesis §5.1.2) and the Levi decomposition
`P_F = M_F N_F`; and their products in `G = GSpin(W) × GSpin(V)`.

## Main definitions

* `wtProj b wt w`: the projection onto the weight-`w` part of the splitting.
* `flagLevi b wt`: the elements of `GSpin(V)` whose image in `SO(V)` commutes with every
  `wtProj b wt w` (i.e. preserves each weight space); it contains the central scalars.
* `GGPData.flagLeviG`: `M_{F_W} × M_{F_V} ⊆ G`.

## Main results

* `IsFlagSplitting.flagLevi_le_flagStab`, `IsFlagSplitting.exists_mem_flagLevi_mul`:
  `M_F ⊆ P_F` and `P_F = M_F N_F` (with `N_F = flagUnip F`).
* `GGPData.flagLeviG_le_whittB`, `GGPData.exists_mem_flagLeviG_mul`: the same for
  `P_{F_W} × P_{F_V} = (M_{F_W} × M_{F_V})(N_{F_W} × N_{F_V})`.

`M ∩ N = 1`, the opposite unipotent radical and the good position of a compact open `K` are not
proved here, so no Iwasawa pair of a Levi subgroup of `G` is built yet.
-/

open MeasureTheory Topology Filter

noncomputable section

namespace GSpinGGP

/-! ## 1. The Levi subgroup of a flag stabilizer in `GSpin(V)` -/

section FlagLevi

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V}
variable {ι : Type*} [Fintype ι]

/-- The projection onto the weight-`w` part of a basis with weights: `b i ↦ b i` if `wt i = w`,
`b i ↦ 0` otherwise. -/
def wtProj (b : Module.Basis ι K V) (wt : ι → ℤ) (w : ℤ) : V →ₗ[K] V :=
  b.constr K fun i => if wt i = w then b i else 0

omit [Invertible (2 : K)] [Fintype ι] in
theorem repr_wtProj (b : Module.Basis ι K V) (wt : ι → ℤ) (w : ℤ) (x : V) (i : ι) :
    b.repr (wtProj b wt w x) i = if wt i = w then b.repr x i else 0 := by
  have key : (b.coord i).comp (wtProj b wt w) = if wt i = w then b.coord i else 0 := by
    refine b.ext fun j => ?_
    simp only [LinearMap.comp_apply, wtProj, Module.Basis.constr_basis, Module.Basis.coord_apply]
    by_cases hij : i = j
    · subst hij; split_ifs <;> simp
    · split_ifs <;> simp [Ne.symm hij]
  have := congr($key x)
  simp only [LinearMap.comp_apply, Module.Basis.coord_apply] at this
  rw [this]
  split_ifs <;> simp

/-- **The Levi subgroup** attached to a splitting `(b, wt)` of the weight filtration of an
isotropic flag (Thesis §5.1.2, `P = M N`): the elements of `GSpin(V)` whose image in `SO(V)`
commutes with every weight projection `wtProj b wt w`, i.e. preserves each weight space of the
splitting.  It contains the central scalars `K^×`, and lies in the flag stabilizer
(`IsFlagSplitting.flagLevi_le_flagStab`). -/
def flagLevi (b : Module.Basis ι K V) (wt : ι → ℤ) : Subgroup (GSpin Q) where
  carrier := {g | ∀ w : ℤ,
    (specP Q g : V →ₗ[K] V) ∘ₗ wtProj b wt w = wtProj b wt w ∘ₗ (specP Q g : V →ₗ[K] V)}
  one_mem' := by intro w; ext v; simp
  mul_mem' := by
    intro g h hg hh w
    rw [map_mul, show ((specP Q g * specP Q h : V ≃ₗ[K] V) : V →ₗ[K] V) =
      (specP Q g : V →ₗ[K] V) ∘ₗ (specP Q h : V →ₗ[K] V) from rfl, LinearMap.comp_assoc, hh w,
      ← LinearMap.comp_assoc, hg w, LinearMap.comp_assoc]
  inv_mem' := by
    intro g hg w
    ext v
    have h := congr($(hg w) (specP Q g⁻¹ v))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h ⊢
    rw [specP_inv_apply_apply] at h
    rw [← h]
    have := specP_inv_apply_apply g⁻¹ (wtProj b wt w (specP Q g⁻¹ v))
    rwa [inv_inv] at this

omit [Fintype ι] in
theorem scalarGSpin_mem_flagLevi (b : Module.Basis ι K V) (wt : ι → ℤ) (c : Kˣ) :
    scalarGSpin Q c ∈ flagLevi (Q := Q) b wt := by
  intro w
  rw [specP_scalarGSpin_eq_one]
  rfl

omit [Invertible (2 : K)] [Fintype ι] in
/-- A map that is homogeneous of degree `0` for the weights commutes with the weight projections. -/
theorem wtProj_comp_of_isHomog {b : Module.Basis ι K V} {wt : ι → ℤ} {A : V →ₗ[K] V}
    (hA : ∀ j, IsHomog b wt (A (b j)) (wt j)) (w : ℤ) :
    A ∘ₗ wtProj b wt w = wtProj b wt w ∘ₗ A := by
  refine b.ext fun j => b.repr.injective (Finsupp.ext fun i => ?_)
  simp only [LinearMap.comp_apply, repr_wtProj]
  rw [show wtProj b wt w (b j) = if wt j = w then b j else 0 by simp [wtProj]]
  by_cases hj : wt j = w
  · rw [ite_eq_left hj]
    split_ifs with hi
    · rfl
    · exact hA j i (by omega)
  · rw [ite_eq_right hj, map_zero, map_zero, Finsupp.zero_apply]
    split_ifs with hi
    · exact (hA j i (by omega)).symm
    · rfl

/-- **The Levi subgroup lies in the flag stabilizer**: `M_F ⊆ P_F`.  An element preserving each
weight space preserves the weight filtration `V_{≥w}`, whose members are those of the flag
(`IsotropicFlag.sub_eq_flagWt`). -/
theorem IsFlagSplitting.flagLevi_le_flagStab [FiniteDimensional K V] {F : IsotropicFlag Q}
    {b : Module.Basis ι K V} {wt : ι → ℤ} (hs : IsFlagSplitting F b wt) :
    flagLevi (Q := Q) b wt ≤ flagStab F := by
  intro g hg
  have hpres : ∀ w, ∀ v ∈ flagWt F w, specP Q g v ∈ flagWt F w := by
    intro w v hv
    rw [hs.mem_flagWt_iff] at hv ⊢
    intro i hi
    have h0 : wtProj b wt (wt i) v = 0 := by
      refine b.repr.injective (Finsupp.ext fun j => ?_)
      rw [repr_wtProj, map_zero, Finsupp.zero_apply]
      split_ifs with hj
      · exact hv j (by omega)
      · rfl
    have h := congr($(hg (wt i)) v)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, h0, map_zero] at h
    have := congr(b.repr $h i)
    rw [repr_wtProj, ite_eq_left rfl, map_zero, Finsupp.zero_apply] at this
    exact this.symm
  refine mem_flagStab_iff.mpr fun i v hv => ?_
  rw [F.sub_eq_flagWt] at hv ⊢
  exact hpres _ v hv

/-- **Levi decomposition of a flag stabilizer** `P_F = M_F N_F` (Thesis §5.1.2): every `p ∈ P_F`
is `m u` with `m` in the Levi subgroup `flagLevi b wt` of a splitting and `u` in the unipotent
radical `flagUnip F`.  From `IsFlagSplitting.exists_levi_decomp` (`p = m y` with `y ∈ K^× N_F`) by
moving the scalar of `y` into `m` (`exists_mul_scalarGSpin_mem_flagUnip_of_mem_flagUnipSO`). -/
theorem IsFlagSplitting.exists_mem_flagLevi_mul [FiniteDimensional K V] (hQ : IsNondeg Q)
    {F : IsotropicFlag Q} {b : Module.Basis ι K V} {wt : ι → ℤ} (hs : IsFlagSplitting F b wt)
    {p : GSpin Q} (hp : p ∈ flagStab F) :
    ∃ m ∈ flagLevi (Q := Q) b wt, ∃ u ∈ flagUnip F, p = m * u := by
  obtain ⟨m, y, he, hm, hy, hy'⟩ := hs.exists_levi_decomp hQ hp
  have hySO : y ∈ flagUnipSO F := mem_flagUnipSO_of_raisesFil hy hy'
  obtain ⟨c, hc⟩ := exists_mul_scalarGSpin_mem_flagUnip_of_mem_flagUnipSO hQ hySO
  refine ⟨m * scalarGSpin Q c⁻¹, (flagLevi b wt).mul_mem
      (wtProj_comp_of_isHomog hm) (scalarGSpin_mem_flagLevi b wt c⁻¹),
    y * scalarGSpin Q c, hc, ?_⟩
  have hcen := Subgroup.mem_center_iff.mp (scalarGSpin_mem_center Q c⁻¹)
  rw [he, mul_assoc, ← mul_assoc (scalarGSpin Q c⁻¹), ← hcen y, mul_assoc y,
    ← map_mul, inv_mul_cancel, map_one, mul_one]

end FlagLevi

/-! ## 2. Levi subgroups of `P_{F_W} × P_{F_V}` -/

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {d : GGPData F}

section LeviG

variable (d)
variable {ιW ιV : Type*} [Fintype ιW] [Fintype ιV]

/-- **The Levi subgroup of `P = P_{F_W} × P_{F_V}`** (`d.whittB F_W F_V`) attached to splittings
`(b_W, wt_W)`, `(b_V, wt_V)` of the two flags: `M = M_{F_W} × M_{F_V}` (Thesis §5.1.2). -/
def flagLeviG (bW : Module.Basis ιW F (Fin d.m → F)) (wtW : ιW → ℤ)
    (bV : Module.Basis ιV F d.V) (wtV : ιV → ℤ) : Subgroup ↥d.G :=
  (flagLevi (Q := d.QW) bW wtW).comap d.fst ⊓ (flagLevi (Q := d.QV) bV wtV).comap d.snd

variable {d}

/-- **Levi decomposition** `P_{F_W} × P_{F_V} = (M_{F_W} × M_{F_V})(N_{F_W} × N_{F_V})`
(Thesis §5.1.2), factorwise from `IsFlagSplitting.exists_mem_flagLevi_mul`. -/
theorem exists_mem_flagLeviG_mul {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV}
    {bW : Module.Basis ιW F (Fin d.m → F)} {wtW : ιW → ℤ}
    {bV : Module.Basis ιV F d.V} {wtV : ιV → ℤ}
    (hsW : IsFlagSplitting FW bW wtW) (hsV : IsFlagSplitting FV bV wtV)
    {p : ↥d.G} (hp : p ∈ d.whittB FW FV) :
    ∃ m ∈ d.flagLeviG bW wtW bV wtV, ∃ u ∈ d.whittU FW FV, p = m * u := by
  obtain ⟨mW, hmW, uW, huW, eW⟩ := hsW.exists_mem_flagLevi_mul d.nondeg hp.1
  obtain ⟨mV, hmV, uV, huV, eV⟩ := hsV.exists_mem_flagLevi_mul d.nondeg_QV hp.2
  refine ⟨d.pair (mW, mV), ⟨hmW, hmV⟩, d.pair (uW, uV), ⟨huW, huV⟩, ?_⟩
  rw [← map_mul, Prod.mk_mul_mk, ← eW, ← eV, pair_fst_snd]

/-- `M_{F_W} × M_{F_V} ⊆ P_{F_W} × P_{F_V}`. -/
theorem flagLeviG_le_whittB {FW : IsotropicFlag d.QW} {FV : IsotropicFlag d.QV}
    {bW : Module.Basis ιW F (Fin d.m → F)} {wtW : ιW → ℤ}
    {bV : Module.Basis ιV F d.V} {wtV : ιV → ℤ}
    (hsW : IsFlagSplitting FW bW wtW) (hsV : IsFlagSplitting FV bV wtV) :
    d.flagLeviG bW wtW bV wtV ≤ d.whittB FW FV :=
  fun _ hm => ⟨hsW.flagLevi_le_flagStab hm.1, hsV.flagLevi_le_flagStab hm.2⟩

end LeviG

end GGPData

end GSpinGGP
