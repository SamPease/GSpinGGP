/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LuoTorus
import GSpinGGP.TraceFormula.SOLieFacts

/-!
# Towards (L4): `J^Lie` of the general spin triple is Luo's `J^Lie`

Ingredients for `exists_JLie_transfer` (`TraceFormula/LuoJLieExp.lean`), which identifies
`J^Lie` of the general spin triple with Luo's `J^Lie` of the special orthogonal triple when
neither `W` nor `V` is a hyperbolic plane.

Uses the transport of Weil measures (`IsWeilMeasure.map`, `Literature/Measure.lean`) and the fact
that `H̄` normalizes `𝔥` and fixes `λ` (`LuoDatum.conj_mem_lieH_of_mem_HbarU`, `SOLieFacts.lean`).

* `LuoDatum.map_conjLieH_eq`, `LuoDatum.kernelLie_mul_left`: an `exp`-compatible measure on `𝔥(F)`
  is `Ad(H̄(F))`-invariant (for conjugation invariant `μ_H`), so Luo's kernel `K^Lie(f, ·)` is left
  `H̄(F)`-invariant.
* `luoOf_flagSub`, `mem_Nset_iff_mem_flagUnipSO`, `toGbarU_mem_HbarU`, `exists_mem_H_toGbarU_eq`:
  `P(H(F)) = H̄(F)`; `exists_continuousMulEquiv_HmodAGH`: `H(F)/A_{G,H}(F) ≃ H̄(F)` as topological
  groups.
* `exists_weil_Hbar`: the Weil measure of `J` on `H(F)\G(F)/A_G(F)` gives one on `H̄(F)\Ḡ(F)`.
* `toSOLin_mem_lieH_iff`, `toSOHCLE`: `ad : 𝔥⁰ ≃ 𝔥`; `kernelLie_toGbar`: the kernels of `J^Lie`
  agree at matched points.
* `exists_JLie_transfer_of`: (L4) follows from the `exp`-compatibility of the transported measures.
-/
noncomputable section

open MeasureTheory Topology Filter

set_option linter.unusedSectionVars false

namespace GSpinGGP


namespace LuoDatum


section KernelInv

open JLie

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (L : LuoDatum F)

/-- `Y ↦ u⁻¹ Y u` on `𝔥(F)`, `u ∈ H̄(F)`, as a linear homeomorphism
(`conj_mem_lieH_of_mem_HbarU`). -/
def conjLieH (u : ↥L.Hbar) : ↥L.lieH ≃L[F] ↥L.lieH :=
  haveI := t2Space_of_moduleTopology F L.Amb
  haveI := isTopologicalRing_of_moduleTopology F L.Amb
  haveI := IsModuleTopology.toContinuousSMul F L.Amb
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun Y => ⟨((((u : ↥L.Gbar) : L.Ambˣ)⁻¹ : L.Ambˣ) : L.Amb) * Y *
          (((u : ↥L.Gbar) : L.Ambˣ) : L.Amb), (L.conj_mem_lieH_of_mem_HbarU u.2 Y.2).1⟩
      map_add' := fun Y Z => Subtype.ext (by simp [mul_add, add_mul])
      map_smul' := fun c Y => Subtype.ext (by simp)
      invFun := fun Y => ⟨(((u : ↥L.Gbar) : L.Ambˣ) : L.Amb) * Y *
          ((((u : ↥L.Gbar) : L.Ambˣ)⁻¹ : L.Ambˣ) : L.Amb), by
        have h := (L.conj_mem_lieH_of_mem_HbarU (L.HbarU.inv_mem u.2) Y.2).1
        rwa [inv_inv] at h⟩
      left_inv := fun Y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun Y => Subtype.ext (by simp [mul_assoc]) }

@[simp] theorem coe_conjLieH (u : ↥L.Hbar) (Y : ↥L.lieH) :
    ((L.conjLieH u Y : ↥L.lieH) : L.Amb) = ((((u : ↥L.Gbar) : L.Ambˣ)⁻¹ : L.Ambˣ) : L.Amb) * Y *
      (((u : ↥L.Gbar) : L.Ambˣ) : L.Amb) := rfl

@[simp] theorem coe_conjLieH_symm (u : ↥L.Hbar) (Y : ↥L.lieH) :
    (((L.conjLieH u).symm Y : ↥L.lieH) : L.Amb) = (((u : ↥L.Gbar) : L.Ambˣ) : L.Amb) * Y *
      ((((u : ↥L.Gbar) : L.Ambˣ)⁻¹ : L.Ambˣ) : L.Amb) := rfl

/-- **`exp`-compatible measures on `𝔥(F)` are `Ad(H̄(F))`-invariant** when `μ_H` is invariant under
conjugation (unimodular): `exp(u⁻¹ X u) = u⁻¹ e^X u` (`expA_units_conj`) carries the defining
identity near `0` for `Ad(u)_* μ` to that for `μ`, and two Haar measures agreeing near `0` are
equal (`Measure.eq_of_isAddHaarMeasure_of_eqOn_nhds`). -/
theorem map_conjLieH_eq {μH : Measure ↥L.Hbar} {μ : Measure ↥L.lieH}
    (hconj : ∀ u : ↥L.Hbar, μH.map (fun h => u⁻¹ * h * u) = μH) (hexp : L.IsExpCompatH μH μ)
    (u : ↥L.Hbar) : μ.map (L.conjLieH u) = μ := by
  have := submodule_isTopologicalAddGroup L.lieH
  obtain ⟨_, _, _, _, _⟩ := submodule_topology L.lieH
  have hμ := hexp.1
  obtain ⟨U, hU, hUS⟩ := hexp.2
  set Φ := L.conjLieH u
  have hΦ : (μ.map Φ).IsAddHaarMeasure :=
    Φ.toLinearEquiv.toAddEquiv.isAddHaarMeasure_map μ Φ.continuous Φ.symm.continuous
  have hU' : U ∩ Φ.symm ⁻¹' U ∈ 𝓝 (0 : ↥L.lieH) :=
    inter_mem hU (Φ.symm.continuous.continuousAt.preimage_mem_nhds (by rwa [map_zero]))
  refine Measure.eq_of_isAddHaarMeasure_of_eqOn_nhds _ _ hU' fun S hS hSU => ?_
  have hpre : Φ ⁻¹' S = Φ.symm '' S := (Φ.toEquiv.image_symm_eq_preimage S).symm
  rw [Measure.map_apply Φ.continuous.measurable hS]
  have hS' : Φ ⁻¹' S ⊆ U := by
    rw [hpre]; rintro _ ⟨Y, hY, rfl⟩; exact (hSU hY).2
  rw [hUS _ (Φ.continuous.measurable hS) hS', hUS S hS (hSU.trans Set.inter_subset_left)]
  -- the `exp`-images correspond under `h ↦ u⁻¹ h u`
  set c : ↥L.Hbar ≃ₜ ↥L.Hbar :=
    { toFun := fun h => u⁻¹ * h * u
      invFun := fun h => u * h * u⁻¹
      left_inv := fun h => by group
      right_inv := fun h => by group
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hset : {h : ↥L.Hbar | ∃ X ∈ Φ ⁻¹' S, (((h : ↥L.Gbar) : L.Ambˣ) : L.Amb) =
      expA F (X : L.Amb)} = c ⁻¹' {h | ∃ X ∈ S, (((h : ↥L.Gbar) : L.Ambˣ) : L.Amb) =
      expA F (X : L.Amb)} := by
    set w : L.Ambˣ := ((u : ↥L.Gbar) : L.Ambˣ)
    have hexpc : ∀ X : L.Amb, expA F (((w⁻¹ : L.Ambˣ) : L.Amb) * X * (w : L.Amb)) =
        ((w⁻¹ : L.Ambˣ) : L.Amb) * expA F X * (w : L.Amb) := fun X => by
      have := expA_units_conj (F := F) w⁻¹ X
      rwa [inv_inv] at this
    have hc : ∀ h : ↥L.Hbar, (((c h : ↥L.Gbar) : L.Ambˣ) : L.Amb) =
        ((w⁻¹ : L.Ambˣ) : L.Amb) * (((h : ↥L.Gbar) : L.Ambˣ) : L.Amb) * (w : L.Amb) := fun h => rfl
    ext h
    simp only [Set.mem_preimage]
    constructor
    · rintro ⟨X, hX, hh⟩
      refine ⟨Φ X, hX, ?_⟩
      rw [hc, hh, coe_conjLieH, hexpc]
    · rintro ⟨Y, hY, hh⟩
      refine ⟨Φ.symm Y, by simpa using hY, ?_⟩
      rw [coe_conjLieH_symm]
      have := congrArg (fun a => (w : L.Amb) * a * ((w⁻¹ : L.Ambˣ) : L.Amb)) hh
      simp only [hc] at this
      rw [expA_units_conj, ← this]
      simp [mul_assoc]
  have hc : μH.map c.toMeasurableEquiv = μH := hconj u
  rw [hset, show (⇑c ⁻¹' {h : ↥L.Hbar | ∃ X ∈ S, (((h : ↥L.Gbar) : L.Ambˣ) : L.Amb) =
      expA F (X : L.Amb)}) = (⇑c.toMeasurableEquiv ⁻¹' {h : ↥L.Hbar | ∃ X ∈ S,
      (((h : ↥L.Gbar) : L.Ambˣ) : L.Amb) = expA F (X : L.Amb)}) from rfl,
    ← MeasurableEquiv.map_apply, hc]

/-- **`K^Lie(f, ·)` is left `H̄(F)`-invariant** (Luo §4): change of variables `Y ↦ u⁻¹ Y u` on
`𝔥(F)`, which preserves `μ_𝔥` (`map_conjLieH_eq`) and `λ` (`conj_mem_lieH_of_mem_HbarU`). -/
theorem kernelLie_mul_left (ψ : NontrivialAddChar F) {μH : Measure ↥L.Hbar}
    {μ : Measure ↥L.lieH} (hconj : ∀ u : ↥L.Hbar, μH.map (fun h => u⁻¹ * h * u) = μH)
    (hexp : L.IsExpCompatH μH μ) (f : ↥L.lie → ℂ) {u : ↥L.Gbar} (hu : u ∈ L.Hbar)
    (x : ↥L.Gbar) : L.kernelLie ψ μ f (u * x) = L.kernelLie ψ μ f x := by
  set Φ := L.conjLieH ⟨u, hu⟩
  have hme : MeasurableEmbedding (Φ : ↥L.lieH → ↥L.lieH) := Φ.toHomeomorph.measurableEmbedding
  unfold kernelLie
  conv_rhs => rw [← L.map_conjLieH_eq hconj hexp ⟨u, hu⟩, hme.integral_map]
  refine integral_congr_ae (Eventually.of_forall fun Y => ?_)
  have hlam : L.lam (((((u : ↥L.Gbar) : L.Ambˣ))⁻¹ : L.Ambˣ) * (Y : L.Amb) *
      (((u : ↥L.Gbar) : L.Ambˣ) : L.Amb)) = L.lam Y :=
    (L.conj_mem_lieH_of_mem_HbarU (Subgroup.mem_subgroupOf.1 hu) Y.2).2
  change L.extFn f (L.conjInv (u * x) Y) * ψ (L.lam Y) =
    L.extFn f (L.conjInv x (((((u : ↥L.Gbar) : L.Ambˣ))⁻¹ : L.Ambˣ) * (Y : L.Amb) *
      (((u : ↥L.Gbar) : L.Ambˣ) : L.Amb))) * ψ (L.lam (((((u : ↥L.Gbar) : L.Ambˣ))⁻¹ : L.Ambˣ) *
        (Y : L.Amb) * (((u : ↥L.Gbar) : L.Ambˣ) : L.Amb)))
  rw [hlam]
  congr 2

end KernelInv

end LuoDatum


/-! ## `H(F)/A_{G,H}(F) ≃ H̄(F)` -/

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

theorem luoScale_ne_zero (i : ℤ) : d.luoScale i ≠ 0 := by
  unfold luoScale
  split_ifs <;> exact zpow_ne_zero _ d.ν.ne_zero

/-- Luo's flag `Z_k = ⟨z^L_r, …, z^L_{r-k+1}⟩` is the flag `⟨z_r, …, z_{r-k+1}⟩` of `d`
(the basis vectors are rescaled by nonzero scalars). -/
theorem luoOf_flagSub {k : ℕ} (hk : k ≤ d.r) :
    d.luoOf.flagSub k = d.flag.sub ⟨k, Nat.lt_succ_of_le hk⟩ := by
  change Submodule.span F (Set.range fun j : Fin k => d.luoOf.zV ((d.r : ℤ) - (j : ℕ))) =
    Submodule.span F (Set.range fun j : Fin k => d.zV ((d.r : ℤ) - (j : ℕ)))
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have h := Submodule.smul_mem (Submodule.span F (Set.range fun j : Fin k =>
      d.zV ((d.r : ℤ) - (j : ℕ)))) (d.luoScale ((d.r : ℤ) - (j : ℕ)))
      (Submodule.subset_span ⟨j, rfl⟩)
    have e : d.luoOf.zV ((d.r : ℤ) - (j : ℕ)) = d.luoScale ((d.r : ℤ) - (j : ℕ)) •
      d.zV ((d.r : ℤ) - (j : ℕ)) := d.luoOf_zV _
    simp only []; rw [e]; exact h
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have h := Submodule.smul_mem (Submodule.span F (Set.range fun j : Fin k =>
      d.luoOf.zV ((d.r : ℤ) - (j : ℕ)))) (d.luoScale ((d.r : ℤ) - (j : ℕ)))⁻¹
      (Submodule.subset_span ⟨j, rfl⟩)
    have e : d.luoOf.zV ((d.r : ℤ) - (j : ℕ)) = d.luoScale ((d.r : ℤ) - (j : ℕ)) •
      d.zV ((d.r : ℤ) - (j : ℕ)) := d.luoOf_zV _
    have e2 : (d.luoScale ((d.r : ℤ) - (j : ℕ)))⁻¹ • d.luoOf.zV ((d.r : ℤ) - (j : ℕ)) =
        d.zV ((d.r : ℤ) - (j : ℕ)) := by
      have h0 := d.luoScale_ne_zero ((d.r : ℤ) - (j : ℕ))
      unfold LuoDatum.zV GGPData.zV
      refine Prod.ext (smul_zero _) ?_
      exact inv_smul_smul₀ h0 _
    simp only []; rw [← e2]; exact h

theorem luoOf_flagSub_r : d.luoOf.flagSub d.r = d.flag.top :=
  d.luoOf_flagSub le_rfl

theorem mem_luoOf_flagSub_iff (k : ℕ) (hk : k ≤ d.r) (v : d.V) :
    v ∈ d.luoOf.flagSub k ↔ v ∈ d.flag.sub ⟨k, Nat.lt_succ_of_le hk⟩ := by
  rw [d.luoOf_flagSub hk]; rfl

theorem mem_luoOf_orthogonal_iff (v : d.V) :
    v ∈ (bform d.luoOf.QV).orthogonal (d.luoOf.flagSub d.luoOf.r) ↔
      v ∈ (bform d.QV).orthogonal d.flag.top := by
  change v ∈ (bform d.QV).orthogonal (d.luoOf.flagSub d.r) ↔ _
  rw [d.luoOf_flagSub_r]

/-- A unit of `End V` with value `P(b)` lies in `SO(V)`. -/
theorem specPV_mem_SOu (b : GSpin d.QV) {n : (Module.End F d.luoOf.V)ˣ}
    (hn : (n : Module.End F d.luoOf.V) = (specP d.QV b : d.V →ₗ[F] d.V)) :
    n ∈ LuoDatum.SOu d.luoOf.QV := by
  change LinearMap.GeneralLinearGroup.generalLinearEquiv F _ n ∈ SOGrp d.QV
  have e : LinearMap.GeneralLinearGroup.generalLinearEquiv F d.luoOf.V n = specP d.QV b :=
    LinearEquiv.ext fun v => by
      change (n : Module.End F d.luoOf.V) v = _
      rw [hn]; rfl
  rw [e, ← range_specP_eq_SOGrp d.nondeg_QV]
  exact ⟨b, rfl⟩

/-- **`P(b) ∈ N` (Luo's unipotent radical) iff `b ∈ F^× · N_F`** (`flagUnipSO`). -/
theorem mem_Nset_iff_mem_flagUnipSO {b : GSpin d.QV} {n : (Module.End F d.luoOf.V)ˣ}
    (hn : (n : Module.End F d.luoOf.V) = (specP d.QV b : d.V →ₗ[F] d.V)) :
    n ∈ d.luoOf.Nset ↔ b ∈ flagUnipSO d.flag := by
  have hP : ∀ v : d.V, @Eq d.V ((n : Module.End F d.luoOf.V) v) (specP d.QV b v) :=
    fun v => by rw [hn]; rfl
  have hsub := d.mem_luoOf_flagSub_iff
  have horth := d.mem_luoOf_orthogonal_iff
  constructor
  · rintro ⟨-, h1, h2⟩
    have hU : ∀ i : Fin d.flag.len, ∀ v ∈ d.flag.sub i.succ,
        specP d.QV b v - v ∈ d.flag.sub i.castSucc := by
      intro i v hv
      have := (hsub i i.2.le _).1 (h1 i i.2 v ((hsub (i + 1) i.2 v).2 hv))
      rwa [hP] at this
    refine ⟨mem_flagStab_iff.mpr fun i v hv => ?_, hU, fun v hv => ?_⟩
    · obtain ⟨i, hi⟩ := i
      cases i with
      | zero =>
        have h0 : d.flag.sub ⟨0, hi⟩ = ⊥ := d.flag.sub_zero
        rw [h0, Submodule.mem_bot] at hv
        rw [hv, map_zero]; exact zero_mem _
      | succ k =>
        have hk : k < d.flag.len := Nat.lt_of_succ_lt_succ hi
        have h := hU ⟨k, hk⟩ v hv
        have hle : d.flag.sub (Fin.castSucc ⟨k, hk⟩) ≤ d.flag.sub (Fin.succ ⟨k, hk⟩) :=
          d.flag.strictMono.monotone (Fin.castSucc_le_succ _)
        have := add_mem (hle h) hv
        rwa [sub_add_cancel] at this
    · have := (hsub d.r le_rfl _).1 (h2 v ((horth v).2 hv))
      rwa [hP] at this
  · rintro ⟨-, h1, h2⟩
    refine ⟨d.specPV_mem_SOu b hn, fun k hk (v : d.V) hv => ?_, fun (v : d.V) hv => ?_⟩
    · have := h1 ⟨k, hk⟩ v ((hsub (k + 1) hk v).1 hv)
      rw [← hP] at this
      exact (hsub k hk.le _).2 this
    · have := h2 v ((horth v).1 hv)
      rw [← hP] at this
      exact (hsub d.r le_rfl _).2 this

/-- `(1, b) ↦ (1, P(b))`. -/
theorem toGbarU_inr (b : GSpin d.QV) : d.toGbarU (d.inr b) = d.luoOf.inrU (d.specPVU b) := by
  apply Units.ext
  rw [toGbarU_val, LuoDatum.val_inrU, fst_inr_eq_one, snd_inr, map_one]
  rfl

/-- **`P(H) ⊆ H̄`**: `h = (a, a)(1, n)` with `n ∈ N`, and `P(n) ∈ N` (Luo's). -/
theorem toGbarU_mem_HbarU {g : ↥d.G} (hg : g ∈ d.H) : d.toGbarU g ∈ d.luoOf.HbarU := by
  have hn : d.nPart g ∈ d.N := hg
  have e : g = d.diag (d.fst g) * d.inr (d.nPart g) := by
    apply d.G_ext
    · exact ((map_mul d.fst _ _).trans (mul_one _)).symm
    · exact ((map_mul d.snd _ _).trans (mul_inv_cancel_left _ _)).symm
  rw [e, map_mul]
  refine d.luoOf.HbarU.mul_mem ?_ ?_
  · rw [← MonoidHom.comp_apply, toGbarU_comp_diag, MonoidHom.comp_apply]
    exact Subgroup.subset_closure (Or.inl ⟨_, d.specPU_mem_SOu _, rfl⟩)
  rw [toGbarU_inr]
  refine Subgroup.subset_closure (Or.inr ⟨_, ?_, rfl⟩)
  exact (d.mem_Nset_iff_mem_flagUnipSO (d.coe_specPVU _)).2 (flagUnip_le_flagUnipSO _ hn)

/-- **`H̄ ⊆ P(H)`**: write `u = (s, (s ⊕ 1) n)` (`mem_HbarU_iff`), lift `s = P(t)` and `n = P(b)`;
then `b ∈ F^× · N_F`, and a scalar multiple of `b` lies in `N_F`
(`exists_smul_sub_one_isNilpotent_of_mem_flagUnipSO`). -/
theorem exists_mem_H_toGbarU_eq {u : d.luoOf.Ambˣ} (hu : u ∈ d.luoOf.HbarU) :
    ∃ g ∈ d.H, d.toGbarU g = u := by
  obtain ⟨s, hs, n, hn, rfl⟩ := d.luoOf.mem_HbarU_iff.1 hu
  obtain ⟨t, hst⟩ := d.exists_specPU_eq_of_mem_SOu hs
  have hnSO : LinearMap.GeneralLinearGroup.generalLinearEquiv F d.luoOf.V n ∈ SOGrp d.QV := hn.1
  rw [← range_specP_eq_SOGrp d.nondeg_QV] at hnSO
  obtain ⟨b, hb⟩ := hnSO
  have hbn : d.specPVU b = n := by
    rw [specPVU_apply, hb]; exact MulEquiv.symm_apply_apply _ _
  have hbSO : b ∈ flagUnipSO d.flag :=
    (d.mem_Nset_iff_mem_flagUnipSO (n := n) (hbn ▸ d.coe_specPVU b)).1 hn
  obtain ⟨c, hc⟩ := exists_smul_sub_one_isNilpotent_of_mem_flagUnipSO d.nondeg_QV hbSO
  have hSO' := (flagUnipSO d.flag).mul_mem hbSO (scalarGSpin_mem_flagUnipSO d.flag c)
  have hbN : b * scalarGSpin d.QV c ∈ d.N :=
    ⟨hSO'.1, hSO'.2.1, hSO'.2.2, by rw [coe_mul_scalarGSpin]; exact hc⟩
  refine ⟨d.diag t * d.inr (b * scalarGSpin d.QV c),
    d.H.mul_mem (d.diag_mem_H t) (d.inr_mem_H hbN), ?_⟩
  have hsc : d.specPVU (b * scalarGSpin d.QV c) = d.specPVU b := by
    have h1 : d.specPVU (scalarGSpin d.QV c) = 1 := by
      apply Units.ext
      rw [coe_specPVU, specP_scalarGSpin_eq_one]
      rfl
    rw [map_mul, h1, mul_one]
  rw [map_mul, toGbarU_inr, hsc, hbn, ← hst]
  exact congrArg (· * d.luoOf.inrU n) (DFunLike.congr_fun d.toGbarU_comp_diag t)

/-- **`H(F)/A_{G,H}(F) ≃ H̄(F)` as topological groups**, compatibly with
`G(F)/A_G(F) ≃ Ḡ(F)`: `toGmodAG` is a closed embedding (`isClosedEmbedding_toGmodAG`), and the
image of `H(F)` in `Ḡ(F)` is `H̄(F)` (`toGbarU_mem_HbarU`, `exists_mem_H_toGbarU_eq`). -/
theorem exists_continuousMulEquiv_HmodAGH (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    (e : d.GmodAG ≃ₜ* ↥d.luoOf.Gbar) (he : ⇑e = fun x : d.GmodAG => d.toGbar (Quotient.out x)) :
    ∃ eH : d.HmodAGH ≃ₜ* ↥d.luoOf.Hbar,
      ∀ q, ((eH q : ↥d.luoOf.Gbar)) = e (d.toGmodAG q) := by
  set f : d.HmodAGH →* ↥d.luoOf.Gbar := e.toMulEquiv.toMonoidHom.comp d.toGmodAG
  have hfmk : ∀ h : ↥d.H, f (QuotientGroup.mk h) = d.toGbar (h : ↥d.G) := by
    intro h
    change e (QuotientGroup.mk (h : ↥d.G)) = _
    rw [he]
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul d.AG (h : ↥d.G)
    change d.toGbar (Quotient.out (QuotientGroup.mk (h : ↥d.G) : d.GmodAG)) = _
    rw [hn, map_mul, d.toGbar_eq_one_of_mem_AG hW hV n.2, mul_one]
  have hmem : ∀ q, f q ∈ d.luoOf.Hbar := by
    intro q
    induction q using QuotientGroup.induction_on with | H h => ?_
    rw [hfmk]
    exact d.toGbarU_mem_HbarU h.2
  set φ : d.HmodAGH →* ↥d.luoOf.Hbar := f.codRestrict d.luoOf.Hbar hmem
  have hfemb : IsEmbedding f :=
    (e.toHomeomorph.isClosedEmbedding.comp d.isClosedEmbedding_toGmodAG).isEmbedding
  have hφc : Continuous φ := continuous_induced_rng.2 hfemb.continuous
  have hφemb : IsEmbedding φ := IsEmbedding.of_comp hφc continuous_subtype_val hfemb
  have hsurj : Function.Surjective φ := by
    intro u
    obtain ⟨g, hg, hgu⟩ := d.exists_mem_H_toGbarU_eq (u := ((u : ↥d.luoOf.Gbar) : d.luoOf.Ambˣ))
      (Subgroup.mem_subgroupOf.1 u.2)
    refine ⟨QuotientGroup.mk ⟨g, hg⟩, Subtype.ext (Subtype.ext ?_)⟩
    change ((f (QuotientGroup.mk ⟨g, hg⟩) : ↥d.luoOf.Gbar) : d.luoOf.Ambˣ) = _
    rw [hfmk]
    exact hgu
  let h := hφemb.toHomeomorphOfSurjective hsurj
  let eM : d.HmodAGH ≃* ↥d.luoOf.Hbar := MulEquiv.ofBijective φ ⟨hφemb.injective, hsurj⟩
  exact ⟨{ eM with continuous_toFun := hφc, continuous_invFun := h.symm.continuous },
    fun q => rfl⟩

/-- **The measures of `J` and `J^Lie` on `H̄(F)\Ḡ(F)`**: there are an isomorphism of topological
groups `H(F)/A_{G,H}(F) ≃ H̄(F)` (`exists_continuousMulEquiv_HmodAGH`), the Haar measure
`μ_H` it carries `Measure.haar` to, and a Weil measure `m` on `H̄(F)\Ḡ(F)` for `muG` and `μ_H`
(the push-forward of `weilMeasureHG`, `IsWeilMeasure.map`), such that integrals over
`H(F)\G(F)/A_G(F)` of a function evaluated at the chosen representatives become integrals over
`H̄(F)\Ḡ(F)` of any left `H̄(F)`-invariant function `K` on `Ḡ(F)` with `K ∘ toGbar = k`. -/
theorem exists_weil_Hbar (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) :
    ∃ (eH : d.HmodAGH ≃ₜ* ↥d.luoOf.Hbar) (m : Measure (CosetSpace d.luoOf.Hbar.subtype)),
      (∀ h : ↥d.H, ((eH (QuotientGroup.mk h) : ↥d.luoOf.Gbar)) = d.toGbar (h : ↥d.G)) ∧
      IsWeilMeasure d.luoOf.Hbar.subtype d.muG ((Measure.haar : Measure d.HmodAGH).map eH) m ∧
      ∀ (K : ↥d.luoOf.Gbar → ℂ) (k : ↥d.G → ℂ), (∀ g, K (d.toGbar g) = k g) →
        (∀ h ∈ d.luoOf.Hbar, ∀ x, K (h * x) = K x) →
        ∫ q : d.HGQuot, k (Quotient.out (CosetSpace.out d.toGmodAG q : d.GmodAG))
            ∂d.weilMeasureHG =
          ∫ q, K (CosetSpace.out d.luoOf.Hbar.subtype q) ∂m := by
  refine (d.exists_continuousMulEquiv_toGbar hW hV).elim fun e he => ?_
  refine (d.exists_continuousMulEquiv_HmodAGH hW hV e he).elim fun eH heH => ?_
  have hcomp : ∀ s, d.luoOf.Hbar.subtype (eH s) = e (d.toGmodAG s) := fun s => heH s
  let ē := CosetSpace.mapHomeomorph d.toGmodAG d.luoOf.Hbar.subtype eH.toMulEquiv e hcomp
  have hR := d.isMulRightInvariant_haar_HmodAGH
  refine ⟨eH, Measure.map ē d.weilMeasureHG, ?_, ?_, ?_⟩
  · intro h
    refine (heH _).trans ((congrFun he _).trans ?_)
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul d.AG (h : ↥d.G)
    change d.toGbar (Quotient.out (QuotientGroup.mk (h : ↥d.G) : d.GmodAG)) = _
    rw [hn, map_mul, d.toGbar_eq_one_of_mem_AG hW hV n.2, mul_one]
  · have h2 := IsWeilMeasure.map (ι := d.toGmodAG) (ι' := d.luoOf.Hbar.subtype)
      d.weilMeasureHG_spec eH e hcomp
    refine (congrArg (fun ν => IsWeilMeasure d.luoOf.Hbar.subtype ν _ _) ?_).mpr h2
    unfold muG
    congr 1
    exact he.symm
  · intro K k hK hinv
    have hK' : ∀ (s : ↥d.luoOf.Hbar) (x : ↥d.luoOf.Gbar), K (d.luoOf.Hbar.subtype s * x) = K x :=
      fun s x => hinv (s : ↥d.luoOf.Gbar) s.2 x
    have hI := integral_map_mapHomeomorph (ι := d.toGmodAG) (ι' := d.luoOf.Hbar.subtype)
      eH.toMulEquiv e hcomp d.weilMeasureHG K hK'
    refine Eq.trans ?_ hI.symm
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    exact ((congrArg K (congrFun he _)).trans (hK _)).symm

/-! ## `𝔥⁰ ≃ 𝔥 = so(W) ⊕ 𝔫` -/

/-- **`ad` carries `𝔫_F` onto Luo's `𝔫`**: for `Z ∈ so_Cliff(V)`, `ad Z ∈ 𝔫` iff `Z ∈ 𝔫_F`
(the flags agree, `luoOf_flagSub`). -/
theorem adV_mem_lieN_iff {Z : CliffordAlgebra d.QV} (hZ : Z ∈ soSub d.QV) :
    adV d.QV Z ∈ d.luoOf.lieN ↔ Z ∈ lieFlagUnip d.flag := by
  have hsub := d.mem_luoOf_flagSub_iff
  have horth := d.mem_luoOf_orthogonal_iff
  constructor
  · rintro ⟨-, h1, h2⟩
    refine ⟨hZ, fun i (v : d.V) hv => ?_, fun (v : d.V) hv => ?_⟩
    · exact (hsub i i.2.le _).1 (h1 i i.2 v ((hsub (i + 1) i.2 v).2 hv))
    · exact (hsub d.r le_rfl _).1 (h2 v ((horth v).2 hv))
  · rintro ⟨-, h1, h2⟩
    refine ⟨adV_mem_skewAdjoint hZ.1, fun k hk (v : d.V) hv => ?_, fun (v : d.V) hv => ?_⟩
    · exact (hsub k hk.le _).2 (h1 ⟨k, hk⟩ v ((hsub (k + 1) hk v).1 hv))
    · exact (hsub d.r le_rfl _).2 (h2 v ((horth v).1 hv))

/-- **`ad` carries `𝔥⁰` onto `𝔥 = so(W) ⊕ 𝔫`**: for `X ∈ 𝔤⁰`,
`ad X_V − (ad X_W ⊕ 0) = ad (X_V − X_W)` (`toSOLin_diagLie`), and `adV_mem_lieN_iff`. -/
theorem toSOLin_mem_lieH_iff {X : d.ambient} (hX : X ∈ d.lieZero) :
    d.toSOLin X ∈ d.luoOf.lieH ↔ X ∈ d.lieH0 := by
  have hW : X.1 ∈ gspin d.QW := hX.1.1
  have hdiag : d.luoOf.extLie (adV d.QW X.1) = adV d.QV (d.diagLie X.1).2 :=
    (congrArg d.luoOf.sndA (d.toSOLin_diagLie hW)).symm
  have hZ : X.2 - (d.diagLie X.1).2 ∈ soSub d.QV :=
    sub_mem hX.2 (map_mem_soSub d.nondeg _ hX.1)
  have e : d.luoOf.sndA (d.toSOLin X) - d.luoOf.extLie (d.luoOf.fstA (d.toSOLin X)) =
      adV d.QV (X.2 - (d.diagLie X.1).2) := by
    rw [sndA_toSOLin, fstA_toSOLin, hdiag, map_sub]
    rfl
  constructor
  · rintro ⟨-, hN⟩
    rw [e] at hN
    exact ⟨hX, (d.adV_mem_lieN_iff hZ).1 hN⟩
  · rintro ⟨-, hN⟩
    refine ⟨d.toSO_mem ⟨X, hX⟩, ?_⟩
    rw [e]
    exact (d.adV_mem_lieN_iff hZ).2 hN

/-- `ad : 𝔥⁰ ≃ 𝔥` as a linear equivalence. -/
def toSOH : ↥d.lieH0 ≃ₗ[F] ↥d.luoOf.lieH where
  toFun X := ⟨d.toSOLin X, (d.toSOLin_mem_lieH_iff (d.lieH0_le_lie0 X.2)).2 X.2⟩
  map_add' X Y := Subtype.ext (map_add d.toSOLin _ _)
  map_smul' c X := Subtype.ext (map_smul d.toSOLin _ _)
  invFun Y := ⟨(d.toSO.symm ⟨Y, Y.2.1⟩ : d.ambient), (d.toSOLin_mem_lieH_iff
      (d.toSO.symm ⟨Y, Y.2.1⟩).2).1 (by rw [toSOLin_toSO_symm]; exact Y.2)⟩
  left_inv X := Subtype.ext <| by
    have h := d.toSO.symm_apply_apply ⟨X, d.lieH0_le_lie0 X.2⟩
    exact (congrArg Subtype.val h : _)
  right_inv Y := Subtype.ext (d.toSOLin_toSO_symm ⟨Y, Y.2.1⟩)

@[simp] theorem coe_toSOH (X : ↥d.lieH0) : (d.toSOH X : d.luoOf.Amb) = d.toSOLin X := rfl

/-- `ad : 𝔥⁰ ≃ 𝔥` is a homeomorphism (finite dimension). -/
def toSOHCLE : ↥d.lieH0 ≃L[F] ↥d.luoOf.lieH :=
  haveI := t2Space_of_moduleTopology F d.ambient
  haveI := isTopologicalRing_of_moduleTopology F d.ambient
  haveI := IsModuleTopology.toContinuousSMul F d.ambient
  haveI := t2Space_of_moduleTopology F d.luoOf.Amb
  haveI := isTopologicalRing_of_moduleTopology F d.luoOf.Amb
  haveI := IsModuleTopology.toContinuousSMul F d.luoOf.Amb
  d.toSOH.toContinuousLinearEquiv

@[simp] theorem coe_toSOHCLE (X : ↥d.lieH0) :
    ((d.toSOHCLE X : ↥d.luoOf.lieH) : d.luoOf.Amb) = d.toSOLin X := rfl

section Kernel

variable (ψ : NontrivialAddChar F)

/-- `extFn (f ∘ toSO⁻¹)` at `ad Z` is `f Z`. -/
theorem extFn_toSOLin (f : ↥d.lieZero → ℂ) (Z : ↥d.lieZero) :
    d.luoOf.extFn (f ∘ d.toSO.symm) (d.toSOLin Z) = f Z := by
  unfold LuoDatum.extFn
  rw [dite_eq_left_of_eq_true (eq_true (d.toSO_mem Z))]
  simp only [Function.comp_apply]
  congr 1
  exact d.toSO.symm_apply_eq.2 (Subtype.ext rfl)

/-- **The kernels of `J^Lie` agree at matched points**: with `μ_𝔥 = ad_* dX`,
`K^Lie_Luo(f ∘ ad⁻¹, P(g)) = K^Lie(f, g)` (change of variables `ad : 𝔥⁰ ≃ 𝔥`;
`ad(g⁻¹ X g) = P(g)⁻¹ ad(X) P(g)`, `toSOLin_adLie0_inv`; `λ ∘ ad = λ`, `lam_toSO`). -/
theorem kernelLie_toGbar (μ : Measure ↥d.lieH0) (f : ↥d.lieZero → ℂ) (g : ↥d.G) :
    d.luoOf.kernelLie ψ (μ.map d.toSOHCLE) (f ∘ d.toSO.symm) (d.toGbar g) =
      ∫ X : ↥d.lieH0, f (d.adLie0 g⁻¹ (d.lieH0Incl X)) * d.xiLie ψ (X : d.ambient) ∂μ := by
  unfold LuoDatum.kernelLie
  have hme : MeasurableEmbedding (d.toSOHCLE : ↥d.lieH0 → ↥d.luoOf.lieH) :=
    d.toSOHCLE.toHomeomorph.measurableEmbedding
  rw [hme.integral_map]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  have h1 := d.toSOLin_adLie0_inv g (d.lieH0Incl X)
  change d.luoOf.extFn (f ∘ d.toSO.symm) (d.luoOf.conjInv (d.toGbar g)
      (d.toSOLin (d.lieH0Incl X : d.ambient))) * ψ (d.luoOf.lam (d.toSOLin X)) =
    f (d.adLie0 g⁻¹ (d.lieH0Incl X)) * ψ (d.lamLie X)
  rw [← h1, d.extFn_toSOLin, ← d.lam_toSO]

/-- `G(F) → Ḡ(F)` is onto (`Pbar_surjective`). -/
theorem toGbar_surjective (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) :
    Function.Surjective d.toGbar := by
  obtain ⟨e, he⟩ := d.exists_continuousMulEquiv_toGbar hW hV
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  exact ⟨Quotient.out y, (congrFun he y).symm⟩

/-- The push-forward of `Measure.haar` along `H(F)/A_{G,H}(F) ≃ H̄(F)` is conjugation invariant
(`H(F)/A_{G,H}(F)` is unimodular, `isMulRightInvariant_haar_HmodAGH`). -/
theorem map_conj_map_haar (eH : d.HmodAGH ≃ₜ* ↥d.luoOf.Hbar) (u : ↥d.luoOf.Hbar) :
    ((Measure.haar : Measure d.HmodAGH).map eH).map (fun h => u⁻¹ * h * u) =
      (Measure.haar : Measure d.HmodAGH).map eH := by
  have := d.isMulRightInvariant_haar_HmodAGH
  exact Measure.map_conj_map_mulEquiv _ eH.toMulEquiv eH.continuous.measurable u

/-- **(L4) reduced to `exp`-compatibility**: `exists_JLie_transfer` holds as soon as the
push-forwards of `Measure.haar` on `H(F)/A_{G,H}(F)` and of `dX` on `𝔥⁰(F)` along
`H(F)/A_{G,H}(F) ≃ H̄(F)` and `ad : 𝔥⁰ ≃ 𝔥` are `exp`-compatible.  The measures are
`μ_H = (e_H)_* dh`, `μ_𝔥 = ad_* dX` and the push-forward of `weilMeasureHG`
(`exists_weil_Hbar`); the kernels agree at matched points (`kernelLie_toGbar`), and Luo's kernel
is left `H̄(F)`-invariant (`LuoDatum.kernelLie_mul_left`). -/
theorem exists_JLie_transfer_of (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    (hexp : ∀ eH : d.HmodAGH ≃ₜ* ↥d.luoOf.Hbar,
      (∀ h : ↥d.H, ((eH (QuotientGroup.mk h) : ↥d.luoOf.Gbar)) = d.toGbar (h : ↥d.G)) →
        d.luoOf.IsExpCompatH ((Measure.haar : Measure d.HmodAGH).map eH)
          (d.measH0.map d.toSOHCLE)) :
    ∃ (μH : Measure ↥d.luoOf.Hbar) (μ𝔥 : Measure ↥d.luoOf.lieH)
      (m : Measure (CosetSpace d.luoOf.Hbar.subtype)),
      μH.IsHaarMeasure ∧ d.luoOf.IsExpCompatH μH μ𝔥 ∧
      IsWeilMeasure d.luoOf.Hbar.subtype d.muG μH m ∧
      ∀ f : ↥d.lieZero → ℂ, d.IsLieScusp f →
        d.distribJLie ψ f = d.luoOf.distribJLie ψ μ𝔥 m (f ∘ d.toSO.symm) := by
  obtain ⟨eH, m, heH, hm, hint⟩ := d.exists_weil_Hbar hW hV
  have hE := hexp eH heH
  refine ⟨(Measure.haar : Measure d.HmodAGH).map eH, d.measH0.map d.toSOHCLE, m,
    eH.toMulEquiv.isHaarMeasure_map Measure.haar eH.continuous eH.symm.continuous,
    hE, hm, fun f _ => ?_⟩
  have hK : ∀ g, d.luoOf.kernelLie ψ (d.measH0.map d.toSOHCLE) (f ∘ d.toSO.symm) (d.toGbar g) =
      d.kernelLie ψ f g := fun g => d.kernelLie_toGbar ψ d.measH0 f g
  exact hint _ _ hK fun hb hhb x =>
    d.luoOf.kernelLie_mul_left ψ (d.map_conj_map_haar eH) hE _ hhb x

end Kernel

end GGPData

end GSpinGGP
