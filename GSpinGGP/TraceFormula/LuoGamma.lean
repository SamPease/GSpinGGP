/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LuoTransfer
import GSpinGGP.TraceFormula.Analytic
import GSpinGGP.GGP.TorusCount
import GSpinGGP.TraceFormula.SOLieFacts

/-!
# `Γ(G,H)` and Luo's `Γ^Lie(Ḡ, H̄)`: the torus of a point

For `x ∈ Γ(G,H)` (`GGPData.IsGammaElt`) we look for `X ∈ so(W)` with `X ∈ Γ^Lie(Ḡ, H̄)`
(`LuoDatum.IsGammaElt`, Luo §7.1) whose torus `H''_X` is the image of `T_x` under
`t ↦ (P(t), P(t) ⊕ 1)`.

* `specPU`, `toGbarU_comp_diag`: `t ↦ (P(t), P(t) ⊕ 1)` is `diagU ∘ P`.
* `torusQuotMap`: the induced continuous injective map `T(F)/A_{G,H}(F) → Ḡ(F)`, with range the
  image of `T(F)` (`range_torusQuotMap`, `torusQuotMap_injective`).
* `luo_isGammaElt_of_regular`: if `Z ∈ gspin(W)` commutes with `x`, `ker (ad Z) = W'_x`, and every
  endomorphism of `W` commuting with `ad Z` and fixing `W'_x` commutes with `P(x)`, then
  `X = ad Z ∈ Γ^Lie(Ḡ, H̄)` and `H''_X` is the image of `T_x` (`torusW_adV_eq_map`, through
  `S_x(F) ⊆ P(T_x(F))`, `GGPData.mem_torusOf_of_specP`; `isCompact_map_torusOf`).
* `exists_luo_isGammaElt_torusOf_eq`: every `x ∈ Γ(G,H)` gives such an `X`, since a regular `Z`
  exists (`GGPData.exists_regular_movedCent`, `GGP/TorusCount.lean`).
* `exists_isGammaElt_torusOf_eq_of_luo` (converse): every `X ∈ Γ^Lie(Ḡ, H̄)` comes from some
  `x ∈ Γ(G,H)` with the same torus: lift `X = ad Z`, take `x = e^{cZ}` with the commutant of `Z`
  (`exists_gspin_commute_iff_trace`), and check `x ∈ Γ(G,H)` (`isGammaElt_of_luo_of_commute_iff`:
  `P(T_x) = H''_X`; `T_x(F)` commutative via `movedPartAbelian_of_commute_iff`; compactness of
  `T_x(F)/A_{G,H}(F)` by the open mapping theorem, `compactSpace_torusQuot_of_isCompact`).
-/

noncomputable section

open CliffordAlgebra Module

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

/-- `P : GSpin(W) → GL(W)`, as units of `End W`. -/
def specPU : ↥(GSpin d.QW) →* (Module.End F d.luoOf.W)ˣ :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F d.luoOf.W).symm.toMonoidHom.comp
    (specP d.QW)

@[simp] theorem coe_specPU (g : ↥(GSpin d.QW)) :
    ((d.specPU g : (Module.End F d.luoOf.W)ˣ) : Module.End F d.luoOf.W) =
      (specP d.QW g : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) := rfl

/-- `P(g) ∈ SO(W)`. -/
theorem specPU_mem_SOu (g : ↥(GSpin d.QW)) : d.specPU g ∈ LuoDatum.SOu d.luoOf.QW := by
  change LinearMap.GeneralLinearGroup.generalLinearEquiv F _
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv F _).symm (specP d.QW g)) ∈ SOGrp d.QW
  rw [MulEquiv.apply_symm_apply, ← range_specP_eq_SOGrp d.nondeg]
  exact ⟨g, rfl⟩

/-- Every element of `SO(W)` is some `P(t)` (`range_specP_eq_SOGrp`). -/
theorem exists_specP_eq_of_mem_SOu {s : (Module.End F d.luoOf.W)ˣ}
    (hs : s ∈ LuoDatum.SOu d.luoOf.QW) :
    ∃ t : ↥(GSpin d.QW), (specP d.QW t : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) = s.val := by
  change LinearMap.GeneralLinearGroup.generalLinearEquiv F _ s ∈ SOGrp d.QW at hs
  rw [← range_specP_eq_SOGrp d.nondeg] at hs
  obtain ⟨t, ht⟩ := hs
  exact ⟨t, by rw [ht]; rfl⟩

/-- `t ↦ (P(t), P(t) ⊕ 1)` is `diagU ∘ P`. -/
theorem toGbarU_comp_diag : d.toGbarU.comp d.diag = d.luoOf.diagU.comp d.specPU := by
  ext t : 2
  refine Prod.ext rfl ?_
  show (specP d.QV (d.incl t) : d.V →ₗ[F] d.V) = _
  rw [d.specP_incl_eq_prodMap]
  rfl

/-- `t ↦ (P(t), P(t) ⊕ 1)` is continuous on `GSpin(W)(F)`. -/
theorem continuous_toGbarU_comp_diag : Continuous (d.toGbarU.comp d.diag) := by
  have hdiag : Continuous d.diag :=
    d.continuous_pair.comp (continuous_id.prodMk d.continuous_incl)
  exact continuous_subtype_val.comp (d.continuous_toGbar.comp hdiag)

/-- The kernel of `t ↦ (P(t), P(t) ⊕ 1)` is that of `P`, i.e. the scalars `F^×`
(`ker_specP`). -/
theorem toGbarU_comp_diag_eq_one_iff (t : ↥(GSpin d.QW)) :
    d.toGbarU.comp d.diag t = 1 ↔ specP d.QW t = 1 := by
  rw [toGbarU_comp_diag, MonoidHom.comp_apply]
  constructor
  · intro h
    have h' := congrArg d.luoOf.unitFst h
    rw [LuoDatum.unitFst_diagU, map_one] at h'
    have h'' := congrArg Units.val h'
    rw [coe_specPU] at h''
    exact LinearEquiv.toLinearMap_injective h''
  · intro h
    have h2 : d.specPU t = 1 := by
      change (LinearMap.GeneralLinearGroup.generalLinearEquiv F d.luoOf.W).symm
        (specP d.QW t) = 1
      rw [h]
      exact map_one _
    rw [h2, map_one]

/-- The scalars `A_{G,H}(F)` of `T(F)` lie in the kernel of `t ↦ (P(t), P(t) ⊕ 1)`. -/
theorem scalarsIn_le_ker_toGbarU_comp_diag (T : Subgroup ↥(GSpin d.QW)) :
    d.scalarsIn T ≤ ((d.toGbarU.comp d.diag).comp T.subtype).ker := by
  intro n hn
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hn
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
    toGbarU_comp_diag_eq_one_iff, ← hc, ← MonoidHom.mem_ker, ker_specP d.nondeg]
  exact ⟨c, rfl⟩

/-- `T(F)/A_{G,H}(F) → Ḡ(F)`, induced by `t ↦ (P(t), P(t) ⊕ 1)`. -/
def torusQuotMap (T : Subgroup ↥(GSpin d.QW)) : d.TorusQuot T →* d.luoOf.Ambˣ :=
  QuotientGroup.lift (d.scalarsIn T) ((d.toGbarU.comp d.diag).comp T.subtype)
    (d.scalarsIn_le_ker_toGbarU_comp_diag T)

theorem continuous_torusQuotMap (T : Subgroup ↥(GSpin d.QW)) : Continuous (d.torusQuotMap T) :=
  (QuotientGroup.isQuotientMap_mk (d.scalarsIn T)).continuous_iff.mpr
    (d.continuous_toGbarU_comp_diag.comp continuous_subtype_val)

/-- The range of `torusQuotMap` is the image of `T(F)`. -/
theorem range_torusQuotMap (T : Subgroup ↥(GSpin d.QW)) :
    (d.torusQuotMap T).range = T.map (d.toGbarU.comp d.diag) := by
  ext a
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨t, t.2, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨QuotientGroup.mk ⟨t, ht⟩, rfl⟩

/-- `torusQuotMap` is injective: the kernel of `t ↦ (P(t), P(t) ⊕ 1)` is `F^×`. -/
theorem torusQuotMap_injective (T : Subgroup ↥(GSpin d.QW)) :
    Function.Injective (d.torusQuotMap T) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  induction y using QuotientGroup.induction_on with | H t => ?_
  have h1 : d.toGbarU.comp d.diag (t : ↥(GSpin d.QW)) = 1 := hy
  rw [toGbarU_comp_diag_eq_one_iff, ← MonoidHom.mem_ker, ker_specP d.nondeg] at h1
  obtain ⟨c, hc⟩ := h1
  rw [QuotientGroup.eq_one_iff]
  exact Subgroup.mem_subgroupOf.mpr ⟨c, hc⟩

section Regular

variable {x : ↥(GSpin d.QW)} {Z : CliffordAlgebra d.QW}

/-- For `x ∈ Γ(G,H)` and `Z` in the moved part of its Lie centralizer, every `t ∈ T_x(F)` commutes
with `Z`: `Z` has the commutant of some `g_Z ∈ T_x(F)` (`exists_gspin_commute_iff`), and `T_x(F)` is
commutative. -/
theorem commute_of_mem_torusOf_of_moved (hx : d.IsGammaElt x) (hZ : Z ∈ gspin d.QW)
    (hZx : ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * Z =
      Z * ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
    (hZf : ∀ w ∈ fixedSub x, adV d.QW Z w = 0) {t : ↥(GSpin d.QW)} (ht : t ∈ d.torusOf x) :
    Commute ((t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) Z := by
  obtain ⟨g, hg⟩ := exists_gspin_commute_iff d.QW hZ
  have hgT : g ∈ d.torusOf x := by
    refine mem_torusOf_of_commute d ((hg _).mpr hZx) fun w hw => (hg _).mpr ?_
    have h := ι_adV hZ w
    rw [hZf w hw, map_zero, eq_comm, sub_eq_zero] at h
    exact h.symm
  exact (hg _).mp (congrArg (fun k : ↥(GSpin d.QW) =>
    ((k : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) (hx.2.1 t ht g hgT).eq)

/-- **`H''_X = P(T_x)` for a regular `X = ad Z`**: let `x ∈ Γ(G,H)` and `Z ∈ gspin(W)` commute with
`x`, with `ker (ad Z) = W'_x`, and such that every endomorphism of `W` commuting with `ad Z` and
fixing `W'_x` commutes with `P(x)`.  Then Luo's `H''_{ad Z} = SO(W)_{ad Z} ∩ Fix(ker ad Z)` is
`P(T_x(F))` (`mem_torusOf_of_specP`, `commute_of_mem_torusOf_of_moved`). -/
theorem torusW_adV_eq_map (hx : d.IsGammaElt x) (hZ : Z ∈ gspin d.QW)
    (hZx : ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * Z =
      Z * ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
    (hker : LinearMap.ker (adV d.QW Z) = fixedSub x)
    (hreg : ∀ s : Module.End F (Fin d.m → F), Commute s (adV d.QW Z) →
      (∀ w ∈ fixedSub x, s w = w) →
        Commute s (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F))) :
    d.luoOf.torusW (adV d.QW Z) = (d.torusOf x).map d.specPU := by
  have hZf : ∀ w ∈ fixedSub x, adV d.QW Z w = 0 := fun w hw => by
    rw [← hker] at hw; exact hw
  ext s
  constructor
  · rintro ⟨hSO, hcomm, hfix⟩
    obtain ⟨t, hs⟩ := d.exists_specP_eq_of_mem_SOu hSO
    have hfix' : ∀ w ∈ fixedSub x, s.val w = w := fun w hw =>
      hfix w (by rw [← hker] at hw; exact hw)
    have hc := hreg s.val hcomm hfix'
    have hcE : Commute (specP d.QW t) (specP d.QW x) := by
      refine LinearEquiv.toLinearMap_injective ?_
      rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul, hs]
      exact hc.eq
    refine ⟨t, d.mem_torusOf_of_specP hx.1 hcE fun v hv => ?_, Units.ext ?_⟩
    · rw [← LinearEquiv.coe_coe, hs]; exact hfix' v hv
    · rw [coe_specPU, hs]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨?_, ?_, fun w hw => ?_⟩
    · exact d.specPU_mem_SOu t
    · rw [coe_specPU]
      exact (commute_iff_adV d.nondeg t hZ).mp
        (d.commute_of_mem_torusOf_of_moved hx hZ hZx hZf ht).eq
    · rw [coe_specPU]
      exact ht.2 w (by rw [← hker]; exact hw)

/-- The image of `T_x(F)` under `t ↦ (P(t), P(t) ⊕ 1)` is compact for `x ∈ Γ(G,H)`: it is the
range of the continuous `torusQuotMap` on the compact `T_x(F)/A_{G,H}(F)`. -/
theorem isCompact_map_torusOf (hx : d.IsGammaElt x) :
    IsCompact ((d.torusOf x).map (d.toGbarU.comp d.diag) : Set d.luoOf.Ambˣ) := by
  have := hx.2.2
  rw [← d.range_torusQuotMap, MonoidHom.coe_range]
  exact isCompact_range (d.continuous_torusQuotMap _)

/-- **A regular `ad Z` gives a point of Luo's `Γ^Lie(Ḡ, H̄)` with the torus of `x`**: under the
hypotheses of `torusW_adV_eq_map`, `X = ad Z` is skew, semisimple, `H''_X` is commutative with
compact `F`-points, and `H''_X` (embedded diagonally) is the image of `T_x(F)` under
`t ↦ (P(t), P(t) ⊕ 1)`. -/
theorem luo_isGammaElt_of_regular (hx : d.IsGammaElt x) (hZ : Z ∈ gspin d.QW)
    (hZx : ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * Z =
      Z * ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
    (hker : LinearMap.ker (adV d.QW Z) = fixedSub x)
    (hreg : ∀ s : Module.End F (Fin d.m → F), Commute s (adV d.QW Z) →
      (∀ w ∈ fixedSub x, s w = w) →
        Commute s (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F))) :
    d.luoOf.IsGammaElt (adV d.QW Z) ∧
      d.luoOf.torusOf (adV d.QW Z) = (d.torusOf x).map (d.toGbarU.comp d.diag) := by
  have hT : d.luoOf.torusOf (adV d.QW Z) = (d.torusOf x).map (d.toGbarU.comp d.diag) := by
    change (d.luoOf.torusW (adV d.QW Z)).map d.luoOf.diagU = _
    rw [d.torusW_adV_eq_map hx hZ hZx hker hreg, Subgroup.map_map, toGbarU_comp_diag]
  have hZf : ∀ w ∈ fixedSub x, adV d.QW Z w = 0 := fun w hw => by
    rw [← hker] at hw; exact hw
  refine ⟨⟨adV_mem_skewAdjoint hZ, ?_, ?_, ?_⟩, hT⟩
  · have hs := isSemisimple_adV hZ (d.isSS_of_commute_of_isGammaElt hx hZ hZx hZf)
    exact isSS_of_isSemisimple hs
  · rw [hT]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (hx.2.1 a ha b hb).map _
  · rw [hT]
    exact isCompact_iff_compactSpace.mp (d.isCompact_map_torusOf hx)

/-- **Every `x ∈ Γ(G,H)` gives a point of Luo's `Γ^Lie(Ḡ, H̄)` with the same torus**: there is
`X ∈ so(W)` with `X ∈ Γ^Lie(Ḡ, H̄)` (Luo §7.1) whose torus `H''_X`, embedded diagonally in `Ḡ`, is the image of `T_x(F)` under
`t ↦ (P(t), P(t) ⊕ 1)` (`exists_regular_movedCent`, `luo_isGammaElt_of_regular`). -/
theorem exists_luo_isGammaElt_torusOf_eq {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) :
    ∃ X : Module.End F d.luoOf.W, d.luoOf.IsGammaElt X ∧
      d.luoOf.torusOf X = (d.torusOf x).map (d.toGbarU.comp d.diag) := by
  obtain ⟨Z, hZ, hZx, hker, hreg⟩ := d.exists_regular_movedCent hx
  exact ⟨_, d.luo_isGammaElt_of_regular hx hZ hZx hker fun s hs _ => hreg s hs⟩

end Regular

/-! ### The converse: from `Γ^Lie(Ḡ, H̄)` to `Γ(G,H)` -/

section Converse

variable {x : ↥(GSpin d.QW)} {Z : CliffordAlgebra d.QW}

/-- If `x` has the commutant of `Z ∈ gspin(W)` in `C(W)`, then `W'_x = ker (ad Z)`. -/
theorem fixedSub_eq_ker_of_commute_iff (hZ : Z ∈ gspin d.QW)
    (hxZ : ∀ Y : CliffordAlgebra d.QW,
      Commute Y ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) ↔ Commute Y Z) :
    fixedSub x = LinearMap.ker (adV d.QW Z) := by
  ext v
  rw [mem_fixedSub_iff_commute_ι, LinearMap.mem_ker, ← (ι_injective d.QW).eq_iff, map_zero,
    ι_adV hZ, sub_eq_zero]
  constructor
  · intro h; exact ((hxZ _).mp h.symm).eq.symm
  · intro h; exact ((hxZ _).mpr (Commute.symm h)).eq.symm

/-- **`H''_{ad Z} = P(T_x)`** when `x` has the commutant of `Z ∈ gspin(W)` in `C(W)`: an element of
`GSpin(W)` commutes with `Z` iff `P(g)` commutes with `ad Z` (`commute_iff_adV`), and
`W'_x = ker (ad Z)` (`fixedSub_eq_ker_of_commute_iff`). -/
theorem torusW_adV_eq_map_of_commute_iff (hZ : Z ∈ gspin d.QW)
    (hxZ : ∀ Y : CliffordAlgebra d.QW,
      Commute Y ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) ↔ Commute Y Z) :
    d.luoOf.torusW (adV d.QW Z) = (d.torusOf x).map d.specPU := by
  have hker := d.fixedSub_eq_ker_of_commute_iff hZ hxZ
  ext s
  constructor
  · rintro ⟨hSO, hcomm, hfix⟩
    obtain ⟨t, hs⟩ := d.exists_specP_eq_of_mem_SOu hSO
    have htZ : ((t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * Z =
        Z * ((t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) :=
      (commute_iff_adV d.nondeg t hZ).mpr (by rw [hs]; exact hcomm)
    refine ⟨t, ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, fun v hv => ?_⟩, Units.ext ?_⟩
    · have h := ((hxZ _).mpr htZ).eq
      exact Subtype.ext (Units.ext h)
    · rw [← LinearEquiv.coe_coe, hs]; exact hfix v (by rwa [hker] at hv)
    · rw [coe_specPU, hs]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨?_, ?_, fun w hw => ?_⟩
    · exact d.specPU_mem_SOu t
    · rw [coe_specPU]
      have htx : Commute ((t : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)
          ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) :=
        congrArg (fun k : ↥(GSpin d.QW) => ((k : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
          (Subgroup.mem_centralizer_singleton_iff.mp ht.1)
      exact (commute_iff_adV d.nondeg t hZ).mp ((hxZ _).mp htx).eq
    · rw [coe_specPU]
      exact ht.2 w (by rw [hker]; exact hw)

/-- **The moved Lie centralizer of `x` is abelian** when `x` has the commutant of `Z ∈ gspin(W)` and
`H''_{ad Z}(F)` is commutative.  For `Y₁, Y₂` in the moved part, `gᵢ = e^{cᵢYᵢ} ∈ T_x(F)` have the
commutants of `Yᵢ` and `tr L_{gᵢ} ≠ 0` (`exists_mem_torusOf_commute_iff`); `P(g₁), P(g₂)` lie in
`H''_{ad Z}(F)` (`torusW_adV_eq_map_of_commute_iff`), so commute, hence so do `g₁, g₂`
(`commute_of_commute_specP_of_trace_ne_zero`: the scalar `g₁g₂g₁⁻¹g₂⁻¹` is `1` by the trace), and
then `Y₁, Y₂`. -/
theorem movedPartAbelian_of_commute_iff (hZ : Z ∈ gspin d.QW)
    (hxZ : ∀ Y : CliffordAlgebra d.QW,
      Commute Y ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) ↔ Commute Y Z)
    (hT : ∀ a ∈ d.luoOf.torusOf (adV d.QW Z), ∀ b ∈ d.luoOf.torusOf (adV d.QW Z), Commute a b) :
    MovedPartAbelian d.QW x := by
  intro Y₁ hY₁ Y₂ hY₂ hf₁ hf₂
  rw [mem_lieCentralizer] at hY₁ hY₂
  obtain ⟨g₁, hg₁T, hg₁, -⟩ := exists_mem_torusOf_commute_iff d hY₁.1 hY₁.2 hf₁
  obtain ⟨g₂, hg₂T, hg₂, htr₂⟩ := exists_mem_torusOf_commute_iff d hY₂.1 hY₂.2 hf₂
  have hS : ∀ g ∈ d.torusOf x, d.luoOf.diagU (d.specPU g) ∈ d.luoOf.torusOf (adV d.QW Z) :=
    fun g hg => Subgroup.mem_map_of_mem _ (by
      rw [d.torusW_adV_eq_map_of_commute_iff hZ hxZ]; exact Subgroup.mem_map_of_mem _ hg)
  have hc := (hT _ (hS g₁ hg₁T) _ (hS g₂ hg₂T)).map d.luoOf.unitFst
  rw [LuoDatum.unitFst_diagU, LuoDatum.unitFst_diagU] at hc
  have hcP : Commute (specP d.QW g₁) (specP d.QW g₂) := by
    refine LinearEquiv.toLinearMap_injective ?_
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul]
    exact congrArg Units.val hc.eq
  have h12 := commute_of_commute_specP_of_trace_ne_zero d.nondeg htr₂ hcP
  have h1 : Commute ((g₁ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)
      ((g₂ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) :=
    congrArg (fun k : ↥(GSpin d.QW) => ((k : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
      h12.eq
  have h3 : Commute Y₂ Y₁ := (hg₁ _).mp ((hg₂ _).mp h1).symm
  rw [Ring.lie_def, sub_eq_zero]
  exact h3.eq.symm

/-- **`T_x(F)/A_{G,H}(F)` is compact if its image is**: `T_x(F)/A_{G,H}(F) → Ḡ(F)`,
`t ↦ (P(t), P(t) ⊕ 1)`, is a continuous injective homomorphism (`ker P = F^×`); onto a compact
image it is open (open mapping theorem, `T_x(F)` being σ-compact), hence a homeomorphism. -/
theorem compactSpace_torusQuot_of_isCompact (x : ↥(GSpin d.QW))
    (hc : IsCompact ((d.torusOf x).map (d.toGbarU.comp d.diag) : Set d.luoOf.Ambˣ)) :
    CompactSpace (d.TorusQuot (d.torusOf x)) := by
  set T := d.torusOf x
  set S := T.map (d.toGbarU.comp d.diag)
  have : CompactSpace ↥S := isCompact_iff_compactSpace.mp hc
  have : T2Space ↥S := subgroup_t2Space F d.luoOf.Amb S
  have : SigmaCompactSpace ↥T := sigmaCompactSpace_torusOf x
  have : SigmaCompactSpace (d.TorusQuot T) :=
    isSigmaCompact_univ_iff.mp (by
      rw [← Set.range_eq_univ.mpr (QuotientGroup.mk_surjective (s := d.scalarsIn T))]
      exact isSigmaCompact_range QuotientGroup.continuous_mk)
  have hR : (d.torusQuotMap T).range = S := d.range_torusQuotMap T
  have hS : ∀ y, d.torusQuotMap T y ∈ S := fun y => by
    rw [← hR]; exact ⟨y, rfl⟩
  let q : d.TorusQuot T →* ↥S := (d.torusQuotMap T).codRestrict S hS
  have hq : Continuous q := continuous_induced_rng.mpr (d.continuous_torusQuotMap T)
  have hsurj : Function.Surjective q := by
    rintro ⟨a, ha⟩
    rw [← hR] at ha
    obtain ⟨y, rfl⟩ := ha
    exact ⟨y, rfl⟩
  have hinj : Function.Injective q := fun y z h =>
    d.torusQuotMap_injective T (congrArg Subtype.val h)
  have hopen : IsOpenMap q := q.isOpenMap_of_sigmaCompact hsurj hq
  let h : d.TorusQuot T ≃ₜ ↥S :=
    (Equiv.ofBijective q ⟨hinj, hsurj⟩).toHomeomorphOfContinuousOpen hq hopen
  exact h.symm.compactSpace

/-- **From Luo's `Γ^Lie(Ḡ, H̄)` to `Γ(G,H)`, for a given lift**: let `Z ∈ gspin(W)` with
`X = ad Z ∈ Γ^Lie(Ḡ, H̄)`, and let `x ∈ GSpin(W)(F)` be semisimple with the commutant of `Z` in
`C(W)`.  Then `x ∈ Γ(G,H)` and `H''_X` (embedded diagonally) is the image of `T_x(F)` under
`t ↦ (P(t), P(t) ⊕ 1)`: `P(T_x(F)) = H''_X(F)` (`torusW_adV_eq_map_of_commute_iff`); `T_x(F)` is
commutative since it is central in the centralizer of `x`
(`commute_torusOf_of_commute_of_movedPartAbelian`, `movedPartAbelian_of_commute_iff`); and
`T_x(F)/A_{G,H}(F)` is compact since its image `H''_X(F)` is
(`compactSpace_torusQuot_of_isCompact`). -/
theorem isGammaElt_of_luo_of_commute_iff (hZ : Z ∈ gspin d.QW)
    (hX : d.luoOf.IsGammaElt (adV d.QW Z))
    (hxZ : ∀ Y : CliffordAlgebra d.QW,
      Commute Y ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) ↔ Commute Y Z)
    (hss : IsSS F (((x : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW)) :
    d.IsGammaElt x ∧
      d.luoOf.torusOf (adV d.QW Z) = (d.torusOf x).map (d.toGbarU.comp d.diag) := by
  have hT : d.luoOf.torusOf (adV d.QW Z) = (d.torusOf x).map (d.toGbarU.comp d.diag) := by
    change (d.luoOf.torusW (adV d.QW Z)).map d.luoOf.diagU = _
    rw [d.torusW_adV_eq_map_of_commute_iff hZ hxZ, Subgroup.map_map, toGbarU_comp_diag]
  have hA := d.movedPartAbelian_of_commute_iff hZ hxZ hX.2.2.1
  refine ⟨⟨hss, fun a ha b hb => ?_, ?_⟩, hT⟩
  · exact (commute_torusOf_of_commute_of_movedPartAbelian hss hA
      (Subgroup.mem_centralizer_singleton_iff.mp hb.1) ha).symm
  · refine d.compactSpace_torusQuot_of_isCompact x ?_
    rw [← hT]
    exact isCompact_iff_compactSpace.mpr hX.2.2.2

/-- **Every point of Luo's `Γ^Lie(Ḡ, H̄)` comes from `Γ(G,H)` with the same torus** (converse of
`exists_luo_isGammaElt_torusOf_eq`): for `X ∈ Γ^Lie(Ḡ, H̄)` (Luo §7.1) there is `x ∈ Γ(G,H)`
whose torus `T_x(F)` maps onto `H''_X` (embedded diagonally in `Ḡ`) under
`t ↦ (P(t), P(t) ⊕ 1)`.  Take `Z ∈ gspin(W)` with `ad Z = X` (`exists_lift_skew`; `Z` is
semisimple since `X` is) and `x = e^{cZ}` for small `c ≠ 0` (`exists_gspin_commute_iff_trace`),
then apply `isGammaElt_of_luo_of_commute_iff`. -/
theorem exists_isGammaElt_torusOf_eq_of_luo {X : Module.End F d.luoOf.W}
    (hX : d.luoOf.IsGammaElt X) :
    ∃ x : ↥(GSpin d.QW), d.IsGammaElt x ∧
      d.luoOf.torusOf X = (d.torusOf x).map (d.toGbarU.comp d.diag) := by
  have hskew : ∀ u v, bform d.QW (X u) v = - bform d.QW u (X v) := by
    intro u v
    have h := (LinearMap.mem_skewAdjointSubmodule _).mp hX.1 u v
    exact h.trans (map_neg ((bform d.QW) u) (X v))
  obtain ⟨Z, hZ, hZX⟩ := exists_lift_skew d.nondeg X hskew
  have hadV : adV d.QW Z = X :=
    LinearMap.ext fun v => ι_injective d.QW (by rw [ι_adV hZ, hZX])
  subst hadV
  have hZss : IsSS F Z :=
    isSemisimple_mulLeft_of_isSemisimple_adV_baseChange d.nondeg hZ
      (isSemisimple_baseChange (isSS_iff_isSemisimple.mp hX.2.1))
  obtain ⟨x, hxZ, -, hxss⟩ := exists_gspin_commute_iff_trace d.QW hZ
  exact ⟨x, d.isGammaElt_of_luo_of_commute_iff hZ hX hxZ (hxss hZss)⟩

end Converse

end GGPData

end GSpinGGP
