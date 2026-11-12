/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LuoTransfer
import GSpinGGP.TraceFormula.Analytic
import GSpinGGP.GGP.TorusFrame
import GSpinGGP.GGP.TorusCount
import GSpinGGP.GGP.GSpinSemisimple
import GSpinGGP.Foundations.FrameDiag

/-!
# From `Γ(G,H)` to Luo's `Γ^Lie(Ḡ, H̄)`: the torus of a point

For `x ∈ Γ(G,H)` (`GGPData.IsGammaElt`) we look for `X ∈ so(W)` with `X ∈ Γ^Lie(Ḡ, H̄)`
(`LuoDatum.IsGammaElt`, Luo §7.1) whose torus `H''_X` is the image of `T_x` under
`t ↦ (P(t), P(t) ⊕ 1)`.

* `commute_of_commute_specP_of_fixes`: if `P(g)` commutes with `P(x)` (`x` semisimple) and is
  the identity on `W'_x = ker (P(x) − 1)`, then `g` commutes with `x`.  By Steinberg's description
  of centralizers (`steinberg_centralizer_connected`) the only condition left is
  `det P(g)|_{W₋₁} = 1`, which follows from `det P(g) = 1` and
  `det P(g) = det P(g)|_{W'_x} · det P(g)|_{W₋₁}` (`det_eq_det_one_mul_det_neg_one_of_charZero`).
* `mem_torusOf_of_specP`: hence `P(T_x(F)) = S_x(F)`, the elements of `SO(W)(F)` commuting with
  `P(x)` and fixing `W'_x` pointwise.
* `luo_isGammaElt_of_regular`: if `Z ∈ gspin(W)` commutes with `x`, `ker (ad Z) = W'_x`, and every
  endomorphism of `W` commuting with `ad Z` and fixing `W'_x` commutes with `P(x)`, then
  `X = ad Z ∈ Γ^Lie(Ḡ, H̄)` and `H''_X` is the image of `T_x`.
-/

noncomputable section

open CliffordAlgebra Module

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

section Steinberg

variable {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

/-- **An element whose image commutes with `P(x)` and fixes `W'_x` commutes with `x`**, for `x`
semisimple: in Steinberg's description (`steinberg_centralizer_connected`) the determinant on
`W'_x` is `1` since `P(g)` is the identity there, and so the determinant on `W₋₁` is `1` since
`det P(g) = 1` is the product of the two (`det_eq_det_one_mul_det_neg_one_of_charZero`). -/
theorem commute_of_commute_specP_of_fixes (hQ : IsNondeg Q) (x : GSpin Q)
    (hx : Module.End.IsSemisimple
      (LinearMap.mulLeft K ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))
    {g : GSpin Q} (hc : Commute (specP Q g) (specP Q x))
    (hfix : ∀ v ∈ fixedSub x, specP Q g v = v) : Commute g x := by
  have hss := Steinberg.isSemisimple_specP_of_isSS Q x hx
  have hB : (bform Q).IsSymm := ⟨fun u v => bform_comm Q u v⟩
  have hdet := IsomCent.det_eq_det_one_mul_det_neg_one_of_charZero hB hQ
    (Steinberg.isIsom_specP x) hss (Steinberg.isIsom_specP g) (Steinberg.commute_toLinearMap hc)
  have hone : ∀ (E : Submodule K V) (hE : ∀ v ∈ E, specP Q g v = v)
      (h : Set.MapsTo (specP Q g : V →ₗ[K] V) E E),
      LinearMap.det ((specP Q g : V →ₗ[K] V).restrict h) = 1 := by
    intro E hE h
    have : (specP Q g : V →ₗ[K] V).restrict h = LinearMap.id :=
      LinearMap.ext fun v => Subtype.ext (hE v v.2)
    rw [this, LinearMap.det_id]
  have hE1 : ∀ v ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) 1, specP Q g v = v :=
    fun v hv => hfix v (by rw [Steinberg.fixedSub_eq_eigenspace]; exact hv)
  rw [hone _ hE1, one_mul, det_specP] at hdet
  have h := (Steinberg.commute_iff hQ x hx g).mpr ⟨hc,
    ⟨mapsTo_fixedSub_of_commute hc, hone _ hfix _⟩,
    ⟨mapsTo_negFixedSub_of_commute hc,
      (Steinberg.det_restrict_eq rfl (Steinberg.negFixedSub_eq_eigenspace x) _ _).trans
        hdet.symm⟩⟩
  exact Subtype.ext h

end Steinberg

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

/-- **`P(T_x(F)) = S_x(F)`**: for semisimple `x`, an element `g ∈ GSpin(W)(F)` with `P(g)`
commuting with `P(x)` and fixing `W'_x` pointwise lies in `T_x(F)`
(`commute_of_commute_specP_of_fixes`). -/
theorem mem_torusOf_of_specP {x : ↥(GSpin d.QW)}
    (hx : IsSS F (((x : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW)) {g : ↥(GSpin d.QW)}
    (hc : Commute (specP d.QW g) (specP d.QW x)) (hfix : ∀ v ∈ fixedSub x, specP d.QW g v = v) :
    g ∈ d.torusOf x :=
  ⟨Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_of_commute_specP_of_fixes d.nondeg x hx hc hfix).eq.symm, hfix⟩

/-- `P : GSpin(W) → GL(W)`, as units of `End W`. -/
def specPU : ↥(GSpin d.QW) →* (Module.End F (Fin d.m → F))ˣ :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin d.m → F)).symm.toMonoidHom.comp
    (specP d.QW)

@[simp] theorem coe_specPU (g : ↥(GSpin d.QW)) :
    ((d.specPU g : (Module.End F (Fin d.m → F))ˣ) : Module.End F (Fin d.m → F)) =
      (specP d.QW g : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) := rfl

/-- `t ↦ (P(t), P(t) ⊕ 1)` is `diagU ∘ P`. -/
theorem toGbarU_comp_diag : d.toGbarU.comp d.diag = d.luoOf.diagU.comp d.specPU := by
  ext t : 2
  refine Prod.ext rfl ?_
  show (specP d.QV (d.incl t) : d.V →ₗ[F] d.V) = _
  rw [d.specP_incl_eq_prodMap]
  rfl

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
    change LinearMap.GeneralLinearGroup.generalLinearEquiv F _ s ∈ SOGrp d.QW at hSO
    rw [← range_specP_eq_SOGrp d.nondeg] at hSO
    obtain ⟨t, ht⟩ := hSO
    have hs : (specP d.QW t : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) = (s : Module.End F _) := by
      rw [ht]; rfl
    have hfix' : ∀ w ∈ fixedSub x, (s : Module.End F (Fin d.m → F)) w = w := fun w hw =>
      hfix w (by rw [hker]; exact hw)
    have hc := hreg s hcomm hfix'
    have hcE : Commute (specP d.QW t) (specP d.QW x) := by
      refine LinearEquiv.toLinearMap_injective ?_
      rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul, hs]
      exact hc.eq
    refine ⟨t, d.mem_torusOf_of_specP hx.1 hcE fun v hv => ?_, Units.ext ?_⟩
    · rw [← LinearEquiv.coe_coe, hs]; exact hfix' v hv
    · rw [coe_specPU, hs]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨?_, ?_, fun w hw => ?_⟩
    · change LinearMap.GeneralLinearGroup.generalLinearEquiv F _
        ((LinearMap.GeneralLinearGroup.generalLinearEquiv F _).symm (specP d.QW t)) ∈ SOGrp d.QW
      rw [MulEquiv.apply_symm_apply, ← range_specP_eq_SOGrp d.nondeg]
      exact ⟨t, rfl⟩
    · rw [coe_specPU]
      exact (commute_iff_adV d.nondeg t hZ).mp
        (d.commute_of_mem_torusOf_of_moved hx hZ hZx hZf ht).eq
    · rw [coe_specPU]
      exact ht.2 w (by rw [← hker]; exact hw)

/-- The image of `T_x(F)` under `t ↦ (P(t), P(t) ⊕ 1)` is compact for `x ∈ Γ(G,H)`: the map is
continuous and factors through the compact `T_x(F)/A_{G,H}(F)` (scalars lie in the kernel of
`P`). -/
theorem isCompact_map_torusOf (hx : d.IsGammaElt x) :
    IsCompact ((d.torusOf x).map (d.toGbarU.comp d.diag) : Set d.luoOf.Ambˣ) := by
  haveI := hx.2.2
  set T := d.torusOf x
  set ψ := d.toGbarU.comp d.diag
  have hψ : Continuous ψ := by
    have hdiag : Continuous d.diag :=
      d.continuous_pair.comp (continuous_id.prodMk d.continuous_incl)
    exact continuous_subtype_val.comp (d.continuous_toGbar.comp hdiag)
  have hker : d.scalarsIn T ≤ (ψ.comp T.subtype).ker := by
    intro n hn
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hn
    have h1 : specP d.QW (scalarGSpin d.QW c) = 1 := by
      rw [← MonoidHom.mem_ker, ker_specP d.nondeg]; exact ⟨c, rfl⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, ← hc,
      toGbarU_comp_diag, MonoidHom.comp_apply]
    have h2 : d.specPU (scalarGSpin d.QW c) = 1 := by
      simp only [specPU, MonoidHom.comp_apply, h1, map_one]
    rw [h2, map_one]
  let q := QuotientGroup.lift (d.scalarsIn T) (ψ.comp T.subtype) hker
  have hq : Continuous q :=
    (QuotientGroup.isQuotientMap_mk (d.scalarsIn T)).continuous_iff.mpr
      (hψ.comp continuous_subtype_val)
  have hrange : ((T.map ψ : Subgroup d.luoOf.Ambˣ) : Set d.luoOf.Ambˣ) = Set.range q := by
    ext a
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨QuotientGroup.mk ⟨t, ht⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨t, t.2, rfl⟩
  rw [hrange]
  exact isCompact_range hq

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
    rw [LuoDatum.torusOf, d.torusW_adV_eq_map hx hZ hZx hker hreg, Subgroup.map_map,
      toGbarU_comp_diag]
  have hZf : ∀ w ∈ fixedSub x, adV d.QW Z w = 0 := fun w hw => by
    rw [← hker] at hw; exact hw
  refine ⟨⟨adV_mem_skewAdjoint hZ, ?_, ?_, ?_⟩, hT⟩
  · have hs := isSemisimple_adV hZ (d.isSS_of_commute_of_isGammaElt hx hZ hZx hZf)
    exact isSS_of_aeval_eq_zero hs.minpoly_squarefree (minpoly.aeval F _)
  · rw [hT]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (hx.2.1 a ha b hb).map _
  · rw [hT]
    exact isCompact_iff_compactSpace.mp (d.isCompact_map_torusOf hx)

end Regular

/-! ### A regular element of the moved Lie centralizer -/

section Exists

open scoped TensorProduct

local notation "Kb" => AlgebraicClosure F

set_option hygiene false in
local notation "Wb" => AlgebraicClosure F ⊗[F] (Fin d.m → F)

set_option hygiene false in
local notation "Qb" => d.QW.baseChange (AlgebraicClosure F)

/-- `ad` commutes with base change: `ad (1 ⊗ Z) = (ad Z)_{F̄}` for `Z ∈ gspin(W)`. -/
theorem adV_gspinBC_tmul {Z : (gspin d.QW).toSubmodule} :
    adV Qb (gspinBC d.QW (1 ⊗ₜ Z)) = (adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb := by
  refine TensorProduct.AlgebraTensorModule.ext fun z v => ?_
  rw [LinearMap.baseChange_tmul, ← mul_one z, ← smul_eq_mul, ← TensorProduct.smul_tmul',
    map_smul, map_smul]
  congr 1
  rw [adV_apply, gspinBC_tmul, ofBaseChange_tmul_eq, map_one, one_mul, ← bcHom_ι, ← map_mul,
    ← map_mul, ← map_sub, ← ι_adV Z.2, bcHom_ι, ιInv_ι]

/-- **The `F̄`-span of the rational moved centralizer**: a skew endomorphism `Y` of `W_{F̄}`
commuting with `P(x)_{F̄}` and vanishing on `W'_x ⊗ F̄` is `ad u` for some `u` in the base change
of the moved part `𝔩_x = ker movedCentMap` (`exists_lift_skew`, `range_gspinBC`,
`mem_movedCent_baseChange`). -/
theorem exists_movedCent_lift (x : ↥(GSpin d.QW)) (Y : Module.End Kb Wb)
    (hs : IsomCent.IsSkew (bform Qb) Y)
    (hc : Commute ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb) Y)
    (hf : ∀ z ∈ Module.End.eigenspace
      ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb) 1, Y z = 0) :
    ∃ u ∈ (LinearMap.ker (movedCentMap d.QW x)).baseChange Kb,
      adV Qb (gspinBC d.QW u) = Y := by
  have hQ := isNondeg_baseChange _ d.nondeg
  let xb : GSpin Qb :=
    ⟨bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ), TorusTransfer.bcUnits_mem_GSpin d.QW x⟩
  have hX : (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb =
      (specP Qb xb : _ →ₗ[Kb] _) :=
    LinearMap.ext fun w => (GGPData.specP_bcUnits d x w).symm
  obtain ⟨Yh, hYh0, hYh⟩ := exists_lift_skew hQ Y hs
  have hYh0' := hYh0
  rw [← LieSubalgebra.mem_toSubmodule, ← range_gspinBC d.QW hQ] at hYh0'
  obtain ⟨u, rfl⟩ := hYh0'
  refine ⟨u, mem_movedCent_baseChange d.QW x u ?_ ?_, ?_⟩
  · rw [hX] at hc
    exact commute_of_lift hQ xb hc hYh0 hYh
  · intro w hw
    have h1 : (1 : Kb) ⊗ₜ[F] w ∈ Module.End.eigenspace
        ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb) 1 := by
      rw [Module.End.mem_eigenspace_iff, one_smul, LinearMap.baseChange_tmul]
      congr 1
      exact (d.mem_fixedSub_iff).mp hw
    have := hYh (1 ⊗ₜ w)
    rw [hf _ h1, map_zero, sub_eq_zero] at this
    exact this
  · exact LinearMap.ext fun v => by rw [adV_apply, hYh, ιInv_ι]

/-- The moved part `ad Z`, `Z ∈ 𝔩_x`, over `F̄`: skew, commuting with `P(x)_{F̄}`, and vanishing
on `ker (P(x)_{F̄} − 1)`. -/
theorem movedCent_baseChange_props (x : ↥(GSpin d.QW))
    {Z : (gspin d.QW).toSubmodule} (hZ : Z ∈ LinearMap.ker (movedCentMap d.QW x)) :
    IsomCent.IsSkew (bform Qb) ((adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb) ∧
      Commute ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb)
        ((adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb) ∧
      ∀ z ∈ Module.End.eigenspace
        ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb) 1,
        (adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb z = 0 := by
  obtain ⟨hc, hf⟩ := mem_ker_movedCentMap hZ
  have hbf : bform Qb = (bform d.QW).baseChange Kb := QuadraticForm.associated_baseChange _
  have hk : ∀ v ∈ fixedSub x, adV d.QW (Z : CliffordAlgebra d.QW) v = 0 := fun v hv => by
    rw [adV_apply, hf v hv, sub_self, map_zero]
  refine ⟨?_, ?_, fun z hz => ?_⟩
  · rw [hbf]; exact IsomCent.IsSkew.baseChange _ (bform_adV Z.2)
  · rw [Commute, SemiconjBy, ← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul,
      (commute_iff_adV d.nondeg x Z.2).mp hc]
  · rw [← specP_bcGSpin, eigenspace_bc_one] at hz
    obtain ⟨u, rfl⟩ := Submodule.toBaseChange_surjective' Kb _ hz
    clear hz
    induction u using TensorProduct.inductionOn with
    | zero => simp
    | tmul k v =>
      rw [Submodule.coe_toBaseChange_tmul, LinearMap.baseChange_tmul, hk v v.2,
        TensorProduct.tmul_zero]
    | add u v hu hv => rw [map_add, Submodule.coe_add, map_add, hu, hv, add_zero]

/-- A `F̄`-linear functional on `End(W_{F̄})` vanishing on `(ad Z)_{F̄}` for all `Z ∈ 𝔩_x` vanishes
on every skew endomorphism commuting with `P(x)_{F̄}` and vanishing on `ker (P(x)_{F̄} − 1)`. -/
theorem eq_zero_of_forall_movedCent (x : ↥(GSpin d.QW)) (γ : Module.End Kb Wb →ₗ[Kb] Kb)
    (hγ : ∀ Z ∈ LinearMap.ker (movedCentMap d.QW x),
      γ ((adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb) = 0)
    (Y : Module.End Kb Wb) (hs : IsomCent.IsSkew (bform Qb) Y)
    (hc : Commute ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb) Y)
    (hf : ∀ z ∈ Module.End.eigenspace
      ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb) 1, Y z = 0) :
    γ Y = 0 := by
  obtain ⟨u, hu, rfl⟩ := d.exists_movedCent_lift x Y hs hc hf
  rw [Submodule.baseChange_eq_span] at hu
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨Z, hZ, rfl⟩ := hy
    rw [TensorProduct.mk_apply, adV_gspinBC_tmul]
    exact hγ Z hZ
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, map_smul, map_smul, ha, smul_zero]

omit [PAdicField F] in
/-- `b(u, v) = ½ polar(u, v)`. -/
theorem bform_eq_half_polar {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)
    (u v : V) : bform Q u v = ⅟2 * QuadraticMap.polar Q u v :=
  QuadraticMap.associated_apply _ _ _ _

/-- Skewness for `b` is skewness for `polar`. -/
theorem isSkew_bform_iff {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)
    (Y : Module.End F V) :
    IsomCent.IsSkew (bform Q) Y ↔
      ∀ u v, QuadraticMap.polar Q (Y u) v = -QuadraticMap.polar Q u (Y v) := by
  have h2 : (⅟2 : F) ≠ 0 := invOf_ne_zero 2
  refine forall_congr' fun u => forall_congr' fun v => ?_
  rw [bform_eq_half_polar, bform_eq_half_polar, ← mul_neg]
  exact mul_right_inj' h2

/-- Two endomorphisms commute if their base changes to `F̄` do. -/
theorem commute_of_commute_baseChange {V : Type*} [AddCommGroup V] [Module F V]
    {A B : Module.End F V} (h : Commute (A.baseChange Kb) (B.baseChange Kb)) : Commute A B := by
  refine LinearMap.ext fun v => Module.Flat.tensorProduct_mk_injective F V Kb ?_
  have := LinearMap.congr_fun h.eq (1 ⊗ₜ v)
  simpa [Module.End.mul_apply, LinearMap.baseChange_tmul] using this

/-- **A regular element of the moved part of the Lie centralizer** (own work): for `x ∈ Γ(G,H)`
there is `Z ∈ gspin(W)` commuting with `x` with `ker (ad Z) = W'_x`, such that every endomorphism of
`W` commuting with `ad Z` commutes with `P(x)`.

Over `F̄`, `P(x)` is diagonal in a hyperbolic eigen-frame `eᵢ, fᵢ` with complement `W'_x ⊗ F̄`
(`exists_hypFrame_torusFbar`).  The moved Lie centralizer is abelian
(`lieAbelian_specP_baseChange`), and contains the regular diagonal map
`D = diag(i + 1 on eᵢ, −(i + 1) on fᵢ, 0 on W'_x)`, so every `(ad Z)_{F̄}`, `Z ∈ 𝔩_x`, is diagonal in
the frame, `αᵢ(Z)` on `eᵢ` and `−αᵢ(Z)` on `fᵢ`.  The `F`-linear maps `αᵢ`, `αᵢ − αⱼ` (`i ≠ j`),
`αᵢ + αⱼ` into `F̄` are nonzero on `𝔩_x`, since their `F̄`-linear extensions are nonzero at `D`, which
lies in the `F̄`-span of `𝔩_x` (`eq_zero_of_forall_movedCent`); `F` being infinite, some `Z ∈ 𝔩_x`
avoids their kernels (`Submodule.exists_forall_notMem_of_forall_ne_top`).  Then `(ad Z)_{F̄}` is a
regular frame-diagonal map, and the conclusions follow from `IsHypFrame.mem_of_diag` and
`IsHypFrame.commute_of_commute_diag`. -/
theorem exists_regular_movedCent {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) :
    ∃ Z ∈ gspin d.QW,
      ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * Z =
        Z * ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) ∧
      LinearMap.ker (adV d.QW Z) = fixedSub x ∧
      ∀ s : Module.End F (Fin d.m → F), Commute s (adV d.QW Z) →
        Commute s (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) := by
  classical
  set Pb := (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb with hPb
  obtain ⟨n, e, f, hF, hT⟩ := exists_hypFrame_torusFbar x hx
  have hPw : ∀ w, specP Qb (bcGSpin d.QW x) w = Pb w := fun w =>
    LinearMap.congr_fun (specP_bcGSpin d.QW x) w
  rw [specP_bcGSpin] at hF hT
  -- `P(x)_{F̄}` is diagonal in the frame
  have hxT : specP Qb (bcGSpin d.QW x) ∈ hypTorus (Module.End.eigenspace Pb 1) e f := by
    rw [← hT]; exact ⟨_, bcGSpin_mem_torusFbar (d.self_mem_torusOf x), rfl⟩
  obtain ⟨hxW, t, hxt⟩ := hxT
  have hPW : ∀ w ∈ Module.End.eigenspace Pb 1, Pb w = (1 : Kb) • w := fun w hw => by
    rw [← hPw, hxW w hw, one_smul]
  have hPe : ∀ i, Pb (e i) = (t i : Kb) • e i := fun i => by rw [← hPw, (hxt i).1]
  have hPf : ∀ i, Pb (f i) = (((t i)⁻¹ : Kbˣ) : Kb) • f i := fun i => by rw [← hPw, (hxt i).2]
  -- the regular diagonal element `D`
  set a : Fin n → Kb := fun j => (((j : ℕ) + 1 : ℕ) : Kb) with ha_def
  have ha0 : ∀ i, a i ≠ 0 := fun i => by simp [a]
  have hainj : Function.Injective a := fun i j hij => by
    simp only [a, Nat.cast_inj, add_left_inj] at hij; exact Fin.ext hij
  have hapos : ∀ i j, a i + a j ≠ 0 := fun i j => by
    simp only [a, ← Nat.cast_add]; exact Nat.cast_ne_zero.mpr (by omega)
  set D : Module.End Kb Wb := ∑ j, (a j • ((polarBilin Qb).flip (f j)).smulRight (e j) -
    a j • ((polarBilin Qb).flip (e j)).smulRight (f j)) with hD_def
  have hDapp : ∀ v, D v = ∑ j, ((a j * QuadraticMap.polar Qb v (f j)) • e j -
      (a j * QuadraticMap.polar Qb v (e j)) • f j) := fun v => by
    simp [D, LinearMap.sum_apply, smul_smul]
  have hDW : ∀ w ∈ Module.End.eigenspace Pb 1, D w = (0 : Kb) • w := fun w hw => by
    rw [hDapp, zero_smul]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [((hF.mem_iff w).1 hw j).1, ((hF.mem_iff w).1 hw j).2]
    simp
  have hDe : ∀ i, D (e i) = a i • e i := fun i => by
    rw [hDapp]
    simp [hF.polar_ee, hF.polar_ef]
  have hDf : ∀ i, D (f i) = (-a i) • f i := fun i => by
    rw [hDapp]
    simp [hF.polar_ff, hF.polar_fe, neg_smul]
  have hsD : IsomCent.IsSkew (bform Qb) D := by
    rw [isSkew_bform_iff]
    intro u v
    rw [hDapp, hDapp, ← polarBilin_apply_apply, ← polarBilin_apply_apply, map_sum, map_sum,
      LinearMap.sum_apply, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      polarBilin_apply_apply, smul_eq_mul]
    rw [QuadraticMap.polar_comm Qb (e j) v, QuadraticMap.polar_comm Qb (f j) v]
    ring
  have hcD : Commute Pb D := hF.linearMap_ext (fun w hw => by
      rw [Module.End.mul_apply, Module.End.mul_apply, hDW w hw, hPW w hw, one_smul, zero_smul,
        map_zero, hDW w hw, zero_smul])
    (fun i => by
      rw [Module.End.mul_apply, Module.End.mul_apply, hDe, hPe, map_smul, map_smul, hPe, hDe,
        smul_comm])
    (fun i => by
      rw [Module.End.mul_apply, Module.End.mul_apply, hDf, hPf, map_smul, map_smul, hPf, hDf,
        smul_comm])
  have hfD : ∀ z ∈ Module.End.eigenspace Pb 1, D z = 0 := fun z hz => by
    rw [hDW z hz, zero_smul]
  have hL := lieAbelian_specP_baseChange x hx
  -- every `(ad Z)_{F̄}`, `Z ∈ 𝔩_x`, is diagonal in the frame
  have hdiag : ∀ Z ∈ LinearMap.ker (movedCentMap d.QW x),
      (∀ i, (adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb (e i) =
        QuadraticMap.polar Qb ((adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb (e i)) (f i) •
          e i) ∧
      ∀ i, (adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb (f i) =
        (-QuadraticMap.polar Qb ((adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb (e i))
          (f i)) • f i := by
    intro Z hZ
    obtain ⟨hsZ, hcZ, hfZ⟩ := d.movedCent_baseChange_props x hZ
    have hcom : Commute D ((adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb) :=
      (hL _ _ hsZ hsD hcZ hcD hfZ hfD).symm
    have hneg : ∀ i, -a i ≠ 0 := fun i => neg_ne_zero.mpr (ha0 i)
    have hnegi : Function.Injective fun i => -a i := fun i j h => hainj (neg_inj.mp h)
    have hab : ∀ i j, a i ≠ -a j := fun i j h => hapos i j (by rw [h, neg_add_cancel])
    have he := hF.eq_smul_e_of_commute_diag hDW hDe hDf ha0 hainj hab hcom
    have hf := hF.eq_smul_f_of_commute_diag hDW hDe hDf hneg hnegi hab hcom
    refine ⟨he, fun i => ?_⟩
    rw [hf i]
    congr 1
    rw [(isSkew_bform_iff _ _).mp hsZ, QuadraticMap.polar_comm, he i,
      QuadraticMap.polar_smul_right, hF.polar_fe]
    simp
  -- the functionals
  let β : Fin n → Module.End Kb Wb →ₗ[Kb] Kb := fun i =>
    { toFun := fun Y => QuadraticMap.polar Qb (Y (e i)) (f i)
      map_add' := fun Y Y' => by simp [QuadraticMap.polar_add_left]
      map_smul' := fun c Y => by simp [QuadraticMap.polar_smul_left] }
  let ι := Fin n ⊕ ({p : Fin n × Fin n // p.1 ≠ p.2} ⊕ (Fin n × Fin n))
  let γ : ι → Module.End Kb Wb →ₗ[Kb] Kb := fun k => match k with
    | .inl i => β i
    | .inr (.inl p) => β p.1.1 - β p.1.2
    | .inr (.inr p) => β p.1 + β p.2
  have hβD : ∀ i, β i D = a i := fun i => by
    show QuadraticMap.polar Qb (D (e i)) (f i) = a i
    rw [hDe, QuadraticMap.polar_smul_left, hF.polar_ef]; simp
  have hγD : ∀ k, γ k D ≠ 0 := by
    rintro (i | ⟨⟨i, j⟩, hij⟩ | ⟨i, j⟩)
    · show β i D ≠ 0; rw [hβD]; exact ha0 i
    · show β i D - β j D ≠ 0
      rw [hβD, hβD, sub_ne_zero]; exact fun h => hij (hainj h)
    · show β i D + β j D ≠ 0; rw [hβD, hβD]; exact hapos i j
  let K𝔩 := LinearMap.ker (movedCentMap d.QW x)
  let φ : ι → ↥K𝔩 →ₗ[F] Kb := fun k =>
    { toFun := fun Z => γ k ((adV d.QW ((Z : (gspin d.QW).toSubmodule) :
        CliffordAlgebra d.QW)).baseChange Kb)
      map_add' := fun Z Z' => by
        simp only [Submodule.coe_add, map_add, LinearMap.baseChange_add]
      map_smul' := fun c Z => by
        simp only [SetLike.val_smul, map_smul, LinearMap.baseChange_smul, RingHom.id_apply]
        exact LinearMap.map_smul_of_tower _ c _ }
  have hne : ∀ k, LinearMap.ker (φ k) ≠ ⊤ := by
    intro k htop
    refine hγD k (d.eq_zero_of_forall_movedCent x (γ k) (fun Z hZ => ?_) D hsD hcD hfD)
    have : (⟨Z, hZ⟩ : ↥K𝔩) ∈ LinearMap.ker (φ k) := htop ▸ Submodule.mem_top
    exact this
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  obtain ⟨Z, hZ⟩ := Submodule.exists_forall_notMem_of_forall_ne_top _ hne
  have hZφ : ∀ k, γ k ((adV d.QW ((Z : (gspin d.QW).toSubmodule) :
      CliffordAlgebra d.QW)).baseChange Kb) ≠ 0 := fun k h => hZ k h
  obtain ⟨hZe, hZf⟩ := hdiag Z Z.2
  obtain ⟨-, -, hYW0⟩ := d.movedCent_baseChange_props x Z.2
  set Y := (adV d.QW ((Z : (gspin d.QW).toSubmodule) : CliffordAlgebra d.QW)).baseChange Kb
    with hY
  set α : Fin n → Kb := fun i => QuadraticMap.polar Qb (Y (e i)) (f i) with hα
  have hYW : ∀ w ∈ Module.End.eigenspace Pb 1, Y w = (0 : Kb) • w := fun w hw => by
    rw [hYW0 w hw, zero_smul]
  have hα0 : ∀ i, α i ≠ 0 := fun i => hZφ (.inl i)
  have hαn : ∀ i, -α i ≠ 0 := fun i => neg_ne_zero.mpr (hα0 i)
  have hαinj : Function.Injective α := fun i j h => by
    by_contra hij
    exact hZφ (.inr (.inl ⟨(i, j), hij⟩)) (sub_eq_zero.mpr h)
  have hαninj : Function.Injective fun i => -α i := fun i j h => hαinj (neg_inj.mp h)
  have hαab : ∀ i j, α i ≠ -α j := fun i j h =>
    hZφ (.inr (.inr (i, j))) (by show α i + α j = 0; rw [h, neg_add_cancel])
  obtain ⟨hcx, hfx⟩ := mem_ker_movedCentMap Z.2
  refine ⟨_, (Z : (gspin d.QW).toSubmodule).2, hcx, ?_, fun s hs => ?_⟩
  · ext v
    constructor
    · intro hv
      have h0 : Y (1 ⊗ₜ v) = (0 : Kb) • (1 ⊗ₜ v) := by
        rw [hY, LinearMap.baseChange_tmul, LinearMap.mem_ker.mp hv, TensorProduct.tmul_zero,
          zero_smul]
      have hmem := hF.mem_of_diag hYW hZe hZf hα0 hαn h0
      rw [Module.End.mem_eigenspace_iff, one_smul, hPb, LinearMap.baseChange_tmul] at hmem
      exact (d.mem_fixedSub_iff).mpr (Module.Flat.tensorProduct_mk_injective F _ Kb hmem)
    · intro hv
      rw [LinearMap.mem_ker, adV_apply, hfx v hv, sub_self, map_zero]
  · have hsb : Commute Y (s.baseChange Kb) := by
      rw [Commute, SemiconjBy, hY, ← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul,
        hs.eq]
    have := hF.commute_of_commute_diag hYW hZe hZf hα0 hαn hαinj hαninj hαab hsb hPW hPe hPf
    exact (d.commute_of_commute_baseChange this).symm

/-- **Helper (a) for `gammaClass_equiv`: every `x ∈ Γ(G,H)` gives a point of Luo's
`Γ^Lie(Ḡ, H̄)` with the same torus**: there is `X ∈ so(W)` with `X ∈ Γ^Lie(Ḡ, H̄)` (Luo §7.1) whose
torus `H''_X`, embedded diagonally in `Ḡ`, is the image of `T_x(F)` under
`t ↦ (P(t), P(t) ⊕ 1)` (`exists_regular_movedCent`, `luo_isGammaElt_of_regular`). -/
theorem exists_luo_isGammaElt_torusOf_eq {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) :
    ∃ X : Module.End F d.luoOf.W, d.luoOf.IsGammaElt X ∧
      d.luoOf.torusOf X = (d.torusOf x).map (d.toGbarU.comp d.diag) := by
  obtain ⟨Z, hZ, hZx, hker, hreg⟩ := d.exists_regular_movedCent hx
  exact ⟨_, d.luo_isGammaElt_of_regular hx hZ hZx hker fun s hs _ => hreg s hs⟩

end Exists

end GGPData

end GSpinGGP
