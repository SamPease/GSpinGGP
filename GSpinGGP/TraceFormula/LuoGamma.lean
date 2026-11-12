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
  `X = ad Z ∈ Γ^Lie(Ḡ, H̄)` and `H''_X` is the image of `T_x` (`torusW_adV_eq_map`,
  `isCompact_map_torusOf`).
* Towards the existence of such a `Z` over `F̄`: `adV_gspinBC_tmul` (`ad` commutes with base
  change), `exists_movedCent_lift` (a skew endomorphism of `W_{F̄}` commuting with `P(x)` and
  vanishing on `W'_x ⊗ F̄` is `ad` of an element of `𝔩_x ⊗ F̄`), `movedCent_baseChange_props`,
  `eq_zero_of_forall_movedCent` (an `F̄`-linear functional vanishing on `(ad 𝔩_x)_{F̄}` vanishes on
  all such endomorphisms).
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
  have hss := isSemisimple_specP_of_isSS Q x hx
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
  have h1 : LinearMap.det ((specP Q g : V →ₗ[K] V).restrict
      (IsomCent.mapsTo_eigenspace_of_commute (Steinberg.commute_toLinearMap hc) 1)) = 1 :=
    hone _ hE1 _
  rw [h1, one_mul, det_specP] at hdet
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
    (commute_of_commute_specP_of_fixes d.nondeg x hx hc hfix).eq, hfix⟩

/-- `P : GSpin(W) → GL(W)`, as units of `End W`. -/
def specPU : ↥(GSpin d.QW) →* (Module.End F d.luoOf.W)ˣ :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F d.luoOf.W).symm.toMonoidHom.comp
    (specP d.QW)

@[simp] theorem coe_specPU (g : ↥(GSpin d.QW)) :
    ((d.specPU g : (Module.End F d.luoOf.W)ˣ) : Module.End F d.luoOf.W) =
      (specP d.QW g : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) := rfl

/-- `t ↦ (P(t), P(t) ⊕ 1)` is `diagU ∘ P`. -/
theorem toGbarU_comp_diag : d.toGbarU.comp d.diag = d.luoOf.diagU.comp d.specPU := by
  ext t : 2
  refine Prod.ext rfl ?_
  show (specP d.QV (d.incl t) : d.V →ₗ[F] d.V) = _
  rw [d.specP_incl_eq_prodMap]
  rfl

section Regular

omit [PAdicField F] in
/-- A semisimple endomorphism is semisimple in the algebra of endomorphisms (`IsSS`). -/
theorem isSS_of_isSemisimple {U : Type*} [AddCommGroup U] [Module F U] [FiniteDimensional F U]
    {X : Module.End F U} (hX : X.IsSemisimple) : IsSS F X := by
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hX.minpoly_squarefree ?_
  have := Polynomial.aeval_algHom_apply (Algebra.lmul F (Module.End F U)) X (minpoly F X)
  rw [minpoly.aeval, map_zero] at this
  rw [← this]
  rfl

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
    have hs : (specP d.QW t : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) = s.val := by
      rw [ht]; rfl
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
  have := hx.2.2
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
      show ψ = d.luoOf.diagU.comp d.specPU from d.toGbarU_comp_diag, MonoidHom.comp_apply]
    have h2 : d.specPU (scalarGSpin d.QW c) = 1 := by
      change (LinearMap.GeneralLinearGroup.generalLinearEquiv F d.luoOf.W).symm
        (specP d.QW (scalarGSpin d.QW c)) = 1
      rw [h1]
      exact map_one _
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
  have e1 : ∀ w : Fin d.m → F, z ⊗ₜ[F] w = z • ((1 : Kb) ⊗ₜ[F] w) := fun w => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [LinearMap.baseChange_tmul, e1, e1, map_smul]
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
  clear hs hc hf
  rw [Submodule.baseChange_eq_span] at hu
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨Z, hZ, rfl⟩ := hy
    rw [TensorProduct.mk_apply, adV_gspinBC_tmul]
    exact hγ Z hZ
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, map_smul, map_smul, ha, smul_zero]

end Exists

end GGPData

end GSpinGGP
