/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LuoTransfer
import GSpinGGP.TraceFormula.Analytic
import GSpinGGP.GGP.TorusCount

/-!
# From `Γ(G,H)` to Luo's `Γ^Lie(Ḡ, H̄)`: the torus of a point

For `x ∈ Γ(G,H)` (`GGPData.IsGammaElt`) we look for `X ∈ so(W)` with `X ∈ Γ^Lie(Ḡ, H̄)`
(`LuoDatum.IsGammaElt`, Luo §7.1) whose torus `H''_X` is the image of `T_x` under
`t ↦ (P(t), P(t) ⊕ 1)`.

* `specPU`, `toGbarU_comp_diag`: `t ↦ (P(t), P(t) ⊕ 1)` is `diagU ∘ P`.
* `luo_isGammaElt_of_regular`: if `Z ∈ gspin(W)` commutes with `x`, `ker (ad Z) = W'_x`, and every
  endomorphism of `W` commuting with `ad Z` and fixing `W'_x` commutes with `P(x)`, then
  `X = ad Z ∈ Γ^Lie(Ḡ, H̄)` and `H''_X` is the image of `T_x` (`torusW_adV_eq_map`, through
  `S_x(F) ⊆ P(T_x(F))`, `GGPData.mem_torusOf_of_specP`; `isCompact_map_torusOf`).
* `exists_luo_isGammaElt_torusOf_eq`: every `x ∈ Γ(G,H)` gives such an `X`, since a regular `Z`
  exists (`GGPData.exists_regular_movedCent`, `GGP/TorusCount.lean`).
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

/-- **Every `x ∈ Γ(G,H)` gives a point of Luo's `Γ^Lie(Ḡ, H̄)` with the same torus**: there is
`X ∈ so(W)` with `X ∈ Γ^Lie(Ḡ, H̄)` (Luo §7.1) whose torus `H''_X`, embedded diagonally in `Ḡ`, is the image of `T_x(F)` under
`t ↦ (P(t), P(t) ⊕ 1)` (`exists_regular_movedCent`, `luo_isGammaElt_of_regular`). -/
theorem exists_luo_isGammaElt_torusOf_eq {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) :
    ∃ X : Module.End F d.luoOf.W, d.luoOf.IsGammaElt X ∧
      d.luoOf.torusOf X = (d.torusOf x).map (d.toGbarU.comp d.diag) := by
  obtain ⟨Z, hZ, hZx, hker, hreg⟩ := d.exists_regular_movedCent hx
  exact ⟨_, d.luo_isGammaElt_of_regular hx hZ hZx hker fun s hs _ => hreg s hs⟩

end Regular

end GGPData

end GSpinGGP
