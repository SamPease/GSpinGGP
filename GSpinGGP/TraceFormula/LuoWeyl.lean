/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LuoGamma
import GSpinGGP.TraceFormula.SOLieFacts
import GSpinGGP.Foundations.CayleyTransform

/-!
# The Weyl groups of a torus of `Γ(G,H)` and of its image in Luo's `𝒯`

For `x ∈ Γ(G,H)` with torus `T = T_x ⊆ GSpin(W)` and `S = P(T) ⊆ SO(W)`,
`N_{GSpin(W)}(T)/Z_{GSpin(W)}(T) ≅ N_{SO(W)}(S)/Z_{SO(W)}(S) ≅ N_{H̄}(T')/Z_{H̄}(T')`, where
`T' = {(s, s ⊕ 1) : s ∈ S}` (Luo, arXiv:2009.13947v1, §7.1).  We prove the equality of the
cardinalities.

* `LuoDatum.weylCardOf_map_diagU`: for `S ⊆ SO(W)`,
  `|W(H̄, (S, S ⊕ 1))| = |N_{SO(W)}(S) : Z_{SO(W)}(S)|`
  (`H̄ = SO(W) ⋉ N`, and the `N`-part of an element normalizing the diagonal torus centralizes it:
  `diagU_mul_inrU_conj_diagU_eq_iff`).
* `GGPData.commute_of_commute_specP_torusOf`: for `x ∈ Γ(G,H)`, if `P(g)` centralizes `P(T_x)` then
  `g` centralizes `T_x`.  The commutator `g t g⁻¹ t⁻¹` is a scalar `±1` (`exists_conj_eq_smul`), so
  this is not formal.  A Cayley transform `s = (μ + X)(μ − X)⁻¹` of a regular `X = ad Z`
  (`exists_regular_movedCent`) lies in `P(T_x)`, has fixed space `W'_x` and no eigenvalue `−1`; as
  `P(g)` commutes with `s`, `det P(g)|_{W'_x} = det P(g) = 1`
  (`det_eq_det_one_mul_det_neg_one_of_charZero`), hence `det P(g)|_{W₋₁} = 1`, and `g` commutes with
  `x` by Steinberg's description (`Steinberg.commute_iff`), hence with `T_x`
  (`commute_torusOf_of_commute`).
* `GGPData.weylCardOf_torusOf_eq`, `GGPData.weylCardOf_eq_of_isNaturalTorusCorr`:
  `|W(T_x)| = |W(H̄, T')|` for the natural correspondence of tori (`IsNaturalTorusCorr`).
-/

noncomputable section

open CliffordAlgebra Module

namespace GSpinGGP

namespace LuoDatum

section Basic

variable {K : Type*} [Field K] [Invertible (2 : K)] (L : LuoDatum K)

/-- **`|W(H̄, T')|` for a diagonal torus** (Luo §7.1): for a subgroup `S` of `SO(W)`, with
`T' = {(s, s ⊕ 1) : s ∈ S}`, `|N_{H̄}(T')/Z_{H̄}(T')| = |N_{SO(W)}(S)/Z_{SO(W)}(S)|`.  The map
`(g, (g ⊕ 1) n) ↦ g` sends `N_{H̄}(T')` onto `N_{SO(W)}(S)` (with section `g ↦ (g, g ⊕ 1)`), and an
element of `N_{H̄}(T')` centralizes `T'` iff its image centralizes `S`, since its `N`-part already
commutes with every `s ⊕ 1` (`diagU_mul_inrU_conj_diagU_eq_iff`). -/
theorem weylCardOf_map_diagU (S : Subgroup ↥(SOu L.QW)) :
    L.weylCardOf (S.map (L.diagU.comp (SOu L.QW).subtype)) =
      (Subgroup.centralizer (S : Set ↥(SOu L.QW))).relIndex
        (Subgroup.normalizer (S : Set ↥(SOu L.QW))) := by
  set ι := L.diagU.comp (SOu L.QW).subtype with hι
  set T := S.map ι with hT
  have hιapp : ∀ s : ↥(SOu L.QW), ι s = L.diagU s := fun _ => rfl
  have hdiagH : ∀ g ∈ SOu L.QW, L.diagU g ∈ L.HbarU := fun g hg =>
    L.mem_HbarU_iff.mpr ⟨g, hg, 1, L.NsetSub.one_mem, by simp⟩
  have hφmem : ∀ u : ↥L.HbarU, L.unitFst u ∈ SOu L.QW := fun u => by
    obtain ⟨g, hg, n, -, hu⟩ := L.mem_HbarU_iff.mp u.2
    rw [hu, unitFst_diagU_mul_inrU]
    exact hg
  let φ : ↥L.HbarU →* ↥(SOu L.QW) :=
    (L.unitFst.comp L.HbarU.subtype).codRestrict _ hφmem
  have hφ : ∀ u : ↥L.HbarU, ((φ u : ↥(SOu L.QW)) : (Module.End K L.W)ˣ) = L.unitFst u :=
    fun _ => rfl
  have hφι : ∀ g : ↥(SOu L.QW), φ ⟨ι g, hdiagH g g.2⟩ = g := fun g =>
    Subtype.ext (by rw [hφ]; exact L.unitFst_diagU _)
  have hmemT : ∀ a : L.Ambˣ, a ∈ T ↔ ∃ s ∈ S, ι s = a := fun a => Subgroup.mem_map
  have hιinj : Function.Injective ι := fun a b h => Subtype.ext (by
    have := congrArg L.unitFst h
    simpa [hιapp] using this)
  -- an element of `N_{H̄}(T')`: its `SO(W)`-part normalizes `S`, its `N`-part centralizes `T'`
  have key : ∀ u : ↥L.HbarU,
      u ∈ Subgroup.normalizer ((T.subgroupOf L.HbarU : Subgroup ↥L.HbarU) : Set ↥L.HbarU) →
      ∀ s ∈ S, φ u * s * (φ u)⁻¹ ∈ S ∧
        ∀ g n, (u : L.Ambˣ) = L.diagU g * L.inrU n →
          n * Units.map L.extGrp (s : (Module.End K L.W)ˣ) =
            Units.map L.extGrp (s : (Module.End K L.W)ˣ) * n := by
    intro u hu s hs
    have h1 : (⟨ι s, hdiagH s s.2⟩ : ↥L.HbarU) ∈ T.subgroupOf L.HbarU :=
      Subgroup.mem_subgroupOf.mpr ((hmemT _).mpr ⟨s, hs, rfl⟩)
    have h2 := (Subgroup.mem_normalizer_iff.mp hu _).mp h1
    obtain ⟨s', hs', he⟩ := (hmemT _).mp (Subgroup.mem_subgroupOf.mp h2)
    obtain ⟨g, -, n, -, hu'⟩ := L.mem_HbarU_iff.mp u.2
    have he' : (L.diagU g * L.inrU n) * L.diagU (s : (Module.End K L.W)ˣ) *
        (L.diagU g * L.inrU n)⁻¹ = L.diagU (s' : (Module.End K L.W)ˣ) := by
      rw [← hu', ← hιapp, ← hιapp, he]; rfl
    have hgs := (L.diagU_mul_inrU_conj_diagU_eq_iff g _ _ n).mp he'
    have hg : (φ u : (Module.End K L.W)ˣ) = g := by
      rw [hφ, hu', unitFst_diagU_mul_inrU]
    refine ⟨?_, fun g' n' hu'' => ?_⟩
    · have : φ u * s * (φ u)⁻¹ = s' := Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hg]
        exact hgs.1)
      rw [this]; exact hs'
    · obtain ⟨rfl, rfl⟩ := (L.diagU_mul_inrU_inj).mp (hu'.symm.trans hu'')
      exact hgs.2
  unfold weylCardOf
  refine Subgroup.relIndex_eq_of_map_eq_of_comap_inf_eq (f := φ) ?_ ?_
  · -- `φ(N_{H̄}(T')) = N_{SO(W)}(S)`
    apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      refine Subgroup.mem_normalizer_iff.mpr fun s => ⟨fun hs => (key u hu s hs).1, fun hs => ?_⟩
      have := (key u⁻¹ (Subgroup.inv_mem _ hu) _ hs).1
      simpa [map_inv, mul_assoc] using this
    · intro g hg
      refine ⟨⟨ι g, hdiagH g g.2⟩, ?_, hφι g⟩
      refine Subgroup.mem_normalizer_iff.mpr fun h => ?_
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      constructor
      · intro hh
        obtain ⟨s, hs, hse⟩ := (hmemT _).mp hh
        refine (hmemT _).mpr ⟨g * s * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg s).mp hs, ?_⟩
        rw [map_mul, map_mul, map_inv, hse]
      · intro hh
        obtain ⟨s, hs, hse⟩ := (hmemT _).mp hh
        refine (hmemT _).mpr ⟨g⁻¹ * s * g, (Subgroup.mem_normalizer_iff''.mp hg s).mp hs, ?_⟩
        rw [map_mul, map_mul, map_inv, hse]
        group
  · -- `N_{H̄}(T') ∩ φ⁻¹(Z_{SO(W)}(S)) = Z_{H̄}(T')`
    apply le_antisymm
    · rintro u ⟨hz, hn⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨s, hs, hse⟩ := (hmemT _).mp (Subgroup.mem_subgroupOf.mp hh)
      obtain ⟨g, -, n, -, hu'⟩ := L.mem_HbarU_iff.mp u.2
      have hg : (φ u : (Module.End K L.W)ˣ) = g := by
        rw [hφ, hu', unitFst_diagU_mul_inrU]
      have hgs : Commute g (s : (Module.End K L.W)ˣ) := by
        have := Subgroup.mem_centralizer_iff.mp hz s hs
        rw [← hg]
        exact (congrArg Subtype.val this).symm
      have hc := (L.commute_diagU_mul_inrU_diagU_iff g s n).mpr
        ⟨hgs, (key u hn s hs).2 g n hu'⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← hse, hιapp, hu']
      exact hc.eq.symm
    · intro u hu
      refine ⟨?_, Subgroup.centralizer_le_normalizer _ hu⟩
      change φ u ∈ Subgroup.centralizer _
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have h1 : (⟨ι s, hdiagH s s.2⟩ : ↥L.HbarU) ∈ T.subgroupOf L.HbarU :=
        Subgroup.mem_subgroupOf.mpr ((hmemT _).mpr ⟨s, hs, rfl⟩)
      have h2 := congrArg φ (Subgroup.mem_centralizer_iff.mp hu _ h1)
      rwa [map_mul, map_mul, hφι] at h2

end Basic

end LuoDatum

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

/-- **The sign obstruction vanishes on `T_x`**: for `x ∈ Γ(G,H)` and `g ∈ GSpin(W)(F)` such that
`P(g)` commutes with `P(t)` for every `t ∈ T_x(F)`, `g` commutes with every `t ∈ T_x(F)`.

Take `Z ∈ gspin(W)` regular in the moved Lie centralizer of `x` (`exists_regular_movedCent`), and
the Cayley transform `s = (μ + X)(μ − X)⁻¹ ∈ F[X]` of `X = ad Z` (`exists_cayley`): a semisimple
isometry with fixed space `ker X = W'_x` and no eigenvalue `−1`, so of determinant `1`, hence in
`H''_X = P(T_x(F))` (`torusW_adV_eq_map`).  `P(g)` commutes with `s`, so
`det P(g) = det P(g)|_{W'_x}` (`det_eq_det_one_mul_det_neg_one_of_charZero`), i.e.
`det P(g)|_{W'_x} = 1`; then `det P(g)|_{W₋₁} = 1` (the same lemma for `P(x)`), so `g` commutes with
`x` (`Steinberg.commute_iff`), hence with `T_x(F)` (`commute_torusOf_of_commute`). -/
theorem commute_of_commute_specP_torusOf {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    {g : ↥(GSpin d.QW)} (hg : ∀ t ∈ d.torusOf x, Commute (specP d.QW g) (specP d.QW t))
    {t : ↥(GSpin d.QW)} (ht : t ∈ d.torusOf x) : Commute g t := by
  obtain ⟨Z, hZ, hZx, hker, hreg⟩ := d.exists_regular_movedCent hx
  have hZf : ∀ w ∈ fixedSub x, adV d.QW Z w = 0 := fun w hw => by
    rw [← hker] at hw; exact hw
  set X : Module.End F (Fin d.m → F) := adV d.QW Z with hX
  have hB : (bform d.QW).IsSymm := ⟨fun u v => bform_comm d.QW u v⟩
  have hnd : (bform d.QW).Nondegenerate := d.nondeg
  have hXskew : (bform d.QW).IsSkewAdjoint X := by
    have h := adV_mem_skewAdjoint hZ
    exact (LinearMap.mem_skewAdjointSubmodule _).mp h
  have hXss : X.IsSemisimple :=
    isSemisimple_adV hZ (d.isSS_of_commute_of_isGammaElt hx hZ hZx hZf)
  obtain ⟨s, hso, hsadj, hsX, hs1, hsm1⟩ := LinearMap.BilinForm.exists_cayley hXskew
  have hsss : s.IsSemisimple := hXss.of_mem_adjoin_singleton hsadj
  -- the eigenspaces of `s`
  have hE1 : Module.End.eigenspace s 1 = fixedSub x := by
    ext v
    rw [Module.End.mem_eigenspace_iff, one_smul, hs1, ← hker]
    rfl
  have hEm1 : ∀ v ∈ Module.End.eigenspace s (-1), v = 0 := fun v hv => by
    rw [Module.End.mem_eigenspace_iff, neg_one_smul] at hv
    exact hsm1 v hv
  have hdet_m1 : ∀ (h : Module.End F (Fin d.m → F))
      (hm : Set.MapsTo h (Module.End.eigenspace s (-1)) (Module.End.eigenspace s (-1))),
      LinearMap.det (h.restrict hm) = 1 := fun h hm => by
    have : Subsingleton ↥(Module.End.eigenspace s (-1)) :=
      ⟨fun a b => Subtype.ext (by rw [hEm1 a a.2, hEm1 b b.2])⟩
    exact LinearMap.det_eq_one_of_subsingleton _
  -- `det s = 1`
  have hdets : LinearMap.det s = 1 := by
    rw [IsomCent.det_eq_det_one_mul_det_neg_one_of_charZero hB hnd hso hsss hso (Commute.refl s),
      hdet_m1 s (IsomCent.mapsTo_eigenspace_of_commute (Commute.refl s) (-1)), mul_one]
    have : s.restrict (IsomCent.mapsTo_eigenspace_of_commute (Commute.refl s) 1) = LinearMap.id :=
      LinearMap.ext fun v => Subtype.ext (by
        have := Module.End.mem_eigenspace_iff.mp v.2
        rw [one_smul] at this
        exact this)
    rw [this, LinearMap.det_id]
  -- `s ∈ P(T_x)`
  have hsinj : Function.Injective s := LinearMap.IsOrthogonal.injective hnd hso
  have hsu : IsUnit s :=
    (LinearMap.isUnit_iff_ker_eq_bot s).mpr (LinearMap.ker_eq_bot.mpr hsinj)
  have hsW : hsu.unit ∈ d.luoOf.torusW X := by
    refine ⟨?_, hsX.eq, fun w hw => (hs1 w).mpr hw⟩
    refine ⟨fun v => ?_, hdets⟩
    change d.QW (s v) = d.QW v
    rw [← QuadraticMap.associated_eq_self_apply F d.QW (s v),
      ← QuadraticMap.associated_eq_self_apply F d.QW v]
    exact hso v v
  rw [d.torusW_adV_eq_map hx hZ hZx hker (fun s' hs' _ => hreg s' hs')] at hsW
  obtain ⟨t₀, ht₀, hts⟩ := hsW
  have hts' : (specP d.QW t₀ : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) = s := by
    rw [← coe_specPU, hts]; rfl
  -- `det P(g)|_{W'_x} = 1`
  set h : Module.End F (Fin d.m → F) := (specP d.QW g : (Fin d.m → F) →ₗ[F] (Fin d.m → F))
  have hhs : Commute s h := by
    rw [← hts']
    exact Steinberg.commute_toLinearMap (hg t₀ ht₀)
  have hdetW' : LinearMap.det (h.restrict (IsomCent.mapsTo_eigenspace_of_commute hhs 1)) = 1 := by
    have := IsomCent.det_eq_det_one_mul_det_neg_one_of_charZero hB hnd hso hsss
      (Steinberg.isOrthogonal_specP g) hhs
    rw [hdet_m1 h (IsomCent.mapsTo_eigenspace_of_commute hhs (-1)), mul_one, det_specP] at this
    exact this.symm
  -- `g` commutes with `x`
  have hcx : Commute (specP d.QW g) (specP d.QW x) := hg x (d.self_mem_torusOf x)
  have hss := isSemisimple_specP_of_isSS d.QW x hx.1
  have hdet := IsomCent.det_eq_det_one_mul_det_neg_one_of_charZero hB hnd
    (Steinberg.isOrthogonal_specP x) hss (Steinberg.isOrthogonal_specP g)
    (Steinberg.commute_toLinearMap hcx)
  have hfix : LinearMap.det ((specP d.QW g : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).restrict
      (mapsTo_fixedSub_of_commute hcx)) = 1 :=
    (IsomCent.det_restrict_congr _ hE1.symm _ _).trans hdetW'
  have h1 : LinearMap.det ((specP d.QW g : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).restrict
      (IsomCent.mapsTo_eigenspace_of_commute (Steinberg.commute_toLinearMap hcx) 1)) = 1 :=
    (IsomCent.det_restrict_congr _ (Steinberg.fixedSub_eq_eigenspace x).symm _ _).trans hfix
  rw [h1, one_mul, det_specP] at hdet
  have hgx := (Steinberg.commute_iff d.nondeg x hx.1 g).mpr ⟨hcx,
    ⟨mapsTo_fixedSub_of_commute hcx, hfix⟩,
    ⟨mapsTo_negFixedSub_of_commute hcx,
      (Steinberg.det_restrict_eq rfl (Steinberg.negFixedSub_eq_eigenspace x) _ _).trans
        hdet.symm⟩⟩
  exact commute_torusOf_of_commute hx (Subtype.ext hgx) ht

/-- **`|W(T)| = |W(H̄, T')|`**, for a subgroup `T` of `GSpin(W)(F)` containing the scalars and such
that `g` centralizes `T` as soon as `P(g)` centralizes `P(T)`, and `T'` the image of `T` under
`t ↦ (P(t), P(t) ⊕ 1)`: both equal `|N_{SO(W)}(S) : Z_{SO(W)}(S)|` for `S = P(T)` (`P` is onto
`SO(W)` with kernel the scalars, `range_specP_eq_SOGrp`, `ker_specP`; `weylCardOf_map_diagU`). -/
theorem weylCardOf_eq_luo_of_centralizer {T : Subgroup ↥(GSpin d.QW)}
    (hsc : (scalarGSpin d.QW).range ≤ T)
    (hZ : ∀ g : ↥(GSpin d.QW), (∀ t ∈ T, Commute (specP d.QW g) (specP d.QW t)) →
      ∀ t ∈ T, Commute g t) :
    weylCardOf d T = d.luoOf.weylCardOf (T.map (d.toGbarU.comp d.diag)) := by
  have hmem : ∀ g : ↥(GSpin d.QW), d.specPU g ∈ LuoDatum.SOu d.luoOf.QW := fun g => by
    change LinearMap.GeneralLinearGroup.generalLinearEquiv F _
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv F _).symm (specP d.QW g)) ∈ SOGrp d.QW
    rw [MulEquiv.apply_symm_apply, ← range_specP_eq_SOGrp d.nondeg]
    exact ⟨g, rfl⟩
  let ψ : ↥(GSpin d.QW) →* ↥(LuoDatum.SOu d.luoOf.QW) := d.specPU.codRestrict _ hmem
  have hψ : ∀ g, ((ψ g : ↥(LuoDatum.SOu d.luoOf.QW)) : (Module.End F d.luoOf.W)ˣ) = d.specPU g :=
    fun _ => rfl
  have hψsurj : Function.Surjective ψ := by
    intro s
    have hs := s.2
    change LinearMap.GeneralLinearGroup.generalLinearEquiv F d.luoOf.W
      (s : (Module.End F d.luoOf.W)ˣ) ∈ SOGrp d.QW at hs
    rw [← range_specP_eq_SOGrp d.nondeg] at hs
    obtain ⟨g, hg⟩ := hs
    refine ⟨g, Subtype.ext (Units.ext ?_)⟩
    rw [hψ, coe_specPU, hg]
    rfl
  have hker : ψ.ker ≤ T := by
    intro g hg
    apply hsc
    rw [← ker_specP d.nondeg, MonoidHom.mem_ker]
    have h1 : d.specPU g = 1 := by
      rw [← hψ, MonoidHom.mem_ker.mp hg]; rfl
    apply LinearEquiv.toLinearMap_injective
    have := congrArg (fun u : (Module.End F d.luoOf.W)ˣ => (u : Module.End F d.luoOf.W)) h1
    simp only [coe_specPU, Units.val_one] at this
    rw [this]
    rfl
  have hcomm : ∀ a b : ↥(GSpin d.QW), Commute (ψ a) (ψ b) →
      Commute (specP d.QW a) (specP d.QW b) := by
    intro a b hab
    apply LinearEquiv.toLinearMap_injective
    have := congrArg (fun u : ↥(LuoDatum.SOu d.luoOf.QW) =>
      ((u : (Module.End F d.luoOf.W)ˣ) : Module.End F d.luoOf.W)) hab.eq
    simp only [Subgroup.coe_mul, Units.val_mul, hψ, coe_specPU] at this
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul]
    exact this
  have hZ' : ∀ g, ψ g ∈ Subgroup.centralizer
      ((T.map ψ : Subgroup _) : Set ↥(LuoDatum.SOu d.luoOf.QW)) →
      g ∈ Subgroup.centralizer (T : Set ↥(GSpin d.QW)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    refine (hZ g (fun t' ht' => hcomm _ _ ?_) t ht).eq.symm
    exact (Subgroup.mem_centralizer_iff.mp hg _ ⟨t', ht', rfl⟩).symm
  have hmap : T.map (d.toGbarU.comp d.diag) =
      (T.map ψ).map (d.luoOf.diagU.comp (LuoDatum.SOu d.luoOf.QW).subtype) := by
    rw [toGbarU_comp_diag, Subgroup.map_map]
    rfl
  unfold weylCardOf
  rw [hmap, LuoDatum.weylCardOf_map_diagU,
    Subgroup.relIndex_centralizer_normalizer_map_of_surjective hψsurj hker hZ']
  rfl

/-- **(L8, Weyl groups) `|W(T_x)| = |W(H̄, T')|`** for `x ∈ Γ(G,H)` and `T'` the image of `T_x`
under `t ↦ (P(t), P(t) ⊕ 1)` (Luo §7.1):
`N_{GSpin(W)}(T)/Z_{GSpin(W)}(T) ≅ N_{SO(W)}(S)/Z_{SO(W)}(S) ≅ N_{H̄}(T')/Z_{H̄}(T')`. -/
theorem weylCardOf_torusOf_eq {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) :
    weylCardOf d (d.torusOf x) =
      d.luoOf.weylCardOf ((d.torusOf x).map (d.toGbarU.comp d.diag)) :=
  d.weylCardOf_eq_luo_of_centralizer (by rintro _ ⟨c, rfl⟩; exact d.scalar_mem_torusOf x c)
    fun _ hg _ ht => d.commute_of_commute_specP_torusOf hx hg ht

/-- **`|W(T)| = |W(H̄, T')|` for corresponding tori**: for a torus `T` of `Γ(G,H)` and a torus `T'`
of Luo's `𝒯` with `IsNaturalTorusCorr T T'` (an `H̄(F)`-conjugate of the image of `T`),
`|N_{GSpin(W)}(T)/Z_{GSpin(W)}(T)| = |N_{H̄}(T')/Z_{H̄}(T')|` (`weylCardOf_torusOf_eq`,
`weylCardOf_map_conj`). -/
theorem weylCardOf_eq_of_isNaturalTorusCorr (T : d.GammaTorus) {T' : Subgroup d.luoOf.Ambˣ}
    (hT : d.IsNaturalTorusCorr T.1 T') : weylCardOf d T.1 = d.luoOf.weylCardOf T' := by
  obtain ⟨x, hx, hxT⟩ := T.2
  obtain ⟨h, hh, rfl⟩ := hT
  rw [d.luoOf.weylCardOf_map_conj hh, ← hxT, d.weylCardOf_torusOf_eq hx]

end GGPData

end GSpinGGP
