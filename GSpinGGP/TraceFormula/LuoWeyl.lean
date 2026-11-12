/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LuoGamma
import GSpinGGP.TraceFormula.SOLieFacts
import GSpinGGP.Foundations.CayleyTransform

/-!
# The Weyl groups of a torus of `Γ(G,H)` and of its image in Luo's `𝒯`

For `x ∈ Γ(G,H)` with torus `T = T_x ⊆ GSpin(W)`, `S = P(T) ⊆ SO(W)` and
`T' = {(s, s ⊕ 1) : s ∈ S}`, the cardinalities
`|N_{GSpin(W)}(T)/Z_{GSpin(W)}(T)|`, `|N_{SO(W)}(S)/Z_{SO(W)}(S)|` and `|W(H̄, T')| =
|N_{H̄}(T')/Z_{H̄}(T')|` (Luo, arXiv:2009.13947v1, §7.1) are equal.  The second equality is
`LuoDatum.weylCardOf_map_diagU` (`TraceFormula/SOLieFacts.lean`); the first is proved here, through
`P : GSpin(W) → SO(W)` (onto, with kernel the scalars).
* `GGPData.commute_of_commute_specP_torusOf`: for `x ∈ Γ(G,H)`, if `P(g)` centralizes `P(T_x)` then
  `g` centralizes `T_x`.  The commutator `g t g⁻¹ t⁻¹` is a scalar `±1` (`exists_conj_eq_smul`), so
  this is not formal.  A Cayley transform `s = (μ + X)(μ − X)⁻¹` of a regular `X = ad Z`
  (`exists_regular_movedCent`) lies in `P(T_x)`, has fixed space `W'_x` and no eigenvalue `−1`; as
  `P(g)` commutes with `s`, `det P(g)|_{W'_x} = det P(g) = 1`
  (`det_eq_det_restrict_one_of_eigenspace_neg_one_eq_bot`), so `g` commutes with `x` by Steinberg's
  description (`commute_of_commute_specP_of_det_fixedSub`), hence with `T_x`
  (`commute_torusOf_of_commute`).
* `GGPData.weylCardOf_torusOf_eq`, `GGPData.weylCardOf_eq_of_isNaturalTorusCorr`:
  `|W(T_x)| = |W(H̄, T')|` for the natural correspondence of tori (`IsNaturalTorusCorr`).
-/

noncomputable section

open CliffordAlgebra Module

namespace GSpinGGP

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
  have hXskew : (bform d.QW).IsSkewAdjoint X :=
    (LinearMap.mem_skewAdjointSubmodule _).mp (adV_mem_skewAdjoint hZ)
  have hXss : X.IsSemisimple :=
    isSemisimple_adV hZ (d.isSS_of_commute_of_isGammaElt hx hZ hZx hZf)
  obtain ⟨s, hso, hsadj, hs1, hsm1⟩ := LinearMap.BilinForm.exists_cayley hXskew
  have hsss : s.IsSemisimple := hXss.of_mem_adjoin_singleton hsadj
  have hsX : Commute s X := (Algebra.commute_of_mem_adjoin_self hsadj).symm
  -- the eigenspaces of `s`
  have hE1 : Module.End.eigenspace s 1 = fixedSub x := by
    ext v
    rw [Module.End.mem_eigenspace_iff, one_smul, hs1, ← hker]
    rfl
  have hEm1 : Module.End.eigenspace s (-1) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Module.End.mem_eigenspace_iff, neg_one_smul] at hv
    exact hsm1 v hv
  -- `s ∈ P(T_x)`
  have hsu : IsUnit s := (LinearMap.isUnit_iff_ker_eq_bot s).mpr
    (LinearMap.ker_eq_bot.mpr (LinearMap.IsOrthogonal.injective hnd hso))
  have hsW : hsu.unit ∈ d.luoOf.torusW X := by
    refine ⟨?_, hsX.eq, fun w hw => (hs1 w).mpr hw⟩
    refine ⟨fun v => ?_, IsomCent.det_eq_one_of_eigenspace_neg_one_eq_bot hB hnd hso hsss hEm1⟩
    change d.QW (s v) = d.QW v
    rw [← QuadraticMap.associated_eq_self_apply F d.QW (s v),
      ← QuadraticMap.associated_eq_self_apply F d.QW v]
    exact hso v v
  rw [d.torusW_adV_eq_map hx hZ hZx hker (fun s' hs' _ => hreg s' hs')] at hsW
  obtain ⟨t₀, ht₀, hts⟩ := hsW
  have hts' : (specP d.QW t₀ : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) = s := by
    rw [← coe_specPU, hts]; rfl
  -- `det P(g)|_{W'_x} = det P(g) = 1`, so `g` commutes with `x`
  set h : Module.End F (Fin d.m → F) := (specP d.QW g : (Fin d.m → F) →ₗ[F] (Fin d.m → F))
  have hhs : Commute s h := by
    rw [← hts']
    exact Steinberg.commute_toLinearMap (hg t₀ ht₀)
  have hdetW' := IsomCent.det_eq_det_restrict_one_of_eigenspace_neg_one_eq_bot hB hnd hso hsss
    (Steinberg.isOrthogonal_specP g) hhs hEm1
  rw [det_specP] at hdetW'
  have hcx : Commute (specP d.QW g) (specP d.QW x) := hg x (d.self_mem_torusOf x)
  have hgx := commute_of_commute_specP_of_det_fixedSub d.nondeg x hx.1 hcx
    ((IsomCent.det_restrict_congr _ hE1.symm _ _).trans hdetW'.symm)
  exact commute_torusOf_of_commute hx hgx ht

/-- **`|W(T)| = |W(H̄, T')|`**, for a subgroup `T` of `GSpin(W)(F)` containing the scalars and such
that `g` centralizes `T` as soon as `P(g)` centralizes `P(T)`, and `T'` the image of `T` under
`t ↦ (P(t), P(t) ⊕ 1)`: both equal `|N_{SO(W)}(S) : Z_{SO(W)}(S)|` for `S = P(T)` (`P` is onto
`SO(W)` with kernel the scalars, `range_specP_eq_SOGrp`, `ker_specP`; `weylCardOf_map_diagU`). -/
theorem weylCardOf_eq_luo_of_centralizer {T : Subgroup ↥(GSpin d.QW)}
    (hsc : (scalarGSpin d.QW).range ≤ T)
    (hZ : ∀ g : ↥(GSpin d.QW), (∀ t ∈ T, Commute (specP d.QW g) (specP d.QW t)) →
      ∀ t ∈ T, Commute g t) :
    weylCardOf d T = d.luoOf.weylCardOf (T.map (d.toGbarU.comp d.diag)) := by
  let ψ : ↥(GSpin d.QW) →* ↥(LuoDatum.SOu d.luoOf.QW) :=
    d.specPU.codRestrict _ d.specPU_mem_SOu
  have hψ : ∀ g, ((ψ g : ↥(LuoDatum.SOu d.luoOf.QW)) : (Module.End F d.luoOf.W)ˣ) = d.specPU g :=
    fun _ => rfl
  have hψsurj : Function.Surjective ψ := by
    intro s
    obtain ⟨g, hg⟩ := d.exists_specP_eq_of_mem_SOu s.2
    exact ⟨g, Subtype.ext (Units.ext (by rw [hψ, coe_specPU, hg]))⟩
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
under `t ↦ (P(t), P(t) ⊕ 1)`: the cardinalities `|N_{GSpin(W)}(T)/Z_{GSpin(W)}(T)|`,
`|N_{SO(W)}(S)/Z_{SO(W)}(S)|` (`S = P(T)`, via `P`) and `|N_{H̄}(T')/Z_{H̄}(T')|` (Luo §7.1) are
equal. -/
theorem weylCardOf_torusOf_eq {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) :
    weylCardOf d (d.torusOf x) =
      d.luoOf.weylCardOf ((d.torusOf x).map (d.toGbarU.comp d.diag)) :=
  d.weylCardOf_eq_luo_of_centralizer (by rintro _ ⟨c, rfl⟩; exact d.scalar_mem_torusOf x c)
    fun _ hg _ ht => d.commute_of_commute_specP_torusOf hx hg ht

/-- **`|W(T)| = |W(H̄, T')|` for corresponding tori**: for a torus `T` of `Γ(G,H)` and a subgroup
`T'` with `IsNaturalTorusCorr T T'` (an `H̄(F)`-conjugate of the image of `T`),
`|N_{GSpin(W)}(T)/Z_{GSpin(W)}(T)| = |N_{H̄}(T')/Z_{H̄}(T')|` (`weylCardOf_torusOf_eq`,
`weylCardOf_map_conj`). -/
theorem weylCardOf_eq_of_isNaturalTorusCorr (T : d.GammaTorus) {T' : Subgroup d.luoOf.Ambˣ}
    (hT : d.IsNaturalTorusCorr T.1 T') : weylCardOf d T.1 = d.luoOf.weylCardOf T' := by
  obtain ⟨x, hx, hxT⟩ := T.2
  obtain ⟨h, hh, rfl⟩ := hT
  rw [d.luoOf.weylCardOf_map_conj hh, ← hxT, d.weylCardOf_torusOf_eq hx]

end GGPData

end GSpinGGP
