/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.WeightedOrbital
import GSpinGGP.GGP.RegularCentralizer

/-!
# `G_x(F)` for regular semisimple `x`

For `x ∈ G_reg(F)` (semisimple, `𝔤_x` abelian; `regularSet`), the two facts about `G_x(F)` that
the weighted orbital integrals of `TraceFormula/WeightedOrbital.lean` take as hypotheses:

* `commute_of_mem_centG`: `G_x(F)` is commutative (it is the group of `F`-points of a maximal
  torus), so every left Haar measure on it is right invariant
  (`isMulRightInvariant_of_mem_regularSet`);
* `centG_le_M`: `G_x(F) ⊆ M(F)` for `x ∈ M(F)` (Waldspurger, Compos. Math. 146 (2010), §2.3:
  `G_x = M_x ⊂ M`; Beuzart-Plessis, Astérisque 418, §1.10).  The sources' `G_x` is the neutral
  component `Z_G(x)⁰`; `centG x` is the full centralizer, which is the same here, since `Z_G(x)` is
  connected (Steinberg; the derived group `Spin × Spin` is simply connected).

Both reduce, factor by factor on `G = GSpin(W) × GSpin(V)`, to `commute_of_isRegular` (not yet
proved), and the second then to `mem_flagLevi_of_commute` (`GGP/RegularCentralizer.lean`).
`weightedOrbitalIntegral_conj_K_of_mem_regularSet` is `weightedOrbitalIntegral_conj_K` for
`x ∈ M(F) ∩ G_reg(F)` with these hypotheses discharged.
-/

noncomputable section

open MeasureTheory

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable {d : GGPData F} {x : ↥d.G}

/-- **`G_x(F)` is commutative for `x ∈ G_reg(F)`**: on each factor `GSpin(W)`, `GSpin(V)` the
components of `x` are regular semisimple (`isLieAbelian_lieCentralizer_fst_snd`), and
`commute_of_isRegular` applies. -/
theorem commute_of_mem_centG (hx : x ∈ regularSet d.G d.lie) {g h : ↥d.G}
    (hg : g ∈ d.centG x) (hh : h ∈ d.centG x) : Commute g h := by
  obtain ⟨hss, hab⟩ := hx
  have hssW := isSS_algHom (AlgHom.fst F _ _) hss
  have hssV := isSS_algHom (AlgHom.snd F _ _) hss
  obtain ⟨habW, habV⟩ := isLieAbelian_lieCentralizer_fst_snd d hab
  have hg' := Subgroup.mem_centralizer_singleton_iff.1 hg
  have hh' := Subgroup.mem_centralizer_singleton_iff.1 hh
  have hW := commute_of_isRegular d.nondeg (d.fst x) hssW habW (hg'.map d.fst) (hh'.map d.fst)
  have hV := commute_of_isRegular d.nondeg_QV (d.snd x) hssV habV (hg'.map d.snd)
    (hh'.map d.snd)
  have hp : Commute (d.fst g, d.snd g) (d.fst h, d.snd h) := Prod.ext hW.eq hV.eq
  simpa only [pair_fst_snd] using hp.map d.pair

/-- **Haar measures on `G_x(F)` are right invariant for `x ∈ G_reg(F)`**: `G_x(F)` is commutative
(`commute_of_mem_centG`).  Not an instance, the regularity of `x` being a hypothesis; consumers
use it with `have`. -/
theorem isMulRightInvariant_of_mem_regularSet (hx : x ∈ regularSet d.G d.lie)
    (μ : Measure ↥(d.centG x)) [μ.IsMulLeftInvariant] : μ.IsMulRightInvariant := by
  refine ⟨fun c => ?_⟩
  have e : (fun a : ↥(d.centG x) => a * c) = (fun a => c * a) :=
    funext fun a => Subtype.ext (commute_of_mem_centG hx a.prop c.prop).eq
  rw [e]
  exact map_mul_left_eq_self μ c

/-- **`G_x(F) ⊆ M(F)` for `x ∈ M(F) ∩ G_reg(F)`** (Waldspurger 2010, §2.3; Beuzart-Plessis
§1.10): factorwise `mem_flagLevi_of_commute_of_isRegular`.  The sources state it for
`G_x = Z_G(x)⁰`; `centG x` is the full centralizer, the same here since `Z_G(x)` is connected
(Steinberg; `Spin` is simply connected). -/
theorem centG_le_M (L : d.FlagLeviDatum) (hx : x ∈ regularSet d.G d.lie) (hxM : x ∈ L.M) :
    d.centG x ≤ L.M := by
  obtain ⟨hss, hab⟩ := hx
  have hssW := isSS_algHom (AlgHom.fst F _ _) hss
  have hssV := isSS_algHom (AlgHom.snd F _ _) hss
  obtain ⟨habW, habV⟩ := isLieAbelian_lieCentralizer_fst_snd d hab
  obtain ⟨hxW, hxV⟩ := hxM
  intro g hg
  have hg' := Subgroup.mem_centralizer_singleton_iff.1 hg
  exact ⟨mem_flagLevi_of_commute_of_isRegular d.nondeg L.hsW hxW hssW habW (hg'.map d.fst),
    mem_flagLevi_of_commute_of_isRegular d.nondeg_QV L.hsV hxV hssV habV (hg'.map d.snd)⟩

/-- **`J_M(x, ·)` is invariant under conjugation by `K`**, for `x ∈ M(F) ∩ G_reg(F)` and any Haar
measure on `G_x(F)`: `weightedOrbitalIntegral_conj_K` with `G_x(F) ⊆ M(F)` (`centG_le_M`) and the
right invariance of the Haar measure (`isMulRightInvariant_of_mem_regularSet`) discharged. -/
theorem weightedOrbitalIntegral_conj_K_of_mem_regularSet {L : d.ReducedLeviDatum}
    {K : d.GoodK L.toFlagLeviDatum} (hx : x ∈ regularSet d.G d.lie) (hxM : x ∈ L.M)
    (μ : Measure ↥(d.centG x)) [μ.IsHaarMeasure] {k : ↥d.G} (hk : k ∈ K.K) (f : ↥d.G → ℂ) :
    d.weightedOrbitalIntegral L K x μ (fun g => f (k * g * k⁻¹)) =
      d.weightedOrbitalIntegral L K x μ f := by
  have := isMulRightInvariant_of_mem_regularSet hx μ
  exact weightedOrbitalIntegral_conj_K (centG_le_M L.toFlagLeviDatum hx hxM) μ hk f

end GGPData

end GSpinGGP
