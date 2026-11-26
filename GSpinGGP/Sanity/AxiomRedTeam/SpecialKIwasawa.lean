/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.SpecialKIwasawa
import GSpinGGP.Sanity.AxiomRedTeam.BPThetaF

/-!
# Checks of `tits_iwasawa_specialStab`

The axiom: for special lattices `S_W`, `S_V` adapted to a flag Levi datum `L`, every `P ∈ 𝒫(M)`
has `G = P · specialStab S_W S_V`.

* (V) **`M = G`, any datum** (`tits_iwasawa_specialStab_check_of_M_eq_top`): then `𝒫(M) = {G}`
  and the conclusion holds with `k = 1`, without the axiom.
* (V) **`toyD`** (`toyD_tits_iwasawa_specialStab_check`): every reduced Levi datum has `M = G`;
  the hypotheses hold for the special lattices `0 ⊆ W`, `𝒪_F z₀ ⊆ V`
  (`toyD_specialW/V_isAdapted`), and the conclusion is proved without the axiom.
* (V) **`gl2Data`, a proper Levi subgroup** (`gl2_tits_iwasawa_specialStab_check`): `M` the
  diagonal torus of `GL₂ ≅ GSpin(3)` (`gl2Levi`), `P` running over **all** of `𝒫(M)` (both
  Borel subgroups containing it), `S_W = 0`, `S_V` the lattice `⟨z₋₁, z₀, ½ z₁⟩`
  (`gl2SpecialW/V`, adapted to `gl2Levi`).  Here `specialStab = gl2K` (`specialStab_eq_latticeK`)
  and `G = P · gl2K` is `gl2_iwasawa`, proved by hand.  This is the instance where the axiom has
  content (`P ≠ G`).
* **Not applicable to a non-special lattice** (`gl2_tits_iwasawa_specialStab_not_iwahori`): the
  lattice `⟨z₋₁, ϖ z₀, ϖ · ½ z₁⟩` satisfies every condition of `SpecialLattice` except `attained`
  (`gl2_iwahori_data`), and no `SpecialLattice` has it as `R`
  (`not_exists_specialLattice_R_eq_iwahori`).  So no instance of the axiom has
  `R_V = ⟨z₋₁, ϖ z₀, ϖ · ½ z₁⟩`.  This is where `attained` is load-bearing: the stabilizer of
  that lattice in `SO(3) ≅ PGL₂` is the normalizer of an Iwahori subgroup, its cut by `H_G = 0`
  in `GL₂` is the Iwahori subgroup `I`, and `GL₂(F) ≠ B · I` for the Borel subgroups `B ⊇ M`
  (`G = ⊔_{w ∈ W} B w I`); standard, not formalized here.  Without `attained` the axiom would
  be false.

**Axioms used by the checks**: none of `tits_iwasawa_specialStab`, and no `sorryAx` (`#print
axioms` in a scratch file: the three (V) checks use only `propext`, `Classical.choice`,
`Quot.sound`; the Iwahori exclusion likewise).

**Conflicts.**  `tits_iwasawa` (`Literature/Tits.lean`) is the same printed decomposition (Tits
3.3.2) for the full-flag parabolic `P₀` and an unspecified compact `K`; the two axioms share no
object (`tits_iwasawa` produces its own `K`).  At `gl2Data` both conclusions hold for `K = gl2K`
and every flag parabolic (`gl2_iwasawa`).  The θ_f axioms of `Literature/BPThetaF.lean` take
`GoodK.IsSpecial` presentations; this axiom is what makes `specialStab` a `GoodK`
(`exists_goodK_eq_specialStab`), and at `toyD`/`gl2Data` the `GoodK`s used there
(`toyD_specialK`, `gl2GoodK`) are built without it.

**Automation probe** (scratch file, not kept: a failing search does not compile): with
the axiom applied at `toyD` and at `gl2Data` (to `gl2SpecialW/V`), `exact?` and `aesop` find no
proof of `False`.

Not covered: `W`, `V` with `d_an ∈ {2, 3, 4}`, Witt index `≥ 2`, a hyperbolic-plane factor.
-/

noncomputable section

open GSpinGGP.Sanity

namespace GSpinGGP.AxiomRedTeam

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **(V) For `M = G` the conclusion holds without the axiom**: every `P ∈ 𝒫(G)` contains `M = G`,
so `g = g · 1`. -/
theorem tits_iwasawa_specialStab_check_of_M_eq_top (d : GGPData F) (L : d.FlagLeviDatum)
    (hM : L.M = ⊤) (SW : SpecialLattice d.QW) (SV : SpecialLattice d.QV) :
    ∀ P ∈ d.parabolics L.M, ∀ g : ↥d.G, ∃ p ∈ P, ∃ k ∈ d.specialStab SW SV, g = p * k := by
  rintro P ⟨FW, FV, rfl, hL⟩ g
  exact ⟨g, hL.le (hM ▸ Subgroup.mem_top g), 1, one_mem _, (mul_one g).symm⟩

local notation "𝕋" => (toyD (F := F))

theorem toyD_specialW_isAdapted (L : (𝕋).ReducedLeviDatum) :
    (toyD_specialW (F := F)).IsAdapted L.bW L.wtW :=
  ⟨fun i => i.elim0, fun i => i.elim0, fun x _ => Subsingleton.elim x 0 ▸ zero_mem _⟩

theorem toyD_specialV_isAdapted (L : (𝕋).ReducedLeviDatum) :
    (toyD_specialV (F := F)).IsAdapted L.bV L.wtV := by
  have hV := toyD_flag_len_eq_zero_V L.FV
  have htop : wtSpan L.bV L.wtV 0 = ⊤ := by
    rw [wtSpan, show {j | L.wtV j = 0} = Set.univ from
      Set.eq_univ_of_forall fun j => L.wtV_eq_zero hV j, Set.image_univ, L.bV.span_eq]
  exact ⟨fun i => i.elim0, fun i => i.elim0, fun x _ => htop ▸ Submodule.mem_top⟩

/-- **(V) at `toyD`**: the hypotheses of the axiom hold (for `toyD_specialW/V`), and its
conclusion holds for every pair of special lattices, without the axiom. -/
theorem toyD_tits_iwasawa_specialStab_check (L : (𝕋).ReducedLeviDatum) :
    (toyD_specialW (F := F)).IsAdapted L.bW L.wtW ∧ (toyD_specialV (F := F)).IsAdapted L.bV L.wtV ∧
      ∀ (SW : SpecialLattice (𝕋).QW) (SV : SpecialLattice (𝕋).QV),
        ∀ P ∈ (𝕋).parabolics L.M, ∀ g : ↥(𝕋).G,
          ∃ p ∈ P, ∃ k ∈ (𝕋).specialStab SW SV, g = p * k :=
  ⟨toyD_specialW_isAdapted L, toyD_specialV_isAdapted L, fun SW SV =>
    tits_iwasawa_specialStab_check_of_M_eq_top _ L.toFlagLeviDatum (toyD_M_eq_top L) SW SV⟩

local notation "𝔾" => (GGPData.gl2Data (F := F))
local notation "𝕃" => (GGPData.gl2Levi (F := F))

/-- **(V) at `gl2Data`, `M` the diagonal torus**: the hypotheses hold for `gl2SpecialW/V`, and
`G = P · specialStab` for every `P ∈ 𝒫(M)`, without the axiom (`specialStab = gl2K`,
`gl2_iwasawa`). -/
theorem gl2_tits_iwasawa_specialStab_check :
    (GGPData.gl2SpecialW (F := F)).IsAdapted (𝕃).bW (𝕃).wtW ∧
      (GGPData.gl2SpecialV (F := F)).IsAdapted (𝕃).bV (𝕃).wtV ∧
      ∀ P ∈ (𝔾).parabolics (𝕃).M, ∀ g : ↥(𝔾).G,
        ∃ p ∈ P, ∃ k ∈ (𝔾).specialStab GGPData.gl2SpecialW GGPData.gl2SpecialV, g = p * k := by
  refine ⟨GGPData.gl2SpecialW_isAdapted, GGPData.gl2SpecialV_isAdapted, ?_⟩
  rintro P ⟨FW, FV, rfl, -⟩ g
  rw [(𝔾).specialStab_eq_latticeK _ _ _ _ GGPData.gl2SpecialW_R GGPData.gl2SpecialV_R
    GGPData.gl2_not_isHypPlane_W GGPData.gl2_not_isHypPlane_V]
  exact GGPData.gl2_iwasawa FW FV g

/-- **The axiom never applies to the Iwahori lattice**: for a uniformizer `ϖ`, every instance
`(S_W, S_V)` of the axiom at `gl2Data` has `R_V ≠ ⟨z₋₁, ϖ z₀, ϖ · ½ z₁⟩`, although that lattice
satisfies every condition of `SpecialLattice` except `attained` (`gl2_iwahori_data`).  Its
`specialStab` would be the Iwahori subgroup `I`, for which `G = B · I` fails (standard, not
formalized), so this exclusion is needed for the axiom to be true. -/
theorem gl2_tits_iwasawa_specialStab_not_iwahori {ϖ : F} (h0 : 0 < ‖ϖ‖) (h1 : ‖ϖ‖ < 1)
    (hmax : ∀ x : F, ‖x‖ < 1 → ‖x‖ ≤ ‖ϖ‖) (SV : SpecialLattice (𝔾).QV) :
    SV.R ≠ GGPData.gl2IwahoriLattice ϖ :=
  fun h => GGPData.not_exists_specialLattice_R_eq_iwahori h0 h1 hmax ⟨SV, h⟩

/-- The hypotheses of `gl2_tits_iwasawa_specialStab_not_iwahori` can be met. -/
theorem gl2_iwahori_exclusion_nonvacuous :
    ∃ ϖ : F, 0 < ‖ϖ‖ ∧ ‖ϖ‖ < 1 ∧
      ∀ SV : SpecialLattice (𝔾).QV, SV.R ≠ GGPData.gl2IwahoriLattice ϖ := by
  obtain ⟨ϖ, h0, h1, hmax⟩ := exists_norm_lt_one_isGreatest (F := F)
  exact ⟨ϖ, h0, h1, gl2_tits_iwasawa_specialStab_not_iwahori h0 h1 hmax⟩

end GSpinGGP.AxiomRedTeam
