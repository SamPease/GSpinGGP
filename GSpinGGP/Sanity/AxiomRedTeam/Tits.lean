/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.LieAudit
import GSpinGGP.Literature.Tits

/-!
# Checks of `tits_iwasawa`

* (V) `tits_iwasawa_check_of_wittIndex_zero`: when `W` and `V` are anisotropic, the only full
  flags are the empty ones, `P₀ = G`, and the conclusion holds with `K = 1`; proved without the
  axiom.  In particular at the toy datum `toyD` (`toyD_tits_iwasawa_check`).
* (V) `tits_iwasawa_check_of_isHypPlane_V`: when `V` is a hyperbolic plane, `A_G = G`, so
  `P₀ = G` for every pair of flags and the conclusion holds with `K = 1`.  At `hypVData`
  (`hypVData_tits_iwasawa_check`) the hypotheses hold with a *nonempty* full flag in `V`
  (`V` isotropic), and the conclusion is proved without the axiom.

Not covered: proper `P₀` (e.g. `W` a hyperbolic plane, `hypWData`), where the axiom has content.
-/

noncomputable section

namespace GSpinGGP.AxiomRedTeam

open GSpinGGP.Sanity

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- The conclusion of `tits_iwasawa` holds with `K = 1` whenever `P₀ = G`. -/
theorem tits_iwasawa_check_of_whittB_eq_top (d : GGPData F) (FW : IsotropicFlag d.QW)
    (FV : IsotropicFlag d.QV) (hB : d.whittB FW FV = ⊤) :
    ∃ K : Subgroup ↥d.G, IsCompact (K : Set ↥d.G) ∧
      ∀ g : ↥d.G, ∃ k ∈ K, ∃ p ∈ d.whittB FW FV, g = k * p :=
  ⟨⊥, by simp only [Subgroup.coe_bot]; exact isCompact_singleton, fun g =>
    ⟨1, one_mem _, g, by rw [hB]; trivial, (one_mul g).symm⟩⟩

/-- For anisotropic `W` and `V`, `P₀ = G` for full flags. -/
theorem whittB_eq_top_of_wittIndex_zero (d : GGPData F) (FW : IsotropicFlag d.QW)
    (FV : IsotropicFlag d.QV) (hW : FW.IsFull) (hV : FV.IsFull)
    (h0W : wittIndex d.QW = 0) (h0V : wittIndex d.QV = 0) : d.whittB FW FV = ⊤ := by
  unfold GGPData.whittB
  rw [flagStab_eq_top_of_len_eq_zero FW (hW.1.trans h0W),
    flagStab_eq_top_of_len_eq_zero FV (hV.1.trans h0V), Subgroup.comap_top, Subgroup.comap_top,
    inf_top_eq]

/-- **(V) The conclusion of `tits_iwasawa` for anisotropic `W` and `V`**, without the axiom:
`K = 1`. -/
theorem tits_iwasawa_check_of_wittIndex_zero (d : GGPData F) (FW : IsotropicFlag d.QW)
    (FV : IsotropicFlag d.QV) (hW : FW.IsFull) (hV : FV.IsFull)
    (h0W : wittIndex d.QW = 0) (h0V : wittIndex d.QV = 0) :
    ∃ K : Subgroup ↥d.G, IsCompact (K : Set ↥d.G) ∧
      ∀ g : ↥d.G, ∃ k ∈ K, ∃ p ∈ d.whittB FW FV, g = k * p :=
  tits_iwasawa_check_of_whittB_eq_top d FW FV
    (whittB_eq_top_of_wittIndex_zero d FW FV hW hV h0W h0V)

local notation "𝕋" => (toyD (F := F))

/-- **(V) at the toy datum**: the hypotheses of `tits_iwasawa` hold (empty flags are full) and its
conclusion is proved without it. -/
theorem toyD_tits_iwasawa_check :
    (emptyFlag (𝕋).QW).IsFull ∧ (emptyFlag (𝕋).QV).IsFull ∧
      ∃ K : Subgroup ↥(𝕋).G, IsCompact (K : Set ↥(𝕋).G) ∧
        ∀ g : ↥(𝕋).G, ∃ k ∈ K, ∃ p ∈ (𝕋).whittB (emptyFlag _) (emptyFlag _), g = k * p :=
  ⟨emptyFlag_isFull toyData_wittIndex_QW, emptyFlag_isFull toyData_wittIndex_QV,
    tits_iwasawa_check_of_wittIndex_zero _ _ _ (emptyFlag_isFull toyData_wittIndex_QW)
      (emptyFlag_isFull toyData_wittIndex_QV) toyData_wittIndex_QW toyData_wittIndex_QV⟩

/-- When `V` is a hyperbolic plane, `P₀ = G` for every pair of flags (`A_G = G` and
`A_G ⊆ P₀`). -/
theorem whittB_eq_top_of_isHypPlane_V (d : GGPData F) (hV : IsHypPlane d.QV)
    (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) : d.whittB FW FV = ⊤ :=
  eq_top_iff.2 ((HypVAux.AG_eq_top hV).symm ▸ d.AG_le_whittB FW FV)

/-- **(V) The conclusion of `tits_iwasawa` when `V` is a hyperbolic plane**, without the axiom. -/
theorem tits_iwasawa_check_of_isHypPlane_V (d : GGPData F) (hV : IsHypPlane d.QV)
    (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV) :
    ∃ K : Subgroup ↥d.G, IsCompact (K : Set ↥d.G) ∧
      ∀ g : ↥d.G, ∃ k ∈ K, ∃ p ∈ d.whittB FW FV, g = k * p :=
  tits_iwasawa_check_of_whittB_eq_top d FW FV (whittB_eq_top_of_isHypPlane_V d hV FW FV)

/-- **(V) at `hypVData`** (`V` isotropic): the hypotheses of `tits_iwasawa` hold with a full flag
of length `1` in `V`, and its conclusion is proved without it. -/
theorem hypVData_tits_iwasawa_check :
    ∃ (FW : IsotropicFlag (hypVData (F := F)).QW) (FV : IsotropicFlag (hypVData (F := F)).QV),
      FW.IsFull ∧ FV.IsFull ∧ FV.len = 1 ∧
      ∃ K : Subgroup ↥(hypVData (F := F)).G, IsCompact (K : Set ↥(hypVData (F := F)).G) ∧
        ∀ g, ∃ k ∈ K, ∃ p ∈ (hypVData (F := F)).whittB FW FV, g = k * p := by
  obtain ⟨FW, hW⟩ := IsotropicFlag.exists_isFull (hypVData (F := F)).QW
  obtain ⟨FV, hV⟩ := IsotropicFlag.exists_isFull (hypVData (F := F)).QV
  exact ⟨FW, FV, hW, hV, hV.1.trans hypVData_isHypPlane_QV.2.2,
    tits_iwasawa_check_of_isHypPlane_V _ hypVData_isHypPlane_QV FW FV⟩

end GSpinGGP.AxiomRedTeam
