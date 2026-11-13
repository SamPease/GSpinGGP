/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.Witnesses
import GSpinGGP.Literature.Tits

/-!
# Checks of `tits_iwasawa`

* (V) `tits_iwasawa_check_of_wittIndex_zero`: when `W` and `V` are anisotropic, the only full
  flags are the empty ones, `P₀ = G`, and the conclusion holds with `K = 1`; proved without the
  axiom.  In particular at the toy datum `toyD` (`toyD_tits_iwasawa_check`).
* (C) `toyD_tits_iwasawa_consistent`: the axiom's `K` at `toyD`, used with `P₀ = G`, gives nothing
  beyond the trivial decomposition: every `g` is `k p` with `p = k⁻¹ g`.

Not covered: isotropic `W` or `V` (proper `P₀`), where the axiom has content.
-/

noncomputable section

namespace GSpinGGP.AxiomRedTeam

open GSpinGGP.Sanity

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]

/-- The stabilizer of a flag of length `0` (only the zero subspace) is everything. -/
theorem flagStab_eq_top_of_len_eq_zero {Q : QuadraticForm K V} (Fl : IsotropicFlag Q)
    (h : Fl.len = 0) : flagStab Fl = ⊤ := by
  refine eq_top_iff.2 fun g _ i => ?_
  have hi : i = 0 := Fin.ext (by have := i.2; simp only [Fin.val_zero]; omega)
  rw [hi, Fl.sub_zero, Submodule.map_bot]

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

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
      ∀ g : ↥d.G, ∃ k ∈ K, ∃ p ∈ d.whittB FW FV, g = k * p := by
  have hB := whittB_eq_top_of_wittIndex_zero d FW FV hW hV h0W h0V
  refine ⟨⊥, by simp only [Subgroup.coe_bot]; exact isCompact_singleton, fun g => ?_⟩
  exact ⟨1, one_mem _, g, by rw [hB]; trivial, (one_mul g).symm⟩

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

/-- **(C) The axiom at the toy datum** agrees with the direct computation: the `p` it provides is
`k⁻¹ g`, which lies in `P₀ = G`. -/
theorem toyD_tits_iwasawa_consistent :
    ∃ K : Subgroup ↥(𝕋).G, IsCompact (K : Set ↥(𝕋).G) ∧
      ∀ g : ↥(𝕋).G, ∃ k ∈ K, k⁻¹ * g ∈ (𝕋).whittB (emptyFlag _) (emptyFlag _) := by
  obtain ⟨K, hK, hdec⟩ := tits_iwasawa (𝕋) (emptyFlag _) (emptyFlag _)
    (emptyFlag_isFull toyData_wittIndex_QW) (emptyFlag_isFull toyData_wittIndex_QV)
  refine ⟨K, hK, fun g => ?_⟩
  obtain ⟨k, hk, p, hp, rfl⟩ := hdec g
  exact ⟨k, hk, by rwa [inv_mul_cancel_left]⟩

end GSpinGGP.AxiomRedTeam
