/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.GL2Weight
import GSpinGGP.TraceFormula.ThetaFBPPresentation
import GSpinGGP.GGP.LeviOpp

/-!
# Two presentations of the torus of `GSpin₃ ≅ GL₂`

At `gl2Data` the torus datum `gl2Levi` has the basis `z₋₁, z₀, z₁` of `V` with weights `−1, 0, 1`.
`gl2Rebase` presents the same torus with the basis permuted by the transposition of `z₋₁` and
`z₁` and every vector doubled: its basis is `2 z₁, 2 z₀, 2 z₋₁` with weights `1, 0, −1` on the same
index type (`gl2Rebase_bV`, `gl2Rebase_wtV`).  So the weight functions differ, and so do the basis
vectors; but the labelled weight spaces are the same (`wtSpan` of weight `w` is the same for each
`w`, so no relabelling is involved), and the library's presentation independence
(`thetaFBP_eq_of_sameWtSpaces`) applies:

* `gl2Rebase_vM_nbar`: `v_T(n̄(t)) = 2 log max(1, ‖t‖) / (−log ‖ϖ‖)` for `gl2Rebase` too;
* `gl2Rebase_thetaFBP`: `θ_f` is the same for `(gl2Rebase, K)` and `(gl2Levi, K)`;
* `gl2Rebase_opp_thetaFBP`: and for `gl2Rebase.opp`, whose weight spaces are those of `gl2Levi`
  relabelled by `w ↦ −w` (a third presentation, with neither the basis nor the weights of
  `gl2Levi`).  Only this one exercises a nontrivial relabelling.

Nothing here uses an axiom or `sorry`.
-/

noncomputable section

open Module GSpinGGP.Sanity

namespace GSpinGGP.GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝔾" => (gl2Data (F := F))

local notation "𝕃" => (gl2Levi (F := F))

/-- The transposition of `z₋₁` and `z₁` in the index type of the basis of `V`. -/
abbrev gl2Swap : (𝕃).ιV ≃ (𝕃).ιV :=
  Equiv.swap (α := Fin 0 ⊕ Fin (2 * 1 + 1)) (Sum.inr 0) (Sum.inr 2)

theorem gl2Swap_symm_zero :
    (gl2Swap (F := F)).symm (Sum.inr 0 : (𝕃).ιV) = (Sum.inr 2 : (𝕃).ιV) := rfl

/-- **The second presentation**: the basis `2 z₁, 2 z₀, 2 z₋₁` of `V`. -/
def gl2Rebase : (𝔾).ReducedLeviDatum :=
  (𝕃).rebase (Equiv.refl _) 1 gl2Swap fun _ => Units.mk0 2 two_ne_zero

theorem gl2Rebase_sameWtSpaces :
    ReducedLeviDatum.SameWtSpacesW 𝕃 gl2Rebase ∧ ReducedLeviDatum.SameWtSpacesV 𝕃 gl2Rebase :=
  (𝕃).sameWtSpaces_rebase _ _ _ _

/-- The weights differ: `z₋₁`'s index carries weight `1` in `gl2Rebase`, `−1` in `gl2Levi`. -/
theorem gl2Rebase_wtV : (gl2Rebase (F := F)).wtV (Sum.inr 0) = 1 ∧ (𝕃).wtV (Sum.inr 0) = -1 := by
  refine ⟨?_, ?_⟩
  · rfl
  · rfl

/-- The basis vectors differ: the first is `2 z₁`. -/
theorem gl2Rebase_bV : (gl2Rebase (F := F)).bV (Sum.inr 0) = (2 : F) • (𝕃).bV (Sum.inr 2) := by
  change ((𝕃).bV.reindex gl2Swap).unitsSMul (fun _ => Units.mk0 (2 : F) two_ne_zero)
    (Sum.inr 0 : (𝕃).ιV) = _
  erw [Basis.unitsSMul_apply, Basis.reindex_apply, gl2Swap_symm_zero, Units.smul_def,
    Units.val_mk0]

/-- `gl2GoodK`, as a good subgroup for `gl2Rebase`. -/
def gl2RebaseK : (𝔾).GoodK (gl2Rebase (F := F)).toFlagLeviDatum :=
  ReducedLeviDatum.goodKOfSameWtSpaces gl2Rebase_sameWtSpaces.1 gl2Rebase_sameWtSpaces.2 gl2GoodK

/-- **The weight of the torus at `n̄(t)` in the second presentation** is the value computed for
`gl2Levi` (`gl2_vM_nbar`). -/
theorem gl2Rebase_vM_nbar {ϖ : F} (h0 : 0 < ‖ϖ‖) (h1 : ‖ϖ‖ < 1)
    (hmax : ∀ x : F, ‖x‖ < 1 → ‖x‖ ≤ ‖ϖ‖) (t : F) :
    (gl2Rebase (F := F)).vM gl2RebaseK (gl2Nbar t) =
      2 * Real.log (max 1 ‖t‖) / (-Real.log ‖ϖ‖) := by
  rw [ReducedLeviDatum.vM_eq_of_sameWtSpaces gl2Rebase_sameWtSpaces.1 gl2Rebase_sameWtSpaces.2
    gl2GoodK gl2RebaseK rfl, gl2_vM_nbar h0 h1 hmax]

/-- **`θ_f` in the second presentation** is `θ_f` in `gl2Levi`, for every `f` and `x`. -/
theorem gl2Rebase_thetaFBP (f : ↥(𝔾).G → ℂ) (x : ↥(𝔾).G) :
    (gl2Rebase (F := F)).thetaFBP gl2RebaseK f x = (𝕃).thetaFBP gl2GoodK f x :=
  ReducedLeviDatum.rebase_thetaFBP _ _ _ _ gl2GoodK f x

/-- **A third presentation**, `gl2Rebase.opp` (basis `2 z₁, 2 z₀, 2 z₋₁`, weights `−1, 0, 1`: the
weight spaces of `gl2Levi` relabelled by `w ↦ −w`), gives the same `θ_f`. -/
theorem gl2Rebase_opp_thetaFBP (f : ↥(𝔾).G → ℂ) (x : ↥(𝔾).G) :
    (gl2Rebase (F := F)).opp.thetaFBP ((gl2Rebase (F := F)).oppK gl2RebaseK) f x =
      (𝕃).thetaFBP gl2GoodK f x :=
  ReducedLeviDatum.thetaFBP_eq_of_sameWtSpaces
    ((gl2Rebase (F := F)).sameWtSpaces_opp.1.trans gl2Rebase_sameWtSpaces.1)
    ((gl2Rebase (F := F)).sameWtSpaces_opp.2.trans gl2Rebase_sameWtSpaces.2) gl2GoodK _ rfl f x

end GSpinGGP.GGPData
