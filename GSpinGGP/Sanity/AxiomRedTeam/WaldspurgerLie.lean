/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.WaldspurgerLie

/-!
# Checks of `waldspurger2010_thm_7_9`

* **Junk values.**  The truncated integrals vanish identically for `f = 0` or `θ = 0`
  (`IN_zero_right`, `IN_zero_left`), without the axiom; so for `f = 0` (very cuspidal) and any `τ`
  representing its orbital pairing, the axiom says `I(θ, τ) = 0` (`Igeom_eq_zero_of_f_zero`), and
  for `θ = 0` that `I(0, τ) = 0` (`Igeom_zero_left`).  The geometric side is built from the
  germs `germLie` (a choice among expansions when one exists), so these are statements about those
  choices: for `τ = 0` and `θ = 0` they hold whenever the chosen expansions of `0` vanish, which is
  the case when the regular coefficients are unique (Harish-Chandra 1999 Cor 5.10).  No
  contradiction is derivable from them alone.
* `0` is very cuspidal, and `τ = 0` represents its orbital pairing, so `Igeom_eq_zero_of_f_zero`
  is not vacuous in `θ`, `f`, `τ` (`isVeryCuspidal_zero`, `isThetaFW1_zero`).

Not covered: an instance where `W1Input` is constructed (special lattices, measures) and both sides
are computed, e.g. `W = 0`, `V` a line.
-/

noncomputable section
open MeasureTheory Topology Filter

namespace GSpinGGP

namespace Sanity

open LuoDatum

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {L : LuoDatum F}
  {ψ : NontrivialAddChar F}

theorem extV_zero : L.extV (0 : ↥L.soV → ℂ) = 0 := by
  funext X; unfold extV; split_ifs <;> rfl

theorem IN_zero_right (I : L.W1Input ψ) (θ : ↥L.soW → ℂ) (N : ℕ) : I.IN θ 0 N = 0 := by
  simp [W1Input.IN, W1Input.Ig, LuoDatum.Ig, fXi, extV_zero]

theorem IN_zero_left (I : L.W1Input ψ) (f : ↥L.soV → ℂ) (N : ℕ) : I.IN 0 f N = 0 := by
  simp [W1Input.IN, W1Input.Ig, LuoDatum.Ig]

theorem isVeryCuspidal_zero : L.IsVeryCuspidal 0 := by
  refine ⟨?_, fun FV _ X _ μ _ => ⟨integrable_zero _ _ _, by simp⟩⟩
  exact ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

theorem isLieQuasiCharacter_zero_soV : IsLieQuasiCharacter L.SOV L.soV L.bV ψ 0 :=
  ⟨fun _ _ _ _ _ _ => rfl,
    fun _ _ => ⟨0, by simp, _, Filter.univ_mem, fun _ _ _ _ _ _ => by simp⟩⟩

theorem isThetaFW1_zero (μG : Measure ↥L.SOV) : L.IsThetaFW1 ψ μG 0 0 := by
  refine ⟨isLieQuasiCharacter_zero_soV, locallyIntegrable_zero, continuousOn_const,
    fun f' _ => ?_⟩
  simp [extV_zero]

/-- The axiom at `f = 0`: `I(θ, τ) = 0` for every `τ` representing the zero pairing. -/
theorem Igeom_eq_zero_of_f_zero (hV : IsNondeg L.QV) (hV2 : ¬ IsHypPlane L.QV) (I : L.W1Input ψ)
    {θ : ↥L.soW → ℂ} (hθ : IsLieQuasiCharacter L.SOW L.soW L.bW ψ θ) {τ : ↥L.soV → ℂ}
    (hτ : L.IsThetaFW1 ψ I.μG 0 τ) : I.Igeom θ τ = 0 := by
  have h := waldspurger2010_thm_7_9 L hV hV2 ψ I θ hθ 0 isVeryCuspidal_zero τ hτ
  rw [show I.IN θ 0 = fun _ => 0 from funext (IN_zero_right I θ)] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- The axiom at `θ = 0` (a quasi-character): `I(0, τ) = 0`. -/
theorem Igeom_zero_left (hV : IsNondeg L.QV) (hV2 : ¬ IsHypPlane L.QV) (I : L.W1Input ψ)
    (h0 : IsLieQuasiCharacter L.SOW L.soW L.bW ψ 0) {f : ↥L.soV → ℂ} (hf : L.IsVeryCuspidal f)
    {τ : ↥L.soV → ℂ} (hτ : L.IsThetaFW1 ψ I.μG f τ) : I.Igeom 0 τ = 0 := by
  have h := waldspurger2010_thm_7_9 L hV hV2 ψ I 0 h0 f hf τ hτ
  rw [show I.IN 0 f = fun _ => 0 from funext (IN_zero_left I f)] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

end Sanity

end GSpinGGP
