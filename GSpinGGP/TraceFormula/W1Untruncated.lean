/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.WaldspurgerLie

/-!
# Waldspurger 2010 Thm 7.9 without truncation

If `g ↦ I(θ, f, g)` is integrable on `U(F)H(F)\G(F)`, then `∫ I(θ, f, g) dg = I(θ, f)`
(`integral_Ig_eq_Igeom`): Waldspurger 2010 Thm 7.9 (`waldspurger2010_thm_7_9`) with dominated
convergence, since `κ_N` is `{0, 1}`-valued and `κ_N(g) = 1` for `N` large (`kappa_spec`, SORRY).
-/

open MeasureTheory Topology Filter

noncomputable section

namespace GSpinGGP

namespace LuoDatum

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] {L : LuoDatum F}
  {ψ : NontrivialAddChar F}

/-- `‖κ_N(g)‖ ≤ 1`. -/
theorem norm_kappa_le (ϖ : F) (R0 : Set ↥L.V0sub) (cZ : ℤ → F) (N : ℕ) (g : ↥L.SOV) :
    ‖L.kappa ϖ R0 cZ N g‖ ≤ 1 := by
  unfold kappa
  split_ifs <;> simp

/-- **`κ_N` on `U(F)H(F)\G(F)`** (W1 §7.2, p. 35).
(i) `q ↦ κ_N(g_q)` is measurable, `g_q` the chosen representative.  (ii) For each `g`,
`κ_N(g) = 1` for `N` large.
Proof sketch (own work).  (i) `κ_N` is right `K`-invariant, and `K`, the stabilizer of a lattice,
is open; it is left `U(F)H(F)`-invariant (W1 §7.2: `H` fixes `v₀`, commutes with `A` and normalizes
`U`), so `κ_N(g_q)` is a locally constant function of `q` (the quotient map is open).
(ii) Iwasawa decomposition `G(F) = U(F) M(F) K` for the special compact subgroup `K` in good
position relative to `M = A G₀` (W1 §7.2, "On peut écrire `g = u a g₀ k`"; Bruhat–Tits I
Prop 4.4.3): write `g = u a g₀ k`; then `|val_F(a_i)| ≤ N` and `g₀⁻¹ v₀ ∈ ϖ^{-N} R₀` for `N` large,
as `R₀` is a lattice of `V₀`.  Status: SORRY. -/
theorem kappa_spec (I : L.W1Input ψ) :
    (∀ N, Measurable fun q => L.kappa I.ϖ I.R0 I.cZ N (CosetSpace.out L.UHbar.subtype q)) ∧
      ∀ q, ∀ᶠ N in atTop, L.kappa I.ϖ I.R0 I.cZ N (CosetSpace.out L.UHbar.subtype q) = 1 := by
  sorry

/-- **Waldspurger 2010 Thm 7.9, untruncated**: if `g ↦ I(θ, f, g)` is integrable on
`U(F)H(F)\G(F)`, then `∫_{U(F)H(F)\G(F)} I(θ, f, g) dg = I(θ, f)`.  From Thm 7.9
(`waldspurger2010_thm_7_9`): `I_N(θ, f) → ∫ I(θ, f, g) dg` by dominated convergence (`κ_N` is
`{0, 1}`-valued and tends to `1` pointwise, `kappa_spec`), and limits are unique. -/
theorem integral_Ig_eq_Igeom (hV : IsNondeg L.QV) (hV2 : ¬ IsHypPlane L.QV) (I : L.W1Input ψ)
    {θ : ↥L.soW → ℂ} (hθ : IsLieQuasiCharacter L.SOW L.soW L.bW ψ θ)
    {f : ↥L.soV → ℂ} (hf : L.IsVeryCuspidal f)
    {τ : ↥L.soV → ℂ} (hτ : L.IsThetaFW1 ψ I.μG f τ)
    (hint : Integrable (fun q => I.Ig θ f (CosetSpace.out L.UHbar.subtype q)) I.m) :
    ∫ q, I.Ig θ f (CosetSpace.out L.UHbar.subtype q) ∂I.m = I.Igeom θ τ := by
  obtain ⟨hmeas, hlim⟩ := kappa_spec I
  have hdct : Tendsto (I.IN θ f) atTop
      (𝓝 (∫ q, I.Ig θ f (CosetSpace.out L.UHbar.subtype q) ∂I.m)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun q => ‖I.Ig θ f (CosetSpace.out L.UHbar.subtype q)‖)
      (fun N => hint.aestronglyMeasurable.mul (hmeas N).aestronglyMeasurable) hint.norm
      (fun N => Filter.Eventually.of_forall fun q => ?_) (Filter.Eventually.of_forall fun q => ?_)
    · rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (norm_kappa_le _ _ _ _ _)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlim q] with N hN
      rw [hN, mul_one]
  exact tendsto_nhds_unique hdct (waldspurger2010_thm_7_9 L hV hV2 ψ I θ hθ f hf τ hτ)

end LuoDatum

end GSpinGGP
