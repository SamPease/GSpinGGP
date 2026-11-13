/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.AxiomRedTeam.HarishChandra
import GSpinGGP.Literature.BPQuasiCharacter
import GSpinGGP.Foundations.GSpinExp

/-!
# Check of `bp_sqrt_weylDisc_mul_locallyBounded` (BP Prop 4.1.1(ii))

* **V at `toyD`, every quasi-character** (`toyD_locallyBounded`): on the toy datum every
  quasi-character `θ` is locally constant (near `y`, `z = y e^X` with `X = log(y⁻¹ z) ∈ 𝔤` small,
  and the expansion at `y` gives `θ(z) = θ(y) ĵ(0, X) = θ(y)`), and `D^G ≡ 1`, so the conclusion holds
  with `C = ‖θ(y)‖`. Proved without the axiom.
* **Non-vacuity**: the hypothesis holds for `θ = 1` (`toyD_isQuasiCharacter_one`).
* **The restriction to `G_reg(F)` is needed** (junk values): `IsQuasiCharacter` does not constrain
  `θ` off `G_reg(F)`, while `weylDisc` is never `0` there being the absolute value of the trailing
  coefficient of a characteristic polynomial; an unrestricted bound would therefore claim something
  about arbitrary values. On `toyD`, `G_reg = G`, so this is not exercised there.

Not covered: nonabelian `G`, nonzero nilpotent orbits (where `D^G` actually vanishes in the limit).
-/

open MeasureTheory Topology Filter GSpinGGP GSpinGGP.Sanity

noncomputable section

namespace GSpinGGP.AxiomRedTeam

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝕋" => (toyD (F := F))

/-- On `toyD`, a quasi-character is constant near every point. -/
theorem toyD_isQuasiCharacter_eventually_eq (ψ : NontrivialAddChar F) {θ : ↥(𝕋).G → ℂ}
    (hθ : IsQuasiCharacter (𝕋).G (𝕋).lie (𝕋).bilin ψ θ) (y : ↥(𝕋).G) :
    ∀ᶠ z in 𝓝 y, θ z = θ y := by
  haveI := isTopologicalRing_of_moduleTopology F (𝕋).ambient
  have hss : IsSS F ((y : (𝕋).ambientˣ) : (𝕋).ambient) :=
    (show y ∈ regularSet (𝕋).G (𝕋).lie by rw [toy_regularSet_eq_univ]; trivial).1
  obtain ⟨c, hc⟩ := hθ.2 y hss
  have hcoeff := toyD_expansion_coeff ψ θ y c hc
  obtain ⟨-, ω, hω, hexp⟩ := hc
  have hL : (lieCentralizer (𝕋).lie ((y : (𝕋).ambientˣ) : (𝕋).ambient)) ≤ (𝕋).lie := inf_le_left
  haveI : Subsingleton (NilOrbit (grpCentralizer (𝕋).G (y : (𝕋).ambientˣ))
      (lieCentralizer (𝕋).lie ((y : (𝕋).ambientˣ) : (𝕋).ambient))) :=
    ⟨fun a b => (toyD_nilOrbit_eq_zero _ _ hL a).trans (toyD_nilOrbit_eq_zero _ _ hL b).symm⟩
  have hsd : ∃ μ, IsSelfDual μ (restrictForm (lieCentralizer (𝕋).lie
      ((y : (𝕋).ambientˣ) : (𝕋).ambient)) (𝕋).bilin) ψ := by
    rw [toy_lieCentralizer_eq]
    exact exists_isSelfDual_toyLie ψ
  obtain ⟨log, hlogc, hlog1, hexplog⟩ := exists_logA (F := F) (A := (𝕋).ambient)
  -- `X` near `0` with `e^X ∈ G` lies in `𝔤`, and in `ω`
  have hnear : ∀ᶠ X in 𝓝 (0 : (𝕋).ambient), X ∈ ω ∧ ∀ g : ↥(𝕋).G,
      ((g : (𝕋).ambientˣ) : (𝕋).ambient) = expA F X → X ∈ (𝕋).lie :=
    (Filter.inter_mem hω (eventually_mem_lie_of_expA_mem (F := F) (𝕋)))
  have hlogt : Tendsto log (𝓝 1) (𝓝 0) := by
    have := hlogc.tendsto; rwa [hlog1] at this
  have hφ : Continuous fun z : ↥(𝕋).G =>
      ((((y⁻¹ * z : ↥(𝕋).G)) : (𝕋).ambientˣ) : (𝕋).ambient) := by
    have : (fun z : ↥(𝕋).G => ((((y⁻¹ * z : ↥(𝕋).G)) : (𝕋).ambientˣ) : (𝕋).ambient)) =
        fun z => (((y⁻¹ : ↥(𝕋).G) : (𝕋).ambientˣ) : (𝕋).ambient) *
          (((z : ↥(𝕋).G) : (𝕋).ambientˣ) : (𝕋).ambient) := by
      funext z; rfl
    rw [this]
    exact continuous_const.mul (Units.continuous_val.comp continuous_subtype_val)
  have hφy : ((((y⁻¹ * y : ↥(𝕋).G)) : (𝕋).ambientˣ) : (𝕋).ambient) = 1 := by simp
  have hT : Tendsto (fun z : ↥(𝕋).G =>
      ((((y⁻¹ * z : ↥(𝕋).G)) : (𝕋).ambientˣ) : (𝕋).ambient)) (𝓝 y) (𝓝 1) := by
    have := hφ.tendsto y; rwa [hφy] at this
  filter_upwards [hT.eventually (hlogt.eventually hnear), hT.eventually hexplog] with z hz hze
  obtain ⟨hzω, hzlie⟩ := hz
  set X := log ((((y⁻¹ * z : ↥(𝕋).G)) : (𝕋).ambientˣ) : (𝕋).ambient)
  have hXlie : X ∈ (𝕋).lie := hzlie (y⁻¹ * z) hze.symm
  have hXL : X ∈ lieCentralizer (𝕋).lie ((y : (𝕋).ambientˣ) : (𝕋).ambient) := by
    rw [toy_lieCentralizer_eq]; exact hXlie
  have hzX : ((z : (𝕋).ambientˣ) : (𝕋).ambient) =
      ((y : (𝕋).ambientˣ) : (𝕋).ambient) * expA F X := by
    rw [hze]
    simp [← mul_assoc]
  have h := hexp X hzω hXL (toyD_isRegularSS _ hL ⟨X, hXL⟩) z hzX
  rw [finsum_eq_single _ (zeroOrbit _ _) (fun O' hO' => (hO' (Subsingleton.elim _ _)).elim),
    jHat_zeroOrbit_eq_one _ _ _ ψ hsd (toyD_isRegularSS _ hL) hXL, mul_one, hcoeff] at h
  exact h

/-- **The conclusion of `bp_sqrt_weylDisc_mul_locallyBounded` at `toyD`, for every
quasi-character**, proved without the axiom. -/
theorem toyD_locallyBounded (ψ : NontrivialAddChar F) {θ : ↥(𝕋).G → ℂ}
    (hθ : IsQuasiCharacter (𝕋).G (𝕋).lie (𝕋).bilin ψ θ) (y : ↥(𝕋).G) :
    ∃ U ∈ 𝓝 y, ∃ C : ℝ, ∀ z ∈ U, z ∈ regularSet (𝕋).G (𝕋).lie →
      Real.sqrt (weylDisc (𝕋).lie (z : (𝕋).ambientˣ)) * ‖θ z‖ ≤ C :=
  ⟨_, toyD_isQuasiCharacter_eventually_eq ψ hθ y, ‖θ y‖, fun z hz _ => by
    rw [toyD_weylDisc, Real.sqrt_one, one_mul, show θ z = θ y from hz]⟩

/-- The axiom's instance at `toyD` for `θ = 1` (hypotheses satisfiable). -/
example (ψ : NontrivialAddChar F) (y : ↥(𝕋).G) :
    ∃ U ∈ 𝓝 y, ∃ C : ℝ, ∀ z ∈ U, z ∈ regularSet (𝕋).G (𝕋).lie →
      Real.sqrt (weylDisc (𝕋).lie (z : (𝕋).ambientˣ)) * ‖(fun _ => (1 : ℂ)) z‖ ≤ C :=
  bp_sqrt_weylDisc_mul_locallyBounded (𝕋) ψ (toyD_isQuasiCharacter_one ψ) y

end GSpinGGP.AxiomRedTeam
