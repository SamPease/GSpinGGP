/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.LieAudit

/-!
# The slices of the descent to `𝔤⁰` at the toy datum

The four `sorry` statements of `TraceFormula/LieDescent.lean` (`exists_isLieDescentNbhd`,
`kernelK_eq_kernelLie_liftLie`, `isLieScusp_liftLie`, `torusIntegral_eq_torusIntegralLie_liftLie`)
are instantiated at the smallest triple (`toyData`: `W = 0`, `V` a line; neither factor is a
hyperbolic plane, so all four apply) and *proved* there, without them:

* `toyD_isLieDescentNbhd`: `ω = 𝔤⁰ = 0`, `Ω₀ = {1}` is a descent neighbourhood (non-vacuity of
  `IsLieDescentNbhd`), and it is conjugate-small for every `ω₀ ∋ 0`;
* `toyD_kernelK_eq_kernelLie_liftLie`: `K(f, x) = f(1) = K^Lie(f_ω, x)` for every descent
  neighbourhood `ω`;
* `toyD_isLieScusp_liftLie`: `f_ω` is strongly cuspidal (there is no proper parabolic);
* `toyD_torusIntegral_eq_torusIntegralLie_liftLie`: both torus integrals equal `f(1)`.

This checks that the normalizations of `J`, `J^Lie`, `θ_f`, `θ_F` and the two torus integrals
match at the zero orbit, and that the lift `f_ω` takes the value `f(1)` at `0`.

Limits of these checks: at the toy datum `𝔤⁰ = 0`, so they exercise no nonzero nilpotent orbit, no
transport of measures by `exp` (all measures are point masses), no dependence on `s`, and no
correspondence of the orbits chosen by `orbitChoice` and `orbitChoiceLie` beyond the zero orbit.
-/

noncomputable section

open MeasureTheory Topology Filter

open scoped Pointwise

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

namespace Sanity

section LieDescentToy

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝕋" => (toyD (F := F))

/-- `A_G(F)·{1} = G(F)` for the toy datum (`A_G = G`). -/
theorem toyD_AG_mul_one : ((𝕋).AG : Set ↥(𝕋).G) * {1} = Set.univ := by
  rw [Set.mul_singleton]
  simp [toyD_AG_eq_top]

/-- **`ω = 𝔤⁰ = 0`, `Ω₀ = {1}` is a descent neighbourhood of the toy datum.** -/
theorem toyD_isLieDescentNbhd :
    (𝕋).IsLieDescentNbhd (Set.univ : Set ↥(𝕋).lieZero) ({1} : Set ↥(𝕋).G) where
  isOpen := isOpen_univ
  isClosed := isClosed_univ
  zero_mem := Set.mem_univ _
  adLie0_mem _ _ _ := Set.mem_univ _
  compact_mod_conj := ⟨Set.univ, Set.finite_univ.isCompact, fun X _ =>
    ⟨1, X, Set.mem_univ _, Subsingleton.elim _ _⟩⟩
  exp_homeo := by
    letI : Unique ↥(Set.univ : Set ↥(𝕋).lieZero) :=
      { default := ⟨0, Set.mem_univ _⟩, uniq := fun _ => Subsingleton.elim _ _ }
    refine ⟨Homeomorph.homeomorphOfUnique _ _, fun X => ?_⟩
    have hX : ((X : ↥(𝕋).lieZero) : (𝕋).ambient) = 0 :=
      congrArg Subtype.val (Subsingleton.elim (X : ↥(𝕋).lieZero) 0)
    rw [hX, expA_zero_eq_one]
    have h1 : ((Homeomorph.homeomorphOfUnique ↥(Set.univ : Set ↥(𝕋).lieZero)
        ↥({1} : Set ↥(𝕋).G) X : ↥({1} : Set ↥(𝕋).G)) : ↥(𝕋).G) = 1 :=
      Set.mem_singleton_iff.mp (Subtype.mem _)
    rw [h1]
    rfl
  eq_of_mul_AG g hg g' hg' _ _ _ := by
    rw [Set.mem_singleton_iff.mp hg, Set.mem_singleton_iff.mp hg']
  isInvariantClopen := by
    rw [toyD_AG_mul_one]
    exact isInvariantClopen_univ _

/-- **`exists_isLieDescentNbhd` at the toy datum**, proved. -/
theorem toyD_exists_isLieDescentNbhd {ω₀ : Set (𝕋).ambient} (hω₀ : ω₀ ∈ 𝓝 (0 : (𝕋).ambient)) :
    ∃ (ω : Set ↥(𝕋).lieZero) (Ω₀ : Set ↥(𝕋).G),
      (𝕋).IsLieDescentNbhd ω Ω₀ ∧ (𝕋).IsConjSmall ω₀ ω :=
  ⟨_, _, toyD_isLieDescentNbhd, fun X _ => ⟨1, 0, mem_of_mem_nhds hω₀, by
    rw [toyD_lie0_eq_zero X.2]; simp⟩⟩

/-- `f_ω(0) = f(1)` for every descent neighbourhood of the toy datum. -/
theorem toyD_liftLie_zero {ω : Set ↥(𝕋).lieZero} {Ω₀ : Set ↥(𝕋).G}
    (hω : (𝕋).IsLieDescentNbhd ω Ω₀) (f : ↥(𝕋).G → ℂ) : (𝕋).liftLie ω f 0 = f 1 :=
  (𝕋).liftLie_eq f hω.zero_mem (by rw [ZeroMemClass.coe_zero, expA_zero_eq_one]; rfl)

variable (χ : CentralCharOn (toyD (F := F))) (ψ : NontrivialAddChar F)

/-- **`kernelK_eq_kernelLie_liftLie` at the toy datum**, proved: both kernels are `f(1)`. -/
theorem toyD_kernelK_eq_kernelLie_liftLie {ω : Set ↥(𝕋).lieZero} {Ω₀ : Set ↥(𝕋).G}
    (hω : (𝕋).IsLieDescentNbhd ω Ω₀) {f : ↥(𝕋).G → ℂ} (hf : f ∈ ScuspTestFn (𝕋) χ)
    (x : ↥(𝕋).G) : kernelK (𝕋) ψ f x = (𝕋).kernelLie ψ ((𝕋).liftLie ω f) x := by
  rw [toyD_kernelK χ ψ hf.2.1, toyD_kernelLie, toyD_liftLie_zero hω]

/-- **`isLieScusp_liftLie` at the toy datum**, proved. -/
theorem toyD_isLieScusp_liftLie (ω : Set ↥(𝕋).lieZero) (f : ↥(𝕋).G → ℂ) :
    (𝕋).IsLieScusp ((𝕋).liftLie ω f) :=
  toyD_isLieScusp _

/-- The Lie torus integral of the toy datum is `θ(0)`, for every torus. -/
theorem toyD_torusIntegralLie (θ : ↥(𝕋).lieZero → ℂ) (T : Subgroup (GSpin (𝕋).QW)) (s : ℝ) :
    (𝕋).torusIntegralLie ψ θ T s = θ 0 := by
  unfold GGPData.torusIntegralLie
  rw [toyD_measLieTorus_eq, integral_of_subsingleton _ _ 0]
  simp only [measureReal_def, Measure.dirac_apply_of_mem (Set.mem_univ _), ENNReal.toReal_one,
    one_smul]
  unfold GGPData.gammaIntegrandLie
  rw [ite_eq_left (by simpa using toyD_isGammaEltLie_zero _), toyD_weylDiscLie, toyD_deltaLie,
    toyD_germLie0 ψ θ (by simpa using toyD_diagLie_zero)]
  simp

/-- The group torus integral of the toy datum is `θ(1)` (for `θ` locally constant and constant on
`diag(GSpin(W))`). -/
theorem toyD_torusIntegral {θ : ↥(𝕋).G → ℂ} (hθ : IsLocallyConstant θ)
    (hθ1 : ∀ t : GSpin (𝕋).QW, θ ((𝕋).diag t) = θ 1) (c : GammaClass (𝕋)) (s : ℝ) :
    torusIntegral ψ (𝕋) θ (Quot.out c).1 s = θ 1 := by
  unfold torusIntegral
  have hT : (Quot.out c).1 = ⊤ := toyD_gammaTorus_val _
  letI : MeasurableSpace ((𝕋).TorusQuot (Quot.out c).1) := borel _
  haveI : BorelSpace ((𝕋).TorusQuot (Quot.out c).1) := ⟨rfl⟩
  rw [integral_of_subsingleton _ _ 1, probHaar_real_univ, one_smul]
  unfold gammaIntegrand
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨toyD_isGammaElt _, by rw [toyD_torusOf, hT]⟩),
    toyD_weylDisc, toyD_germ ψ hθ, toyD_deltaGGP, hθ1, Real.sqrt_one, Real.one_rpow]
  simp

/-- **`torusIntegral_eq_torusIntegralLie_liftLie` at the toy datum**, proved: both sides are
`c f(1)`, `c = dcScaleAG`. -/
theorem toyD_torusIntegral_eq_torusIntegralLie_liftLie {ω : Set ↥(𝕋).lieZero}
    {Ω₀ : Set ↥(𝕋).G} (hω : (𝕋).IsLieDescentNbhd ω Ω₀) {f : ↥(𝕋).G → ℂ}
    (hf : f ∈ ScuspTestFn (𝕋) χ) (c : GammaClass (𝕋)) (s : ℝ) :
    torusIntegral ψ (𝕋) (thetaF (𝕋) f) (Quot.out c).1 s =
      (𝕋).torusIntegralLie ψ ((𝕋).thetaFLie ψ ((𝕋).liftLie ω f)) (Quot.out c).1 s := by
  rw [toyD_torusIntegralLie, toyD_thetaFLie, Pi.smul_apply, toyD_liftLie_zero hω,
    toyD_thetaF_eq hf.1.continuous]
  exact toyD_torusIntegral ψ (θ := ((𝕋).dcScaleAG.toReal : ℂ) • f)
    (hf.1.comp fun z => ((𝕋).dcScaleAG.toReal : ℂ) * z)
    (fun t => by simp only [Pi.smul_apply, toyD_apply_diag χ hf.2.1]) c s

end LieDescentToy

end Sanity

end GSpinGGP
