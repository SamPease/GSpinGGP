/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.Witnesses

/-!
# Shared computations for the axiom checks

Computed without any literature axiom except `exists_isSelfDual` (used for `ĵ(0, ·) = 1`):

* the trivial representation has character `1`: `tr 1(f) = ∫ f` (`traceOf_trivialRep`,
  `isCharacterOf_trivialRep`);
* on the toy datum `toyD` (`W = 0`, `V` a line, `G ≅ F^× × F^×` abelian): the trivial
  representation is tempered (`toyD_trivialRep_isTempered`), its normalized character
  `characterOn 1 G_reg` is the constant `1` (`toyD_characterOn_trivial`), every local expansion of
  any function `θ` at any `x` has coefficient `θ(x)` (`toyD_expansion_coeff`; the only nilpotent
  orbit of `𝔤_x` is `0` and `ĵ(0, ·) = 1`), so the germ of a quasi-character at `x` is its value
  `θ(x)` (`toyD_germ_of_isQC`).
-/

open MeasureTheory GSpinGGP GSpinGGP.Sanity

noncomputable section

namespace GSpinGGP.AxiomRedTeam

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section TrivialRep

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] [TotallyDisconnectedSpace G]

theorem fixedSpace_trivialRep (K : Subgroup G) : fixedSpace (trivialRep G) K = ⊤ :=
  eq_top_iff.2 fun v _ k _ => trivialRep_ρ_apply G k v

theorem opOf_trivialRep {f : G → ℂ} (hf : f ∈ testFunctions G) (v : (trivialRep G).H) :
    opOf (trivialRep G) f v = (∫ g, f g ∂(Measure.haar : Measure G)) • v := by
  rw [opOf_apply _ (opIntegrable_of_mem_testFunctions _ hf)]
  simp_rw [trivialRep_ρ_apply]
  exact integral_smul_const _ _

/-- `tr 1(f) = ∫_G f` for the trivial representation. -/
theorem traceOf_trivialRep {f : G → ℂ} (hf : f ∈ testFunctions G) :
    traceOf (trivialRep G) f = ∫ g, f g ∂(Measure.haar : Measure G) := by
  have hG : ∀ U ∈ nhds (1 : G), ∃ K : Subgroup G,
      IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U := fun U hU => by
    obtain ⟨K, h1, h2, h3⟩ := exists_compactOpenSubgroup_subset isOpen_interior
      (mem_interior_iff_mem_nhds.mpr hU)
    exact ⟨K, h1, h2, h3.trans interior_subset⟩
  obtain ⟨K, hKo, hKc, hKb⟩ := exists_biInvariant hG hf
  have : FiniteDimensional ℂ (trivialRep G).H := inferInstanceAs (FiniteDimensional ℂ ℂ)
  have hTD : TraceDatum (trivialRep G) f K :=
    ⟨hKo, hKc, hKb, inferInstance, fun v hv => opOf_mem_fixedSpace _ hf hKb hv⟩
  rw [traceOf_eq _ _ K hTD]
  have hres : (opOf (trivialRep G) f).toLinearMap.restrict hTD.2.2.2.2 =
      (∫ g, f g ∂(Measure.haar : Measure G)) • LinearMap.id := by
    ext v
    simp only [LinearMap.coe_restrict_apply, ContinuousLinearMap.coe_coe, LinearMap.smul_apply,
      LinearMap.id_coe, id_eq, Submodule.coe_smul]
    exact opOf_trivialRep hf _
  rw [hres, map_smul, LinearMap.trace_id, fixedSpace_trivialRep, finrank_top]
  have : Module.finrank ℂ (trivialRep G).H = 1 := Module.finrank_self ℂ
  simp [this]

/-- The trivial representation has character `1`. -/
theorem isCharacterOf_trivialRep : IsCharacterOf (trivialRep G) (fun _ => (1 : ℂ)) := by
  refine ⟨locallyIntegrable_const 1, fun f hf => ?_⟩
  rw [traceOf_trivialRep hf]
  simp

end TrivialRep

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

section Toy

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝕋" => (toyD (F := F))

local instance : TotallyDisconnectedSpace ↥(𝕋).G := totallyDisconnectedSpace_subgroup F _ _
local instance : SigmaCompactSpace ↥(𝕋).G :=
  subgroup_sigmaCompactSpace_of_isClosed F _ _ (𝕋).isClosed_G

/-- The trivial representation of the toy `G` is tempered (`G` is abelian, hence amenable). -/
theorem toyD_trivialRep_isTempered : IsTempered (trivialRep ↥(𝕋).G) :=
  ⟨trivialRep_isIrreducible _,
    weaklyContainedIn_leftRegular_of_isClosed_comm F _ (𝕋).isClosed_G
      (fun g h => toyD_G_comm g h) _ (trivialRep_ρ_apply _)⟩

/-- The normalized character `θ_1 = characterOn 1 G_reg` of the toy `G` is the constant `1`. -/
theorem toyD_characterOn_trivial :
    characterOn (trivialRep ↥(𝕋).G) (regularSet (𝕋).G (𝕋).lie) = fun _ => 1 := by
  obtain ⟨hch, hcont⟩ := characterOn_spec (trivialRep ↥(𝕋).G) (regularSet (𝕋).G (𝕋).lie)
    ⟨fun _ => 1, isCharacterOf_trivialRep, continuousOn_const⟩
  rw [toy_regularSet_eq_univ, continuousOn_univ] at hcont
  rw [toy_regularSet_eq_univ] at hch ⊢
  exact (Continuous.ae_eq_iff_eq _ hcont continuous_const).1
    (hch.ae_eq isCharacterOf_trivialRep)

/-- On `toyD`, every local expansion of any function `θ` at any `x` has coefficient `θ(x)`:
evaluate the expansion at `X = 0`, where the only orbit is `0` and `ĵ(0, 0) = 1`. -/
theorem toyD_expansion_coeff (ψ : NontrivialAddChar F) (θ : ↥(𝕋).G → ℂ) (x : ↥(𝕋).G)
    (c : NilOrbit (grpCentralizer (𝕋).G (x : (𝕋).ambientˣ))
      (lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient)) → ℂ)
    (hc : HasGermExpansion (𝕋).G (𝕋).lie (𝕋).bilin ψ θ x c) (O) : c O = θ x := by
  have hL : (lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient)) ≤ (𝕋).lie := inf_le_left
  haveI : Subsingleton (NilOrbit (grpCentralizer (𝕋).G (x : (𝕋).ambientˣ))
      (lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient))) :=
    ⟨fun a b => (toyD_nilOrbit_eq_zero _ _ hL a).trans (toyD_nilOrbit_eq_zero _ _ hL b).symm⟩
  have hsd : ∃ μ, IsSelfDual μ (restrictForm (lieCentralizer (𝕋).lie
      ((x : (𝕋).ambientˣ) : (𝕋).ambient)) (𝕋).bilin) ψ := by
    rw [toy_lieCentralizer_eq]
    exact exists_isSelfDual_toyLie ψ
  obtain ⟨-, ω, hω, hexp⟩ := hc
  have h0 := hexp 0 (mem_of_mem_nhds hω) (zero_mem _) (toyD_isRegularSS _ hL 0) x
    (by rw [expA_zero, mul_one])
  rw [finsum_eq_single _ (zeroOrbit _ _) (fun O' hO' => (hO' (Subsingleton.elim _ _)).elim),
    jHat_zeroOrbit_eq_one _ _ _ ψ hsd (toyD_isRegularSS _ hL) (zero_mem _), mul_one,
    ← Subsingleton.elim O (zeroOrbit _ _)] at h0
  exact h0.symm

/-- On `toyD`, the germ of a quasi-character at `x` is its value at `x`. -/
theorem toyD_germ_of_isQC (ψ : NontrivialAddChar F) {θ : ↥(𝕋).G → ℂ}
    (hθ : IsQuasiCharacter (𝕋).G (𝕋).lie (𝕋).bilin ψ θ) (x : ↥(𝕋).G) (O) :
    germ (𝕋).G (𝕋).lie (𝕋).bilin ψ θ x O = θ x := by
  have hss : IsSS F ((x : (𝕋).ambientˣ) : (𝕋).ambient) :=
    (show x ∈ regularSet (𝕋).G (𝕋).lie by rw [toy_regularSet_eq_univ]; trivial).1
  have hE := hθ.2 x hss
  unfold germ
  rw [ite_eq_left_of_eq_true _ _ (eq_true (toyD_mem_nilReg _ _ O)),
    dite_eq_left_of_eq_true (eq_true hE)]
  exact toyD_expansion_coeff ψ θ x _ hE.choose_spec O

end Toy

end GSpinGGP.AxiomRedTeam
