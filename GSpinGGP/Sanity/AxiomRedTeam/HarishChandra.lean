/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Sanity.AxiomRedTeam.Common
import GSpinGGP.Literature.HarishChandra
import GSpinGGP.Literature.GSpin
import GSpinGGP.Literature.Waldspurger
import GSpinGGP.GGP.Germs

/-!
# Checks of the Harish-Chandra, germ and Waldspurger axioms

Unless said otherwise, each conclusion is verified *without* the axiom at the toy datum `toyD`
(`W = 0`, `V` a line, `G ≅ F^× × F^×`), for the trivial representation.  For `germ_unique` and
`rodier_germ_one` the axiom's own instance at `toyD` is also shown to agree with that computation.

* `dixmier_commutant_scalar`: the commutant of the one-dimensional trivial representation is `ℂ`
  (`scalar_of_C`); for the two-dimensional trivial representation of the trivial group
  (commutant `M₂(ℂ)`, reducible) the axiom gives the same verdict as a direct proof
  (`triv2_not_irreducible`, `triv2_not_irreducible_via_dixmier`).
* `hc_regular_open_dense_conull`: `D^G ≡ 1` on `toyD`, so `G_reg = G` (`toyD_hc_regular_check`).
* `hc_character_exists`, `hc_character_isQuasiCharacter`: `θ_1 = 1` is a quasi-character
  (`toyD_hc_character_exists_check`, `toyD_hc_isQuasiCharacter_check`).
* `emoryTakeda_mult_le_one`: `m(1) = 1` exactly (`toyD_mult_eq_one_check`).
* `germ_unique`: holds at `toyD` for every function, not only quasi-characters
  (`toyD_germ_unique`), with satisfiable hypotheses (`toyD_germ_unique_nonvacuous`).  Two
  consequences of the axiom on any datum: orbit measures of distinct orbits, one of them regular,
  are distinct (`false_of_orbitMeasure_eq`), and `ĵ(O, ·)` is not eventually `0` near `0` on
  regular elements for `O` regular (`germ_unique_forces_jHat_ne_zero`), so an orbit measure of `O`
  in the sense of `IsOrbitMeasure` exists.
* `rodier_germ_one`: the trivial representation has a model for every Whittaker datum of `toyD`,
  and its germ at `1` is `1` (`toyD_rodier_trivialRep`).
* `waldspurger_goodNbhd`: smoke test only (`toyD_goodNbhd_smoke`): its output is consistent with
  the abelian toy group; the exponential-homeomorphism clause is not checked.

Not covered: nonzero nilpotent orbits and nonabelian `G` (only the zero orbit occurs in `toyD`).
-/

open MeasureTheory Topology Filter GSpinGGP GSpinGGP.Sanity

noncomputable section

namespace GSpinGGP.AxiomRedTeam

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## `dixmier_commutant_scalar` -/

theorem scalar_of_C (T : ℂ →L[ℂ] ℂ) : ∃ c : ℂ, T = c • (1 : ℂ →L[ℂ] ℂ) := by
  refine ⟨T 1, ContinuousLinearMap.ext fun v => ?_⟩
  have h := T.map_smul v 1
  simp only [smul_eq_mul, mul_one] at h
  simp [h, mul_comm]

/-- The conclusion of `dixmier_commutant_scalar` for any one-dimensional trivial representation. -/
example (G : Type) [Group G] [TopologicalSpace G] (T : (trivialRep G).H →L[ℂ] (trivialRep G).H) :
    ∃ c : ℂ, T = c • (1 : (trivialRep G).H →L[ℂ] (trivialRep G).H) := scalar_of_C T

/-- `ℂ²`. -/
abbrev E2 := EuclideanSpace ℂ (Fin 2)

theorem E2_e0_ne : (EuclideanSpace.single 0 1 : E2) ≠ 0 := by
  intro h
  have := congrArg (fun v : E2 => v 0) h
  simp at this

theorem E2_e1_not_mem :
    (EuclideanSpace.single 1 1 : E2) ∉ (ℂ ∙ (EuclideanSpace.single 0 1 : E2)) := by
  intro h
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp h
  have := congrArg (fun v : E2 => v 1) ha
  simp at this

/-- The two-dimensional trivial representation of the trivial group: its commutant is `M₂(ℂ)`. -/
abbrev triv2 : UnitaryRep Unit where
  H := E2
  ρ := 1
  unitary_ρ _ := one_mem _
  strongCont _ := continuous_const

theorem triv2_ρ (g : Unit) (v : E2) : triv2.ρ g v = v := by
  have : ((1 : Unit →* (E2 →L[ℂ] E2)) g) = 1 := MonoidHom.one_apply g
  exact congrArg (fun T : E2 →L[ℂ] E2 => T v) this

/-- Direct proof: `triv2` is reducible (the line `ℂ e₀` is invariant). -/
theorem triv2_not_irreducible : ¬ triv2.IsIrreducible := by
  rintro ⟨-, h⟩
  have h' : ∀ W : Submodule ℂ E2, IsClosed (W : Set E2) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => h W hW fun g v hv => (triv2_ρ g v).symm ▸ hv
  rcases h' (ℂ ∙ (EuclideanSpace.single 0 1 : E2)) (Submodule.closed_of_finiteDimensional _)
    with h0 | h1
  · have : (EuclideanSpace.single 0 1 : E2) ∈ (ℂ ∙ (EuclideanSpace.single 0 1 : E2)) :=
      Submodule.mem_span_singleton_self _
    rw [h0, Submodule.mem_bot] at this
    exact E2_e0_ne this
  · exact E2_e1_not_mem (h1 ▸ Submodule.mem_top)

/-- The projection onto the first coordinate; it commutes with `triv2` and is not scalar. -/
def P2 : E2 →L[ℂ] E2 :=
  (EuclideanSpace.proj (0 : Fin 2)).smulRight (EuclideanSpace.single (0 : Fin 2) (1 : ℂ))

theorem P2_not_scalar (c : ℂ) : P2 ≠ c • (1 : E2 →L[ℂ] E2) := by
  intro hc
  have h0 := congrArg (fun T : E2 →L[ℂ] E2 => T (EuclideanSpace.single 0 1) 0) hc
  have h1 := congrArg (fun T : E2 →L[ℂ] E2 => T (EuclideanSpace.single 1 1) 1) hc
  simp [P2] at h0 h1
  rw [← h0] at h1
  exact one_ne_zero h1.symm

/-- The same conclusion through `dixmier_commutant_scalar`. -/
theorem triv2_not_irreducible_via_dixmier : ¬ triv2.IsIrreducible := fun hirr => by
  obtain ⟨c, hc⟩ := dixmier_commutant_scalar triv2 hirr P2 fun g => by
    ext v : 1
    change P2 (triv2.ρ g v) = triv2.ρ g (P2 v)
    rw [triv2_ρ, triv2_ρ]
  exact P2_not_scalar c hc

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

section Toy

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "𝕋" => (toyD (F := F))

/-! ## `hc_regular_open_dense_conull`, `hc_character_*`, `emoryTakeda_mult_le_one` -/

/-- `D^G = 1` on the toy datum (`G` acts trivially on `𝔤`). -/
theorem toyD_hcDisc (x : ↥(𝕋).G) : hcDisc (𝕋) x = 1 := by
  have hconj : ∀ X : (𝕋).ambient, conjAd F (x : (𝕋).ambientˣ) X = X := fun X => by
    rw [conjAd_apply, toyD_ambient_comm ((x : (𝕋).ambientˣ) : (𝕋).ambient) X, mul_assoc,
      Units.mul_inv, mul_one]
  have hst : ∀ X ∈ (𝕋).lie.toSubmodule, conjAd F (x : (𝕋).ambientˣ) X ∈ (𝕋).lie.toSubmodule :=
    fun X hX => by rw [hconj]; exact hX
  unfold hcDisc
  rw [dite_eq_left_of_eq_true (eq_true hst)]
  have h0 : (conjAd F (x : (𝕋).ambientˣ)).toLinearEquiv.toLinearMap.restrict hst = 1 :=
    LinearMap.ext fun v => Subtype.ext (hconj (v : (𝕋).ambient))
  have hrank : lieRank (𝕋).lie = Module.finrank F ↥(𝕋).lie := by
    have hc : ∀ X : ↥(𝕋).lie, Module.finrank F ↥(lieCentralizer (𝕋).lie (X : (𝕋).ambient)) =
        Module.finrank F ↥(𝕋).lie := fun X => by rw [toy_lieCentralizer_eq]
    unfold lieRank
    simp only [hc, ciInf_const]
  rw [h0, sub_self, LinearMap.charpoly_zero, hrank]
  have : Module.finrank F ↥(𝕋).lie.toSubmodule = Module.finrank F ↥(𝕋).lie := rfl
  rw [this, Polynomial.coeff_X_pow_self]

/-- Conclusion of `hc_regular_open_dense_conull` on `toyD`: `G_reg = G`. -/
theorem toyD_hc_regular_check :
    IsOpen {x : ↥(𝕋).G | hcDisc (𝕋) x ≠ 0} ∧ Dense {x : ↥(𝕋).G | hcDisc (𝕋) x ≠ 0} ∧
      (Measure.haar : Measure ↥(𝕋).G) {x : ↥(𝕋).G | hcDisc (𝕋) x ≠ 0}ᶜ = 0 := by
  have : {x : ↥(𝕋).G | hcDisc (𝕋) x ≠ 0} = Set.univ :=
    Set.eq_univ_of_forall fun x => by simp [toyD_hcDisc x]
  rw [this]
  exact ⟨isOpen_univ, dense_univ, by simp⟩

/-- Conclusion of `hc_character_exists` for `(toyD, 1)`. -/
theorem toyD_hc_character_exists_check :
    ∃ θ : ↥(𝕋).G → ℂ, IsCharacterOf (trivialRep ↥(𝕋).G) θ ∧
      ContinuousOn θ {x : ↥(𝕋).G | hcDisc (𝕋) x ≠ 0} :=
  ⟨fun _ => 1, isCharacterOf_trivialRep, continuousOn_const⟩

/-- The constant `1` is a quasi-character of the toy `G` (only the zero orbit, `ĵ(0, ·) = 1`). -/
theorem toyD_isQuasiCharacter_one (ψ : NontrivialAddChar F) :
    IsQuasiCharacter (𝕋).G (𝕋).lie (𝕋).bilin ψ (fun _ => 1) := by
  refine ⟨fun _ _ _ => rfl, fun x _ => ?_⟩
  have hL : (lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient)) ≤ (𝕋).lie := inf_le_left
  have : Subsingleton (NilOrbit (grpCentralizer (𝕋).G (x : (𝕋).ambientˣ))
      (lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient))) :=
    ⟨fun a b => (toyD_nilOrbit_eq_zero _ _ hL a).trans (toyD_nilOrbit_eq_zero _ _ hL b).symm⟩
  have hsd : ∃ μ, IsSelfDual μ (restrictForm (lieCentralizer (𝕋).lie
      ((x : (𝕋).ambientˣ) : (𝕋).ambient)) (𝕋).bilin) ψ := by
    rw [toy_lieCentralizer_eq]
    exact exists_isSelfDual_toyLie ψ
  refine ⟨fun _ => 1, Set.toFinite _, Set.univ, Filter.univ_mem, fun X _ hXL _ y _ => ?_⟩
  rw [finsum_eq_single _ (zeroOrbit _ _) (fun O' hO' => (hO' (Subsingleton.elim _ _)).elim),
    jHat_zeroOrbit_eq_one _ _ _ ψ hsd (toyD_isRegularSS _ hL) hXL, mul_one]

/-- Conclusion of `hc_character_isQuasiCharacter` for `(toyD, 1)`. -/
theorem toyD_hc_isQuasiCharacter_check (ψ : NontrivialAddChar F) :
    IsQuasiCharacter (𝕋).G (𝕋).lie (𝕋).bilin ψ
      (characterOn (trivialRep ↥(𝕋).G) (regularSet (𝕋).G (𝕋).lie)) := by
  rw [toyD_characterOn_trivial]
  exact toyD_isQuasiCharacter_one ψ

/-- On `toyD`, `r = 0`, so `ξ ≡ 1` on `H`. -/
theorem toyD_xi_eq_one (ψ : NontrivialAddChar F) (h : ↥(𝕋).H) : (𝕋).xi ψ.toAddChar h = 1 := by
  have : IsEmpty (Fin (𝕋).r) := inferInstanceAs (IsEmpty (Fin 0))
  have : (𝕋).lam h = 0 := Finset.sum_of_isEmpty _
  simp [GGPData.xi, this]

/-- Conclusion of `emoryTakeda_mult_le_one` for `(toyD, 1)`: `π^∞ ⊆ ℂ`. -/
theorem toyD_mult_le_one_check (ψ : NontrivialAddChar F) :
    GSpinGGP.multiplicity (trivialRep ↥(𝕋).G) (𝕋).H ((𝕋).xi ψ.toAddChar) ≤ 1 := by
  have : FiniteDimensional ℂ (trivialRep ↥(𝕋).G).H := inferInstanceAs (FiniteDimensional ℂ ℂ)
  have h1 : Module.finrank ℂ (trivialRep ↥(𝕋).G).H = 1 := Module.finrank_self ℂ
  have hS : Module.finrank ℂ ↥(smoothVectors (trivialRep ↥(𝕋).G)) ≤ 1 :=
    (Submodule.finrank_le _).trans h1.le
  have hD : Module.finrank ℂ (Module.Dual ℂ ↥(smoothVectors (trivialRep ↥(𝕋).G))) ≤ 1 := by
    rw [Subspace.dual_finrank_eq]; exact hS
  have hE : Module.rank ℂ ↥(equivariantForms (trivialRep ↥(𝕋).G) (𝕋).H ((𝕋).xi ψ.toAddChar))
      ≤ 1 := by
    refine (Submodule.rank_le _).trans ?_
    rw [← Module.finrank_eq_rank]
    exact_mod_cast hD
  unfold GSpinGGP.multiplicity
  calc Cardinal.toENat (Module.rank ℂ _) ≤ Cardinal.toENat 1 := Cardinal.toENat.monotone' hE
    _ = 1 := by simp

/-- Sharp form: the multiplicity of the trivial representation is exactly `1`, so the
Emory–Takeda bound is attained. -/
theorem toyD_mult_eq_one_check (ψ : NontrivialAddChar F) :
    GSpinGGP.multiplicity (trivialRep ↥(𝕋).G) (𝕋).H ((𝕋).xi ψ.toAddChar) = 1 := by
  have hne := (hasModel_iff_multiplicity_ne_zero _ _ _).1
    (trivialRep_hasModel _ (𝕋).H _ (toyD_xi_eq_one ψ))
  rcases Order.le_one_iff.mp (toyD_mult_le_one_check ψ) with h | h
  · exact absurd h hne
  · exact h

/-! ## `germ_unique` -/

/-- **`germ_unique` at `toyD`, for every function `θ`**: two expansions of `θ` at `x` have the
same coefficients, both equal to `θ(x)`. -/
theorem toyD_germ_unique (ψ : NontrivialAddChar F) (θ : ↥(𝕋).G → ℂ) (x : ↥(𝕋).G)
    (c c' : NilOrbit (grpCentralizer (𝕋).G x)
      (lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient)) → ℂ)
    (hc : HasGermExpansion (𝕋).G (𝕋).lie (𝕋).bilin ψ θ x c)
    (hc' : HasGermExpansion (𝕋).G (𝕋).lie (𝕋).bilin ψ θ x c') :
    ∀ O ∈ NilReg (grpCentralizer (𝕋).G x)
      (lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient)), c O = c' O := fun O _ =>
  (toyD_expansion_coeff ψ θ x c hc O).trans (toyD_expansion_coeff ψ θ x c' hc' O).symm

/-- The hypotheses of `germ_unique` are satisfiable at `toyD`: the constant `1` has an expansion
at `1`. -/
theorem toyD_germ_unique_nonvacuous (ψ : NontrivialAddChar F) :
    ∃ c, HasGermExpansion (𝕋).G (𝕋).lie (𝕋).bilin ψ (fun _ => (1 : ℂ)) 1 c := by
  have h := toyD_germ (F := F) ψ (θ := fun _ => (1 : ℂ)) (IsLocallyConstant.const 1) 1
    (zeroOrbit _ _)
  by_contra hne
  unfold germ at h
  rw [if_pos (toyD_mem_nilReg _ _ _), dif_neg hne] at h
  exact zero_ne_one h

/-- The axiom's instance at `toyD` (agrees with `toyD_germ_unique`). -/
example (ψ : NontrivialAddChar F) (θ : ↥(𝕋).G → ℂ) (x : ↥(𝕋).G)
    (hx : IsSS F ((x : (𝕋).ambientˣ) : (𝕋).ambient))
    (c c' : NilOrbit (grpCentralizer (𝕋).G x)
      (lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient)) → ℂ)
    (hc : HasGermExpansion (𝕋).G (𝕋).lie (𝕋).bilin ψ θ x c)
    (hc' : HasGermExpansion (𝕋).G (𝕋).lie (𝕋).bilin ψ θ x c') :
    (∀ O ∈ NilReg _ _, c O = c' O) :=
  germ_unique (𝕋) ψ θ x hx c c' hc hc'

/-! ## `rodier_germ_one` -/

/-- **The conclusion of `rodier_germ_one` at `toyD` for `π = 1`**: for every Whittaker datum
`w` the trivial representation has a `w`-model, and its germ at `1` is `1`. -/
theorem toyD_rodier_trivialRep (ψ : NontrivialAddChar F) (x : ↥(𝕋).G) (hx : x = 1)
    (O : NilOrbit (grpCentralizer (𝕋).G x)
      (lieCentralizer (𝕋).lie ((x : (𝕋).ambientˣ) : (𝕋).ambient)))
    (w : WhittakerDatum (𝕋)) :
    (HasModel (trivialRep ↥(𝕋).G) w.U w.χ →
        germ (𝕋).G (𝕋).lie (𝕋).bilin ψ
          (characterOn (trivialRep ↥(𝕋).G) (regularSet (𝕋).G (𝕋).lie)) x O = 1) ∧
      (¬ HasModel (trivialRep ↥(𝕋).G) w.U w.χ →
        germ (𝕋).G (𝕋).lie (𝕋).bilin ψ
          (characterOn (trivialRep ↥(𝕋).G) (regularSet (𝕋).G (𝕋).lie)) x O = 0) := by
  have hm : HasModel (trivialRep ↥(𝕋).G) w.U w.χ := toy_hasModel_trivial w
  refine ⟨fun _ => ?_, fun h => absurd hm h⟩
  rw [toyD_characterOn_trivial]
  exact toyD_germ ψ (IsLocallyConstant.const 1) x O

/-- The axiom's instance at `toyD` gives the same value. -/
example (ψ : NontrivialAddChar F)
    (O : NilOrbit (grpCentralizer (𝕋).G (1 : ↥(𝕋).G))
      (lieCentralizer (𝕋).lie (((1 : ↥(𝕋).G) : (𝕋).ambientˣ) : (𝕋).ambient)))
    (hO : O ∈ NilReg _ _) :
    germ (𝕋).G (𝕋).lie (𝕋).bilin ψ
      (characterOn (trivialRep ↥(𝕋).G) (regularSet (𝕋).G (𝕋).lie)) 1 O = 1 := by
  obtain ⟨w, hw⟩ := rodier_germ_one (𝕋) toyData_isQuasiSplit ψ 1 rfl O hO
  exact (hw _ toyD_trivialRep_isTempered).1 (toy_hasModel_trivial w)

/-! ## `waldspurger_goodNbhd` -/

/-- **Smoke test of `waldspurger_goodNbhd` at `toyD`**: the neighbourhood `Ω ∋ x` it provides is
compact open with `Ω ⊆ x · exp(𝔤)`, which is true in the abelian toy group; nothing false
follows.  The exponential-homeomorphism clause is not checked. -/
theorem toyD_goodNbhd_smoke (x : ↥(𝕋).G) (hx : IsSS F ((x : (𝕋).ambientˣ) : (𝕋).ambient))
    {ω₀ : Set (𝕋).ambient} (hω₀ : ω₀ ∈ 𝓝 (0 : (𝕋).ambient)) :
    ∃ Ω : Set ↥(𝕋).G, x ∈ Ω ∧ IsOpen Ω ∧ IsCompact Ω ∧
      ∀ g ∈ Ω, ∃ X : (𝕋).ambient, ((g : (𝕋).ambientˣ) : (𝕋).ambient) =
        ((x : (𝕋).ambientˣ) : (𝕋).ambient) * expA F X := by
  obtain ⟨ω, E, Ω, -, h0, -, -, -, -, hEx, ⟨e, he⟩, hΩo, hΩc, -, hΩeq, ⟨K, hK, hΩK⟩, -⟩ :=
    waldspurger_goodNbhd (𝕋) x hx hω₀
  have h1E : (1 : ↥(𝕋).G) ∈ E := by
    have hv := he ⟨0, h0⟩
    rw [expA_zero] at hv
    have : ((e ⟨0, h0⟩ : ↥E) : ↥(𝕋).G) = 1 := Subtype.ext (Units.ext hv)
    rw [← this]; exact (e ⟨0, h0⟩).2
  refine ⟨Ω, ?_, hΩo, ?_, ?_⟩
  · rw [hΩeq]; exact ⟨1, 1, h1E, by simp⟩
  · refine hK.of_isClosed_subset hΩc fun g hg => ?_
    obtain ⟨y, k, hk, rfl⟩ := hΩK g hg
    rw [toyD_G_comm y k, mul_assoc, mul_inv_cancel, mul_one]; exact hk
  · intro g hg
    rw [hΩeq] at hg
    obtain ⟨y, z, hz, rfl⟩ := hg
    obtain ⟨X, hX⟩ := e.surjective ⟨z, hz⟩
    refine ⟨X, ?_⟩
    rw [toyD_G_comm y, mul_assoc, mul_inv_cancel, mul_one, Subgroup.coe_mul, Units.val_mul,
      ← he X, hX]

end Toy

/-! ## Consequences of `germ_unique` on any datum -/

section General

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- `ĵ(O, ·)` depends on `O` only through its orbit measure: `IsJHat` mentions `O` only through
`orbitMeasure`. -/
theorem jHat_eq_of_orbitMeasure_eq {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A]
    [TopologicalSpace A] [IsModuleTopology F A] (G : Subgroup Aˣ) (𝔤 : LieSubalgebra F A)
    (b : LinearMap.BilinForm F A) (ψ : NontrivialAddChar F) (O O' : NilOrbit G 𝔤)
    (h : orbitMeasure G 𝔤 b ψ O = orbitMeasure G 𝔤 b ψ O') :
    jHat G 𝔤 b ψ O = jHat G 𝔤 b ψ O' := by
  have hp : IsJHat G 𝔤 b ψ O = IsJHat G 𝔤 b ψ O' := by
    funext j; unfold IsJHat; rw [h]
  unfold jHat
  funext X
  rw [hp]

/-- Under `germ_unique`, two distinct nilpotent orbits of `𝔤_x`, one of them regular, have
distinct orbit measures (otherwise `ĵ(O, ·) = ĵ(O', ·)` and `θ = 0` has two expansions). -/
theorem false_of_orbitMeasure_eq (d : GGPData F) (ψ : NontrivialAddChar F) (x : ↥d.G)
    (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    (O O' : NilOrbit (grpCentralizer d.G x)
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)))
    (hO : O ∈ NilReg _ _) (hne : O ≠ O')
    (h : orbitMeasure (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))
      d.bilin ψ O = orbitMeasure (grpCentralizer d.G x)
        (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) d.bilin ψ O') : False := by
  classical
  have hj := jHat_eq_of_orbitMeasure_eq (grpCentralizer d.G x)
    (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) d.bilin ψ O O' h
  set c : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))
      → ℂ := fun P => (if P = O then 1 else 0) - (if P = O' then 1 else 0)
  have hfin : (Function.support c).Finite := by
    refine (Set.toFinite ({O, O'} : Set _)).subset fun P hP => ?_
    by_contra hP'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hP'
    exact hP (by simp [c, hP'.1, hP'.2])
  have hexp : HasGermExpansion d.G d.lie d.bilin ψ 0 x c := by
    refine ⟨hfin, Set.univ, Filter.univ_mem, fun X _ _ _ y _ => ?_⟩
    have hsupp : (Function.support fun P => c P * jHat (grpCentralizer d.G x)
        (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) d.bilin ψ P X) ⊆
        (({O, O'} : Finset _) : Set _) := by
      intro P hP
      by_contra h'
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff, not_or] at h'
      exact hP (by simp [c, h'.1, h'.2])
    rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_pair hne]
    simp [c, hne, Ne.symm hne, hj]
  have := germ_unique d ψ 0 x hx c 0 hexp (hasGermExpansion_zero d ψ x) O hO
  simp [c, hne] at this

/-- Under `germ_unique`, for `O` regular, `ĵ(O, ·)` is not eventually `0` near `0` on the regular
semisimple elements of `𝔤_x` (otherwise `0` and `δ_O` are two expansions of `θ = 0`).  Since
`ĵ(O, ·)` is `0` when no orbit measure of `O` exists, this implies that one exists. -/
theorem germ_unique_forces_jHat_ne_zero (d : GGPData F) (ψ : NontrivialAddChar F) (x : ↥d.G)
    (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    (O : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)))
    (hO : O ∈ NilReg (grpCentralizer d.G x)
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))) :
    ∀ ω ∈ 𝓝 (0 : d.ambient), ∃ X ∈ ω, X ∈ lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient) ∧
      IsRegularSS (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) X ∧
      jHat (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))
        d.bilin ψ O X ≠ 0 := by
  classical
  intro ω hω
  by_contra hcon
  push_neg at hcon
  have h0 : HasGermExpansion d.G d.lie d.bilin ψ 0 x 0 :=
    ⟨by simp, ω, hω, fun X _ _ _ y _ => by simp⟩
  have h1 : HasGermExpansion d.G d.lie d.bilin ψ 0 x (Pi.single O 1) := by
    refine ⟨(Set.finite_singleton O).subset fun O' hO' => ?_, ω, hω, fun X hXω hXc hXr y _ => ?_⟩
    · by_contra h; exact hO' (Pi.single_eq_of_ne h _)
    · rw [finsum_eq_single _ O (fun O' hO' => by rw [Pi.single_eq_of_ne hO', zero_mul]),
        Pi.single_eq_same, one_mul, hcon X hXω hXc hXr]
      rfl
  have := germ_unique d ψ 0 x hx 0 (Pi.single O 1) h0 h1 O hO
  simp at this

end General

end GSpinGGP.AxiomRedTeam
