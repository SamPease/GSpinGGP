/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.Fourier
import GSpinGGP.Literature.Measure
import GSpinGGP.Literature.Parabolic
import GSpinGGP.Literature.TraceFormula
import GSpinGGP.TraceFormula.Lie
import GSpinGGP.Sanity.Witnesses

/-!
# Checks of the measure-theoretic axioms

* `exists_isSelfDual`: its nondegeneracy hypothesis is needed: for `B = 0` on `V = F` no measure
  is self-dual (`not_isSelfDual_zero`); on the zero space the measure it provides is `δ_0`.
* `weil_quotient_radon`: for `S = Γ`, `ι = id`, `μ = ν`, the point mass at the unique coset is a
  Weil measure (`isWeilMeasure_id_dirac`, no axiom), and the axiom's measure equals it
  (`weil_id_eq`); rescaling `μ` by `2` rescales the quotient measure by `2` (`weil_id_two`).
* `integral_eq_mul_integral_compact_integral`: the conclusion is proved for `P = G`, `K = 1` and any
  locally compact second countable group (`integral_formula_top_bot`), and the axiom's
  hypotheses are satisfiable (`P = 1`, `K = G` compact, the circle).
* `bp_integrable_kernel_scusp`: the conclusion holds whenever `A_G = G`
  (`bp_conclusion_of_AG_eq_top`), in particular when `V` is a hyperbolic plane (`G` is a torus,
  the cuspidality hypothesis is vacuous; `bp_conclusion_of_hypPlane`) and on `toyD`
  (`bp_conclusion_toyD`).

Not covered: `weil_quotient_radon` for a proper closed subgroup; the integration formula for a
proper parabolic; `bp_integrable_kernel_scusp` with `G/A_G` noncompact.
-/

open MeasureTheory GSpinGGP Topology

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GSpinGGP.AxiomRedTeam

section SelfDual

/-- The nondegeneracy hypothesis of `exists_isSelfDual` is load-bearing: for `B = 0` on `V = F`
no measure is self-dual (the left side of inversion does not depend on `Z`). -/
theorem not_isSelfDual_zero {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]
    [ProperSpace F] [MeasurableSpace F] (μ : Measure F) (ψ : NontrivialAddChar F) :
    ¬ IsSelfDual μ (0 : LinearMap.BilinForm F F) ψ := by
  rintro ⟨-, h⟩
  classical
  set f : F → ℂ := Set.indicator (Metric.closedBall (0 : F) 1) (fun _ => 1)
  have hf : IsTestFn f := by
    refine ⟨?_, ?_⟩
    · have hs := IsUltrametricDist.isClopen_closedBall (0 : F) (r := 1) one_ne_zero
      rw [IsLocallyConstant.iff_eventually_eq]
      intro x
      by_cases hx : x ∈ Metric.closedBall (0 : F) 1
      · filter_upwards [hs.isOpen.mem_nhds hx] with y hy
        simp [f, Set.indicator_of_mem hy, Set.indicator_of_mem hx]
      · filter_upwards [hs.isClosed.isOpen_compl.mem_nhds hx] with y hy
        simp [f, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
    · exact HasCompactSupport.intro (isCompact_closedBall 0 1)
        (fun x hx => Set.indicator_of_notMem hx _)
  obtain ⟨z, hz⟩ := NormedField.exists_one_lt_norm F
  have h0 := h f hf 0
  have hz' := h f hf z
  simp only [LinearMap.zero_apply, neg_zero] at h0 hz'
  have : f 0 = f z := h0.symm.trans hz'
  simp [f, Set.indicator] at this
  linarith


/-- `exists_isSelfDual` at the zero space: its witness is forced to be `dirac 0`. -/
example {F : Type} [NontriviallyNormedField F] [PAdicField F] [MeasurableSpace (Fin 0 → F)]
    [BorelSpace (Fin 0 → F)] (ψ : NontrivialAddChar F) :
    (exists_isSelfDual (0 : LinearMap.BilinForm F (Fin 0 → F))
      ⟨fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩ ψ).choose =
      Measure.dirac 0 :=
  Sanity.eq_dirac_of_isSelfDual (exists_isSelfDual (0 : LinearMap.BilinForm F (Fin 0 → F))
    ⟨fun _ _ => Subsingleton.elim _ _, fun _ _ => Subsingleton.elim _ _⟩ ψ).choose_spec

end SelfDual

section Weil
variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
  [T2Space Γ] [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ]

local instance subsingleton_cosetSpace_id : Subsingleton (CosetSpace (MonoidHom.id Γ)) :=
  ⟨fun x y => by
    induction x using CosetSpace.ind with | h a => ?_
    induction y using CosetSpace.ind with | h b => ?_
    exact (CosetSpace.mk_eq_mk_iff _ _ _).2 <| (CosetSpace.rel_iff _ _ _).2 ⟨b * a⁻¹, by simp⟩⟩

/-- Axiom-free: for `S = Γ`, `ι = id`, `μ = ν`, the point mass at the unique coset is a Weil
measure (right invariance of `ν`). -/
theorem isWeilMeasure_id_dirac (ν : Measure Γ) [ν.IsMulRightInvariant] :
    IsWeilMeasure (MonoidHom.id Γ) ν ν (Measure.dirac (CosetSpace.mk _ 1)) := by
  intro φ _ _
  have hsm : StronglyMeasurable
      (fun q : CosetSpace (MonoidHom.id Γ) => ∫ s, φ (MonoidHom.id Γ s * CosetSpace.out _ q) ∂ν) :=
    stronglyMeasurable_const' fun a b => by rw [Subsingleton.elim a b]
  rw [integral_dirac' _ _ hsm]
  simp only [MonoidHom.id_apply]
  exact (integral_mul_right_eq_self (μ := ν) φ _).symm

/-- The axiom's measure in this instance is pinned to `dirac`: uniqueness clause + the explicit
witness. Also checks that rescaling `ν` by `2` gives `2 • dirac` (no normalization clash). -/
theorem weil_id_eq (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] :
    (weil_quotient_radon (MonoidHom.id Γ) continuous_id Topology.IsClosedEmbedding.id ν ν).choose =
      Measure.dirac (CosetSpace.mk _ 1) := by
  obtain ⟨hm, huniq⟩ :=
    (weil_quotient_radon (MonoidHom.id Γ) continuous_id Topology.IsClosedEmbedding.id ν
      ν).choose_spec
  exact (huniq _ inferInstance (isWeilMeasure_id_dirac ν)).symm

theorem weil_id_two (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant] :
    ∀ m, IsWeilMeasure (MonoidHom.id Γ) ((2 : ENNReal) • ν) ν m →
      m = (2 : ENNReal) • Measure.dirac (CosetSpace.mk _ 1) := by
  intro m hm
  have h2 := (isWeilMeasure_id_dirac ν).smul_left (2 : ENNReal)
  have : ((2 : ENNReal) • ν).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul ν (by norm_num) (by norm_num)
  exact IsWeilMeasure.unique continuous_id Topology.IsClosedEmbedding.id hm h2

/-- Instantiate at a concrete non-discrete group (`Circle`) so the binder list is satisfiable. -/
example : (weil_quotient_radon (MonoidHom.id Circle) continuous_id Topology.IsClosedEmbedding.id
      (Measure.haar : Measure Circle) Measure.haar).choose = Measure.dirac (CosetSpace.mk _ 1) :=
  weil_id_eq _

end Weil

section Parabolic
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

local instance locallyCompactSpace_top : LocallyCompactSpace ↥(⊤ : Subgroup G) :=
  (show IsClosed ((⊤ : Subgroup G) : Set G) by simp [isClosed_univ]).locallyCompactSpace

/-- Axiom-free proof of the conclusion of `integral_eq_mul_integral_compact_integral` for
`P = ⊤`, `K = ⊥` (any LCSC group, compact or not): `c` is the Haar scalar factor between
`haar_G` and the pushforward of `haar_⊤`. -/
theorem integral_formula_top_bot :
    ∃ c : ℝ, 0 < c ∧ ∀ f : G → ℂ, Continuous f → HasCompactSupport f →
      ∫ x, f x ∂(Measure.haar : Measure G) =
        c * ∫ k : ↥(⊥ : Subgroup G), ∫ p : ↥(⊤ : Subgroup G), f ((p : G) * (k : G))
          ∂(Measure.haar : Measure ↥(⊤ : Subgroup G))
          ∂(Measure.haar : Measure ↥(⊥ : Subgroup G)) := by
  set ι : ↥(⊤ : Subgroup G) →* G := (⊤ : Subgroup G).subtype
  have hemb : IsClosedEmbedding ι :=
    ⟨IsEmbedding.subtypeVal, by simp [ι, Subgroup.coe_subtype, isClosed_univ]⟩
  have hsurj : Function.Surjective ι := fun g => ⟨⟨g, trivial⟩, rfl⟩
  set μT : Measure G := Measure.map ι Measure.haar
  have : μT.IsHaarMeasure :=
    Measure.isHaarMeasure_map _ ι hemb.continuous hsurj hemb.tendsto_cocompact
  set a := Measure.haarScalarFactor (Measure.haar : Measure G) μT
  have ha : 0 < a := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have hG : (Measure.haar : Measure G) = a • μT := Measure.isMulLeftInvariant_eq_smul _ _
  refine ⟨a, ha, fun f _ _ => ?_⟩
  -- the outer integral over the trivial subgroup
  have hbot : ∀ g : ↥(⊥ : Subgroup G) → ℂ,
      ∫ k, g k ∂(Measure.haar : Measure ↥(⊥ : Subgroup G)) = g 1 := by
    intro g
    have : g = fun _ => g 1 := funext fun k => congrArg g (Subsingleton.elim k 1)
    rw [this, integral_const, haar_univ_eq_one_of_subsingleton', one_smul]
  rw [hbot]
  simp only [OneMemClass.coe_one, mul_one]
  have hmap : ∫ x, f x ∂μT = ∫ p : ↥(⊤ : Subgroup G), f (p : G) ∂Measure.haar :=
    hemb.measurableEmbedding.integral_map (fun x => f x)
  rw [← hmap, hG, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]


local instance compactSpace_top_circle : CompactSpace ↥(⊤ : Subgroup Circle) :=
  isCompact_iff_compactSpace.mp (by simpa using isCompact_univ)

/-- The axiom at `G = Circle`, `P = ⊥`, `K = ⊤` (compact `G`): hypotheses satisfiable. -/
example : ∃ c : ℝ, 0 < c ∧ ∀ f : Circle → ℂ, Continuous f → HasCompactSupport f →
      ∫ x, f x ∂(Measure.haar : Measure Circle) =
        c * ∫ k : ↥(⊤ : Subgroup Circle), ∫ p : ↥(⊥ : Subgroup Circle),
          f ((p : Circle) * (k : Circle))
          ∂(Measure.haar : Measure ↥(⊥ : Subgroup Circle))
          ∂(Measure.haar : Measure ↥(⊤ : Subgroup Circle)) :=
  integral_eq_mul_integral_compact_integral ⊥ ⊤ (by simp)
    (fun g => ⟨1, rfl, g, trivial, (one_mul g).symm⟩)

end Parabolic

section BP
variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- Axiom-free: when `V` is a hyperbolic plane (so `G` is a torus, `hcusp` is vacuous, and the
kernel is the constant `∫ f₀ f'`), the conclusion of `bp_integrable_kernel_scusp` still holds,
because `A_G = G` (`AG_eq_top`) and `G/A_G` is a point.  This is the case where a too-small
`A_G` would have made the axiom false. -/
theorem bp_conclusion_of_AG_eq_top (d : GGPData F) (hA : d.AG = ⊤) (f₀ f' : ↥d.G → ℂ) :
    Integrable (fun x : ↥d.G ⧸ d.AG =>
        ∫ g : ↥d.G, f₀ ((Quotient.out x)⁻¹ * g * Quotient.out x) * f' g ∂Measure.haar)
      Measure.haar := by
  have : Subsingleton (↥d.G ⧸ d.AG) :=
    ⟨fun x y => Quotient.inductionOn₂' x y fun _ _ =>
      QuotientGroup.eq.mpr (by rw [hA]; trivial)⟩
  have : IsFiniteMeasure (Measure.haar : Measure (↥d.G ⧸ d.AG)) := by
    constructor
    have h : (Set.univ : Set (↥d.G ⧸ d.AG)) ⊆ {1} := fun x _ => Subsingleton.elim x 1
    exact (measure_mono h).trans_lt (isCompact_singleton.measure_lt_top)
  set k := fun x : ↥d.G ⧸ d.AG =>
        ∫ g : ↥d.G, f₀ ((Quotient.out x)⁻¹ * g * Quotient.out x) * f' g ∂Measure.haar
  have : k = fun _ => k 1 := funext fun x => congrArg k (Subsingleton.elim x 1)
  rw [this]
  exact integrable_const _

/-- `V` a hyperbolic plane: `G` is a torus, `hcusp` is vacuous, the kernel is the constant
`∫ f₀ f'`; the conclusion holds because `A_G = G`. -/
theorem bp_conclusion_of_hypPlane (d : GGPData F) (hV : IsHypPlane d.QV) (f₀ f' : ↥d.G → ℂ) :
    Integrable (fun x : ↥d.G ⧸ d.AG =>
        ∫ g : ↥d.G, f₀ ((Quotient.out x)⁻¹ * g * Quotient.out x) * f' g ∂Measure.haar)
      Measure.haar :=
  bp_conclusion_of_AG_eq_top d (HypVAux.AG_eq_top (d := d) hV) f₀ f'

/-- Unconditional instance: the toy datum (`W = 0`, `V = ⟨z₀⟩`, `G` abelian, `A_G = G`). -/
theorem bp_conclusion_toyD (f₀ f' : ↥(Sanity.toyD (F := F)).G → ℂ) :
    Integrable (fun x : ↥(Sanity.toyD (F := F)).G ⧸ (Sanity.toyD (F := F)).AG =>
        ∫ g, f₀ ((Quotient.out x)⁻¹ * g * Quotient.out x) * f' g ∂Measure.haar)
      Measure.haar :=
  bp_conclusion_of_AG_eq_top _ Sanity.toyD_AG_eq_top f₀ f'

/-- The same statement, typed exactly as the axiom's conclusion (same instances). -/
example (d : GGPData F) (hV : IsHypPlane d.QV) (f₀ : ↥d.G → ℂ) (hf₀ : f₀ ∈ testFunctions ↥d.G)
    (hcusp : ∀ (FW : IsotropicFlag d.QW) (FV : IsotropicFlag d.QV), d.IsProperFlagPair FW FV →
      ∀ p ∈ d.whittB FW FV, ∫ u : ↥(d.whittU FW FV), f₀ (p * u) ∂Measure.haar = 0)
    (f' : ↥d.G → ℂ) (hf' : f' ∈ testFunctions ↥d.G) :
    type_of% (LitTF.bp_integrable_kernel_scusp d f₀ hf₀ hcusp f' hf') :=
  bp_conclusion_of_hypPlane d hV f₀ f'

end BP

end GSpinGGP.AxiomRedTeam
