import GSpinGGP.GGP.Triple
import TauCeti.Topology.Algebra.Group.ClosedSubgroup

/-!
# Transporting torus integrals

The integrals `∫_{T(F)/A(F)} f` of `m_{geom,s}` (`torusIntegral`, Thesis §6.5) are taken against the
probability Haar measure `probHaar`.  A continuous group isomorphism `e : T ≃ T'` carrying the
scalars onto the scalars induces a continuous isomorphism `T(F)/A(F) ≃ T'(F)/A'(F)` (Tau Ceti
`ContinuousMulEquiv.quotientCongr`), which carries
probability Haar measure to probability Haar measure (uniqueness of Haar measure).  So
`torusIntegral` is transported along `e`, given the pointwise relation of the integrands
(`torusIntegral_eq_of_mulEquiv`).  Used for the stable rearrangement (Thesis (6.7.2)–(6.7.5)).
-/

open MeasureTheory

namespace GSpinGGP

section ProbHaar

variable (Q : Type*) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [MeasurableSpace Q] [BorelSpace Q]

variable {Q}

/-- A continuous group isomorphism of compact groups carries probability Haar measure to
probability Haar measure (`Measure.isHaarMeasure_eq_of_isProbabilityMeasure`). -/
theorem map_probHaar {R : Type*} [CompactSpace Q] [Group R] [TopologicalSpace R]
    [IsTopologicalGroup R] [MeasurableSpace R] [BorelSpace R] [CompactSpace R] (e : Q ≃ₜ* R) :
    (probHaar Q).map e = probHaar R := by
  have : IsProbabilityMeasure ((probHaar Q).map e) :=
    (Measure.isProbabilityMeasure_map_iff e.continuous.measurable.aemeasurable).mpr inferInstance
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure _ _

end ProbHaar

namespace GGPData

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- **Transport of `torusIntegral`** along a continuous group isomorphism `e : T ≃ T'` carrying the
scalars `A(F) ⊆ T` onto the scalars `A'(F) ⊆ T'`: if the integrands satisfy
`f'(e t) = c · f(t)` on `T` and `f'` is `A'(F)`-invariant on `T'`, then
`∫_{T'/A'} f' = c ∫_{T/A} f` for the probability Haar measures (`map_probHaar`). -/
theorem torusIntegral_eq_of_mulEquiv {d d' : GGPData F} (ψ : NontrivialAddChar F)
    {θ : ↥d.G → ℂ} {θ' : ↥d'.G → ℂ} {T : Subgroup ↥(GSpin d.QW)}
    {T' : Subgroup ↥(GSpin d'.QW)} {s : ℝ} [CompactSpace (d.TorusQuot T)]
    [CompactSpace (d'.TorusQuot T')] (e : ↥T ≃ₜ* ↥T')
    (he : (d.scalarsIn T).map e.toMulEquiv.toMonoidHom = d'.scalarsIn T') (c : ℂ)
    (hrel : ∀ t : ↥T, gammaIntegrand ψ d' θ' T' s (e t : ↥(GSpin d'.QW)) =
      c * gammaIntegrand ψ d θ T s (t : ↥(GSpin d.QW)))
    (hinv : ∀ t a : ↥T', a ∈ d'.scalarsIn T' →
      gammaIntegrand ψ d' θ' T' s ((t * a : ↥T') : ↥(GSpin d'.QW)) =
        gammaIntegrand ψ d' θ' T' s (t : ↥(GSpin d'.QW))) :
    torusIntegral ψ d' θ' T' s = c * torusIntegral ψ d θ T s := by
  let _ : MeasurableSpace (d.TorusQuot T) := borel _
  have _ : BorelSpace (d.TorusQuot T) := ⟨rfl⟩
  let _ : MeasurableSpace (d'.TorusQuot T') := borel _
  have _ : BorelSpace (d'.TorusQuot T') := ⟨rfl⟩
  let E := e.quotientCongr _ _ he
  have hval : ∀ q : d.TorusQuot T,
      gammaIntegrand ψ d' θ' T' s ((Quotient.out (E q) : ↥T') : ↥(GSpin d'.QW)) =
        c * gammaIntegrand ψ d θ T s ((Quotient.out q : ↥T) : ↥(GSpin d.QW)) := by
    intro q
    have hq : ((e (Quotient.out q) : ↥T') : d'.TorusQuot T') = E q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨a, ha, hout⟩ : ∃ a ∈ d'.scalarsIn T', Quotient.out (E q) = e (Quotient.out q) * a := by
      have h := QuotientGroup.leftRel_apply.mp (Quotient.exact (hq.trans (QuotientGroup.out_eq' _).symm))
      exact ⟨_, h, by group⟩
    rw [hout, hinv _ _ ha, hrel]
  change (∫ q, gammaIntegrand ψ d' θ' T' s ((Quotient.out q : ↥T') : ↥(GSpin d'.QW))
      ∂(probHaar (d'.TorusQuot T'))) =
    c * ∫ q, gammaIntegrand ψ d θ T s ((Quotient.out q : ↥T) : ↥(GSpin d.QW))
      ∂(probHaar (d.TorusQuot T))
  rw [← map_probHaar E, ← integral_const_mul]
  exact ((E.toHomeomorph.measurableEmbedding).integral_map _).trans
    (integral_congr_ae (Filter.Eventually.of_forall hval))

end GGPData

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F] in
/-- A generator `x` of the torus class `c` (`T = T_x`, `x ∈ Γ(G,H)`). -/
noncomputable def gammaGen (d : GGPData F) (c : GammaClass d) : ↥(GSpin d.QW) :=
  (Quot.out c).2.choose

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F] in
theorem gammaGen_spec (d : GGPData F) (c : GammaClass d) :
    d.IsGammaElt (gammaGen d c) ∧ d.torusOf (gammaGen d c) = (Quot.out c).1 :=
  (Quot.out c).2.choose_spec

end GSpinGGP
