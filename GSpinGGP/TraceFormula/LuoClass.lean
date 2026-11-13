/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LuoWeyl
import GSpinGGP.TraceFormula.LuoJLieExp
import GSpinGGP.TraceFormula.CThetaTransport

/-!
# The classes of tori of `Γ(G,H)` and of Luo's `Γ^Lie(Ḡ, H̄)`; `J^Lie = m^Lie_geom(θ_f)`

* `GGPData.gammaClass_equiv` (L8): `t ↦ (P(t), P(t) ⊕ 1)` induces a bijection between the
  `GSpin(W)(F)`-conjugacy classes of tori `T_x`, `x ∈ Γ(G,H)`, and the `H̄(F)`-conjugacy classes of
  Luo's tori `H''_X`, `X ∈ Γ^Lie(Ḡ, H̄)` (Luo, arXiv:2009.13947v1, §7.1), preserving `|W(T)|`.
  The image of `T_x` is a Luo torus (`exists_luo_isGammaElt_torusOf_eq`) and every Luo torus is one
  (`exists_isGammaElt_torusOf_eq_of_luo`); `GSpin(W)`-conjugate tori have `H̄`-conjugate images,
  since `(P(g), P(g) ⊕ 1) ∈ H̄`; conversely, if the images are conjugate by
  `h = (g, (g ⊕ 1) n) ∈ H̄` (`mem_HbarU_iff`), then `P(T_y) = g P(T_x) g⁻¹`, `g = P(g̃)` with
  `g̃ ∈ GSpin(W)`, and `T_y = g̃ T_x g̃⁻¹` since both contain `ker P = F^×`.  The Weyl groups are
  matched by `weylCardOf_eq_of_isNaturalTorusCorr`.
* `GGPData.distribJLie_eq_mGeomLie_of_luo`: Thesis Thm 12.2.2 on `𝔤⁰`, from Luo Thm 7.3.3 and the
  identifications (L1)–(L9) (`TraceFormula/LuoTransfer.lean` and this file).
-/

noncomputable section

open MeasureTheory Topology Filter

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

/-! ## (L8) The classes of tori -/

/-- `(P(g), P(g) ⊕ 1) ∈ H̄(F)` for `g ∈ GSpin(W)(F)`. -/
theorem toGbarU_comp_diag_mem_HbarU (g : ↥(GSpin d.QW)) :
    d.toGbarU.comp d.diag g ∈ d.luoOf.HbarU := by
  rw [toGbarU_comp_diag, MonoidHom.comp_apply]
  exact Subgroup.subset_closure (Or.inl ⟨_, d.specPU_mem_SOu g, rfl⟩)

/-- **`GSpin(W)(F)`-conjugate tori have `H̄(F)`-conjugate images** under
`t ↦ (P(t), P(t) ⊕ 1)`. -/
theorem exists_conj_map_of_torusConj {T T' : d.GammaTorus} (h : d.TorusConj T T') :
    ∃ h' ∈ d.luoOf.HbarU, T'.1.map (d.toGbarU.comp d.diag) =
      (T.1.map (d.toGbarU.comp d.diag)).map (MulAut.conj h').toMonoidHom := by
  obtain ⟨g, hg⟩ := h
  exact ⟨_, d.toGbarU_comp_diag_mem_HbarU g, by rw [hg, Subgroup.map_map_conj]⟩

/-- **Tori of `Γ(G,H)` with `H̄(F)`-conjugate images are `GSpin(W)(F)`-conjugate.**  Write
`h = (g, (g ⊕ 1) n)` (`mem_HbarU_iff`); the `GL(W)`-components give `P(T') = g P(T) g⁻¹`; lift
`g = P(g̃)` (`exists_specP_eq_of_mem_SOu`); then `T' = g̃ T g̃⁻¹`, since both contain
`ker P = F^×` (`ker_specPU`, `scalar_mem_torusOf`). -/
theorem torusConj_of_conj_map {T T' : d.GammaTorus} {h : d.luoOf.Ambˣ} (hh : h ∈ d.luoOf.HbarU)
    (heq : T'.1.map (d.toGbarU.comp d.diag) =
      (T.1.map (d.toGbarU.comp d.diag)).map (MulAut.conj h).toMonoidHom) :
    d.TorusConj T T' := by
  obtain ⟨g', hg''⟩ := d.exists_specPU_eq_unitFst hh
  have h1 : T'.1.map d.specPU = (T.1.map (MulAut.conj g').toMonoidHom).map d.specPU := by
    rw [← d.map_unitFst_conj_map hg'', ← heq, Subgroup.map_map, unitFst_comp_toGbarU_comp_diag]
  have hsc : ∀ T : d.GammaTorus, (scalarGSpin d.QW).range ≤ T.1 := by
    intro T
    obtain ⟨x, -, hx⟩ := T.2
    rw [← hx]
    rintro _ ⟨c, rfl⟩
    exact d.scalar_mem_torusOf x c
  refine ⟨g', Subgroup.map_injective_of_ker_le (f := d.specPU) ?_ ?_ h1⟩
  · rw [ker_specPU]
    exact hsc T'
  · rw [ker_specPU]
    rintro _ ⟨c, rfl⟩
    refine ⟨scalarGSpin d.QW c, hsc T ⟨c, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [(scalarGSpin_commute d.QW c g').eq.symm, mul_inv_cancel_right]

set_option linter.unusedVariables false in
/-- **(L8) The index sets of `Γ^Lie` agree**: `P` maps the tori `T_x` of `GammaClass d` onto the
tori `H''_X` of Luo's `𝒯` (`T_x(F)/A_{G,H}(F) ≅ H''_X(F)`), compatibly with conjugacy (by
`GSpin(W)(F)`, resp. `H̄(F)`; `N ⊆ H̄` does not normalize a torus of `SO(W)` nontrivially), and
`|N_{GSpin(W)}(T)/Z_{GSpin(W)}(T)| = |N_{H̄}(T)/Z_{H̄}(T)|`: there is a bijection of classes
matching each torus with the conjugacy class of its image (`IsNaturalTorusCorr`).
The class map is `T ↦ [T.map (t ↦ (P(t), P(t) ⊕ 1))]`: well defined by
`exists_conj_map_of_torusConj`, injective by `torusConj_of_conj_map`, onto by
`exists_isGammaElt_torusOf_eq_of_luo`; `|W|` by `weylCardOf_eq_of_isNaturalTorusCorr`.  The
hypotheses `hW`, `hV` are not used. -/
theorem gammaClass_equiv (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) :
    ∃ e : GammaClass d ≃ d.luoOf.GammaClass,
      (∀ c, d.IsNaturalTorusCorr (Quot.out c).1 (Quot.out (e c)).1) ∧
      ∀ c, weylCard d c = d.luoOf.weylCardOf (Quot.out (e c)).1 := by
  have hL := d.luoOf.torusConj_equivalence
  let Φ : d.GammaTorus → d.luoOf.GammaTorus := fun T =>
    ⟨T.1.map (d.toGbarU.comp d.diag), by
      obtain ⟨x, hx, hxT⟩ := T.2
      rw [← hxT]
      exact d.exists_luo_isGammaElt_torusOf_eq hx⟩
  let f : GammaClass d → d.luoOf.GammaClass := Quot.map Φ fun _ _ h =>
    d.exists_conj_map_of_torusConj h
  have hf : Function.Bijective f := by
    refine ⟨fun c₁ c₂ h => ?_, fun c => ?_⟩
    · induction c₁ using Quot.ind with | mk T₁ => ?_
      induction c₂ using Quot.ind with | mk T₂ => ?_
      obtain ⟨h', hh', heq⟩ := hL.eqvGen_iff.1 (Quot.eqvGen_exact h)
      exact Quot.sound (d.torusConj_of_conj_map hh' heq)
    · induction c using Quot.ind with | mk T' => ?_
      obtain ⟨X, hX, hXT⟩ := T'.2
      obtain ⟨x, hx, hxX⟩ := d.exists_isGammaElt_torusOf_eq_of_luo hX
      exact ⟨Quot.mk _ ⟨d.torusOf x, x, hx, rfl⟩,
        congrArg (Quot.mk _) (Subtype.ext (hXT ▸ hxX).symm)⟩
  let e := Equiv.ofBijective f hf
  have hcorr : ∀ c, d.IsNaturalTorusCorr (Quot.out c).1 (Quot.out (e c)).1 := by
    intro c
    have h1 : Quot.mk d.luoOf.TorusConj (Φ (Quot.out c)) = Quot.mk _ (Quot.out (e c)) :=
      (congrArg e (Quot.out_eq c)).trans (Quot.out_eq (e c)).symm
    exact hL.eqvGen_iff.1 (Quot.eqvGen_exact h1)
  exact ⟨e, hcorr, fun c => d.weylCardOf_eq_of_isNaturalTorusCorr (Quot.out c) (hcorr c)⟩

/-! ## `J^Lie = m^Lie_geom(θ_f)` on `𝔤⁰` -/

variable (ψ : NontrivialAddChar F)

/-- **Thesis Thm 12.2.2 on `𝔤⁰`: `J^Lie(f) = m^Lie_geom(θ_f)`** for `f ∈ S_scusp(𝔤⁰(F))`, when
neither `W` nor `V` is a hyperbolic plane: Luo Thm 7.3.3 for the special orthogonal triple
(`luo_lie_geomExpansion_SO`), transported by (L1)–(L9). -/
theorem distribJLie_eq_mGeomLie_of_luo (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    {f : ↥d.lieZero → ℂ} (hf : d.IsLieScusp f) :
    d.distribJLie ψ f = d.mGeomLie ψ (d.thetaFLie ψ f) := by
  have := d.muG_isHaarMeasure hW hV
  obtain ⟨μH, μ𝔥, m, hμH, h𝔥, hm, hJ⟩ :=
    d.exists_JLie_transfer ψ hW hV
  obtain ⟨e, hen, he⟩ := d.gammaClass_equiv hW hV
  obtain ⟨μT, hμT, hT⟩ := d.torusIntegralLie_toSO ψ hW hV e hen
  obtain ⟨θ, ⟨h1, h2, h3⟩, hqc, hlim⟩ :=
    luo_lie_geomExpansion_SO d.luoOf hW hV ψ d.muG μH μ𝔥 h𝔥 m hm μT hμT
      (f ∘ d.toSO.symm) (d.isScusp_toSO hf)
  have hθ : d.IsThetaFLie ψ f (θ ∘ d.toSO) := d.isThetaFLie_of_SO ψ hW hV hf h1 h2 h3
  have hreg := d.isThetaFLie_eqOn_regular ψ
    (d.isThetaFLie_thetaFLie_of_exists ψ ⟨_, hθ⟩) hθ
  rw [d.mGeomLie_congr_regularSet ψ hreg, hJ f hf]
  have hc := fun T X hX => d.cTheta_toSO ψ hW hV hqc T X hX
  have hev : d.luoOf.mGeomLieS ψ μT θ =ᶠ[𝓝[>] (0 : ℝ)] d.mGeomLieS ψ (θ ∘ d.toSO) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (d.mGeomLieS_toSO ψ e he μT (hT θ hqc hc) hs).symm
  exact ((hlim.congr' hev).limUnder_eq).symm

end GGPData

end GSpinGGP
