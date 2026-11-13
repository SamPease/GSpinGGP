/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LuoTorusExp
import GSpinGGP.TraceFormula.LuoTorusConj

/-!
# The torus integrals of `m^Lie_geom` and of Luo's `m^Lie_geom`

* `torusIntegralLie_eq_luo`: for a torus `T` of `Γ(G,H)` the integral over `𝔱⁰(F)` is Luo's
  integral over `𝔱(F)` for `φ(T)`, by the change of variables `ad : 𝔱⁰ ≃ 𝔱`, given that `ad`
  carries `𝔱⁰_♮` onto `𝔱_♮` and the germs match;
* `torusIntegralLie_toSO_of`: the conclusion of `torusIntegralLie_toSO` from that matching and the
  invariance of the torus integrals under `GSpin(W)(F)`-conjugation of the torus;
  `torusIntegralLie_toSO_of_germ_conj`: the same from that matching and the conjugation invariance
  of the germs (`torusIntegralLie_conj_of`).
-/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.style.haveILetI false

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

variable (ψ : NontrivialAddChar F)

/-- **The torus integral over `𝔱⁰(F)` is Luo's integral over `𝔱(F)`** for a torus `T = T_x` of
`Γ(G,H)` and its image `φ(T)`, for any `exp`-compatible `μ'` on `𝔱(F)` (Thesis §12.1; Luo §7.1):
`μ' = ad_* ν(T) dX` (`isExpCompatT_map_lieTorusCLE`, `LuoDatum.IsExpCompatT.unique`), and the
integrands correspond under `X ↦ ad (X, X)` given that `ad` carries `𝔱⁰_♮` onto `𝔱_♮` (`hnat`)
and the germs match (`hc`); `D^G` and `Δ` match by `weylDiscLie_toSOLin`, `deltaLie_eq_delta`. -/
theorem torusIntegralLie_eq_luo {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    (hnat : ∀ X : ↥(d.lieTorus (d.torusOf x)), d.IsGammaEltLie (d.torusOf x) X ↔
      d.luoOf.IsNat ((d.torusOf x).map (d.toGbarU.comp d.diag)) (d.toSOLin (d.diagLie X)))
    {θ : ↥d.luoOf.lie → ℂ}
    (hc : ∀ X : CliffordAlgebra d.QW, d.IsGammaEltLie (d.torusOf x) X →
      d.germLie0 ψ (θ ∘ d.toSO) (d.diagLie X) (d.orbitChoiceLie X) =
        d.luoOf.cTheta ψ θ (d.toSOLin (d.diagLie X)))
    {T' : Subgroup d.luoOf.Ambˣ} (hT' : T' = (d.torusOf x).map (d.toGbarU.comp d.diag))
    {μ' : Measure ↥(d.luoOf.lieTorus T')} (hμ' : d.luoOf.IsExpCompatT T' μ') (s : ℝ) :
    d.torusIntegralLie ψ (θ ∘ d.toSO) (d.torusOf x) s =
      ∫ Y : ↥(d.luoOf.lieTorus T'), d.luoOf.gammaIntegrand ψ θ T' s Y ∂μ' := by
  subst hT'
  obtain ⟨μ, hμ⟩ := d.exists_isExpCompatT ⟨_, x, hx, rfl⟩
  obtain rfl := LuoDatum.IsExpCompatT.unique hμ' (d.isExpCompatT_map_lieTorusCLE hx hμ)
  let e := d.lieTorusCLE (d.torusOf x)
  let eM := e.toHomeomorph.toMeasurableEquiv
  have hmap : μ.map e = μ.map eM := rfl
  unfold torusIntegralLie
  rw [d.measLieTorus_eq hμ, hmap, integral_map_equiv]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  change d.gammaIntegrandLie ψ (θ ∘ d.toSO) (d.torusOf x) s X =
    d.luoOf.gammaIntegrand ψ θ _ s (d.toSOLin (d.diagLie X))
  unfold gammaIntegrandLie LuoDatum.gammaIntegrand
  by_cases h : d.IsGammaEltLie (d.torusOf x) X
  · rw [ite_eq_left h, ite_eq_left ((hnat X).mp h), hc _ h, d.deltaLie_eq_delta,
      d.weylDiscLie_toSOLin (d.diagLie_mem_lieZero X.2.1)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((hnat X).mpr h'))]

/-- **Reduction of `torusIntegralLie_toSO`** to two statements about the tori of `Γ(G,H)`:
`ad` carries `𝔱⁰_♮` onto Luo's `𝔱_♮` (`hnat`), and the torus integrals of `θ ∘ ad` are invariant
under `GSpin(W)(F)`-conjugation of the tori of `Γ(G,H)` (`hconj`). The measures are the
`exp`-compatible ones (`exists_luo_isExpCompatT`); the representative of `e c` is `φ(g T_x g⁻¹)`
with `T_x` the representative of `c` (`exists_conj_eq_map_of_isNaturalTorusCorr`), and
`g T_x g⁻¹ = T_{gxg⁻¹}` is a torus of `Γ(G,H)` (`torusOf_conj`, `isGammaElt_conj`), where
`torusIntegralLie_eq_luo` applies. -/
theorem torusIntegralLie_toSO_of
    (hnat : ∀ (x : ↥(GSpin d.QW)), d.IsGammaElt x → ∀ X : ↥(d.lieTorus (d.torusOf x)),
      d.IsGammaEltLie (d.torusOf x) X ↔
        d.luoOf.IsNat ((d.torusOf x).map (d.toGbarU.comp d.diag)) (d.toSOLin (d.diagLie X)))
    (hconj : ∀ θ : ↥d.luoOf.lie → ℂ,
      IsLieQuasiCharacter d.luoOf.Gbar d.luoOf.lie d.luoOf.traceForm ψ θ →
      ∀ (x g : ↥(GSpin d.QW)), d.IsGammaElt x → ∀ s : ℝ,
        d.torusIntegralLie ψ (θ ∘ d.toSO) ((d.torusOf x).map (MulAut.conj g).toMonoidHom) s =
          d.torusIntegralLie ψ (θ ∘ d.toSO) (d.torusOf x) s)
    (e : GammaClass d ≃ d.luoOf.GammaClass)
    (hen : ∀ c, d.IsNaturalTorusCorr (Quot.out c).1 (Quot.out (e c)).1) :
    ∃ μT : ∀ T : d.luoOf.GammaTorus, Measure ↥(d.luoOf.lieTorus T.1),
      (∀ T, d.luoOf.IsExpCompatT T.1 (μT T)) ∧
      ∀ θ : ↥d.luoOf.lie → ℂ,
        IsLieQuasiCharacter d.luoOf.Gbar d.luoOf.lie d.luoOf.traceForm ψ θ →
        (∀ (T : d.GammaTorus) (X : CliffordAlgebra d.QW), d.IsGammaEltLie T.1 X →
          d.germLie0 ψ (θ ∘ d.toSO) (d.diagLie X) (d.orbitChoiceLie X) =
            d.luoOf.cTheta ψ θ (d.toSOLin (d.diagLie X))) →
        ∀ (c : GammaClass d) (s : ℝ), 0 < s →
          d.torusIntegralLie ψ (θ ∘ d.toSO) (Quot.out c).1 s =
            ∫ X : ↥(d.luoOf.lieTorus (Quot.out (e c)).1),
              d.luoOf.gammaIntegrand ψ θ (Quot.out (e c)).1 s X ∂μT (Quot.out (e c)) := by
  classical
  let μT : ∀ T : d.luoOf.GammaTorus, Measure ↥(d.luoOf.lieTorus T.1) := fun T =>
    if h : ∃ μ, d.luoOf.IsExpCompatT T.1 μ then h.choose else 0
  have hμT : ∀ T, d.luoOf.IsExpCompatT T.1 (μT T) := fun T => by
    have h := d.exists_luo_isExpCompatT T
    simp only [μT, dite_eq_left h]
    exact h.choose_spec
  refine ⟨μT, hμT, fun θ hθ hc c s _ => ?_⟩
  obtain ⟨x, hx, hxT⟩ := (Quot.out c).2
  obtain ⟨g, hg⟩ := d.exists_conj_eq_map_of_isNaturalTorusCorr (Quot.out (e c)) (hen c)
  rw [← hxT] at hg ⊢
  have hx' := d.isGammaElt_conj hx g
  rw [← hconj θ hθ x g hx s, ← d.torusOf_conj]
  rw [← d.torusOf_conj] at hg
  exact d.torusIntegralLie_eq_luo ψ hx' (hnat _ hx') (hc ⟨_, _, hx', rfl⟩) hg (hμT _) s

/-- **Reduction of `torusIntegralLie_toSO`** to `ad` matching `𝔱⁰_♮` with `𝔱_♮` (`hnat`) and the
invariance of the germs `c_{θ, O_X}(X)` of `θ ∘ ad` under `X ↦ g X g⁻¹` on the tori of
`Γ(G,H)` (`hgerm`): `torusIntegralLie_toSO_of` with `torusIntegralLie_conj_of`. When neither `W`
nor `V` is a hyperbolic plane, `hgerm` reduces by `cTheta_toSO` (at `T_x` and at
`T_{gxg⁻¹} = g T_x g⁻¹`) to the invariance of Luo's `c_θ` under conjugation by `φ(g)`. -/
theorem torusIntegralLie_toSO_of_germ_conj
    (hnat : ∀ (x : ↥(GSpin d.QW)), d.IsGammaElt x → ∀ X : ↥(d.lieTorus (d.torusOf x)),
      d.IsGammaEltLie (d.torusOf x) X ↔
        d.luoOf.IsNat ((d.torusOf x).map (d.toGbarU.comp d.diag)) (d.toSOLin (d.diagLie X)))
    (hgerm : ∀ θ : ↥d.luoOf.lie → ℂ,
      IsLieQuasiCharacter d.luoOf.Gbar d.luoOf.lie d.luoOf.traceForm ψ θ →
      ∀ (x g : ↥(GSpin d.QW)), d.IsGammaElt x →
        ∀ X : CliffordAlgebra d.QW, d.IsGammaEltLie (d.torusOf x) X →
          d.germLie0 ψ (θ ∘ d.toSO)
              (d.diagLie (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X *
                (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) :
                  CliffordAlgebra d.QW)))
              (d.orbitChoiceLie (((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X *
                (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) :
                  CliffordAlgebra d.QW))) =
            d.germLie0 ψ (θ ∘ d.toSO) (d.diagLie X) (d.orbitChoiceLie X))
    (e : GammaClass d ≃ d.luoOf.GammaClass)
    (hen : ∀ c, d.IsNaturalTorusCorr (Quot.out c).1 (Quot.out (e c)).1) :
    ∃ μT : ∀ T : d.luoOf.GammaTorus, Measure ↥(d.luoOf.lieTorus T.1),
      (∀ T, d.luoOf.IsExpCompatT T.1 (μT T)) ∧
      ∀ θ : ↥d.luoOf.lie → ℂ,
        IsLieQuasiCharacter d.luoOf.Gbar d.luoOf.lie d.luoOf.traceForm ψ θ →
        (∀ (T : d.GammaTorus) (X : CliffordAlgebra d.QW), d.IsGammaEltLie T.1 X →
          d.germLie0 ψ (θ ∘ d.toSO) (d.diagLie X) (d.orbitChoiceLie X) =
            d.luoOf.cTheta ψ θ (d.toSOLin (d.diagLie X))) →
        ∀ (c : GammaClass d) (s : ℝ), 0 < s →
          d.torusIntegralLie ψ (θ ∘ d.toSO) (Quot.out c).1 s =
            ∫ X : ↥(d.luoOf.lieTorus (Quot.out (e c)).1),
              d.luoOf.gammaIntegrand ψ θ (Quot.out (e c)).1 s X ∂μT (Quot.out (e c)) :=
  d.torusIntegralLie_toSO_of ψ hnat
    (fun θ hθ x g hx s => d.torusIntegralLie_conj_of ψ hx g (hgerm θ hθ x g hx) s) e hen

end GGPData

end GSpinGGP
