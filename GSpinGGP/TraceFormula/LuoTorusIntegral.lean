/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LuoTorusExp

/-!
# The torus integrals of `m^Lie_geom` and of Luo's `m^Lie_geom`

* `torusIntegralLie_eq_luo`: for a torus `T` of `Γ(G,H)` the integral over `𝔱⁰(F)` is Luo's
  integral over `𝔱(F)` for `φ(T)`, by the change of variables `ad : 𝔱⁰ ≃ 𝔱`, given that `ad`
  carries `𝔱⁰_♮` onto `𝔱_♮` and the germs match;
* `torusIntegralLie_toSO_of`: the conclusion of `torusIntegralLie_toSO` from that matching and the
  invariance of the torus integrals under `GSpin(W)(F)`-conjugation of the torus.
-/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.style.haveILetI false

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

/-- The kernel of `φ : t ↦ (P(t), P(t) ⊕ 1)` on `GSpin(W)(F)` is the scalars `F^×`. -/
theorem ker_toGbarU_comp_diag : (d.toGbarU.comp d.diag).ker = (scalarGSpin d.QW).range := by
  ext t
  rw [MonoidHom.mem_ker, toGbarU_comp_diag_eq_one_iff, ← MonoidHom.mem_ker, ker_specP d.nondeg]

/-- The scalars `F^×` lie in every torus `T_x` and in its conjugates. -/
theorem range_scalarGSpin_le_map_conj (x g : ↥(GSpin d.QW)) :
    (scalarGSpin d.QW).range ≤ (d.torusOf x).map (MulAut.conj g).toMonoidHom := by
  rintro _ ⟨c, rfl⟩
  refine ⟨scalarGSpin d.QW c, d.scalar_mem_torusOf x c, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [(scalarGSpin_commute d.QW c g).eq.symm, mul_inv_cancel_right]

/-- **A conjugate of a torus of `Γ(G,H)` whose image is a torus of Luo's `𝒯` is again a torus of
`Γ(G,H)`**: if `φ(g T_x g⁻¹)` is a Luo torus, it is `φ(T_{x'})` for some `x' ∈ Γ(G,H)`
(`exists_isGammaElt_torusOf_eq_of_luo`), and `T_{x'} = g T_x g⁻¹` as both contain
`ker φ = F^×`. -/
theorem exists_isGammaElt_torusOf_eq_conj {x g : ↥(GSpin d.QW)} (T' : d.luoOf.GammaTorus)
    (hT' : T'.1 = ((d.torusOf x).map (MulAut.conj g).toMonoidHom).map (d.toGbarU.comp d.diag)) :
    ∃ x', d.IsGammaElt x' ∧ d.torusOf x' = (d.torusOf x).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨X, hX, hXT⟩ := T'.2
  obtain ⟨x', hx', hx'X⟩ := d.exists_isGammaElt_torusOf_eq_of_luo hX
  refine ⟨x', hx', Subgroup.map_injective_of_ker_le (f := d.toGbarU.comp d.diag) ?_ ?_ ?_⟩
  · rw [ker_toGbarU_comp_diag]
    rintro _ ⟨c, rfl⟩
    exact d.scalar_mem_torusOf x' c
  · rw [ker_toGbarU_comp_diag]
    exact d.range_scalarGSpin_le_map_conj x g
  · rw [← hx'X, hXT, hT']

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
under `GSpin(W)(F)`-conjugation of the torus (`hconj`). The measures are the `exp`-compatible ones
(`exists_luo_isExpCompatT`); the representative of `e c` is `φ(g T g⁻¹)` with `T` the
representative of `c` (`exists_conj_eq_map_of_isNaturalTorusCorr`), and `g T g⁻¹` is a torus of
`Γ(G,H)` (`exists_isGammaElt_torusOf_eq_conj`), where `torusIntegralLie_eq_luo` applies. -/
theorem torusIntegralLie_toSO_of
    (hnat : ∀ (x : ↥(GSpin d.QW)), d.IsGammaElt x → ∀ X : ↥(d.lieTorus (d.torusOf x)),
      d.IsGammaEltLie (d.torusOf x) X ↔
        d.luoOf.IsNat ((d.torusOf x).map (d.toGbarU.comp d.diag)) (d.toSOLin (d.diagLie X)))
    (hconj : ∀ θ : ↥d.luoOf.lie → ℂ,
      IsLieQuasiCharacter d.luoOf.Gbar d.luoOf.lie d.luoOf.traceForm ψ θ →
      ∀ (x : ↥(GSpin d.QW)), d.IsGammaElt x → ∀ (g : ↥(GSpin d.QW)) (s : ℝ),
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
  obtain ⟨x', hx', hx'T⟩ := d.exists_isGammaElt_torusOf_eq_conj (Quot.out (e c)) hg
  rw [← hconj θ hθ x hx g s, ← hx'T]
  rw [← hx'T] at hg
  exact d.torusIntegralLie_eq_luo ψ hx' (hnat x' hx') (hc ⟨_, x', hx', rfl⟩) hg (hμT _) s

end GGPData

end GSpinGGP
