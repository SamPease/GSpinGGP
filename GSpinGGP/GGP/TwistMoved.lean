/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.FixerTwist
import GSpinGGP.GGP.BlockCoords

/-!
# Twisting `W''_x` along `S_x`

Statement (S) of Thesis Prop. 6.5.1(iv): for `x ∈ Γ(G,H)` with `W''_x = (W'_x)^⊥` of dimension
`≥ 3`, or an anisotropic plane, some `β ∈ H¹(F, S_x)` twists `W` into a form `W_{q_x(β)} ≇ W`.

Proof: in block coordinates for `W = W''_x ⊥ W'_x` (`exists_blockCoords`), twist the block
`W''_x` into the other form of its dimension and discriminant (`WittParity.exists_other_class`,
`TwistPlane.exists_blockTwist`); the cocycle `B⁻¹ (R_σ ⊕ 1) B` takes values in `SO(W)_{W'_x}(F̄)`
(`conj_blockDiagGL_mem_fixerBar`), so by Kottwitz 1986, Lemma 10.2
(`exists_isTwistBy_torusBar_of_fixerBar`) the twisted form is also a twist by a cocycle in
`S_x(F̄)`; it is not isometric to `W` by Witt cancellation.
-/

noncomputable section

open Module Matrix

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- **A block twist descends to `S_x`**: for `x ∈ Γ(G,H)` and block coordinates `B` for
`W = W''_x ⊥ W'_x` (`W'_x` in the second block), replacing the first block by a form `Q₂'` of the same
discriminant gives a form `Q'_B = Bᵀ (Q₂' ⊕ G₃) B` of the discriminant of `W`, the twist of `W` by a
cocycle with values in `S_x(F̄)` (`TwistPlane.exists_blockTwist_core`,
`conj_blockDiagGL_mem_fixerBar`, Kottwitz 1986, Lemma 10.2). -/
theorem exists_isTwistBy_torusBar_of_blockCoords {d : GGPData F} {x : ↥(GSpin d.QW)}
    (hx : d.IsGammaElt x) {κ : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ}
    (e : Fin n ⊕ κ ≃ Fin d.m) (B : GL (Fin d.m) F) {Q₂ Q₂' : QuadraticForm F (Fin n → F)}
    (hnd' : IsNondeg Q₂') (hdr : QuadClassify.DiscRel Q₂ Q₂') {G₃ : Matrix κ κ F}
    (hG₃ : G₃.IsSymm)
    (hB : d.QW.toMatrix' = (B : Matrix (Fin d.m) (Fin d.m) F)ᵀ *
      TwistPlane.blockDiag e Q₂.toMatrix' G₃ * B)
    (hfix : ∀ v ∈ fixedSub x, ∀ i, ((B : Matrix (Fin d.m) (Fin d.m) F) *ᵥ v) (e (Sum.inl i)) = 0) :
    IsNondeg ((B : Matrix (Fin d.m) (Fin d.m) F)ᵀ * TwistPlane.blockDiag e Q₂'.toMatrix' G₃ *
        B).toQuadraticForm' ∧
      SameDisc d.QW ((B : Matrix (Fin d.m) (Fin d.m) F)ᵀ * TwistPlane.blockDiag e Q₂'.toMatrix' G₃ *
        B).toQuadraticForm' ∧
      ∃ a : GalCocycle (d.torusBarFbar x), IsTwistBy d.QW ((B : Matrix (Fin d.m) (Fin d.m) F)ᵀ *
        TwistPlane.blockDiag e Q₂'.toMatrix' G₃ * B).toQuadraticForm' a.toFun := by
  have hQ₂ := TwistPlane.isNondeg_of_blockDiag d.nondeg e B hB
  obtain ⟨X, hnd, hsd, hgram, hcoc, E, hE, hEX⟩ :=
    TwistPlane.exists_blockTwist_core d.nondeg e B hQ₂ hnd' hdr G₃ hG₃ hB
  let c : GalCocycle (d.fixerBar x) :=
    { toFun := fun σ => X⁻¹ * galGL d.m σ X
      mem' := fun σ => by
        obtain ⟨R, hR, hRdet, hXR⟩ := hcoc σ
        rw [hXR]
        exact TwistDescent.conj_blockDiagGL_mem_fixerBar e B hB hfix R hR hRdet
      cocycle' := fun σ τ => by
        rw [galGL_mul, map_mul, map_inv]
        group
      continuous' := ⟨E, hE, fun σ τ hστ => by rw [hEX σ τ hστ]⟩ }
  have htw : IsTwistBy d.QW _ c.toFun := (TwistDescent.isTwistBy_iff _ _ _).2
    ⟨TwistDescent.isoOfGL d.QW _ X hgram, fun σ => by rw [TwistDescent.glOf_isoOfGL]⟩
  exact ⟨hnd, hsd, d.exists_isTwistBy_torusBar_of_fixerBar hx c htw⟩

/-- **Statement (S) for `W''_x` of dimension `≥ 3` or an anisotropic plane** (Thesis Prop. 6.5.1(iv),
first half; own work, from Kottwitz 1986, Lemma 10.2): for `x ∈ Γ(G,H)`, if `W''_x = (W'_x)^⊥` has
dimension `≥ 3` or is an anisotropic plane, some `β ∈ H¹(F, S_x)` has `W_{q_x(β)} ≇ W`. -/
theorem exists_twistIdx_not_isometric_of_moved {d : GGPData F} (IF : InnerFormSystem d)
    {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    (hn : 3 ≤ finrank F ↥((bform d.QW).orthogonal (fixedSub x)) ∨
      (finrank F ↥((bform d.QW).orthogonal (fixedSub x)) = 2 ∧
        (d.QW.comp ((bform d.QW).orthogonal (fixedSub x)).subtype).Anisotropic)) :
    ∃ β α, TwistIdx IF x β α ∧ ¬ Nonempty (d.QW.IsometryEquiv (IF.twist α).Q') := by
  classical
  set U := (bform d.QW).orthogonal (fixedSub x) with hUdef
  have hdisj := fixedSub_inf_movedSub_of_isSS x hx.1
  have hcW := isCompl_fixedSub_orthogonal d.nondeg x hdisj
  have horth : ∀ u ∈ U, ∀ u' ∈ fixedSub x, bform d.QW u u' = 0 := fun u hu u' hu' => by
    rw [QuadraticMap.associated_isSymm]
    exact hu u' hu'
  obtain ⟨e, B, hB, hfix⟩ := TwistPlane.exists_blockCoords d.QW hcW.symm horth
  set G₃ := QuadraticForm.toMatrix' ((d.QW.comp (fixedSub x).subtype).comp
    (finBasis F (fixedSub x)).equivFun.symm.toLinearMap)
  have hG₃ : G₃.IsSymm := QuadraticForm.isSymm_toMatrix' _
  set Q₂ := (d.QW.comp U.subtype).comp (finBasis F U).equivFun.symm.toLinearMap with hQ₂def
  have hQ₂ : IsNondeg Q₂ := TwistPlane.isNondeg_of_blockDiag d.nondeg e B hB
  have hn' : 3 ≤ finrank F U ∨ (finrank F U = 2 ∧ Q₂.Anisotropic) := by
    rcases hn with h | ⟨h, ha⟩
    · exact Or.inl h
    · refine Or.inr ⟨h, fun v hv => ?_⟩
      have := ha _ hv
      exact (finBasis F U).equivFun.symm.injective (this.trans (map_zero _).symm)
  obtain ⟨Q₂', hnd', hdr, hniso⟩ := WittParity.exists_other_class_of hQ₂ hn'
  obtain ⟨hnd, hsd, a, ha⟩ :=
    exists_isTwistBy_torusBar_of_blockCoords hx e B hnd' hdr hG₃ hB hfix
  obtain ⟨α, ⟨ψ⟩, -⟩ := IF.classify _ hnd hsd
  exact ⟨H1.mk a, α, ⟨a, rfl, TwistDescent.isTwistBy_of_isometryEquiv ψ ha⟩,
    fun ⟨φ⟩ => TwistPlane.not_nonempty_isometryEquiv_blockForm e B hB hniso ⟨φ.trans ψ.symm⟩⟩

end GSpinGGP
