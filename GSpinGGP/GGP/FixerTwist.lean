/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.Kottwitz1986
import GSpinGGP.GGP.TwistDescent
import GSpinGGP.GGP.TwistPlane

/-!
# Twists of `W` fixing `W'_x`, and their descent to `S_x`

* `glOf_mem_fixerBar`: the matrix of an `F̄`-isometry of `W` of determinant `1` fixing `W'_x ⊗ F̄`
  lies in `(SO(W)_{W'_x})(F̄) = fixerBar d x` (lift through `P`, `gspin_specP_surjective_SO`).
* `isTwistBy_conj`: changing a twisting cocycle `c` to `h⁻¹ c σ(h)` with `h ∈ SO(W)(F̄)` keeps
  `IsTwistBy`.
* `exists_isTwistBy_torusBar_of_fixerBar`: a twist of `W` by a cocycle in `fixerBar d x` is also a
  twist by a cocycle in `S_x(F̄)`, for `x ∈ Γ(G,H)` (Kottwitz 1986, Lemma 10.2,
  `exists_rel_torusBar_of_fixerBar`).
-/

noncomputable section

open scoped TensorProduct
open Matrix

namespace GSpinGGP

namespace TwistDescent

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

variable {d : GGPData F} {x : ↥(GSpin d.QW)}

/-- An `F̄`-isometry of `W` of determinant `1` fixing `W'_x ⊗ F̄` has its matrix in
`fixerBar d x`: it is `P(g)` for some `g ∈ GSpin(W)(F̄)` (`gspin_specP_surjective_SO`), and `g`
fixes `W'_x ⊗ F̄`. -/
theorem glOf_mem_fixerBar (a : (d.QW.baseChange Kb).IsometryEquiv (d.QW.baseChange Kb))
    (hdet : ((glOf a : GL (Fin d.m) Kb) : Matrix (Fin d.m) (Fin d.m) Kb).det = 1)
    (hfix : ∀ w ∈ (fixedSub x).baseChange Kb, a w = w) : glOf a ∈ d.fixerBar x := by
  have hdet' : LinearMap.det (a.toLinearEquiv : (Kb ⊗[F] (Fin d.m → F)) →ₗ[Kb] _) = 1 := by
    rw [← LinearMap.det_toMatrix (bcBasis F d.m)]
    exact hdet
  obtain ⟨g, hg⟩ := gspin_specP_surjective_SO (d.QW.baseChange Kb)
    (isNondeg_baseChange d.QW d.nondeg) a.toLinearEquiv a.map_app hdet'
  have hga : ∀ w, specPIso g w = a w := fun w => by
    rw [specPIso_apply, hg]; rfl
  refine ⟨g, fun w hw => ?_, ?_⟩
  · change specPIso g w = w
    rw [hga]; exact hfix w hw
  · rw [← glOf_specPIso]; exact glOf_congr hga

/-- The isometry with matrix in `fixerBar d x` fixes `W'_x ⊗ F̄`. -/
theorem apply_eq_self_of_glOf_mem_fixerBar
    (a : (d.QW.baseChange Kb).IsometryEquiv (d.QW.baseChange Kb)) (ha : glOf a ∈ d.fixerBar x)
    {w : Kb ⊗[F] (Fin d.m → F)} (hw : w ∈ (fixedSub x).baseChange Kb) : a w = w := by
  obtain ⟨t, ht, hta⟩ := ha
  rw [apply_eq_of_glOf_eq (e' := specPIso t) (by rw [glOf_specPIso, hta]) w]
  exact ht w hw

/-- **Changing a twisting cocycle by a coboundary in `SO(W)(F̄)`**: if `c` is the cocycle of
`φ : W_{F̄} ≃ W'_{F̄}` and `h = P(g)`, then `h⁻¹ c_σ σ(h)` is the cocycle of `φ ∘ P(g)`. -/
theorem isTwistBy_conj {Q' : QuadraticForm F (Fin d.m → F)} {c : GalF F → GL (Fin d.m) Kb}
    (hc : IsTwistBy d.QW Q' c) {h : GL (Fin d.m) Kb} (hh : h ∈ (specMatFbar d.QW).range) :
    IsTwistBy d.QW Q' (fun σ => h⁻¹ * c σ * galGL d.m σ h) := by
  obtain ⟨φ, hφ⟩ := (isTwistBy_iff _ _ _).1 hc
  obtain ⟨g, rfl⟩ := hh
  refine (isTwistBy_iff _ _ _).2 ⟨(specPIso g).trans φ, fun σ => ?_⟩
  rw [glOf_trans, glOf_specPIso, hφ σ, map_mul]
  group

omit [PAdicField F] in
/-- The matrix action in the rational basis: `bcE (toLin M w) = M *ᵥ bcE w`. -/
theorem bcE_toLin {m : ℕ} (M : Matrix (Fin m) (Fin m) Kb) (w : Kb ⊗[F] (Fin m → F)) :
    InnerTwistAux.bcE m (Matrix.toLin (bcBasis F m) (bcBasis F m) M w) =
      M *ᵥ InnerTwistAux.bcE m w := by
  ext i
  simp [InnerTwistAux.bcE, Matrix.toLin_apply, Module.Basis.equivFun_apply, Matrix.mulVec, dotProduct,
    Finsupp.single_apply]

open TwistPlane in
/-- **`B⁻¹ (R ⊕ 1) B ∈ (SO(W)_{W'_x})(F̄)`** for block coordinates `B` (`Q = Bᵀ (Q₂ ⊕ G₃) B`) in which
`W'_x` lies in the second block, and `R ∈ SO(Q₂)(F̄)` (`glOf_mem_fixerBar`). -/
theorem conj_blockDiagGL_mem_fixerBar {κ : Type*} [Fintype κ] [DecidableEq κ] {n : ℕ}
    (e : Fin n ⊕ κ ≃ Fin d.m) (B : GL (Fin d.m) F) {Q₂ : QuadraticForm F (Fin n → F)}
    {G₃ : Matrix κ κ F}
    (hB : d.QW.toMatrix' = (B : Matrix (Fin d.m) (Fin d.m) F)ᵀ * blockDiag e Q₂.toMatrix' G₃ * B)
    (hfix : ∀ v ∈ fixedSub x, ∀ i, ((B : Matrix (Fin d.m) (Fin d.m) F) *ᵥ v) (e (Sum.inl i)) = 0)
    (R : GL (Fin n) Kb)
    (hR : (R : Matrix (Fin n) (Fin n) Kb)ᵀ * Q₂.toMatrix'.map (algebraMap F Kb) * R =
      Q₂.toMatrix'.map (algebraMap F Kb)) (hRdet : (R : Matrix (Fin n) (Fin n) Kb).det = 1) :
    (Units.map (algebraMap F Kb).mapMatrix.toMonoidHom B)⁻¹ * blockDiagGL e R *
      Units.map (algebraMap F Kb).mapMatrix.toMonoidHom B ∈ d.fixerBar x := by
  classical
  set Bb : GL (Fin d.m) Kb := Units.map (algebraMap F Kb).mapMatrix.toMonoidHom B with hBbdef
  set N : GL (Fin d.m) Kb := blockDiagGL e R with hNdef
  set D : Matrix (Fin d.m) (Fin d.m) Kb :=
    blockDiag e (Q₂.toMatrix'.map (algebraMap F Kb)) (G₃.map (algebraMap F Kb)) with hDdef
  set M : GL (Fin d.m) Kb := Bb⁻¹ * N * Bb with hMdef
  have hBb : (Bb : Matrix (Fin d.m) (Fin d.m) Kb) =
      (B : Matrix (Fin d.m) (Fin d.m) F).map (algebraMap F Kb) := rfl
  have hQ : d.QW.toMatrix'.map (algebraMap F Kb) =
      (Bb : Matrix (Fin d.m) (Fin d.m) Kb)ᵀ * D * Bb := by
    rw [hB, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, ← hBb, hDdef, TwistPlane.blockDiag_map]
  have hND : (N : Matrix (Fin d.m) (Fin d.m) Kb)ᵀ * D * N = D := by
    rw [hNdef, TwistPlane.coe_blockDiagGL, hDdef, TwistPlane.blockDiag_transpose, TwistPlane.blockDiag_mul, TwistPlane.blockDiag_mul, hR]
    simp
  have hBM : (Bb : Matrix (Fin d.m) (Fin d.m) Kb) * M = N * Bb := by
    rw [hMdef, Units.val_mul, Units.val_mul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
  have hgram : (M : Matrix (Fin d.m) (Fin d.m) Kb)ᵀ * d.QW.toMatrix'.map (algebraMap F Kb) * M =
      d.QW.toMatrix'.map (algebraMap F Kb) := by
    rw [hQ]
    obtain ⟨Mm, hMm⟩ : ∃ Mm : Matrix (Fin d.m) (Fin d.m) Kb, Mm = M := ⟨_, rfl⟩
    obtain ⟨Bm, hBm⟩ : ∃ Bm : Matrix (Fin d.m) (Fin d.m) Kb, Bm = Bb := ⟨_, rfl⟩
    obtain ⟨Nm, hNm⟩ : ∃ Nm : Matrix (Fin d.m) (Fin d.m) Kb, Nm = N := ⟨_, rfl⟩
    rw [← hMm, ← hBm]
    rw [← hMm, ← hBm, ← hNm] at hBM
    rw [← hNm] at hND
    calc Mmᵀ * (Bmᵀ * D * Bm) * Mm = (Bm * Mm)ᵀ * D * (Bm * Mm) := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = (Nm * Bm)ᵀ * D * (Nm * Bm) := by rw [hBM]
      _ = Bmᵀ * (Nmᵀ * D * Nm) * Bm := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hND]
  have hglM := glOf_isoOfGL d.QW d.QW M hgram
  rw [← hglM]
  refine glOf_mem_fixerBar _ ?_ ?_
  · rw [hglM, hMdef, Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hNdef,
      TwistPlane.coe_blockDiagGL, TwistPlane.det_blockDiag, hRdet, Matrix.det_one, one_mul, mul_one, ← Matrix.det_mul,
      ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
  · -- `M` fixes the rational vectors of `W'_x`, hence `W'_x ⊗ F̄`
    have hfixM : ∀ v ∈ fixedSub x, (M : Matrix (Fin d.m) (Fin d.m) Kb) *ᵥ ((algebraMap F Kb) ∘ v) =
        (algebraMap F Kb) ∘ v := by
      intro v hv
      have hz : (Bb : Matrix (Fin d.m) (Fin d.m) Kb) *ᵥ ((algebraMap F Kb) ∘ v) =
          (algebraMap F Kb) ∘ ((B : Matrix (Fin d.m) (Fin d.m) F) *ᵥ v) := by
        rw [hBb]; funext i; exact (RingHom.map_mulVec _ _ _ i).symm
      have hNz : (N : Matrix (Fin d.m) (Fin d.m) Kb) *ᵥ
          ((algebraMap F Kb) ∘ ((B : Matrix (Fin d.m) (Fin d.m) F) *ᵥ v)) =
          (algebraMap F Kb) ∘ ((B : Matrix (Fin d.m) (Fin d.m) F) *ᵥ v) := by
        funext k
        obtain ⟨k', rfl⟩ := e.surjective k
        rcases k' with i | j
        · rw [hNdef, coe_blockDiagGL, TwistPlane.blockDiag_mulVec_inl]
          have h0 : (fun j => ((algebraMap F Kb) ∘ ((B : Matrix (Fin d.m) (Fin d.m) F) *ᵥ v))
              (e (Sum.inl j))) = 0 := funext fun j => by simp [hfix v hv j]
          rw [h0, Matrix.mulVec_zero]
          simp [hfix v hv i]
        · rw [hNdef, coe_blockDiagGL, TwistPlane.blockDiag_mulVec_inr, Matrix.one_mulVec]
      rw [hMdef, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz,
        hNz, ← hz, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    intro w hw
    rw [Submodule.baseChange_eq_span] at hw
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, hv, rfl⟩ := hy
      apply (InnerTwistAux.bcE d.m).injective
      have hc : InnerTwistAux.bcE d.m ((TensorProduct.mk F Kb (Fin d.m → F) 1) v) =
          (algebraMap F Kb) ∘ v := by
        ext j
        simp [InnerTwistAux.bcE, bcBasis, Algebra.smul_def]
      change InnerTwistAux.bcE d.m (Matrix.toLin (bcBasis F d.m) (bcBasis F d.m)
        (M : Matrix (Fin d.m) (Fin d.m) Kb) _) = _
      rw [bcE_toLin, hc, hfixM v hv]
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | smul c a _ ha => rw [map_smul, ha]

end TwistDescent

namespace GGPData

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

/-- **Twists fixing `W'_x` descend to `S_x`** (Kottwitz 1986, Lemma 10.2,
`exists_rel_torusBar_of_fixerBar`): for `x ∈ Γ(G,H)`, if `W'` is the twist of `W` by a cocycle with
values in `(SO(W)_{W'_x})(F̄)`, it is also the twist of `W` by a cocycle with values in `S_x(F̄)`. -/
theorem exists_isTwistBy_torusBar_of_fixerBar (d : GGPData F) {x : ↥(GSpin d.QW)}
    (hx : d.IsGammaElt x) {Q' : QuadraticForm F (Fin d.m → F)} (c : GalCocycle (d.fixerBar x))
    (hc : IsTwistBy d.QW Q' c.toFun) :
    ∃ a : GalCocycle (d.torusBarFbar x), IsTwistBy d.QW Q' a.toFun := by
  obtain ⟨a, h, hh, ha⟩ := exists_rel_torusBar_of_fixerBar d x hx c
  obtain ⟨g, -, rfl⟩ := hh
  refine ⟨a, ?_⟩
  have := TwistDescent.isTwistBy_conj hc (h := specMatFbar d.QW g) ⟨g, rfl⟩
  convert this using 1
  funext σ
  exact ha σ

end GGPData

end GSpinGGP
