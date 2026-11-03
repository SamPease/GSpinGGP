/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TwistPlane
import GSpinGGP.Foundations.HypPlane
import GSpinGGP.GGP.Steinberg

/-!
# The plane twist lies in the torus `S_x`

Continuation of `GGP/TwistPlane.lean`.  In the coordinates `B` of `exists_planeTwist`, suppose
`P(x)` preserves the anisotropic plane `Π` with determinant `1` and `Π ⊥ W'_x`.  Over `F̄` the plane
is hyperbolic, with a hyperbolic pair `f, f'`; `SO(Π)(F̄)` is the split torus scaling `f, f'` by
`t⁻¹, t`, and its lift `h(t) = f f' + t f' f` (`Foundations/HypPlane.lean`) commutes with `x` and
fixes `W'_x`.  Hence every `B⁻¹ (R ⊕ 1) B` with `R ∈ SO(Q₂)(F̄)` lies in `S_x(F̄)`
(`conj_blockDiagGL_mem_torusBarFbar`).

This needs an `x`-stable plane in `W''_x`: a `2`-dimensional `−1`-eigenspace or a self-reciprocal
quadratic factor of `P(x)|_{W''_x}`.  When every irreducible factor has degree `≥ 4` there is none
(an element `B⁻¹ (R ⊕ 1) B` of `S_x(F̄)` forces `Π_{F̄}` to be spanned by eigenlines of `x`).
-/

noncomputable section

open Matrix CliffordAlgebra
open scoped TensorProduct

namespace GSpinGGP

namespace TwistPlane

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

/-- **The lift of the split torus lies in `T_x(F̄)`.**  Let `f, f'` be a hyperbolic pair of
`W_{F̄}` scaled by `s, s⁻¹` under `P(x)` and orthogonal to `W'_x`.  Then `h(t) = f f' + t f' f`
commutes with `x` and fixes `W'_x`. -/
theorem hypGSpin_mem_torusFbar {d : GGPData F} (x : GSpin d.QW)
    {f f' : Kb ⊗[F] (Fin d.m → F)} (hf : d.QW.baseChange Kb f = 0)
    (hf' : d.QW.baseChange Kb f' = 0) (hp : QuadraticMap.polar (d.QW.baseChange Kb) f f' = 1)
    {s : Kbˣ}
    (hxf : (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb f = (s : Kb) • f)
    (hxf' : (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb f' =
      ((s⁻¹ : Kbˣ) : Kb) • f')
    (horth : ∀ w ∈ (fixedSub x).baseChange Kb,
      QuadraticMap.polar (d.QW.baseChange Kb) f w = 0 ∧
        QuadraticMap.polar (d.QW.baseChange Kb) f' w = 0)
    (t : Kbˣ) : hypGSpin hf hf' hp t ∈ d.torusFbar x := by
  refine ⟨?_, fun w hw => ?_⟩
  · have hc := commute_hypUnit hf hf' hp (g := bcGSpin d.QW x) (s := s)
      (by rw [← LinearEquiv.coe_coe, specP_bcGSpin]; exact hxf)
      (by rw [← LinearEquiv.coe_coe, specP_bcGSpin]; exact hxf') t
    exact Units.ext hc.symm.eq
  · rw [specP_hypGSpin, (horth w hw).1, (horth w hw).2]
    simp only [zero_smul, smul_zero, add_zero]


section Split

variable {m : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ] (e : Fin 2 ⊕ κ ≃ Fin m)
  (B : GL (Fin m) F) {Q : QuadraticForm F (Fin m → F)} {G₂ : Matrix (Fin 2) (Fin 2) F}
  {G₃ : Matrix κ κ F}

/-- The base-changed form, in the coordinates `bcE`, is the form of the Gram matrix. -/
theorem baseChange_eq_toQuadraticForm' (w : Kb ⊗[F] (Fin m → F)) :
    Q.baseChange Kb w =
      (Q.toMatrix'.map (algebraMap F Kb)).toQuadraticForm' (InnerTwistAux.bcE m w) := by
  rw [← InnerTwistAux.toMatrix'_qbar, QuadraticForm.toMatrix'_toQuadraticForm']
  simp [InnerTwistAux.qbar]

omit [PAdicField F] in
theorem isUnit_det_map_transpose (B : GL (Fin m) F) :
    IsUnit (((B : Matrix (Fin m) (Fin m) F).map (algebraMap F Kb))ᵀ).det := by
  rw [det_transpose]
  have h := (Matrix.isUnits_det_units B).map (algebraMap F Kb)
  rw [RingHom.map_det] at h
  exact h

/-- The block-diagonal Gram matrix over `F̄`. -/
abbrev blockBar (G₂ : Matrix (Fin 2) (Fin 2) F) (G₃ : Matrix κ κ F) :
    Matrix (Fin m) (Fin m) Kb :=
  reindex e e (fromBlocks (G₂.map (algebraMap F Kb)) 0 0 (G₃.map (algebraMap F Kb)))

/-- `W_{F̄} ≃ Π_{F̄} ⊥ Π^⊥_{F̄}` in the coordinates `B` (`Q.toMatrix' = Bᵀ (G₂ ⊕ G₃) B`). -/
def splitIso (hB : Q.toMatrix' = (B : Matrix (Fin m) (Fin m) F)ᵀ * blockDiag e G₂ G₃ * B) :
    (Q.baseChange Kb).IsometryEquiv ((G₂.map (algebraMap F Kb)).toQuadraticForm'.prod
      (G₃.map (algebraMap F Kb)).toQuadraticForm') where
  toLinearEquiv := (InnerTwistAux.bcE m).trans
    ((Matrix.isometryEquivCongr (isUnit_det_map_transpose B) (blockBar e G₂ G₃)).toLinearEquiv.trans
      ((Matrix.isometryEquivReindex e
          (fromBlocks (G₂.map (algebraMap F Kb)) 0 0
            (G₃.map (algebraMap F Kb)))).toLinearEquiv.trans
        (Matrix.isometryEquivFromBlocks (G₂.map (algebraMap F Kb))
          (G₃.map (algebraMap F Kb))).toLinearEquiv))
  map_app' w := by
    have hG : Q.toMatrix'.map (algebraMap F Kb) =
        ((B : Matrix (Fin m) (Fin m) F).map (algebraMap F Kb))ᵀ * blockBar e G₂ G₃ *
          ((B : Matrix (Fin m) (Fin m) F).map (algebraMap F Kb))ᵀᵀ := by
      rw [hB, Matrix.transpose_transpose, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
        blockDiag_map]
      rfl
    change ((G₂.map (algebraMap F Kb)).toQuadraticForm'.prod
      (G₃.map (algebraMap F Kb)).toQuadraticForm') ((Matrix.isometryEquivFromBlocks
        (G₂.map (algebraMap F Kb)) (G₃.map (algebraMap F Kb)))
        ((Matrix.isometryEquivReindex e
          (fromBlocks (G₂.map (algebraMap F Kb)) 0 0 (G₃.map (algebraMap F Kb))))
          ((Matrix.isometryEquivCongr (isUnit_det_map_transpose B) (blockBar e G₂ G₃))
            (InnerTwistAux.bcE m w)))) = _
    rw [QuadraticMap.IsometryEquiv.map_app, QuadraticMap.IsometryEquiv.map_app,
      QuadraticMap.IsometryEquiv.map_app, baseChange_eq_toQuadraticForm', hG]

theorem splitIso_apply (hB : Q.toMatrix' = (B : Matrix (Fin m) (Fin m) F)ᵀ * blockDiag e G₂ G₃ * B)
    (w : Kb ⊗[F] (Fin m → F)) :
    splitIso e B hB w =
      (fun i => (((B : Matrix (Fin m) (Fin m) F).map (algebraMap F Kb)) *ᵥ
          InnerTwistAux.bcE m w) (e (Sum.inl i)),
        fun j => (((B : Matrix (Fin m) (Fin m) F).map (algebraMap F Kb)) *ᵥ
          InnerTwistAux.bcE m w) (e (Sum.inr j))) := rfl

end Split



/-- The coordinates of a base-changed endomorphism. -/
theorem bcE_baseChange {m : ℕ} (L : (Fin m → F) →ₗ[F] (Fin m → F)) (w : Kb ⊗[F] (Fin m → F)) :
    InnerTwistAux.bcE m (L.baseChange Kb w) =
      (LinearMap.toMatrix' L).map (algebraMap F Kb) *ᵥ InnerTwistAux.bcE m w := by
  have htm : ∀ (z : Kb) (u : Fin m → F),
      InnerTwistAux.bcE m (z ⊗ₜ[F] u) = fun i => z * algebraMap F Kb (u i) := fun z u => by
    ext i
    simp [InnerTwistAux.bcE, bcBasis, Algebra.smul_def, mul_comm]
  induction w using TensorProduct.inductionOn with
  | tmul z u =>
    rw [LinearMap.baseChange_tmul, htm, htm]
    ext i
    simp only [mulVec, dotProduct, Matrix.map_apply]
    rw [← Matrix.toLin'_toMatrix' L, Matrix.toLin'_apply, LinearMap.toMatrix'_toLin']
    simp only [mulVec, dotProduct, map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  | add w₁ w₂ h₁ h₂ => simp only [map_add, h₁, h₂, mulVec_add]

/-- **The plane twist lies in `S_x`.**  In the coordinates of `exists_planeTwist`, suppose `P(x)`
is block-diagonal, `B P(x) = (A ⊕ C) B` with `A ∈ SO(Q₂)(F)`, and `W'_x ⊆ Π^⊥` (the
`Π`-coordinates of a fixed vector vanish).  Then `B⁻¹ (R ⊕ 1) B ∈ S_x(F̄)` for every
`R ∈ SO(Q₂)(F̄)`.  (`hA` follows from `hx`, `hB` and `P(x)` being an isometry; it is kept as a
hypothesis for convenience.) -/
theorem conj_blockDiagGL_mem_torusBarFbar {d : GGPData F} (x : GSpin d.QW) {κ : Type*}
    [Fintype κ] [DecidableEq κ] (e : Fin 2 ⊕ κ ≃ Fin d.m) (B : GL (Fin d.m) F)
    {Q₂ : QuadraticForm F (Fin 2 → F)} (hQ₂ : IsNondeg Q₂) {G₃ : Matrix κ κ F}
    (hB : d.QW.toMatrix' = (B : Matrix (Fin d.m) (Fin d.m) F)ᵀ * blockDiag e Q₂.toMatrix' G₃ * B)
    {A : Matrix (Fin 2) (Fin 2) F} {C : Matrix κ κ F} (hA : Aᵀ * Q₂.toMatrix' * A = Q₂.toMatrix')
    (hAdet : A.det = 1)
    (hx : (B : Matrix (Fin d.m) (Fin d.m) F) *
      LinearMap.toMatrix' (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) = blockDiag e A C * B)
    (hfix : ∀ v ∈ fixedSub x, ∀ i, ((B : Matrix (Fin d.m) (Fin d.m) F) *ᵥ v) (e (Sum.inl i)) = 0)
    (R : GL (Fin 2) Kb)
    (hR : (R : Matrix (Fin 2) (Fin 2) Kb)ᵀ * Q₂.toMatrix'.map (algebraMap F Kb) * R =
      Q₂.toMatrix'.map (algebraMap F Kb)) (hRdet : (R : Matrix (Fin 2) (Fin 2) Kb).det = 1) :
    (Units.map (algebraMap F Kb).mapMatrix.toMonoidHom B)⁻¹ * blockDiagGL e R *
      Units.map (algebraMap F Kb).mapMatrix.toMonoidHom B ∈ d.torusBarFbar x := by
  classical
  set q₂ : QuadraticForm Kb (Fin 2 → Kb) := (Q₂.toMatrix'.map (algebraMap F Kb)).toQuadraticForm'
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ, Ψ = splitIso e B hB := ⟨_, rfl⟩
  -- a hyperbolic pair of the plane over `F̄`
  have hq₂ : IsNondeg q₂ := by
    rw [InnerTwistAux.isNondeg_iff_discr'_ne_zero, QuadraticForm.discr',
      Matrix.toMatrix'_toQuadraticForm' ((QuadraticForm.isSymm_toMatrix' Q₂).map _),
      show (Q₂.toMatrix'.map (algebraMap F Kb)).det = algebraMap F Kb Q₂.toMatrix'.det from
        (RingHom.map_det _ _).symm]
    exact (map_ne_zero _).2 ((InnerTwistAux.isNondeg_iff_discr'_ne_zero Q₂).1 hQ₂)
  obtain ⟨f₀, hf₀0, hf₀⟩ := QuadClassify.exists_isotropic_of_isSquare q₂ (IsAlgClosed.isSquare _)
  obtain ⟨f₀', hf₀', hp₀⟩ := exists_hyperbolicPair_of_isotropic hq₂ hf₀0 hf₀
  have hdim : Module.finrank Kb (Fin 2 → Kb) = 2 := Module.finrank_fin_fun Kb
  -- `R` and `A` are the split torus in the pair `f₀, f₀'`
  have hRiso : ∀ v, q₂ (Matrix.toLin' (R : Matrix (Fin 2) (Fin 2) Kb) v) = q₂ v := fun v => by
    rw [Matrix.toLin'_apply, toQuadraticForm'_mulVec, hR]
  obtain ⟨t, hRf, hRf'⟩ := exists_smul_of_isometry_det_one hdim hf₀ hf₀' hp₀
    (Matrix.toLin' (R : Matrix (Fin 2) (Fin 2) Kb)) hRiso (by rw [LinearMap.det_toLin', hRdet])
  have hAiso : ∀ v, q₂ (Matrix.toLin' (A.map (algebraMap F Kb)) v) = q₂ v := fun v => by
    rw [Matrix.toLin'_apply, toQuadraticForm'_mulVec, ← Matrix.transpose_map, ← Matrix.map_mul,
      ← Matrix.map_mul, hA]
  obtain ⟨s, hAf, hAf'⟩ := exists_smul_of_isometry_det_one hdim hf₀ hf₀' hp₀
    (Matrix.toLin' (A.map (algebraMap F Kb))) hAiso (by
      rw [LinearMap.det_toLin', show (A.map (algebraMap F Kb)).det = algebraMap F Kb A.det from
        (RingHom.map_det _ _).symm, hAdet, map_one])
  -- the hyperbolic pair in `W_{F̄}`
  set f := Ψ.symm (f₀, 0) with hfdef
  set f' := Ψ.symm (f₀', 0) with hf'def
  have hf : d.QW.baseChange Kb f = 0 := by
    rw [hfdef, QuadraticMap.IsometryEquiv.map_app]; simpa using hf₀
  have hf' : d.QW.baseChange Kb f' = 0 := by
    rw [hf'def, QuadraticMap.IsometryEquiv.map_app]; simpa using hf₀'
  have hp : QuadraticMap.polar (d.QW.baseChange Kb) f f' = 1 := by
    rw [hfdef, hf'def, QuadraticMap.IsometryEquiv.polar_apply, QuadraticMap.polar_prod, hp₀]
    simp
  -- `Ψ` intertwines `P(x)` with `A ⊕ C`
  have hΨx : ∀ w, Ψ ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb w) =
      (A.map (algebraMap F Kb) *ᵥ (Ψ w).1, C.map (algebraMap F Kb) *ᵥ (Ψ w).2) := fun w => by
    have hxb : (B : Matrix (Fin d.m) (Fin d.m) F).map (algebraMap F Kb) *
        (LinearMap.toMatrix' (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F))).map
          (algebraMap F Kb) = blockDiag e (A.map (algebraMap F Kb)) (C.map (algebraMap F Kb)) *
            (B : Matrix (Fin d.m) (Fin d.m) F).map (algebraMap F Kb) := by
      rw [← Matrix.map_mul, hx, Matrix.map_mul, blockDiag_map]
    rw [hΨ, splitIso_apply, splitIso_apply, bcE_baseChange, mulVec_mulVec, hxb, ← mulVec_mulVec]
    ext i
    · exact blockDiag_mulVec_inl e _ _ _ i
    · exact blockDiag_mulVec_inr e _ _ _ i
  -- `W'_x ⊆ Π^⊥`
  have hΨfix : ∀ w ∈ (fixedSub x).baseChange Kb, (Ψ w).1 = 0 := by
    intro w hw
    rw [Submodule.baseChange_eq_span] at hw
    induction hw using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨v, hv, rfl⟩ := hy
      rw [hΨ, splitIso_apply]
      ext i
      have hc : InnerTwistAux.bcE d.m ((TensorProduct.mk F Kb (Fin d.m → F) 1) v) =
          (algebraMap F Kb) ∘ v := by
        ext j
        simp [InnerTwistAux.bcE, bcBasis, Algebra.smul_def]
      simp only [hc]
      rw [← RingHom.map_mulVec, hfix v hv i, map_zero, Pi.zero_apply]
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, Prod.fst_add, ha, hb, add_zero]
    | smul c a _ ha => rw [map_smul, Prod.smul_fst, ha, smul_zero]
  have horth : ∀ w ∈ (fixedSub x).baseChange Kb,
      QuadraticMap.polar (d.QW.baseChange Kb) f w = 0 ∧
        QuadraticMap.polar (d.QW.baseChange Kb) f' w = 0 := fun w hw => by
    have h1 : w = Ψ.symm (Ψ w) := (Ψ.symm_apply_apply w).symm
    rw [h1, hfdef, hf'def, QuadraticMap.IsometryEquiv.polar_apply,
      QuadraticMap.IsometryEquiv.polar_apply, QuadraticMap.polar_prod, QuadraticMap.polar_prod,
      hΨfix w hw]
    simp
  -- `x` scales the pair by `s⁻¹, s`
  have hΨsmul : ∀ (c : Kb) (p : (Fin 2 → Kb) × (κ → Kb)), Ψ.symm (c • p) = c • Ψ.symm p :=
    fun c p => map_smul Ψ.symm.toLinearEquiv c p
  have hxf : (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb f =
      (((s⁻¹ : Kbˣ)) : Kb) • f := by
    refine Ψ.injective ?_
    change Ψ _ = Ψ _
    rw [hΨx, hfdef, Ψ.apply_symm_apply, ← hΨsmul, Ψ.apply_symm_apply]
    simp only [← Matrix.toLin'_apply, hAf, map_zero, Prod.smul_mk, smul_zero]
  have hxf' : (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb f' =
      ((((s⁻¹ : Kbˣ))⁻¹ : Kbˣ) : Kb) • f' := by
    refine Ψ.injective ?_
    change Ψ _ = Ψ _
    rw [hΨx, hf'def, Ψ.apply_symm_apply, ← hΨsmul, Ψ.apply_symm_apply, inv_inv]
    simp only [← Matrix.toLin'_apply, hAf', map_zero, Prod.smul_mk, smul_zero]
  have hmem := hypGSpin_mem_torusFbar x hf hf' hp hxf hxf' horth t
  -- `h(t)` acts as `R ⊕ 1`
  have hΨh : ∀ w, Ψ (specP _ (hypGSpin hf hf' hp t) w) =
      (Matrix.toLin' (R : Matrix (Fin 2) (Fin 2) Kb) (Ψ w).1, (Ψ w).2) := fun w => by
    have hw : w = Ψ.symm (Ψ w) := (Ψ.symm_apply_apply w).symm
    have hpol : ∀ g₀ : Fin 2 → Kb, QuadraticMap.polar (d.QW.baseChange Kb) (Ψ.symm (g₀, 0)) w =
        QuadraticMap.polar q₂ g₀ (Ψ w).1 := fun g₀ => by
      conv_lhs => rw [hw]
      rw [QuadraticMap.IsometryEquiv.polar_apply, QuadraticMap.polar_prod]
      simp only [QuadraticMap.polar_zero_left, add_zero]
      rfl
    rw [specP_hypGSpin, hfdef, hf'def, hpol, hpol,
      apply_eq_of_smul_hyperbolicPair hdim hf₀ hf₀' hp₀ _ hRf hRf']
    simp only [map_add, map_smul, Ψ.apply_symm_apply, Prod.smul_mk, smul_zero]
    refine Prod.ext ?_ ?_ <;> simp
  -- the matrix of `P(h(t))`
  refine ⟨hypGSpin hf hf' hp t, hmem, Units.ext ?_⟩
  set Bm : Matrix (Fin d.m) (Fin d.m) Kb := (B : Matrix (Fin d.m) (Fin d.m) F).map (algebraMap F Kb)
  have hBb : ((Units.map (algebraMap F Kb).mapMatrix.toMonoidHom B : GL (Fin d.m) Kb) :
      Matrix (Fin d.m) (Fin d.m) Kb) = Bm := rfl
  rw [coe_specMatFbar, TwistDescent.toMatrix_bc, Units.val_mul, Units.val_mul, coe_blockDiagGL, hBb,
    ← LinearMap.toMatrix'_toLin' (_ * _ * Bm)]
  congr 1
  refine LinearMap.ext fun v => ?_
  set w := (InnerTwistAux.bcE d.m).symm v
  have hv : InnerTwistAux.bcE d.m w = v := (InnerTwistAux.bcE d.m).apply_symm_apply v
  -- in block coordinates
  have key : Bm *ᵥ InnerTwistAux.bcE d.m (specP _ (hypGSpin hf hf' hp t) w) =
      blockDiag e (R : Matrix (Fin 2) (Fin 2) Kb) 1 *ᵥ (Bm *ᵥ v) := by
    have h1 := hΨh w
    rw [hΨ, splitIso_apply, splitIso_apply] at h1
    funext k
    obtain ⟨a, rfl⟩ := e.surjective k
    rcases a with i | j
    · rw [blockDiag_mulVec_inl, ← hv]
      exact congrFun (congrArg Prod.fst h1) i
    · rw [blockDiag_mulVec_inr, Matrix.one_mulVec, ← hv]
      exact congrFun (congrArg Prod.snd h1) j
  have hBinv : ((Units.map (algebraMap F Kb).mapMatrix.toMonoidHom B)⁻¹ : GL (Fin d.m) Kb) *ᵥ
      (Bm *ᵥ InnerTwistAux.bcE d.m (specP _ (hypGSpin hf hf' hp t) w)) =
      InnerTwistAux.bcE d.m (specP _ (hypGSpin hf hf' hp t) w) := by
    rw [mulVec_mulVec, ← hBb, Units.inv_mul, one_mulVec]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Matrix.toLin'_apply]
  rw [← hBinv, key, mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc]

end TwistPlane

end GSpinGGP
