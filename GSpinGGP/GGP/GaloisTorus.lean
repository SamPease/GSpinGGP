/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.Kottwitz
import GSpinGGP.GGP.TorusCommute
import GSpinGGP.GGP.MovedCentralizer
import GSpinGGP.GGP.Steinberg
import GSpinGGP.GGP.TwistDescent

/-!
# The Galois action on `S_x(F̄)`

The Galois action on `F̄ ⊗ V` (`galV`), on `C(V)_{F̄}` (`galC`) and on `GSpin(V)(F̄)` (`galGS`);
`S_x(F̄)` is Galois-stable (`galGL_mem_torusBarFbar`) and, for `x ∈ Γ(G,H)`, commutative
(`torusBarFbar_commute`).  Own work, elementary.
-/

noncomputable section

open scoped Classical

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

variable {d : GGPData F}

section EndElemGal

open CliffordAlgebra
open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- The Galois action `σ ⊗ 1` on `F̄ ⊗ V` (an `F`-linear, `σ`-semilinear map). -/
def galV (σ : GalF F) : AlgebraicClosure F ⊗[F] V →ₗ[F] AlgebraicClosure F ⊗[F] V :=
  LinearMap.rTensor V (σ : AlgebraicClosure F →ₐ[F] AlgebraicClosure F).toLinearMap

theorem galV_tmul (σ : GalF F) (z : AlgebraicClosure F) (v : V) :
    galV σ (z ⊗ₜ[F] v) = σ z ⊗ₜ[F] v := rfl

theorem galV_smul (σ : GalF F) (c : AlgebraicClosure F) (w : AlgebraicClosure F ⊗[F] V) :
    galV σ (c • w) = σ c • galV σ w := by
  induction w using TensorProduct.inductionOn with
  | tmul z v => rw [TensorProduct.smul_tmul', galV_tmul, galV_tmul, smul_eq_mul, map_mul,
      TensorProduct.smul_tmul', smul_eq_mul]
  | add a b ha hb => rw [smul_add, map_add, map_add, ha, hb, smul_add]

theorem galV_mul (σ τ : GalF F) (w : AlgebraicClosure F ⊗[F] V) :
    galV σ (galV τ w) = galV (σ * τ) w := by
  induction w using TensorProduct.inductionOn with
  | tmul z v => rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]

theorem galV_one (w : AlgebraicClosure F ⊗[F] V) : galV (1 : GalF F) w = w := by
  induction w using TensorProduct.inductionOn with
  | tmul z v => rfl
  | add a b ha hb => rw [map_add, ha, hb]

theorem galV_inv_galV (σ : GalF F) (w : AlgebraicClosure F ⊗[F] V) :
    galV σ⁻¹ (galV σ w) = w := by
  rw [galV_mul, inv_mul_cancel, galV_one]

theorem galV_galV_inv (σ : GalF F) (w : AlgebraicClosure F ⊗[F] V) :
    galV σ (galV σ⁻¹ w) = w := by
  rw [galV_mul, mul_inv_cancel, galV_one]

/-- `σ` preserves `p ⊗ F̄` for an `F`-subspace `p`. -/
theorem galV_mem_baseChange (σ : GalF F) (p : Submodule F V) {w : AlgebraicClosure F ⊗[F] V}
    (hw : w ∈ p.baseChange (AlgebraicClosure F)) : galV σ w ∈ p.baseChange (AlgebraicClosure F) := by
  obtain ⟨u, rfl⟩ := hw
  induction u using TensorProduct.inductionOn with
  | tmul z v => exact Submodule.tmul_mem_baseChange_of_mem _ v.2
  | add a b ha hb => rw [map_add, map_add]; exact Submodule.add_mem _ ha hb

/-- The coordinates of `σ w` in the rational basis are `σ` of those of `w`. -/
theorem bcBasis_repr_galV {m : ℕ} (σ : GalF F) (w : AlgebraicClosure F ⊗[F] (Fin m → F))
    (i : Fin m) : (bcBasis F m).repr (galV σ w) i = σ ((bcBasis F m).repr w i) := by
  induction w using TensorProduct.inductionOn with
  | tmul z v =>
    rw [galV_tmul, bcBasis, Module.Basis.baseChange_repr_tmul, Module.Basis.baseChange_repr_tmul,
      Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]
  | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb]

theorem galV_bcBasis {m : ℕ} (σ : GalF F) (j : Fin m) :
    galV σ (bcBasis F m j) = bcBasis F m j := by
  rw [bcBasis, Module.Basis.baseChange_apply, galV_tmul, map_one]

/-- If `f'` is the Galois conjugate of `f` (`f' ∘ σ = σ ∘ f`), its matrix in the rational basis is
`σ` applied entrywise. -/
theorem toMatrix_of_galV_comm {m : ℕ} (σ : GalF F)
    (f f' : (AlgebraicClosure F ⊗[F] (Fin m → F)) →ₗ[AlgebraicClosure F]
      (AlgebraicClosure F ⊗[F] (Fin m → F)))
    (h : ∀ w, f' (galV σ w) = galV σ (f w)) :
    LinearMap.toMatrix (bcBasis F m) (bcBasis F m) f' =
      (LinearMap.toMatrix (bcBasis F m) (bcBasis F m) f).map σ := by
  ext i j
  rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, ← galV_bcBasis σ j, h,
    bcBasis_repr_galV, galV_bcBasis]

/-! Galois action on the Clifford algebra -/

/-- `σ(ι(w)) = ι(σ w)` in `C(V)_{F̄} ≅ F̄ ⊗ C(V)`. -/
theorem galC_ι (Q : QuadraticForm F V) (σ : GalF F) (w : AlgebraicClosure F ⊗[F] V) :
    galC Q σ (ι (Q.baseChange (AlgebraicClosure F)) w) =
      ι (Q.baseChange (AlgebraicClosure F)) (galV σ w) := by
  induction w using TensorProduct.inductionOn with
  | tmul z v =>
    simp only [galC, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, toBaseChange_ι, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
      ofBaseChange_tmul_ι, galV_tmul]
    rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- `σ` acts on the scalars `F̄ ⊆ C(V)_{F̄}` by `σ`. -/
theorem galC_algebraMap (Q : QuadraticForm F V) (σ : GalF F) (c : AlgebraicClosure F) :
    galC Q σ (algebraMap (AlgebraicClosure F) (CliffordAlgebra (Q.baseChange (AlgebraicClosure F))) c)
      = algebraMap _ _ (σ c) := by
  simp only [galC, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, Algebra.TensorProduct.map_tmul, map_one]
  rw [ofBaseChange_tmul_one]
  rfl

/-- `σ` fixes the rational elements `C(V) ⊆ C(V)_{F̄}`. -/
theorem galC_bcHom (Q : QuadraticForm F V) (σ : GalF F) (a : CliffordAlgebra Q) :
    galC Q σ (bcHom Q a) = bcHom Q a := by
  simp only [galC, bcHom, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply, toBaseChange_ofBaseChange,
    Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq]

/-- `galC` is an action of `Γ_F`. -/
theorem galC_galC (Q : QuadraticForm F V) (σ τ : GalF F)
    (a : CliffordAlgebra (Q.baseChange (AlgebraicClosure F))) :
    galC Q σ (galC Q τ a) = galC Q (σ * τ) a := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => rw [galC_algebraMap, galC_algebraMap, galC_algebraMap]; rfl
  | ι x => rw [galC_ι, galC_ι, galC_ι, galV_mul]
  | mul a b ha hb => rw [map_mul, map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]

theorem galC_one (Q : QuadraticForm F V) (a : CliffordAlgebra (Q.baseChange (AlgebraicClosure F))) :
    galC Q (1 : GalF F) a = a := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => rw [galC_algebraMap]; rfl
  | ι x => rw [galC_ι, galV_one]
  | mul a b ha hb => rw [map_mul, ha, hb]
  | add a b ha hb => rw [map_add, ha, hb]

/-- `σ` preserves the even Clifford algebra. -/
theorem galC_mem_even (Q : QuadraticForm F V) (σ : GalF F)
    {a : CliffordAlgebra (Q.baseChange (AlgebraicClosure F))}
    (ha : a ∈ even (Q.baseChange (AlgebraicClosure F))) :
    galC Q σ a ∈ even (Q.baseChange (AlgebraicClosure F)) := by
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at ha ⊢
  induction a, ha using even_induction with
  | algebraMap r => rw [galC_algebraMap]; exact SetLike.algebraMap_mem_graded _ _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul, galC_ι, galC_ι]
    exact zero_add (0 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero _ _ _) ih

/-- `galC` on units. -/
def galCU (Q : QuadraticForm F V) (σ : GalF F) :
    (CliffordAlgebra (Q.baseChange (AlgebraicClosure F)))ˣ →*
      (CliffordAlgebra (Q.baseChange (AlgebraicClosure F)))ˣ :=
  Units.map (galC Q σ).toMonoidHom

theorem coe_galCU (Q : QuadraticForm F V) (σ : GalF F)
    (g : (CliffordAlgebra (Q.baseChange (AlgebraicClosure F)))ˣ) :
    ((galCU Q σ g : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) = galC Q σ g := rfl

theorem coe_galCU_inv (Q : QuadraticForm F V) (σ : GalF F)
    (g : (CliffordAlgebra (Q.baseChange (AlgebraicClosure F)))ˣ) :
    (((galCU Q σ g)⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
      galC Q σ ((g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) := by
  rw [← map_inv]; rfl

/-- `σ` preserves `GSpin(V)(F̄)`: it preserves `C⁺` and maps `ι(F̄ ⊗ V)` onto itself. -/
theorem galCU_mem_GSpin (Q : QuadraticForm F V) (σ : GalF F)
    {g : (CliffordAlgebra (Q.baseChange (AlgebraicClosure F)))ˣ}
    (hg : g ∈ GSpin (Q.baseChange (AlgebraicClosure F))) :
    galCU Q σ g ∈ GSpin (Q.baseChange (AlgebraicClosure F)) := by
  obtain ⟨h0, h1, h2⟩ := hg
  refine ⟨galC_mem_even Q σ h0, fun v => ?_, fun v => ?_⟩
  · obtain ⟨w, hw⟩ := h1 (galV σ⁻¹ v)
    refine ⟨galV σ w, ?_⟩
    rw [← galC_ι, hw, map_mul, map_mul, galC_ι, galV_galV_inv, coe_galCU_inv, coe_galCU]
  · obtain ⟨w, hw⟩ := h2 (galV σ⁻¹ v)
    refine ⟨galV σ w, ?_⟩
    rw [← galC_ι, hw, map_mul, map_mul, galC_ι, galV_galV_inv, coe_galCU_inv, coe_galCU]

/-- `galC` on `GSpin(Q)(F̄)`. -/
def galGS (Q : QuadraticForm F V) (σ : GalF F) (g : GSpin (Q.baseChange (AlgebraicClosure F))) :
    GSpin (Q.baseChange (AlgebraicClosure F)) :=
  ⟨galCU Q σ g, galCU_mem_GSpin Q σ g.2⟩

/-- `P(σ g) ∘ σ = σ ∘ P(g)`. -/
theorem specP_galGS (Q : QuadraticForm F V) (σ : GalF F)
    (g : GSpin (Q.baseChange (AlgebraicClosure F))) (w : AlgebraicClosure F ⊗[F] V) :
    specP (Q.baseChange (AlgebraicClosure F)) (galGS Q σ g) (galV σ w) =
      galV σ (specP (Q.baseChange (AlgebraicClosure F)) g w) := by
  apply ι_injective (Q.baseChange (AlgebraicClosure F))
  rw [ι_specP, ← galC_ι Q σ (specP _ g w), ι_specP, map_mul, map_mul, galC_ι]
  rfl

/-- `σ(T_x(F̄)) = T_x(F̄)`: `σ` fixes `x` (`galC_bcHom`) and preserves `W'_x ⊗ F̄`. -/
theorem galGS_mem_torusFbar (x : ↥(GSpin d.QW)) (σ : GalF F)
    {g : GSpin (d.QW.baseChange (AlgebraicClosure F))} (hg : g ∈ d.torusFbar x) :
    galGS d.QW σ g ∈ d.torusFbar x := by
  refine ⟨?_, fun w hw => ?_⟩
  · have hc := Units.ext_iff.1 hg.1
    have hb : ((bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ) : (CliffordAlgebra _)ˣ) :
        CliffordAlgebra _) = galC d.QW σ (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ) :
          (CliffordAlgebra _)ˣ) := (galC_bcHom d.QW σ _).symm
    apply Units.ext
    show galC d.QW σ _ * _ = _ * galC d.QW σ _
    simp only [Units.val_mul] at hc
    rw [hb, ← map_mul, ← map_mul, hc]
  · have hw' := galV_mem_baseChange σ⁻¹ _ hw
    rw [← galV_galV_inv σ w, specP_galGS, hg.2 _ hw']

end EndElemGal

/-- **`S_x(F̄)` is commutative** for `x ∈ Γ(G,H)` (own work).  Proved from
`isSemisimple_specP_baseChange` and `lieAbelian_specP_baseChange` by `GGPData.torusBarFbar_commute_of`: the group of determinant-`1` isometries of `W_{F̄}`
commuting with the semisimple `X` and fixing `ker (X − 1)` is commutative when the corresponding
Lie algebra is (`IsomCent.commute_of_lieAbelian`: the eigenvalues `λ ≠ ±1` of `X` on `W''_x` are
simple, `dim E_{−1} ≤ 2`, and on `E_{−1}` the determinant is `1`). -/
theorem torusBarFbar_commute (x : ↥(GSpin d.QW)) (hx : d.IsGammaElt x) :
    ∀ s ∈ d.torusBarFbar x, ∀ t ∈ d.torusBarFbar x, Commute s t :=
  d.torusBarFbar_commute_of x (isSemisimple_specP_baseChange x hx.1)
    (lieAbelian_specP_baseChange x hx)

/-- `P` commutes with the Galois action: the matrix of `P(σ g)` is `σ` of that of `P(g)`. -/
theorem specMatFbar_galGS (σ : GalF F) (g : GSpin (d.QW.baseChange (AlgebraicClosure F))) :
    specMatFbar d.QW (galGS d.QW σ g) = galGL d.m σ (specMatFbar d.QW g) := by
  apply Units.ext
  rw [coe_specMatFbar, coe_galGL, coe_specMatFbar]
  exact toMatrix_of_galV_comm σ _ _ fun w => specP_galGS d.QW σ g w

/-- **`S_x(F̄)` is Galois-stable** (own work, elementary): `σ` acts on `GSpin(W)(F̄)` by `galC`,
fixes `x` and `W'_x ⊗ F̄` (both are defined over `F`), and `P` is defined over `F`, so the matrix of
`P(σ g)` is `σ` applied to that of `P(g)`. -/
theorem galGL_mem_torusBarFbar (x : ↥(GSpin d.QW)) (σ : GalF F) :
    ∀ s ∈ d.torusBarFbar x, galGL d.m σ s ∈ d.torusBarFbar x := by
  rintro s ⟨g, hg, rfl⟩
  exact ⟨_, galGS_mem_torusFbar x σ hg, specMatFbar_galGS σ g⟩

/-! ### `T_y` from `S_y(F̄)` -/

/-- `P(t)` over `F̄` fixes `U ⊗ F̄` iff `P(t)` fixes `U`. -/
theorem specP_bcGSpin_fixes_iff (t : GSpin d.QW) (U : Submodule F (Fin d.m → F)) :
    (∀ w ∈ U.baseChange (AlgebraicClosure F),
        specP (d.QW.baseChange (AlgebraicClosure F)) (bcGSpin d.QW t) w = w) ↔
      ∀ v ∈ U, specP d.QW t v = v := by
  have hP : ∀ w, specP (d.QW.baseChange (AlgebraicClosure F)) (bcGSpin d.QW t) w =
      ((specP d.QW t : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange (AlgebraicClosure F)) w :=
    fun w => LinearMap.congr_fun (specP_bcGSpin d.QW t) w
  constructor
  · intro h v hv
    have h1 := h (1 ⊗ₜ v) (Submodule.tmul_mem_baseChange_of_mem 1 hv)
    rw [hP, LinearMap.baseChange_tmul] at h1
    exact Module.Flat.tensorProduct_mk_injective F (Fin d.m → F) (AlgebraicClosure F) (by simpa using h1)
  · intro h w hw
    rw [hP]
    rw [Submodule.baseChange_eq_span] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      simp [LinearMap.baseChange_tmul, h v hv]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul a x _ hx => rw [map_smul, hx]

/-- **`T_y = P⁻¹(S_y(F̄)) ∩ GSpin(W)(F)`**: `t ∈ T_y` iff `P(t)`, over `F̄`, lies in `S_y(F̄)`.
(`⇐`: two elements of `GSpin(W)(F̄)` with the same image under `P` differ by a central scalar,
`ker_specP`.) -/
theorem mem_torusOf_iff (y t : GSpin d.QW) :
    t ∈ d.torusOf y ↔ specMatFbar d.QW (bcGSpin d.QW t) ∈ d.torusBarFbar y := by
  rw [GGPData.torusOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hc, hf⟩
    refine ⟨bcGSpin d.QW t, ⟨?_, (specP_bcGSpin_fixes_iff t _).2 hf⟩, rfl⟩
    have := congrArg (fun g : GSpin d.QW => bcUnits d.QW (g : (CliffordAlgebra d.QW)ˣ)) hc
    simp only [Subgroup.coe_mul, map_mul] at this
    unfold Commute SemiconjBy
    exact this
  · rintro ⟨g, ⟨hgc, hgf⟩, hgt⟩
    -- `P(bc t) = P(g)`
    have hP : specP _ (bcGSpin d.QW t) = specP _ g := by
      have := hgt.symm
      simp only [specMatFbar, MonoidHom.coe_comp, Function.comp_apply] at this
      exact (MulEquiv.injective _ ((Units.map_injective
        (LinearMap.toMatrixAlgEquiv (bcBasis F d.m)).injective) this))
    obtain ⟨c, hc⟩ : bcGSpin d.QW t * g⁻¹ ∈ (scalarGSpin _).range := by
      rw [← ker_specP (isNondeg_baseChange _ d.nondeg), MonoidHom.mem_ker, map_mul, map_inv, hP,
        mul_inv_cancel]
    have ht : bcGSpin d.QW t = scalarGSpin _ c * g := by rw [hc, inv_mul_cancel_right]
    refine ⟨?_, (specP_bcGSpin_fixes_iff t _).1 fun w hw => by
      rw [hP]; exact hgf w hw⟩
    apply bcGSpin_injective d.QW
    have hcen := Subgroup.mem_center_iff.mp
      (scalarGSpin_mem_center (d.QW.baseChange (AlgebraicClosure F)) c)
    have hgy : g * bcGSpin d.QW y = bcGSpin d.QW y * g := Subtype.ext hgc.eq
    rw [map_mul, map_mul, ht, mul_assoc, hgy, ← mul_assoc, ← hcen, mul_assoc]

/-- The matrix of `P(t)` over `F̄` is that of `P(t)` mapped to `F̄`. -/
theorem coe_specMatFbar_bcGSpin (t : GSpin d.QW) :
    ((specMatFbar d.QW (bcGSpin d.QW t) : GL (Fin d.m) (AlgebraicClosure F)) :
        Matrix (Fin d.m) (Fin d.m) (AlgebraicClosure F)) =
      (LinearMap.toMatrix' (specP d.QW t : (Fin d.m → F) →ₗ[F] (Fin d.m → F))).map
        (algebraMap F (AlgebraicClosure F)) := by
  rw [coe_specMatFbar, specP_bcGSpin]
  ext i j
  simp [LinearMap.toMatrix_apply, bcBasis, LinearMap.toMatrix'_apply, Algebra.algebraMap_eq_smul_one]

open Matrix in
/-- **Rational points of `SO(W)`**: a Galois-fixed element of `P(GSpin(W)(F̄)) ⊆ GL_m(F̄)` is the
image of some `t ∈ GSpin(W)(F)` (its entries lie in `F`, `TwistDescent.exists_map_of_fixed`; it is an
isometry of determinant `1`; `gspin_specP_surjective_SO`). -/
theorem exists_specMatFbar_bcGSpin_eq {h : GL (Fin d.m) (AlgebraicClosure F)}
    (hA : h ∈ (specMatFbar d.QW).range) (hfix : ∀ σ : GalF F, galGL d.m σ h = h) :
    ∃ t : GSpin d.QW, specMatFbar d.QW (bcGSpin d.QW t) = h := by
  obtain ⟨g, rfl⟩ := hA
  set X : Matrix (Fin d.m) (Fin d.m) (AlgebraicClosure F) :=
    ((specMatFbar d.QW g : GL (Fin d.m) (AlgebraicClosure F)) :
      Matrix (Fin d.m) (Fin d.m) (AlgebraicClosure F))
  obtain ⟨N, hN⟩ := TwistDescent.exists_map_of_fixed X fun σ => by
    have := congrArg (fun u : GL (Fin d.m) (AlgebraicClosure F) =>
      (u : Matrix (Fin d.m) (Fin d.m) (AlgebraicClosure F))) (hfix σ)
    simpa [coe_galGL] using this
  have hinj : Function.Injective (fun M : Matrix (Fin d.m) (Fin d.m) F =>
      M.map (algebraMap F (AlgebraicClosure F))) :=
    Matrix.map_injective (algebraMap F (AlgebraicClosure F)).injective
  have hgram : Nᵀ * d.QW.toMatrix' * N = d.QW.toMatrix' := hinj <| by
    simp only [Matrix.map_mul, Matrix.transpose_map, hN]
    exact TwistDescent.gram_specMatFbar d.QW g
  have hdet : N.det = 1 := (algebraMap F (AlgebraicClosure F)).injective <| by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hN, map_one]
    exact TwistDescent.det_specMatFbar d.QW g
  set e := TwistDescent.isometryEquivOfMatrix N (by rw [hdet]; exact one_ne_zero) hgram
  set φ := e.toLinearEquiv
  have hφ : ∀ v, d.QW (φ v) = d.QW v := e.map_app
  have hφl : (φ : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) = Matrix.toLin' N :=
    TwistDescent.coe_isometryEquivOfMatrix N _ hgram
  have hφdet : LinearMap.det (φ : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) = 1 := by
    rw [hφl, LinearMap.det_toLin', hdet]
  obtain ⟨t, ht⟩ := gspin_specP_surjective_SO d.QW d.nondeg φ hφ hφdet
  refine ⟨t, Units.ext ?_⟩
  rw [coe_specMatFbar_bcGSpin, ht]
  show _ = X
  rw [← hN, hφl, LinearMap.toMatrix'_toLin']

end GSpinGGP
