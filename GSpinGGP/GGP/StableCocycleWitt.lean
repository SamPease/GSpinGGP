/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.StableCocycleEven

/-!
# The cocycle of `y` when `dim W'_x` is even

On the `V`-factor `dim V'_x = dim W'_x + dim Z` is odd, so the witness `ψ_V` of strong stable
conjugacy on `V` is rational on `V'_x` (`galIso_trans_symm_eq_self_of_odd`), and gives an `F`-isometry
`W'_x ⊕ Z ≅ W'_y ⊕ Z`; Witt cancellation gives `W'_x ≅ W'_y`, and the change of witness
(`exists_isStableIso_of_isometry`) gives the cocycle.  With the odd case (`exists_isStableIso_of_odd`)
this gives, for each such `y`, a class in `H¹(F, S_x)` over `α` (`exists_isStableIso`; the forward
direction of Thesis Prop. 6.6.1(iii), whose `H¹(F, T_x)` becomes `H¹(F, S_x)`).  Independence of the
choices is not shown here.
Own work, elementary.
-/

noncomputable section

namespace GSpinGGP

open CliffordAlgebra TwistDescent TorusTransfer
open scoped TensorProduct

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

section Det

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
  {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}

/-- `C(ψ)` carrying `x` to `y` matches the fixed spaces: `dim W'_x = dim W'_y`. -/
theorem finrank_fixedSub_eq_of_map [FiniteDimensional F V₁] [FiniteDimensional F V₂]
    (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) {x : GSpin Q₁} {y : GSpin Q₂}
    (h : CliffordAlgebra.map ψ.toIsometry (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra _) =
      (bcUnits Q₂ (y : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra _)) :
    Module.finrank F (fixedSub x) = Module.finrank F (fixedSub y) := by
  set Ex := Module.End.eigenspace (specP _ (bcGSpin Q₁ x) : Kb ⊗[F] V₁ →ₗ[Kb] _) 1
  set Ey := Module.End.eigenspace (specP _ (bcGSpin Q₂ y) : Kb ⊗[F] V₂ →ₗ[Kb] _) 1
  have hint := WitnessChange.apply_specP_bcGSpin ψ h
  have hmap : Ex.map (ψ.toLinearEquiv : Kb ⊗[F] V₁ →ₗ[Kb] Kb ⊗[F] V₂) = Ey := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      simp only [SetLike.mem_coe, Ex, Ey, Module.End.mem_eigenspace_iff, one_smul] at hw ⊢
      change specP _ (bcGSpin Q₂ y) (ψ w) = ψ w
      rw [← hint]
      exact congrArg ψ hw
    · intro u hu
      refine ⟨ψ.symm u, ?_, ψ.apply_symm_apply u⟩
      simp only [SetLike.mem_coe, Ex, Ey, Module.End.mem_eigenspace_iff, one_smul] at hu ⊢
      apply ψ.injective
      change ψ (specP _ (bcGSpin Q₁ x) (ψ.symm u)) = ψ (ψ.symm u)
      rw [hint, ψ.apply_symm_apply]
      exact hu
  have e1 := (ψ.toLinearEquiv.submoduleMap Ex).finrank_eq
  rw [hmap] at e1
  rw [← GGPData.finrank_eigenspace_bc_one Q₁ x, ← GGPData.finrank_eigenspace_bc_one Q₂ y]
  exact e1

/-- **Descent of a rational witness**: if `C(ψ)` carries `x` to `y` and the cocycle `ψ⁻¹ ∘ σψ` is the
identity on `W'_x ⊗ F̄`, then `ψ` restricts to an `F`-isometry `θ : W'_x ≅ W'_y`:
`ψ(1 ⊗ v) = 1 ⊗ θ(v)`. -/
theorem exists_isometryEquiv_fixedSub [FiniteDimensional F V₁] [FiniteDimensional F V₂]
    (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) {x : GSpin Q₁} {y : GSpin Q₂}
    (h : CliffordAlgebra.map ψ.toIsometry (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra _) =
      (bcUnits Q₂ (y : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra _))
    (hfix : ∀ σ : GalF F, ∀ w ∈ (fixedSub x).baseChange Kb, (galIso σ ψ).trans ψ.symm w = w) :
    ∃ θ : (Q₁.comp (fixedSub x).subtype).IsometryEquiv (Q₂.comp (fixedSub y).subtype),
      ∀ v : fixedSub x, ψ (1 ⊗ₜ (v : V₁)) = (1 : Kb) ⊗ₜ[F] ((θ v : fixedSub y) : V₂) := by
  have hmk₁ := Module.Flat.tensorProduct_mk_injective (R := F) (S := Kb) (M := V₁)
  have hmk₂ := Module.Flat.tensorProduct_mk_injective (R := F) (S := Kb) (M := V₂)
  -- `ψ(1 ⊗ v)` is rational for `v ∈ W'_x`
  have hrat : ∀ v : fixedSub x, ∃ v' : V₂, (1 : Kb) ⊗ₜ[F] v' = ψ (1 ⊗ₜ (v : V₁)) := by
    intro v
    refine exists_tmul_of_fixed V₂ _ fun σ => ?_
    have h1 := hfix σ (1 ⊗ₜ (v : V₁)) (Submodule.tmul_mem_baseChange_of_mem 1 v.2)
    have h2 : galIso σ ψ (1 ⊗ₜ (v : V₁)) = ψ (1 ⊗ₜ (v : V₁)) :=
      calc galIso σ ψ (1 ⊗ₜ (v : V₁)) = ψ (ψ.symm (galIso σ ψ (1 ⊗ₜ (v : V₁)))) :=
            (ψ.apply_symm_apply _).symm
        _ = ψ (1 ⊗ₜ (v : V₁)) := congrArg ψ h1
    rw [galIso_apply, galV_tmul, map_one] at h2
    exact h2
  choose θ hθ using hrat
  have hθ' : ∀ v : fixedSub x, ψ (1 ⊗ₜ (v : V₁)) = (1 : Kb) ⊗ₜ[F] θ v := fun v => (hθ v).symm
  have hadd : ∀ v w, θ (v + w) = θ v + θ w := fun v w => hmk₂ <| by
    change (1 : Kb) ⊗ₜ[F] θ (v + w) = (1 : Kb) ⊗ₜ[F] (θ v + θ w)
    rw [TensorProduct.tmul_add, ← hθ', ← hθ', ← hθ', Submodule.coe_add, TensorProduct.tmul_add,
      map_add]
  have hsmul : ∀ (c : F) v, θ (c • v) = c • θ v := fun c v => hmk₂ <| by
    change (1 : Kb) ⊗ₜ[F] θ (c • v) = (1 : Kb) ⊗ₜ[F] (c • θ v)
    rw [← hθ', Submodule.coe_smul, TensorProduct.tmul_smul, TensorProduct.tmul_smul, ← hθ',
      ← algebraMap_smul Kb c, ← algebraMap_smul Kb c, map_smul]
  set θL : fixedSub x →ₗ[F] V₂ := ⟨⟨θ, hadd⟩, hsmul⟩
  -- `θ` lands in `W'_y`
  have hθy : ∀ v, θL v ∈ fixedSub y := fun v => by
    rw [mem_fixedSub_iff]
    apply hmk₂
    change (1 : Kb) ⊗ₜ[F] specP Q₂ y (θ v) = (1 : Kb) ⊗ₜ[F] θ v
    have hP : specP _ (bcGSpin Q₂ y) ((1 : Kb) ⊗ₜ[F] θ v) = (1 : Kb) ⊗ₜ[F] specP Q₂ y (θ v) := by
      rw [← LinearEquiv.coe_coe, specP_bcGSpin]; rfl
    rw [← hP, ← hθ', ← WitnessChange.apply_specP_bcGSpin ψ h]
    congr 1
    have hP' : specP _ (bcGSpin Q₁ x) ((1 : Kb) ⊗ₜ[F] (v : V₁)) =
        (1 : Kb) ⊗ₜ[F] specP Q₁ x (v : V₁) := by
      rw [← LinearEquiv.coe_coe, specP_bcGSpin]; rfl
    rw [hP', show specP Q₁ x (v : V₁) = v from (mem_fixedSub_iff x _).1 v.2]
  set θy : fixedSub x →ₗ[F] fixedSub y := θL.codRestrict _ hθy
  have hQ : ∀ v, Q₂ (θ v) = Q₁ v := fun v => by
    have h1 := ψ.map_app (1 ⊗ₜ (v : V₁))
    rw [hθ', QuadraticForm.baseChange_tmul, QuadraticForm.baseChange_tmul, mul_one,
      ← Algebra.algebraMap_eq_smul_one, ← Algebra.algebraMap_eq_smul_one] at h1
    exact (algebraMap F Kb).injective h1
  have hinj : Function.Injective θy := fun v w hvw => by
    have e : θ v = θ w := congrArg Subtype.val hvw
    apply Subtype.ext
    apply hmk₁
    apply ψ.injective
    change ψ (1 ⊗ₜ (v : V₁)) = ψ (1 ⊗ₜ (w : V₁))
    rw [hθ', hθ', e]
  exact ⟨⟨θy.linearEquivOfInjective hinj (finrank_fixedSub_eq_of_map ψ h), fun v => hQ v⟩,
    fun v => hθ' v⟩

end Det

/-- The cocycle of `φ_α ⊕ id_Z` has determinant `1`. -/
theorem GGPData.det_galIso_twistV (d : GGPData F) (τ : InnerTwist d.QW) (σ : GalF F) :
    LinearMap.det ((galIso σ (d.twistV τ)).trans (d.twistV τ).symm : Kb ⊗[F] d.V →ₗ[Kb] _) = 1 := by
  set P := (prodBaseChange d.QW d.QZ).toLinearEquiv
  set a := (galIso σ τ.φ).trans τ.φ.symm
  have key : ((galIso σ (d.twistV τ)).trans (d.twistV τ).symm : Kb ⊗[F] d.V →ₗ[Kb] _) =
      P.symm.toLinearMap ∘ₗ (a.toLinearEquiv.toLinearMap.prodMap LinearMap.id) ∘ₗ P.toLinearMap := by
    refine LinearMap.ext fun u => ?_
    apply (prodBaseChange d.QW d.QZ).toLinearEquiv.injective
    change prodBaseChange d.QW d.QZ ((prodBaseChange d.QW d.QZ).symm
      ((τ.φ.symm ((prodBaseChange τ.Q' d.QZ) (galV σ ((prodBaseChange τ.Q' d.QZ).symm
        (τ.φ (prodBaseChange d.QW d.QZ (galV σ⁻¹ u)).1, (prodBaseChange d.QW d.QZ (galV σ⁻¹ u)).2)))).1,
       ((prodBaseChange τ.Q' d.QZ) (galV σ ((prodBaseChange τ.Q' d.QZ).symm
        (τ.φ (prodBaseChange d.QW d.QZ (galV σ⁻¹ u)).1,
          (prodBaseChange d.QW d.QZ (galV σ⁻¹ u)).2)))).2))) =
      prodBaseChange d.QW d.QZ ((prodBaseChange d.QW d.QZ).symm
        (a (prodBaseChange d.QW d.QZ u).1, (prodBaseChange d.QW d.QZ u).2))
    rw [galV_prodBaseChange_symm, QuadraticMap.IsometryEquiv.apply_symm_apply, prodBaseChange_galV,
      galV_galV_inv]
    simp only [QuadraticMap.IsometryEquiv.apply_symm_apply]
    rfl
  have hc := LinearMap.det_conj (a.toLinearEquiv.toLinearMap.prodMap LinearMap.id) P.symm
  rw [LinearEquiv.symm_symm] at hc
  rw [key, hc, LinearMap.det_prodMap, LinearMap.det_id, mul_one]
  exact det_galIso_trans_symm_innerTwist τ σ

namespace GGPData

variable (d : GGPData F)

variable {d}

/-- **The cocycle of `y`** (the forward direction of Thesis Prop. 6.6.1(iii); independence of `ψ` is not
shown here): for `x ∈ Γ(G,H)`
and `y` strongly stably conjugate to `x`, some `ψ` with `C(ψ) x = y` has its cocycle in `S_x`.
If `dim W'_x` is odd, `ψ = P(g_W) ∘ φ_α` works (`exists_isStableIso_of_odd`).  Otherwise
`dim V'_x = dim W'_x + dim Z` is odd, so `P(g_V) ∘ (φ_α ⊕ id_Z)` is rational on `V'_x` and gives
`W'_x ⊕ Z ≅ W'_y ⊕ Z` over `F`; Witt cancellation gives `W'_x ≅ W'_y`, and the witness on `W` can be
changed accordingly (`exists_isStableIso_of_isometry`). -/
theorem exists_isStableIso (τ : InnerTwist d.QW) {x : GSpin d.QW} (hx : d.IsGammaElt x)
    {y : GSpin (d.twist τ).QW} (hxy : d.StronglyStablyConjW τ x y) :
    ∃ ψ, d.IsStableIso τ x y ψ := by
  rcases Nat.even_or_odd (Module.finrank F (fixedSub x)) with he | ho
  swap
  · exact d.exists_isStableIso_of_odd τ hx hxy ho
  -- the `V`-factor
  obtain ⟨gV, hgV, hconjV, hratV⟩ := hxy.2
  set gV' : GSpin ((d.twist τ).QV.baseChange Kb) := ⟨gV, hgV⟩
  have hmapV : CliffordAlgebra.map ((d.twistV τ).trans (specPIso gV')).toIsometry
      (bcUnits d.QV ((d.incl x : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra _) =
      (bcUnits (d.twist τ).QV (((d.twist τ).incl y : GSpin (d.twist τ).QV) :
        (CliffordAlgebra (d.twist τ).QV)ˣ) : CliffordAlgebra _) := by
    rw [← psiA_eq_map]
    exact congrArg Units.val hconjV
  have hxssV := isSemisimple_specP_of_isSS d.QV (d.incl x) (d.isSS_incl hx.1)
  have hoddV : Odd (Module.finrank F (fixedSub (d.incl x))) := by
    rw [(d.QVfixIso x).symm.toLinearEquiv.finrank_eq, Module.finrank_prod, Module.finrank_fin_fun]
    exact he.add_odd (odd_two_mul_add_one _)
  have hfixV : ∀ σ : GalF F, ∀ w ∈ (fixedSub (d.incl x)).baseChange Kb,
      (galIso σ ((d.twistV τ).trans (specPIso gV'))).trans ((d.twistV τ).trans (specPIso gV')).symm w =
        w := fun σ w hw => by
    have hdet : LinearMap.det (((galIso σ ((d.twistV τ).trans (specPIso gV'))).trans
        ((d.twistV τ).trans (specPIso gV')).symm).toLinearEquiv : Kb ⊗[F] d.V →ₗ[Kb] _) = 1 := by
      rw [det_galIso_trans_specPIso, d.det_galIso_twistV]
    rw [← GGPData.eigenspace_bc_one] at hw
    exact galIso_trans_symm_eq_self_of_odd d.nondeg_QV (d.twistV τ) gV' hxssV hratV σ hdet hoddV hw
  obtain ⟨θV, -⟩ := exists_isometryEquiv_fixedSub _ hmapV hfixV
  -- Witt cancellation of `Z`
  have e := (QuadraticMap.IsometryEquiv.prodComm _ _).trans ((d.QVfixIso x).trans
    (θV.trans (((d.twist τ).QVfixIso y).symm.trans (QuadraticMap.IsometryEquiv.prodComm _ _))))
  obtain ⟨θ⟩ := witt_cancellation d.QZ _ _ ⟨e⟩
  obtain ⟨g, hg, hconj, -⟩ := hxy.1
  exact d.exists_isStableIso_of_isometry τ hx ⟨g, hg, hconj⟩ θ

end GGPData

end GSpinGGP
