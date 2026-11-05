/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.StableCocycleWitt

/-!
# The class of `y` in `H¹(F, S_x)` is well defined, and determines `y`

Two isometries `ψ, ψ'` computing the class of `y` (`GGPData.IsStableIso`) give cohomologous cocycles
in `S_x` (`IsStableIso.rel`): `c = ψ⁻¹ ψ'` is `P(k₀)` with `k₀` commuting with `x` (by the normalization
`det ψ = det φ_α`), `c` is rational on `W'_x` (`exists_isometryEquiv_fixedSub`), its restriction there
has determinant `1` (Steinberg) and lifts to `k_r ∈ GSpin(W)(F)` supported on `W'_x`, and
`k_r⁻¹ k₀ ∈ T_x(F̄)`.  Conjugating `y` by a rational `g` does not change the cocycle
(`IsStableIso.conj`), so the class depends only on the `GSpin(W_α)(F)`-conjugacy class of `y`
(`IsStableIso.mk_eq`).  Conversely equal classes come from conjugate elements
(`IsStableIso.exists_conj_of_mk_eq`).  Thesis Prop. 6.6.1(iii); own work, elementary.
-/

noncomputable section

namespace GSpinGGP

open CliffordAlgebra TwistDescent TorusTransfer
open scoped TensorProduct

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

/-- An algebra map out of a Clifford algebra has image commuting with `z` if the images of the
generators do. -/
theorem commute_of_commute_ι {R V A : Type*} [CommRing R] [AddCommGroup V] [Module R V] [Ring A]
    [Algebra R A] {Q : QuadraticForm R V} (φ : CliffordAlgebra Q →ₐ[R] A) {z : A}
    (h : ∀ v, Commute (φ (ι Q v)) z) (a : CliffordAlgebra Q) : Commute (φ a) z := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact Algebra.commute_algebraMap_left r z
  | ι v => exact h v
  | mul a b ha hb => rw [map_mul]; exact ha.mul_left hb
  | add a b ha hb => rw [map_add]; exact ha.add_left hb

/-- An element of `S_x(F̄)`, as an isometry, is the identity on `W'_x ⊗ F̄`. -/
theorem apply_eq_self_of_glOf_mem_torusBarFbar (d : GGPData F) {x : GSpin d.QW}
    (a : (d.QW.baseChange Kb).IsometryEquiv (d.QW.baseChange Kb)) (ha : glOf a ∈ d.torusBarFbar x)
    {w : Kb ⊗[F] (Fin d.m → F)} (hw : w ∈ (fixedSub x).baseChange Kb) : a w = w := by
  obtain ⟨t, ht, hta⟩ := ha
  have h1 := congrArg Units.val hta
  rw [coe_specMatFbar, coe_glOf] at h1
  have e : (a.toLinearEquiv : (Kb ⊗[F] (Fin d.m → F)) →ₗ[Kb] (Kb ⊗[F] (Fin d.m → F))) =
      (specP _ t : (Kb ⊗[F] (Fin d.m → F)) →ₗ[Kb] (Kb ⊗[F] (Fin d.m → F))) :=
    ((LinearMap.toMatrix (bcBasis F d.m) (bcBasis F d.m)).injective h1).symm
  change (a.toLinearEquiv : (Kb ⊗[F] (Fin d.m → F)) →ₗ[Kb] (Kb ⊗[F] (Fin d.m → F))) w = w
  rw [e]
  exact ht.2 w hw

namespace GGPData

open WitnessChange

variable {d : GGPData F}

/-- The cocycle of a witness is trivial on `W'_x ⊗ F̄`. -/
theorem IsStableIso.fix {τ : InnerTwist d.QW} {x : GSpin d.QW} {y : GSpin (d.twist τ).QW}
    {ψ : (d.QW.baseChange Kb).IsometryEquiv (τ.Q'.baseChange Kb)} (h : d.IsStableIso τ x y ψ)
    (σ : GalF F) {w : Kb ⊗[F] (Fin d.m → F)} (hw : w ∈ (fixedSub x).baseChange Kb) :
    (galIso σ ψ).trans ψ.symm w = w :=
  apply_eq_self_of_glOf_mem_torusBarFbar d _ (by rw [glOf_trans, glOf_symm, glOf_galIso]; exact h.2.1 σ) hw

/-- **Two witnesses give cohomologous cocycles** in `S_x` (well-definedness of the class of `y`,
Thesis Prop. 6.6.1(iii)). -/
theorem IsStableIso.rel {τ : InnerTwist d.QW} {x : GSpin d.QW} (hx : d.IsGammaElt x)
    {y : GSpin (d.twist τ).QW} {ψ ψ' : (d.QW.baseChange Kb).IsometryEquiv (τ.Q'.baseChange Kb)}
    (h : d.IsStableIso τ x y ψ) (h' : d.IsStableIso τ x y ψ') :
    GalCocycle.Rel h.cocycle h'.cocycle := by
  classical
  set W := Fin d.m → F
  set X : (CliffordAlgebra (d.QW.baseChange Kb))ˣ := bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ)
  have hQL := isNondeg_baseChange d.QW d.nondeg
  have hnd := isNondeg_fixedSub_of_isSS d.nondeg x hx.1
  have hc := isCompl_fixedSub_movedSub x (fixedSub_inf_movedSub_of_isSS x hx.1)
  obtain ⟨θ, hθ⟩ := exists_isometryEquiv_fixedSub ψ h.1 (fun σ _ hw => h.fix σ hw)
  obtain ⟨θ', hθ'⟩ := exists_isometryEquiv_fixedSub ψ' h'.1 (fun σ _ hw => h'.fix σ hw)
  -- `c = ψ⁻¹ ψ'` has determinant `1`
  obtain ⟨c, hcdef⟩ : ∃ c, ψ'.trans ψ.symm = c := ⟨_, rfl⟩
  have hglc : glOf c = (glOf ψ)⁻¹ * glOf ψ' := by rw [← hcdef, glOf_trans, glOf_symm]
  have hdetc : LinearMap.det (c.toLinearEquiv : (Kb ⊗[F] W) →ₗ[Kb] (Kb ⊗[F] W)) = 1 := by
    rw [← LinearMap.det_toMatrix (bcBasis F d.m), ← coe_glOf, hglc, Units.val_mul, Matrix.det_mul,
      h'.2.2, ← h.2.2, ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.det_one]
  obtain ⟨k₀, hk₀⟩ := gspin_specP_surjective_SO _ hQL c.toLinearEquiv c.map_app hdetc
  have hk₀w : ∀ w, specP _ k₀ w = c w := fun w => by rw [hk₀]; rfl
  -- `k₀` commutes with `x`
  have hcx : CliffordAlgebra.map c.toIsometry (X : CliffordAlgebra _) = X := by
    rw [← hcdef, map_trans_apply, h'.1, ← h.1, map_symm_map]
  have hk₀x : Commute k₀ (bcGSpin d.QW x) := by
    have hmap : CliffordAlgebra.map c.toIsometry = CliffordAlgebra.map (specPIso k₀).toIsometry := by
      congr 1
      ext v
      exact (hk₀w v).symm
    rw [hmap, map_specPIso_apply] at hcx
    apply Subtype.ext; apply Units.ext
    change ((k₀ : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb)) *
        (X : CliffordAlgebra _) =
      (X : CliffordAlgebra _) *
        ((k₀ : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb))
    conv_rhs => rw [← hcx]
    simp only [mul_assoc, Units.inv_mul, mul_one]
  -- `c = r ⊗ 1` on `W'_x ⊗ F̄`, `r = θ⁻¹ θ'` rational
  set r := θ'.trans θ.symm
  have hcr : ∀ v : fixedSub x, c (1 ⊗ₜ (v : W)) = 1 ⊗ₜ ((r v : fixedSub x) : W) := fun v => by
    have e := hθ (r v)
    rw [show θ (r v) = θ' v from θ.apply_symm_apply _] at e
    rw [← hcdef]
    change ψ.symm (ψ' (1 ⊗ₜ (v : W))) = _
    rw [hθ', ← e, ψ.symm_apply_apply]
  -- `det r = 1` (Steinberg: `det P(k₀)|_{E₁} = 1`)
  have hsemiL : Module.End.IsSemisimple
      (specP (d.QW.baseChange Kb) (bcGSpin d.QW x) : Kb ⊗[F] W →ₗ[Kb] _) := by
    rw [specP_bcGSpin]
    exact IsomCent.isSemisimple_baseChange_algebraicClosure (isSemisimple_specP_of_isSS d.QW x hx.1)
  obtain ⟨hcom, hdet1⟩ := Steinberg.det_restrict_one_eq_one_of_commute hQL (bcGSpin d.QW x) hsemiL k₀ hk₀x
  obtain ⟨f, hfa⟩ : ∃ f : W →ₗ[F] W, ∀ a : fixedSub x, f a = r a := by
    refine ⟨(fixedSub x).subtype ∘ₗ (r.toLinearEquiv : fixedSub x →ₗ[F] fixedSub x) ∘ₗ
      (fixedSub x).projectionOnto (movedSub x) hc +
      (LinearMap.id - (fixedSub x).projection (movedSub x) hc), fun a => ?_⟩
    rw [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
      Submodule.projection_apply_left, sub_self, add_zero, LinearMap.comp_apply,
      LinearMap.comp_apply, Submodule.projectionOnto_apply_left]
    rfl
  have hfp : Set.MapsTo f (fixedSub x) (fixedSub x) := fun a ha => by
    rw [show f a = r ⟨a, ha⟩ from hfa ⟨a, ha⟩]; exact (r ⟨a, ha⟩).2
  have hagree : ∀ w ∈ (fixedSub x).baseChange Kb, specP _ k₀ w = f.baseChange Kb w := by
    intro w hw
    have hle : (fixedSub x).baseChange Kb ≤ LinearMap.eqLocus
        (specP _ k₀ : Kb ⊗[F] W →ₗ[Kb] Kb ⊗[F] W) (f.baseChange Kb) := by
      rw [Submodule.baseChange_eq_span, Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      change specP _ k₀ (1 ⊗ₜ a) = f.baseChange Kb (1 ⊗ₜ a)
      rw [hk₀w, hcr ⟨a, ha⟩, LinearMap.baseChange_tmul, hfa ⟨a, ha⟩]
    exact hle hw
  have hfp' : Set.MapsTo (f.baseChange Kb) ((fixedSub x).baseChange Kb)
      ((fixedSub x).baseChange Kb) := by
    have hle : (fixedSub x).baseChange Kb ≤ ((fixedSub x).baseChange Kb).comap (f.baseChange Kb) := by
      conv_lhs => rw [Submodule.baseChange_eq_span]
      rw [Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      change f.baseChange Kb (1 ⊗ₜ a) ∈ (fixedSub x).baseChange Kb
      rw [LinearMap.baseChange_tmul]
      exact Submodule.tmul_mem_baseChange_of_mem 1 (hfp ha)
    exact fun w hw => hle hw
  have hk₀p : Set.MapsTo (specP _ k₀ : Kb ⊗[F] W →ₗ[Kb] Kb ⊗[F] W) ((fixedSub x).baseChange Kb)
      ((fixedSub x).baseChange Kb) := fun w hw => by
    rw [LinearEquiv.coe_coe, hagree w hw]; exact hfp' hw
  have hdetr : LinearMap.det (r.toLinearEquiv : fixedSub x →ₗ[F] fixedSub x) = 1 := by
    have e1 := IsomCent.det_restrict_congr (specP _ k₀ : Kb ⊗[F] W →ₗ[Kb] Kb ⊗[F] W)
      (GGPData.eigenspace_bc_one d.QW x)
      (IsomCent.mapsTo_eigenspace_of_commute (Steinberg.commute_toLinearMap hcom) 1) hk₀p
    have e2 : (specP _ k₀ : Kb ⊗[F] W →ₗ[Kb] Kb ⊗[F] W).restrict hk₀p =
        (f.baseChange Kb).restrict hfp' :=
      LinearMap.ext fun w => Subtype.ext (hagree w w.2)
    have e4 : f.restrict hfp = (r.toLinearEquiv : fixedSub x →ₗ[F] fixedSub x) :=
      LinearMap.ext fun a => Subtype.ext (hfa a)
    have e3 := IsomCent.det_restrict_baseChange (L := Kb) f hfp hfp'
    rw [e4, ← e2, ← e1, hdet1] at e3
    exact (algebraMap F Kb).injective (by rw [map_one]; exact e3.symm)
  -- a rational lift `k_r ∈ GSpin(W)(F)` of `r ⊕ 1`; it commutes with `x`
  obtain ⟨k', hk'⟩ := gspin_specP_surjective_SO (d.QW.comp (fixedSub x).subtype) hnd
    r.toLinearEquiv r.map_app hdetr
  let ι' : (d.QW.comp (fixedSub x).subtype) →qᵢ d.QW := ⟨(fixedSub x).subtype, fun _ => rfl⟩
  obtain ⟨kr, hkrdef⟩ : ∃ kr, GSpin.map ι' hnd k' = kr := ⟨_, rfl⟩
  have hkr : ∀ a : fixedSub x, specP d.QW kr a = r a := fun a => by
    have e := specP_map_apply ι' hnd k' a
    rw [hkrdef, hk'] at e
    exact e
  have hkrx : Commute kr x := by
    apply Subtype.ext; apply Units.ext
    change ((kr : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * _ = _ * _
    rw [← hkrdef, GSpin.coe_map]
    refine (commute_of_commute_ι (CliffordAlgebra.map ι') (fun v => ?_) _).eq
    rw [CliffordAlgebra.map_apply_ι]
    exact (commute_ι_of_specP_eq x ((GSpinGGP.mem_fixedSub_iff x _).1 v.2)).symm
  -- `P(k̃_r) = c` on `W'_x ⊗ F̄`
  have hPkr : ∀ v : W, specP _ (bcGSpin d.QW kr) ((1 : Kb) ⊗ₜ[F] v) = (1 : Kb) ⊗ₜ[F] specP d.QW kr v :=
    fun v => by rw [← LinearEquiv.coe_coe, specP_bcGSpin]; rfl
  have hcw : ∀ w ∈ (fixedSub x).baseChange Kb, c w = specP _ (bcGSpin d.QW kr) w := by
    intro w hw
    have hle : (fixedSub x).baseChange Kb ≤ LinearMap.eqLocus
        (c.toLinearEquiv : Kb ⊗[F] W →ₗ[Kb] Kb ⊗[F] W)
        (specP _ (bcGSpin d.QW kr) : Kb ⊗[F] W →ₗ[Kb] Kb ⊗[F] W) := by
      rw [Submodule.baseChange_eq_span, Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      change c (1 ⊗ₜ a) = specP _ (bcGSpin d.QW kr) (1 ⊗ₜ a)
      rw [hcr ⟨a, ha⟩, hPkr, hkr ⟨a, ha⟩]
    exact hle hw
  -- `s = k̃_r⁻¹ k₀ ∈ T_x(F̄)`
  obtain ⟨s, hsdef⟩ : ∃ s : GSpin (d.QW.baseChange Kb), (bcGSpin d.QW kr)⁻¹ * k₀ = s := ⟨_, rfl⟩
  have hs : s ∈ d.torusFbar x := by
    have h1 : Commute (bcGSpin d.QW kr) (bcGSpin d.QW x) := hkrx.map (bcGSpin d.QW)
    have h2 : Commute s (bcGSpin d.QW x) := hsdef ▸ h1.inv_left.mul_left hk₀x
    refine ⟨congrArg Subtype.val h2.eq, fun w hw => ?_⟩
    rw [← hsdef, map_mul, LinearEquiv.mul_apply, hk₀w, hcw w hw, map_inv]
    exact (specP _ (bcGSpin d.QW kr)).symm_apply_apply w
  -- the cocycle identity
  obtain ⟨M, hMdef⟩ : ∃ M, specMatFbar d.QW (bcGSpin d.QW kr) = M := ⟨_, rfl⟩
  obtain ⟨S, hSdef⟩ : ∃ S, specMatFbar d.QW s = S := ⟨_, rfl⟩
  have hglψ' : glOf ψ' = glOf ψ * (M * S) := by
    have e1 : glOf c = specMatFbar d.QW k₀ := by
      rw [← glOf_specPIso]
      exact Units.ext (congrArg (LinearMap.toMatrix (bcBasis F d.m) (bcBasis F d.m))
        (LinearMap.ext fun w => (hk₀w w).symm))
    have e2 : k₀ = bcGSpin d.QW kr * s := by rw [← hsdef, mul_inv_cancel_left]
    rw [← hMdef, ← hSdef, ← map_mul, ← e2, ← e1, hglc, mul_inv_cancel_left]
  have hM : ∀ σ : GalF F, galGL d.m σ M = M := fun σ => Units.ext (by
    rw [← hMdef, coe_galGL, coe_specMatFbar_bcGSpin, map_algebraMap_fixed])
  have hMa : ∀ a ∈ d.torusBarFbar x, a * M = M * a := by
    rintro _ ⟨t, ht, rfl⟩
    rw [← hMdef, ← map_mul, ← map_mul]
    congr 1
    -- `t` commutes with `k̃_r`, which is generated by `ι(W'_x)`
    apply Subtype.ext; apply Units.ext
    change ((t : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra _) *
        bcHom d.QW ((kr : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) =
      bcHom d.QW ((kr : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) *
        ((t : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra _)
    rw [← hkrdef, GSpin.coe_map]
    let bc : CliffordAlgebra d.QW →ₐ[F] CliffordAlgebra (d.QW.baseChange Kb) :=
      ((CliffordAlgebra.ofBaseChange Kb d.QW).restrictScalars F).comp
        Algebra.TensorProduct.includeRight
    have hbc : ∀ z, bcHom d.QW z = bc z := fun _ => rfl
    rw [hbc, ← AlgHom.comp_apply]
    refine (commute_of_commute_ι (bc.comp (CliffordAlgebra.map ι')) (fun v => ?_) _).eq.symm
    rw [AlgHom.comp_apply, CliffordAlgebra.map_apply_ι, ← hbc, bcHom_ι]
    exact (commute_ι_of_specP_eq t (ht.2 _ (Submodule.tmul_mem_baseChange_of_mem 1 v.2))).symm
  refine ⟨S, ⟨s, hs, hSdef⟩, fun σ => ?_⟩
  change (glOf ψ')⁻¹ * galGL d.m σ (glOf ψ') =
    S⁻¹ * ((glOf ψ)⁻¹ * galGL d.m σ (glOf ψ)) * galGL d.m σ S
  have ha := hMa _ (h.2.1 σ)
  rw [hglψ', map_mul, map_mul, hM σ]
  calc (glOf ψ * (M * S))⁻¹ * (galGL d.m σ (glOf ψ) * (M * galGL d.m σ S))
      = S⁻¹ * M⁻¹ * ((glOf ψ)⁻¹ * galGL d.m σ (glOf ψ) * M) * galGL d.m σ S := by group
    _ = S⁻¹ * ((glOf ψ)⁻¹ * galGL d.m σ (glOf ψ)) * galGL d.m σ S := by rw [ha]; group

/-- **Conjugating `y` by a rational `g`** composes the witness with `P(g)`, which does not change the
cocycle. -/
theorem IsStableIso.conj {τ : InnerTwist d.QW} {x : GSpin d.QW} {y : GSpin (d.twist τ).QW}
    {ψ : (d.QW.baseChange Kb).IsometryEquiv (τ.Q'.baseChange Kb)} (h : d.IsStableIso τ x y ψ)
    (g : GSpin (d.twist τ).QW) :
    ∃ h' : d.IsStableIso τ x (g * y * g⁻¹) (ψ.trans (specPIso (bcGSpin τ.Q' g))),
      ∀ σ, h'.cocycle.toFun σ = h.cocycle.toFun σ := by
  obtain ⟨N, hNdef⟩ : ∃ N, specMatFbar τ.Q' (bcGSpin τ.Q' g) = N := ⟨_, rfl⟩
  have hN : ∀ σ : GalF F, galGL d.m σ N = N := fun σ => Units.ext (by
    rw [← hNdef, coe_galGL, coe_specMatFbar_bcGSpin (d := d.twist τ), map_algebraMap_fixed])
  have hgl : glOf (ψ.trans (specPIso (bcGSpin τ.Q' g))) = N * glOf ψ := by
    rw [glOf_trans, glOf_specPIso, hNdef]
  have hco : ∀ σ : GalF F, (glOf (ψ.trans (specPIso (bcGSpin τ.Q' g))))⁻¹ *
      galGL d.m σ (glOf (ψ.trans (specPIso (bcGSpin τ.Q' g)))) =
      (glOf ψ)⁻¹ * galGL d.m σ (glOf ψ) := fun σ => by
    rw [hgl, map_mul, hN σ]; group
  refine ⟨⟨?_, fun σ => (hco σ).symm ▸ h.2.1 σ, (det_glOf_trans_specPIso_eq _ _).trans h.2.2⟩,
    fun σ => hco σ⟩
  rw [map_trans_apply, map_specPIso_apply, h.1]
  simp [bcGSpin, map_mul, map_inv]

/-- **The class of `y` in `H¹(F, S_x)` is well defined** on `GSpin(W_α)(F)`-conjugacy classes and
independent of the witness (Thesis Prop. 6.6.1(iii)). -/
theorem IsStableIso.mk_eq {τ : InnerTwist d.QW} {x : GSpin d.QW} (hx : d.IsGammaElt x)
    {y y' : GSpin (d.twist τ).QW} (g : GSpin (d.twist τ).QW) (hy : y' = g * y * g⁻¹)
    {ψ ψ' : (d.QW.baseChange Kb).IsometryEquiv (τ.Q'.baseChange Kb)}
    (h : d.IsStableIso τ x y ψ) (h' : d.IsStableIso τ x y' ψ') :
    H1.mk h.cocycle = H1.mk h'.cocycle := by
  subst hy
  obtain ⟨h'', hco⟩ := h.conj g
  refine (H1.mk_eq_mk.2 ⟨1, (d.torusBarFbar x).one_mem, fun σ => ?_⟩).trans
    (H1.mk_eq_mk.2 (h''.rel hx h'))
  rw [hco σ, inv_one, one_mul, map_one, mul_one]

/-- **Equal classes come from conjugate elements** (injectivity in Thesis Prop. 6.6.1(iii)): if the
cocycles of `y` and `y'` are cohomologous in `S_x`, then `y' = g y g⁻¹` for some `g ∈ GSpin(W_α)(F)`.
(With `b_σ = t⁻¹ a_σ σ(t)`, the isometry `ψ' ∘ (ψ ∘ P(t))⁻¹` of `W_{α,F̄}` is Galois-fixed of determinant
`1`, so it is `P(g)` for a rational `g`.) -/
theorem IsStableIso.exists_conj_of_mk_eq {τ : InnerTwist d.QW} {x : GSpin d.QW}
    {y y' : GSpin (d.twist τ).QW} {ψ ψ' : (d.QW.baseChange Kb).IsometryEquiv (τ.Q'.baseChange Kb)}
    (h : d.IsStableIso τ x y ψ) (h' : d.IsStableIso τ x y' ψ')
    (heq : H1.mk h.cocycle = H1.mk h'.cocycle) :
    ∃ g : GSpin (d.twist τ).QW, y' = g * y * g⁻¹ := by
  obtain ⟨S, ⟨t, ht, hSt⟩, hrel⟩ := H1.mk_eq_mk.1 heq
  -- the isometry `χ = ψ' ∘ (ψ ∘ P(t))⁻¹` of `W_{α,F̄}`
  obtain ⟨A, hAdef⟩ : ∃ A, (specPIso t).trans ψ = A := ⟨_, rfl⟩
  obtain ⟨χ, hχdef⟩ : ∃ χ, A.symm.trans ψ' = χ := ⟨_, rfl⟩
  have hglA : glOf A = glOf ψ * S := by rw [← hAdef, glOf_trans, glOf_specPIso, hSt]
  have hglχ : glOf χ = glOf ψ' * (glOf ψ * S)⁻¹ := by rw [← hχdef, glOf_trans, glOf_symm, hglA]
  -- `χ` is Galois-fixed
  have hfix : ∀ σ : GalF F, galGL d.m σ (glOf χ) = glOf χ := by
    intro σ
    have e : (glOf ψ')⁻¹ * galGL d.m σ (glOf ψ') =
        S⁻¹ * ((glOf ψ)⁻¹ * galGL d.m σ (glOf ψ)) * galGL d.m σ S := hrel σ
    have e' : galGL d.m σ (glOf ψ') =
        glOf ψ' * (S⁻¹ * ((glOf ψ)⁻¹ * galGL d.m σ (glOf ψ)) * galGL d.m σ S) := by
      rw [← e, mul_inv_cancel_left]
    rw [hglχ, map_mul, map_inv, map_mul, e']
    group
  -- `det χ = 1`, so `χ = P(k)`
  have hdetχ : LinearMap.det (χ.toLinearEquiv : Kb ⊗[F] (Fin d.m → F) →ₗ[Kb] _) = 1 := by
    have h1 : ((((glOf ψ * S)⁻¹ : GL (Fin d.m) Kb)) : Matrix (Fin d.m) (Fin d.m) Kb).det *
        (((glOf ψ * S : GL (Fin d.m) Kb)) : Matrix (Fin d.m) (Fin d.m) Kb).det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one]
    have h2 : (((glOf ψ * S : GL (Fin d.m) Kb)) : Matrix (Fin d.m) (Fin d.m) Kb).det =
        ((glOf ψ' : GL (Fin d.m) Kb) : Matrix (Fin d.m) (Fin d.m) Kb).det := by
      rw [Units.val_mul, Matrix.det_mul, ← hSt, det_specMatFbar, mul_one, h.2.2, h'.2.2]
    rw [← LinearMap.det_toMatrix (bcBasis F d.m), ← coe_glOf, hglχ, Units.val_mul, Matrix.det_mul,
      ← h2, mul_comm, h1]
  obtain ⟨k, hk⟩ := gspin_specP_surjective_SO _ (isNondeg_baseChange τ.Q' τ.nondeg') χ.toLinearEquiv
    χ.map_app hdetχ
  have hkχ : specMatFbar τ.Q' k = glOf χ := by
    rw [← glOf_specPIso]
    exact Units.ext (congrArg (LinearMap.toMatrix (bcBasis F d.m) (bcBasis F d.m))
      (LinearMap.ext fun w => by change specP _ k w = χ w; rw [hk]; rfl))
  obtain ⟨g, hg⟩ := exists_specMatFbar_bcGSpin_eq (d := d.twist τ) ⟨k, hkχ⟩ hfix
  have hχg : ∀ w, χ w = specP _ (bcGSpin τ.Q' g) w := fun w => by
    have e : LinearMap.toMatrix (bcBasis F d.m) (bcBasis F d.m)
        (χ.toLinearEquiv : Kb ⊗[F] (Fin d.m → F) →ₗ[Kb] _) =
        LinearMap.toMatrix (bcBasis F d.m) (bcBasis F d.m)
          (specP _ (bcGSpin τ.Q' g) : Kb ⊗[F] (Fin d.m → F) →ₗ[Kb] _) := by
      rw [← coe_glOf, ← coe_specMatFbar]
      exact (congrArg Units.val hg).symm
    exact LinearMap.congr_fun ((LinearMap.toMatrix _ _).injective e) w
  -- `C(χ)` carries `y` to `y'`
  set X : (CliffordAlgebra (d.QW.baseChange Kb))ˣ := bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ)
  have htX : ((t : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb)) * (X : CliffordAlgebra (d.QW.baseChange Kb)) *
      (((t : (CliffordAlgebra (d.QW.baseChange Kb))ˣ)⁻¹ : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb)) = X := by
    have e : ((t : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb)) * (X : CliffordAlgebra (d.QW.baseChange Kb)) =
        (X : CliffordAlgebra (d.QW.baseChange Kb)) * ((t : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb)) :=
      congrArg Units.val ht.1.eq
    rw [e, mul_assoc, Units.mul_inv, mul_one]
  have hAx : CliffordAlgebra.map A.toIsometry (X : CliffordAlgebra _) =
      bcUnits τ.Q' (y : (CliffordAlgebra τ.Q')ˣ) := by
    rw [← hAdef, map_trans_apply, map_specPIso_apply, htX, h.1]
  have hχy : CliffordAlgebra.map χ.toIsometry (bcUnits τ.Q' (y : (CliffordAlgebra τ.Q')ˣ) :
      CliffordAlgebra _) = bcUnits τ.Q' (y' : (CliffordAlgebra τ.Q')ˣ) := by
    rw [← hχdef, map_trans_apply, ← hAx, map_symm_map, h'.1]
  have hmapχ : CliffordAlgebra.map χ.toIsometry =
      CliffordAlgebra.map (specPIso (bcGSpin τ.Q' g)).toIsometry := by
    congr 1
    ext w
    exact hχg w
  rw [hmapχ, map_specPIso_apply] at hχy
  refine ⟨g, bcUnits_GSpin_injective τ.Q' (Units.ext ?_)⟩
  rw [← hχy]
  simp [bcGSpin, map_mul, map_inv]

end GGPData

end GSpinGGP
