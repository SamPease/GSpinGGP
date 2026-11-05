/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.GaloisTorus
import GSpinGGP.GGP.TwistDescent
import GSpinGGP.GGP.TorusTransport
import GSpinGGP.GGP.Steinberg
import GSpinGGP.GGP.ConjCocycle

/-!
# The cocycle of a strongly stably conjugate element

For an `F̄`-isometry `ψ : W_{F̄} ≃ W'_{F̄}`, its Galois conjugate `σψ = σ ∘ ψ ∘ σ⁻¹` (`galIso`) is again an
isometry, with matrix `σ(Ψ)` (`glOf_galIso`), and `C(ψ)` intertwines the Galois actions on the Clifford
algebras up to replacing `ψ` by `σψ` (`galC_map`, in `GGP/GaloisTorus`).

For strong stable conjugacy (Thesis §6.1) through `Ad(g) ∘ C(φ)`, put `ψ = P(g) ∘ φ` and
`a_σ = ψ⁻¹ ∘ σψ`: the rationality clause says that `C(a_σ)` fixes the centralizer of `x` pointwise
(`map_galIso_trans_symm_of_ratAt`), and then `a_σ` is the identity on an odd-dimensional `W'_x ⊗ F̄`
(`galIso_trans_symm_eq_self_of_odd`).

If `C(ψ)` carries `x` to a rational element, then `C(a_σ) x = x` (`map_galIso_trans_symm_bcUnits`);
such an `a_σ` of determinant `1` that is the identity on `W'_x ⊗ F̄` lies in `S_x(F̄)`
(`inv_mul_galGL_glOf_mem_torusBarFbar`).  `GGPData.IsStableIso` packages an isometry `ψ` with
`C(ψ) x = y` whose cocycle `σ ↦ ψ⁻¹ ∘ σψ` lies in `S_x`; its class in `H¹(F, S_x)` maps to `α`
(`IsStableIso.twistIdx`).  Such a `ψ` exists when `dim W'_x` is odd (`exists_isStableIso_of_odd`).
These give the map `y ↦ [a]` of Thesis Prop. 6.6.1(iii).  Own work, elementary.
-/

noncomputable section

namespace GSpinGGP

open CliffordAlgebra TwistDescent
open scoped TensorProduct

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

section GalIso

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]

/-- The matrix of `σψ` is `σ` applied to the matrix of `ψ`. -/
theorem glOf_galIso {m : ℕ} {Q₁ Q₂ : QuadraticForm F (Fin m → F)} (σ : GalF F)
    (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) :
    glOf (galIso σ ψ) = galGL m σ (glOf ψ) :=
  Units.ext (toMatrix_of_galV_comm σ _ _ (fun w => galIso_galV σ ψ w))

end GalIso

section Strong

open TorusTransfer

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
  {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}

/-- **The strong condition as a fixed-point condition**: if `Ad(g) ∘ C(φ)` is defined over `F` on
the centralizer of `x`, then with `ψ = P(g) ∘ φ` the isometry `a_σ = ψ⁻¹ ∘ σψ` acts trivially (through
`C(a_σ)`) on every element of `GSpin(Q₁)(F̄)` commuting with `x`. -/
theorem map_galIso_trans_symm_of_ratAt (φ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb))
    (g : GSpin (Q₂.baseChange Kb)) {x : (CliffordAlgebra Q₁)ˣ}
    (hrat : RatAt φ (g : (CliffordAlgebra _)ˣ) x) (σ : GalF F)
    {w : (CliffordAlgebra (Q₁.baseChange Kb))ˣ} (hw : w ∈ GSpin (Q₁.baseChange Kb))
    (hwx : Commute w (bcUnits Q₁ x)) :
    CliffordAlgebra.map ((galIso σ (φ.trans (specPIso g))).trans
      (φ.trans (specPIso g)).symm).toIsometry (w : CliffordAlgebra _) = w := by
  set ψ := φ.trans (specPIso g)
  set z := galCU Q₁ σ⁻¹ w
  have hz : z ∈ GSpin (Q₁.baseChange Kb) := galCU_mem_GSpin Q₁ σ⁻¹ hw
  have hzx : Commute z (bcUnits Q₁ x) := by
    have h1 := hwx.map (galCU Q₁ σ⁻¹)
    have h2 : galCU Q₁ σ⁻¹ (bcUnits Q₁ x) = bcUnits Q₁ x :=
      Units.ext (galC_bcHom Q₁ σ⁻¹ (x : CliffordAlgebra Q₁))
    rwa [h2] at h1
  have hσz : galC Q₁ σ (z : CliffordAlgebra _) = w := by
    rw [coe_galCU, galC_galC, mul_inv_cancel, galC_one]
  have key : galC Q₂ σ (psiA φ (g : (CliffordAlgebra _)ˣ) z) =
      psiA φ (g : (CliffordAlgebra _)ˣ) (galC Q₁ σ (z : CliffordAlgebra _)) := hrat σ z hz hzx
  rw [psiA_eq_map, psiA_eq_map, galC_map, hσz] at key
  calc CliffordAlgebra.map ((galIso σ ψ).trans ψ.symm).toIsometry (w : CliffordAlgebra _)
      = CliffordAlgebra.map ψ.symm.toIsometry
          (CliffordAlgebra.map (galIso σ ψ).toIsometry (w : CliffordAlgebra _)) :=
        map_trans_apply _ _ _
    _ = w := by rw [key, map_symm_map]

end Strong

section OddFixed

open TorusTransfer Steinberg IsomCent

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
  {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}

/-- **Odd-dimensional fixed spaces are fixed by the cocycle.**  Let `Ad(g) ∘ C(φ)` satisfy the
rationality clause of strong stable conjugacy at a semisimple `x`, put `ψ = P(g) ∘ φ` and
`a_σ = ψ⁻¹ ∘ σψ`, and assume `det a_σ = 1`.  If `dim W'_x` is odd, then `a_σ` is the identity on
`W'_x ⊗ F̄`.  (Lift `a_σ` to `u ∈ GSpin(F̄)`; `u` commutes with `x` and with every `ι(w) ι(w')`,
`w, w' ∈ W'_x ⊗ F̄`, so `a_σ` is a scalar `c` with `c² = 1` there, and `det a_σ|_{W'} = 1` by
Steinberg; `c^{odd} = 1` forces `c = 1`.) -/
theorem galIso_trans_symm_eq_self_of_odd [FiniteDimensional F V₁] (hQ₁ : IsNondeg Q₁)
    (φ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) (g : GSpin (Q₂.baseChange Kb))
    {x : GSpin Q₁} (hxss : Module.End.IsSemisimple (specP Q₁ x : V₁ →ₗ[F] V₁))
    (hrat : RatAt φ (g : (CliffordAlgebra _)ˣ) (x : (CliffordAlgebra Q₁)ˣ)) (σ : GalF F)
    (hdet : LinearMap.det (((galIso σ (φ.trans (specPIso g))).trans
      (φ.trans (specPIso g)).symm).toLinearEquiv : Kb ⊗[F] V₁ →ₗ[Kb] Kb ⊗[F] V₁) = 1)
    (hodd : Odd (Module.finrank F (fixedSub x)))
    {w : Kb ⊗[F] V₁}
    (hw : w ∈ Module.End.eigenspace (specP _ (bcGSpin Q₁ x) : Kb ⊗[F] V₁ →ₗ[Kb] _) 1) :
    (galIso σ (φ.trans (specPIso g))).trans (φ.trans (specPIso g)).symm w = w := by
  classical
  -- `C(a)` fixes the centralizer of `x̃`
  have hfix : ∀ z : (CliffordAlgebra (Q₁.baseChange Kb))ˣ, z ∈ GSpin (Q₁.baseChange Kb) →
      Commute z (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ)) →
      CliffordAlgebra.map ((galIso σ (φ.trans (specPIso g))).trans
        (φ.trans (specPIso g)).symm).toIsometry (z : CliffordAlgebra _) = z :=
    fun z hz hc => map_galIso_trans_symm_of_ratAt φ g hrat σ hz hc
  obtain ⟨a, ha⟩ : ∃ a, (galIso σ (φ.trans (specPIso g))).trans (φ.trans (specPIso g)).symm = a :=
    ⟨_, rfl⟩
  rw [ha] at hfix hdet ⊢
  clear ha hrat
  have hQL : IsNondeg (Q₁.baseChange Kb) := isNondeg_baseChange Q₁ hQ₁
  -- lift `a` to `u ∈ GSpin(F̄)`
  obtain ⟨u, hu⟩ := gspin_specP_surjective_SO (Q₁.baseChange Kb) hQL a.toLinearEquiv a.map_app hdet
  have hau : ∀ v, a v = specP (Q₁.baseChange Kb) u v := fun v => by rw [hu]; rfl
  have hmap : ∀ c, CliffordAlgebra.map a.toIsometry c = CliffordAlgebra.map (specPIso u).toIsometry c := by
    intro c
    congr 2
    ext v
    exact hau v
  have hux : Commute u (bcGSpin Q₁ x) := by
    have h := hfix (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ)) (bcGSpin Q₁ x).2 (Commute.refl _)
    rw [hmap, map_specPIso_apply] at h
    apply Subtype.ext; apply Units.ext
    show ((u : (CliffordAlgebra (Q₁.baseChange Kb))ˣ) : CliffordAlgebra (Q₁.baseChange Kb)) *
        (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra (Q₁.baseChange Kb)) =
      (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra (Q₁.baseChange Kb)) *
        ((u : (CliffordAlgebra (Q₁.baseChange Kb))ˣ) : CliffordAlgebra (Q₁.baseChange Kb))
    conv_rhs => rw [← h]
    simp only [mul_assoc, Units.inv_mul, mul_one]
  have hsemiL : Module.End.IsSemisimple (specP (Q₁.baseChange Kb) (bcGSpin Q₁ x) : Kb ⊗[F] V₁ →ₗ[Kb] _) := by
    rw [specP_bcGSpin]; exact isSemisimple_baseChange_algebraicClosure hxss
  obtain ⟨hc, hdet1⟩ := det_restrict_one_eq_one_of_commute hQL (bcGSpin Q₁ x) hsemiL u hux
  set E := Module.End.eigenspace (specP (Q₁.baseChange Kb) (bcGSpin Q₁ x) : Kb ⊗[F] V₁ →ₗ[Kb] _) 1
  have hmaps : ∀ v ∈ E, a v ∈ E := fun v hv => by
    rw [hau]; exact mapsTo_eigenspace_of_commute (commute_toLinearMap hc) 1 v hv
  -- vectors of `E` commute with `x̃` in the Clifford algebra
  have hιE : ∀ v ∈ E, ι (Q₁.baseChange Kb) v *
      (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra (Q₁.baseChange Kb)) =
      (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra (Q₁.baseChange Kb)) *
        ι (Q₁.baseChange Kb) v := by
    intro v hv
    have h1 : specP (Q₁.baseChange Kb) (bcGSpin Q₁ x) v = v := by
      rw [Module.End.mem_eigenspace_iff, one_smul] at hv; exact hv
    have h2 := ι_specP (bcGSpin Q₁ x) v
    rw [h1] at h2
    change ι (Q₁.baseChange Kb) v = (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra _) *
      ι (Q₁.baseChange Kb) v * (((bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ))⁻¹ :
        (CliffordAlgebra (Q₁.baseChange Kb))ˣ) : CliffordAlgebra _) at h2
    conv_lhs => rw [h2]
    simp only [mul_assoc, Units.inv_mul, mul_one]
  -- `a` is a scalar `c`, `c² = 1`, on `E`
  have hdimE : Module.finrank Kb E = Module.finrank F (fixedSub x) :=
    GGPData.finrank_eigenspace_bc_one Q₁ x
  have hBsymm : (bform (Q₁.baseChange Kb)).IsSymm := ⟨fun u v => bform_comm (Q₁.baseChange Kb) u v⟩
  have hpair := (pairing_eigenspace hBsymm hQL (isIsom_specP (bcGSpin Q₁ x)) hsemiL 1).2
  rw [inv_one] at hpair
  obtain ⟨c, hc2, hcE⟩ : ∃ c : Kb, c * c = 1 ∧ ∀ v ∈ E, a v = c • v := by
    obtain ⟨k, hk⟩ := id hodd
    rcases Nat.lt_or_ge (Module.finrank Kb E) 3 with hlt | hge
    · -- `E` is a line
      have h1 : Module.finrank Kb E = 1 := by omega
      have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ h1
      obtain ⟨e0, he0⟩ := exists_ne (0 : E)
      obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one (K := Kb) (V := E) h1 he0 (⟨a e0, hmaps _ e0.2⟩ : E)
      have hce : ∀ v ∈ E, a v = c • v := by
        intro v hv
        obtain ⟨t, ht⟩ := exists_smul_eq_of_finrank_eq_one (K := Kb) (V := E) h1 he0 (⟨v, hv⟩ : E)
        have ht' : t • (e0 : Kb ⊗[F] V₁) = v := congrArg Subtype.val ht
        have hc' : c • (e0 : Kb ⊗[F] V₁) = a e0 := congrArg Subtype.val hc
        rw [← ht', map_smul, ← hc', smul_comm]
      refine ⟨c, ?_, hce⟩
      -- `q(e₀) ≠ 0` and `q(c e₀) = q(e₀)`
      have hq : Q₁.baseChange Kb (e0 : Kb ⊗[F] V₁) ≠ 0 := by
        intro h0
        apply he0
        refine Subtype.ext (hpair _ e0.2 fun w hw => ?_)
        obtain ⟨t, ht⟩ := exists_smul_eq_of_finrank_eq_one (K := Kb) (V := E) h1 he0 (⟨w, hw⟩ : E)
        have hw' : w = t • (e0 : Kb ⊗[F] V₁) := (congrArg Subtype.val ht).symm
        rw [hw', LinearMap.map_smul, bform, QuadraticMap.associated_eq_self_apply, h0, smul_zero]
      have h := a.map_app e0
      rw [hce _ e0.2, QuadraticMap.map_smul, smul_eq_mul] at h
      exact (mul_left_eq_self₀.mp h).resolve_right hq
    · refine exists_smul_of_ι_mul_ι_eq (p := E) (Q := Q₁.baseChange Kb) hge ?_
        (T := a.toLinearEquiv.toLinearMap) hmaps fun u₁ hu₁ w₁ hw₁ hq₁ hq₂ => ?_
      · rw [isNondeg_iff]
        intro v hv
        exact Subtype.ext (hpair v v.2 fun w hw => by
          simpa [bform, QuadraticMap.associated_comp] using hv ⟨w, hw⟩)
      · have hcomm : Commute ((gspinPair (Q₁.baseChange Kb) hq₁ hq₂ : GSpin _) :
            (CliffordAlgebra (Q₁.baseChange Kb))ˣ) (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ)) := by
          apply Units.ext
          change ι (Q₁.baseChange Kb) u₁ * ι (Q₁.baseChange Kb) w₁ * _ =
            _ * (ι (Q₁.baseChange Kb) u₁ * ι (Q₁.baseChange Kb) w₁)
          rw [mul_assoc, hιE w₁ hw₁, ← mul_assoc, hιE u₁ hu₁, mul_assoc]
        have h := hfix _ (gspinPair (Q₁.baseChange Kb) hq₁ hq₂).2 hcomm
        rw [coe_gspinPair, map_mul, CliffordAlgebra.map_apply_ι,
          CliffordAlgebra.map_apply_ι] at h
        exact h
  -- `det a|_E = c^{dim E} = 1`, `dim E` odd
  have hdetc : ∀ R : Module.End Kb E, (∀ v : E, (R v : Kb ⊗[F] V₁) = c • (v : Kb ⊗[F] V₁)) →
      LinearMap.det R = c ^ Module.finrank Kb E := by
    intro R hR
    have : Module.Free Kb E := Module.Free.of_divisionRing Kb E
    have : Module.Finite Kb E := FiniteDimensional.finiteDimensional_submodule E
    have : R = c • LinearMap.id := LinearMap.ext fun v => Subtype.ext (by simp [hR])
    rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]
  rw [hdetc _ (fun v => by
    rw [LinearMap.restrict_apply]; exact (hau v).symm.trans (hcE v v.2)), hdimE] at hdet1
  obtain ⟨k, hk⟩ := hodd
  have hc1 : c = 1 := by
    rw [hk, pow_succ, pow_mul, sq, hc2, one_pow, one_mul] at hdet1
    exact hdet1
  rw [hcE w hw, hc1, one_smul]

/-- If `ψ` is rational on `p` (`ψ(1 ⊗ a) = 1 ⊗ θ(a)`), then `a_σ = ψ⁻¹ ∘ σψ` is the identity on
`p ⊗ F̄`. -/
theorem galIso_trans_symm_eq_self_of_tmul (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb))
    {p : Submodule F V₁} (θ : p → V₂) (hψ : ∀ a : p, ψ (1 ⊗ₜ (a : V₁)) = 1 ⊗ₜ θ a) (σ : GalF F)
    {w : Kb ⊗[F] V₁} (hw : w ∈ p.baseChange Kb) : (galIso σ ψ).trans ψ.symm w = w := by
  have hle : p.baseChange Kb ≤ LinearMap.eqLocus
      ((galIso σ ψ).trans ψ.symm).toLinearEquiv.toLinearMap LinearMap.id := by
    rw [Submodule.baseChange_eq_span, Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    change ψ.symm (galIso σ ψ (1 ⊗ₜ a)) = 1 ⊗ₜ a
    rw [galIso_apply, galV_tmul, map_one, hψ ⟨a, ha⟩, galV_tmul, map_one, ← hψ ⟨a, ha⟩,
      ψ.symm_apply_apply]
  exact hle hw

/-- `ψ = P(g) ∘ e` and `e` have cocycles of the same determinant. -/
theorem det_galIso_trans_specPIso [FiniteDimensional F V₁] [FiniteDimensional F V₂]
    (e : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) (g : GSpin (Q₂.baseChange Kb))
    (σ : GalF F) :
    LinearMap.det ((galIso σ (e.trans (specPIso g))).trans (e.trans (specPIso g)).symm :
        Kb ⊗[F] V₁ →ₗ[Kb] Kb ⊗[F] V₁) =
      LinearMap.det ((galIso σ e).trans e.symm : Kb ⊗[F] V₁ →ₗ[Kb] Kb ⊗[F] V₁) := by
  set M : (Kb ⊗[F] V₂) →ₗ[Kb] (Kb ⊗[F] V₂) := (specP _ (g⁻¹ * galGS Q₂ σ g)).toLinearMap
  have key : ((galIso σ (e.trans (specPIso g))).trans (e.trans (specPIso g)).symm :
      Kb ⊗[F] V₁ →ₗ[Kb] Kb ⊗[F] V₁) =
      ((e.symm.toLinearEquiv : (Kb ⊗[F] V₂) →ₗ[Kb] _) ∘ₗ M ∘ₗ
        (e.toLinearEquiv : (Kb ⊗[F] V₁) →ₗ[Kb] _)) ∘ₗ
        ((galIso σ e).trans e.symm : Kb ⊗[F] V₁ →ₗ[Kb] Kb ⊗[F] V₁) := by
    refine LinearMap.ext fun w => ?_
    change (e.trans (specPIso g)).symm (galV σ (specP _ g (e (galV σ⁻¹ w)))) =
      e.symm (specP _ (g⁻¹ * galGS Q₂ σ g) (e (e.symm (galV σ (e (galV σ⁻¹ w))))))
    rw [e.apply_symm_apply, map_mul, LinearEquiv.mul_apply, ← specP_galGS]
    change e.symm (specP _ g⁻¹ _) = _
    rfl
  have hc : LinearMap.det ((e.symm.toLinearEquiv : (Kb ⊗[F] V₂) →ₗ[Kb] _) ∘ₗ M ∘ₗ
      (e.toLinearEquiv : (Kb ⊗[F] V₁) →ₗ[Kb] _)) = LinearMap.det M :=
    LinearMap.det_conj M e.symm.toLinearEquiv
  have hM : LinearMap.det M = 1 := det_specP _
  rw [key, LinearMap.det_comp, hc, hM, one_mul]

/-- The cocycle of an inner twist has determinant `1`. -/
theorem det_galIso_trans_symm_innerTwist {m : ℕ} {Q : QuadraticForm F (Fin m → F)} (τ : InnerTwist Q)
    (σ : GalF F) :
    LinearMap.det ((galIso σ τ.φ).trans τ.φ.symm : Kb ⊗[F] (Fin m → F) →ₗ[Kb] _) = 1 := by
  have h := det_glOf_inv_mul_galGL τ σ
  rw [← glOf_galIso, ← glOf_symm, ← glOf_trans, coe_glOf, LinearMap.det_toMatrix] at h
  exact h

end OddFixed

section Torus

/-! ### The cocycle lies in `S_x` -/

open TorusTransfer

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
  {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}

/-- If `C(ψ)` carries the rational `x` to the rational `y`, then `a_σ = ψ⁻¹ ∘ σψ` fixes `x` (through
`C(a_σ)`). -/
theorem map_galIso_trans_symm_bcUnits (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb))
    {x : (CliffordAlgebra Q₁)ˣ} {y : (CliffordAlgebra Q₂)ˣ}
    (h : CliffordAlgebra.map ψ.toIsometry (bcUnits Q₁ x : CliffordAlgebra _) = bcUnits Q₂ y)
    (σ : GalF F) :
    CliffordAlgebra.map ((galIso σ ψ).trans ψ.symm).toIsometry (bcUnits Q₁ x : CliffordAlgebra _) =
      bcUnits Q₁ x := by
  have hx : galC Q₁ σ (bcUnits Q₁ x : CliffordAlgebra _) = bcUnits Q₁ x :=
    galC_bcHom Q₁ σ (x : CliffordAlgebra Q₁)
  have hy : galC Q₂ σ (bcUnits Q₂ y : CliffordAlgebra _) = bcUnits Q₂ y :=
    galC_bcHom Q₂ σ (y : CliffordAlgebra Q₂)
  have h1 : CliffordAlgebra.map (galIso σ ψ).toIsometry (bcUnits Q₁ x : CliffordAlgebra _) =
      bcUnits Q₂ y := by
    rw [← hx, ← galC_map, h, hy]
  rw [map_trans_apply, h1, ← h, map_symm_map]

/-- **The cocycle lies in `S_x`.**  If `C(ψ)` carries `x` to a rational element, `det a_σ = 1`, and
`a_σ = ψ⁻¹ ∘ σψ` is the identity on `W'_x ⊗ F̄`, then `a_σ = P(t_σ)` with `t_σ ∈ T_x(F̄)`: lift `a_σ`
to `GSpin(W)(F̄)` (`a_σ ∈ SO`); `C(a_σ)` is conjugation by the lift, which therefore commutes with `x`. -/
theorem inv_mul_galGL_glOf_mem_torusBarFbar (d : GGPData F) (x : GSpin d.QW)
    {Q' : QuadraticForm F (Fin d.m → F)} (ψ : (d.QW.baseChange Kb).IsometryEquiv (Q'.baseChange Kb))
    {y : (CliffordAlgebra Q')ˣ}
    (hxy : CliffordAlgebra.map ψ.toIsometry (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ) :
      CliffordAlgebra _) = bcUnits Q' y) (σ : GalF F)
    (hdet : (((glOf ψ)⁻¹ * galGL d.m σ (glOf ψ) : GL (Fin d.m) Kb) :
      Matrix (Fin d.m) (Fin d.m) Kb).det = 1)
    (hfix : ∀ w ∈ (fixedSub x).baseChange Kb, (galIso σ ψ).trans ψ.symm w = w) :
    (glOf ψ)⁻¹ * galGL d.m σ (glOf ψ) ∈ d.torusBarFbar x := by
  have hx := map_galIso_trans_symm_bcUnits ψ hxy σ
  obtain ⟨a, ha⟩ : ∃ a, (galIso σ ψ).trans ψ.symm = a := ⟨_, rfl⟩
  have hga : glOf a = (glOf ψ)⁻¹ * galGL d.m σ (glOf ψ) := by
    rw [← ha, glOf_trans, glOf_symm, glOf_galIso]
  rw [ha] at hx hfix
  rw [← hga] at hdet ⊢
  clear ha hga
  have hdet' : LinearMap.det (a.toLinearEquiv : Kb ⊗[F] (Fin d.m → F) →ₗ[Kb] _) = 1 := by
    rw [← LinearMap.det_toMatrix (bcBasis F d.m)]; exact hdet
  obtain ⟨u, hu⟩ := gspin_specP_surjective_SO (d.QW.baseChange Kb)
    (isNondeg_baseChange d.QW d.nondeg) a.toLinearEquiv a.map_app hdet'
  have hau : ∀ v, a v = specPIso u v := fun v => by rw [specPIso_apply, hu]; rfl
  have hgl : glOf a = glOf (specPIso u) := Units.ext (congrArg (LinearMap.toMatrix _ _)
    (LinearMap.ext hau))
  have hmap : CliffordAlgebra.map a.toIsometry = CliffordAlgebra.map (specPIso u).toIsometry := by
    congr 1
    ext v
    exact hau v
  refine ⟨u, ⟨?_, fun w hw => (hau w).symm.trans (hfix w hw)⟩, (hgl.trans (glOf_specPIso u)).symm⟩
  rw [hmap, map_specPIso_apply] at hx
  apply Units.ext
  show ((u : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb)) *
      (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra _) =
    (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra _) *
      ((u : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb))
  conv_rhs => rw [← hx]
  simp only [mul_assoc, Units.inv_mul, mul_one]

end Torus

/-! ### The cocycle of `y ∈ Γ(G_α, H_α)` strongly stably conjugate to `x` -/

namespace GGPData

open TorusTransfer

variable (d : GGPData F)

/-- `ψ : W_{F̄} ≃ W_{α,F̄}` **computes the class of `y`** (Thesis Prop. 6.6.1(iii), proof): `C(ψ)` carries
`x` to `y`, and `a_σ = ψ⁻¹ ∘ σψ` lies in `S_x(F̄)` for every `σ`.  Then `σ ↦ a_σ` is a cocycle of
`Γ_F` in `S_x` (`IsStableIso.cocycle`) whose image in `H¹(F, SO(W))` is `α`
(`IsStableIso.twistIdx`).  The thesis's cocycle `g⁻¹ c_{α,σ} σ(g)` takes values in `T_x`; this is its
image in `S_x = T_x/A_{G,H}`, as in `n_alpha_eq_card_twistIdx`. -/
def IsStableIso (τ : InnerTwist d.QW) (x : GSpin d.QW) (y : GSpin (d.twist τ).QW)
    (ψ : (d.QW.baseChange Kb).IsometryEquiv (τ.Q'.baseChange Kb)) : Prop :=
  CliffordAlgebra.map ψ.toIsometry (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra _) =
      bcUnits τ.Q' (y : (CliffordAlgebra τ.Q')ˣ) ∧
    ∀ σ : GalF F, (glOf ψ)⁻¹ * galGL d.m σ (glOf ψ) ∈ d.torusBarFbar x

variable {d}

/-- The cocycle `σ ↦ ψ⁻¹ ∘ σψ` in `S_x`. -/
def IsStableIso.cocycle {τ : InnerTwist d.QW} {x : GSpin d.QW} {y : GSpin (d.twist τ).QW}
    {ψ : (d.QW.baseChange Kb).IsometryEquiv (τ.Q'.baseChange Kb)} (h : d.IsStableIso τ x y ψ) :
    GalCocycle (d.torusBarFbar x) :=
  conjCocycle (glOf ψ) h.2

/-- The class of the cocycle of `y` maps to `α` in `H¹(F, SO(W))`. -/
theorem IsStableIso.twistIdx (IF : InnerFormSystem d) {α : IF.Idx} {x : GSpin d.QW}
    {y : GSpin (IF.data α).QW}
    {ψ : (d.QW.baseChange Kb).IsometryEquiv ((IF.twist α).Q'.baseChange Kb)}
    (h : d.IsStableIso (IF.twist α) x y ψ) : TwistIdx IF x (H1.mk h.cocycle) α :=
  ⟨h.cocycle, rfl, (isTwistBy_iff _ _ _).2 ⟨ψ, fun _ => rfl⟩⟩

/-- **The cocycle of `y`, when `dim W'_x` is odd** (Thesis Prop. 6.6.1(iii), proof): the witness `g` of
strong stable conjugacy on the `W`-factor gives `ψ = P(g) ∘ φ_α`, and `a_σ = ψ⁻¹ ∘ σψ` is the
identity on `W'_x ⊗ F̄` (`galIso_trans_symm_eq_self_of_odd`), so it lies in `S_x(F̄)`.  For
`x ∈ Γ(G,H)` the `-1`-eigenspace of `x̄` has even dimension, so this is the case `dim W` odd. -/
theorem exists_isStableIso_of_odd (τ : InnerTwist d.QW) {x : GSpin d.QW} (hx : d.IsGammaElt x)
    {y : GSpin (d.twist τ).QW} (hxy : d.StronglyStablyConjW τ x y)
    (hodd : Odd (Module.finrank F (fixedSub x))) : ∃ ψ, d.IsStableIso τ x y ψ := by
  obtain ⟨g, hg, hconj, hrat⟩ := hxy.1
  set g' : GSpin (τ.Q'.baseChange Kb) := ⟨g, hg⟩
  have hxss := isSemisimple_specP_of_isSS d.QW x hx.1
  have hmap : CliffordAlgebra.map (τ.φ.trans (specPIso g')).toIsometry
      (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra _) =
      bcUnits τ.Q' (y : (CliffordAlgebra τ.Q')ˣ) := by
    rw [← psiA_eq_map]
    exact congrArg Units.val hconj
  refine ⟨τ.φ.trans (specPIso g'), hmap, fun σ => ?_⟩
  have hdet := det_glOf_trans_specPIso τ g' σ
  refine inv_mul_galGL_glOf_mem_torusBarFbar d x _ hmap σ hdet fun w hw => ?_
  have hdet' : LinearMap.det (((galIso σ (τ.φ.trans (specPIso g'))).trans
      (τ.φ.trans (specPIso g')).symm).toLinearEquiv : Kb ⊗[F] (Fin d.m → F) →ₗ[Kb] _) = 1 := by
    rw [det_galIso_trans_specPIso]
    exact det_galIso_trans_symm_innerTwist τ σ
  rw [← GGPData.eigenspace_bc_one] at hw
  exact galIso_trans_symm_eq_self_of_odd d.nondeg τ.φ g' hxss hrat σ hdet' hodd hw

end GGPData

end GSpinGGP
