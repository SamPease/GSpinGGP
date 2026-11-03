/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.GaloisTorus
import GSpinGGP.GGP.TwistDescent
import GSpinGGP.GGP.TorusTransport
import GSpinGGP.GGP.Steinberg

/-!
# The cocycle of a strongly stably conjugate element

For an `F̄`-isometry `ψ : W_{F̄} ≃ W'_{F̄}`, its Galois conjugate `σψ = σ ∘ ψ ∘ σ⁻¹` (`galIso`) is again an
isometry, with matrix `σ(Ψ)` (`glOf_galIso`), and `C(ψ)` intertwines the Galois actions on the Clifford
algebras up to replacing `ψ` by `σψ` (`galC_map`).  Own work, elementary.
-/

noncomputable section

namespace GSpinGGP

open CliffordAlgebra TwistDescent
open scoped TensorProduct

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

section GalIso

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]

/-- `C(ψ)` intertwines the Galois actions when `ψ'` is the Galois conjugate of `ψ`. -/
theorem galC_map_of_galV {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂} (σ : GalF F)
    (ψ ψ' : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb))
    (h : ∀ w, galV σ (ψ w) = ψ' (galV σ w)) (a : CliffordAlgebra (Q₁.baseChange Kb)) :
    galC Q₂ σ (CliffordAlgebra.map ψ.toIsometry a) =
      CliffordAlgebra.map ψ'.toIsometry (galC Q₁ σ a) := by
  induction a using CliffordAlgebra.induction with
  | algebraMap r => simp only [AlgHom.commutes, galC_algebraMap]
  | ι x => rw [map_apply_ι, galC_ι, galC_ι, map_apply_ι]; exact congrArg _ (h x)
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb, map_mul, map_mul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- `q_{F̄}(σ w) = σ(q_{F̄}(w))`. -/
theorem baseChange_galV (Q : QuadraticForm F V₁) (σ : GalF F) (w : Kb ⊗[F] V₁) :
    Q.baseChange Kb (galV σ w) = σ (Q.baseChange Kb w) := by
  apply (algebraMap Kb (CliffordAlgebra (Q.baseChange Kb))).injective
  rw [← ι_sq_scalar, ← galC_algebraMap Q σ, ← ι_sq_scalar, map_mul, galC_ι]

/-- The Galois conjugate `σψ = σ ∘ ψ ∘ σ⁻¹` of an `F̄`-isometry, as an `F̄`-isometry. -/
def galIso {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂} (σ : GalF F)
    (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) :
    (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb) where
  toFun w := galV σ (ψ (galV σ⁻¹ w))
  invFun w := galV σ (ψ.symm (galV σ⁻¹ w))
  left_inv w := by simp only [galV_inv_galV, QuadraticMap.IsometryEquiv.symm_apply_apply,
    galV_galV_inv]
  right_inv w := by simp only [galV_inv_galV, QuadraticMap.IsometryEquiv.apply_symm_apply,
    galV_galV_inv]
  map_add' w w' := by simp only [map_add]
  map_smul' c w := by
    rw [galV_smul, map_smul, galV_smul, RingHom.id_apply]
    congr 1
    exact AlgEquiv.apply_symm_apply σ c
  map_app' w := by
    change Q₂.baseChange Kb (galV σ (ψ (galV σ⁻¹ w))) = _
    rw [baseChange_galV, QuadraticMap.IsometryEquiv.map_app, ← baseChange_galV, galV_galV_inv]

theorem galIso_apply {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂} (σ : GalF F)
    (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) (w : Kb ⊗[F] V₁) :
    galIso σ ψ w = galV σ (ψ (galV σ⁻¹ w)) := rfl

theorem galIso_galV {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂} (σ : GalF F)
    (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb)) (w : Kb ⊗[F] V₁) :
    galIso σ ψ (galV σ w) = galV σ (ψ w) := by
  rw [galIso_apply, galV_inv_galV]

/-- `σ(C(ψ) a) = C(σψ)(σ a)`. -/
theorem galC_map {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂} (σ : GalF F)
    (ψ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb))
    (a : CliffordAlgebra (Q₁.baseChange Kb)) :
    galC Q₂ σ (CliffordAlgebra.map ψ.toIsometry a) =
      CliffordAlgebra.map (galIso σ ψ).toIsometry (galC Q₁ σ a) :=
  galC_map_of_galV σ ψ _ (fun w => (galIso_galV σ ψ w).symm) a

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

/-- `Ad(g) ∘ C(φ) = C(P(g) ∘ φ)`. -/
theorem psiA_eq_map (φ : (Q₁.baseChange Kb).IsometryEquiv (Q₂.baseChange Kb))
    (g : GSpin (Q₂.baseChange Kb)) (a : CliffordAlgebra (Q₁.baseChange Kb)) :
    psiA φ (g : (CliffordAlgebra _)ˣ) a = CliffordAlgebra.map (φ.trans (specPIso g)).toIsometry a := by
  rw [psiA, ← map_specPIso_apply]
  show _ = CliffordAlgebra.map ((specPIso g).toIsometry.comp φ.toIsometry) a
  rw [← CliffordAlgebra.map_comp_map]
  rfl

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
          (CliffordAlgebra.map (galIso σ ψ).toIsometry (w : CliffordAlgebra _)) := by
        rw [← AlgHom.comp_apply, CliffordAlgebra.map_comp_map]; rfl
    _ = w := by rw [key, map_symm_map]

end Strong

namespace Steinberg

open IsomCent

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

/-- **Elements commuting with `x` have determinant `1` on `W₊₁`**, over an algebraically closed
field: if `g` commutes with `x` and `P(x)` is semisimple, `det P(g)|_{E₁(P x)} = 1`. -/
theorem det_restrict_one_eq_one_of_commute [CharZero K] [IsAlgClosed K] [FiniteDimensional K V]
    (hQ : IsNondeg Q) (x : GSpin Q) (hx : Module.End.IsSemisimple (specP Q x : V →ₗ[K] V))
    (g : GSpin Q) (hgx : Commute g x) :
    ∃ hc : Commute (specP Q g) (specP Q x), LinearMap.det ((specP Q g : V →ₗ[K] V).restrict
      (mapsTo_eigenspace_of_commute (commute_toLinearMap hc) 1)) = 1 := by
  have hc : Commute (specP Q g) (specP Q x) := by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, hgx.eq]
  refine ⟨hc, ?_⟩
  have hB : (bform Q).IsSymm := ⟨fun u v => bform_comm Q u v⟩
  have hn := (commute_iff_det_negFixedSub hQ x hx g hc).1 hgx
  have hdet := det_eq_det_one_mul_det_neg_one_of_charZero hB hQ (isIsom_specP x) hx
    (isIsom_specP g) (commute_toLinearMap hc)
  rw [hn, mul_one, det_specP] at hdet
  exact hdet.symm

end Steinberg

section OddFixed

open TorusTransfer Steinberg IsomCent

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
  {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}

/-- `dim_{F̄} E₁(P(x)_{F̄}) = dim_F W'_x`. -/
theorem finrank_eigenspace_one_bcGSpin [FiniteDimensional F V₁] (x : GSpin Q₁) :
    Module.finrank Kb (Module.End.eigenspace (specP _ (bcGSpin Q₁ x) : Kb ⊗[F] V₁ →ₗ[Kb] _) 1) =
      Module.finrank F (fixedSub x) := by
  have h : Module.End.eigenspace (specP _ (bcGSpin Q₁ x) : Kb ⊗[F] V₁ →ₗ[Kb] _) 1 =
      LinearMap.ker (((specP Q₁ x : V₁ →ₗ[F] V₁) - LinearMap.id).baseChange Kb) := by
    rw [specP_bcGSpin, Module.End.eigenspace_def, LinearMap.baseChange_sub, LinearMap.baseChange_id]
    simp only [one_smul]
    rfl
  rw [h, fixedSub]
  exact (LinearMap.tensorKerEquiv Kb Kb _).finrank_eq.symm.trans Module.finrank_baseChange

set_option maxHeartbeats 1000000 in
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
    finrank_eigenspace_one_bcGSpin x
  have hBsymm : (bform (Q₁.baseChange Kb)).IsSymm := ⟨fun u v => bform_comm (Q₁.baseChange Kb) u v⟩
  have hpair := (pairing_eigenspace hBsymm hQL (isIsom_specP (bcGSpin Q₁ x)) hsemiL 1).2
  rw [inv_one] at hpair
  obtain ⟨c, hc2, hcE⟩ : ∃ c : Kb, c * c = 1 ∧ ∀ v ∈ E, a v = c • v := by
    rcases hodd with ⟨k, hk⟩
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
    haveI : Module.Free Kb E := Module.Free.of_divisionRing Kb E
    haveI : Module.Finite Kb E := FiniteDimensional.finiteDimensional_submodule E
    have : R = c • LinearMap.id := LinearMap.ext fun v => Subtype.ext (by simp [hR])
    rw [this, LinearMap.det_smul, LinearMap.det_id, mul_one]
  rw [hdetc _ (fun v => by
    rw [LinearMap.restrict_coe_apply]; exact (hau v).symm.trans (hcE v v.2)), hdimE] at hdet1
  obtain ⟨k, hk⟩ := hodd
  have hc1 : c = 1 := by
    rw [hk, pow_succ, pow_mul, sq, hc2, one_pow, one_mul] at hdet1
    exact hdet1
  rw [hcE w hw, hc1, one_smul]

end OddFixed

end GSpinGGP
