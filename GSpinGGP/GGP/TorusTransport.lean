import GSpinGGP.GGP.TorusCommute

/-!
# Transport of centralizers along a strong stable conjugacy

If `Ad(g) ∘ C(φ)` carries `x̄` to `ȳ` and is defined over `F` on the centralizer of `x`
(`TorusTransfer.RatAt`), it restricts to an isomorphism of groups from the centralizer of `x` in
`GSpin(Q₁)(F)` to that of `y` in `GSpin(Q₂)(F)`, which also matches the pointwise stabilizers of
`W'_x` and `W'_y` (Thesis Prop. 6.6.1(ii), the torus isomorphism).
-/

noncomputable section

open CliffordAlgebra Module
open scoped TensorProduct

namespace GSpinGGP
namespace TorusTransfer

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
  {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}

section Inverse

variable (φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F)))
  (g : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ)

theorem map_symm_map (a : CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F))) :
    CliffordAlgebra.map φ.symm.toIsometry (CliffordAlgebra.map φ.toIsometry a) = a :=
  (CliffordAlgebra.equivOfIsometry φ).symm_apply_apply a

theorem map_map_symm (b : CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F))) :
    CliffordAlgebra.map φ.toIsometry (CliffordAlgebra.map φ.symm.toIsometry b) = b :=
  (CliffordAlgebra.equivOfIsometry φ).apply_symm_apply b

/-- The inverse of `Ad(g) ∘ C(φ)` is `Ad(C(φ⁻¹)(g⁻¹)) ∘ C(φ⁻¹)`. -/
theorem psiA_symm_psiA (a : CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F))) :
    psiA φ.symm (cliffUnits φ.symm g⁻¹) (psiA φ g a) = a := by
  have e1 : ((cliffUnits φ.symm g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
      CliffordAlgebra.map φ.symm.toIsometry ((g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) := rfl
  have e2 : (((cliffUnits φ.symm g⁻¹)⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
      CliffordAlgebra.map φ.symm.toIsometry (g : CliffordAlgebra _) := by
    rw [← map_inv, inv_inv]; rfl
  simp only [psiA, e1, e2, map_mul, map_symm_map]
  simp only [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  rw [mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]

theorem psiA_psiA_symm (b : CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F))) :
    psiA φ g (psiA φ.symm (cliffUnits φ.symm g⁻¹) b) = b := by
  have e1 : ((cliffUnits φ.symm g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
      CliffordAlgebra.map φ.symm.toIsometry ((g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) := rfl
  have e2 : (((cliffUnits φ.symm g⁻¹)⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
      CliffordAlgebra.map φ.symm.toIsometry (g : CliffordAlgebra _) := by
    rw [← map_inv, inv_inv]; rfl
  simp only [psiA, e1, e2, map_mul, map_map_symm]
  simp only [← mul_assoc, Units.mul_inv, one_mul]
  rw [mul_assoc, Units.mul_inv, mul_one]

theorem psiU_symm_psiU (z : (CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F)))ˣ) :
    psiU φ.symm (cliffUnits φ.symm g⁻¹) (psiU φ g z) = z :=
  Units.ext (psiA_symm_psiA φ g z)

theorem psiU_psiU_symm (z : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ) :
    psiU φ g (psiU φ.symm (cliffUnits φ.symm g⁻¹) z) = z :=
  Units.ext (psiA_psiA_symm φ g z)

variable {φ g}

/-- The inverse transport is again defined over `F` on the centralizer of `y`. -/
theorem ratAt_symm (hg : g ∈ GSpin (Q₂.baseChange (AlgebraicClosure F))) {x : GSpin Q₁}
    {y : (CliffordAlgebra Q₂)ˣ} (hrat : RatAt φ g (x : (CliffordAlgebra Q₁)ˣ))
    (hconj : psiU φ g (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ)) = bcUnits Q₂ y) :
    RatAt φ.symm (cliffUnits φ.symm g⁻¹) y := by
  intro σ z hz hzy
  set w := psiU φ.symm (cliffUnits φ.symm g⁻¹) z
  have hw : w ∈ GSpin (Q₁.baseChange (AlgebraicClosure F)) := by
    show cliffUnits φ.symm g⁻¹ * cliffUnits φ.symm z * (cliffUnits φ.symm g⁻¹)⁻¹ ∈ _
    have hg' := cliffUnits_mem_GSpin φ.symm ((GSpin _).inv_mem hg)
    exact (GSpin _).mul_mem ((GSpin _).mul_mem hg' (cliffUnits_mem_GSpin φ.symm hz))
      ((GSpin _).inv_mem hg')
  have hwx : Commute w (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ)) := by
    have := hzy.map (psiU φ.symm (cliffUnits φ.symm g⁻¹))
    rwa [← hconj, psiU_symm_psiU] at this
  have h := hrat σ w hw hwx
  rw [← psiU_eq, psiU_psiU_symm] at h
  change galC Q₁ σ (w : CliffordAlgebra _) =
    psiA φ.symm (cliffUnits φ.symm g⁻¹) (galC Q₂ σ z)
  rw [h]
  exact (psiA_symm_psiA φ g _).symm

end Inverse

section Hom

variable {φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F))}
  {g : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ}
  (hg : g ∈ GSpin (Q₂.baseChange (AlgebraicClosure F))) {x : GSpin Q₁}
  (hrat : RatAt φ g (x : (CliffordAlgebra Q₁)ˣ))

theorem bcUnits_GSpin_injective (Q : QuadraticForm F V₁) :
    Function.Injective fun t : GSpin Q => bcUnits Q (t : (CliffordAlgebra Q)ˣ) :=
  fun _ _ h => Subtype.ext (bcUnits_injective Q h)

theorem commute_of_mem_centralizer (t : Subgroup.centralizer {x}) :
    Commute ((t : GSpin Q₁) : (CliffordAlgebra Q₁)ˣ) (x : (CliffordAlgebra Q₁)ˣ) :=
  congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp t.2 x rfl).symm

/-- The transport of `t ∈ Z(x)(F)`: the rational element with base change `Ad(g) C(φ)(t̄)`. -/
def transport (t : Subgroup.centralizer {x}) : GSpin Q₂ :=
  Classical.choose (exists_transport hg hrat (t : GSpin Q₁) (commute_of_mem_centralizer t))

theorem bcUnits_transport (t : Subgroup.centralizer {x}) :
    bcUnits Q₂ ((transport hg hrat t : GSpin Q₂) : (CliffordAlgebra Q₂)ˣ) =
      psiU φ g (bcUnits Q₁ ((t : GSpin Q₁) : (CliffordAlgebra Q₁)ˣ)) :=
  Classical.choose_spec (exists_transport hg hrat (t : GSpin Q₁) (commute_of_mem_centralizer t))

/-- The transport as a group homomorphism `Z(x)(F) → GSpin(Q₂)(F)`. -/
def transportHom : Subgroup.centralizer {x} →* GSpin Q₂ where
  toFun := transport hg hrat
  map_one' := bcUnits_GSpin_injective Q₂ (by
    show bcUnits Q₂ _ = bcUnits Q₂ _
    rw [bcUnits_transport]; simp)
  map_mul' s t := bcUnits_GSpin_injective Q₂ (by
    show bcUnits Q₂ _ = bcUnits Q₂ _
    simp only [Subgroup.coe_mul, map_mul, bcUnits_transport])

theorem bcUnits_transportHom (t : Subgroup.centralizer {x}) :
    bcUnits Q₂ ((transportHom hg hrat t : GSpin Q₂) : (CliffordAlgebra Q₂)ˣ) =
      psiU φ g (bcUnits Q₁ ((t : GSpin Q₁) : (CliffordAlgebra Q₁)ˣ)) :=
  bcUnits_transport hg hrat t

/-- `b̄` commutes with `ι(w)` iff `P(b)_{F̄}` fixes `w`. -/
theorem bcUnits_commute_ι_iff {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)
    (b : GSpin Q) (w : AlgebraicClosure F ⊗[F] V) :
    ((bcUnits Q (b : (CliffordAlgebra Q)ˣ) : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) *
        ι (Q.baseChange (AlgebraicClosure F)) w =
      ι (Q.baseChange (AlgebraicClosure F)) w *
        ((bcUnits Q (b : (CliffordAlgebra Q)ˣ) : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) ↔
      (specP Q b : V →ₗ[F] V).baseChange (AlgebraicClosure F) w = w := by
  set B := bcUnits Q (b : (CliffordAlgebra Q)ˣ)
  have h := bcUnits_conj_ι' Q b w
  constructor
  · intro hc
    apply ι_injective (Q.baseChange (AlgebraicClosure F))
    rw [← h, hc, mul_assoc, Units.mul_inv, mul_one]
  · intro hf
    rw [hf] at h
    have e : ((B : (CliffordAlgebra _)ˣ) : CliffordAlgebra (Q.baseChange (AlgebraicClosure F))) *
        ι _ w = (B : CliffordAlgebra _) * ι _ w * ((B⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) *
          (B : CliffordAlgebra _) := by
      rw [Units.inv_mul_cancel_right]
    rw [e, h]

include hg in
/-- **The transport preserves pointwise stabilizers**: if `t` fixes `W'_x`, its transport fixes
`W'_y`. -/
theorem transportHom_mem_fixerOf {y : GSpin Q₂}
    (hconj : psiU φ g (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ)) = bcUnits Q₂ (y : (CliffordAlgebra Q₂)ˣ))
    (t : Subgroup.centralizer {x}) (ht : (t : GSpin Q₁) ∈ fixerOf Q₁ (fixedSub x)) :
    transportHom hg hrat t ∈ fixerOf Q₂ (fixedSub y) := by
  intro w hw
  have hw' : specP Q₂ y w = w := by
    have := LinearMap.mem_ker.mp hw
    rwa [LinearMap.sub_apply, sub_eq_zero] at this
  apply Module.Flat.tensorProduct_mk_injective F V₂ (AlgebraicClosure F)
  show (1 : AlgebraicClosure F) ⊗ₜ[F] (specP Q₂ (transportHom hg hrat t) w) = 1 ⊗ₜ w
  rw [← LinearEquiv.coe_coe, ← LinearMap.baseChange_tmul]
  set W := ι (Q₂.baseChange (AlgebraicClosure F)) ((1 : AlgebraicClosure F) ⊗ₜ[F] w)
  have hyW := (bcUnits_commute_ι_iff Q₂ y (1 ⊗ₜ w)).2 (by
    rw [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, hw'])
  obtain ⟨u, hu⟩ := hg.2.2 ((1 : AlgebraicClosure F) ⊗ₜ[F] w)
  set u' := φ.symm u
  have hψ : psiA φ g (ι _ u') = W := by
    rw [psiA_ι, φ.apply_symm_apply, hu]
    simp only [mul_assoc, Units.mul_inv, mul_one]
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have hx' : ((bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ) : (CliffordAlgebra _)ˣ) :
      CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F))) * ι _ u' =
      ι _ u' * ((bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ) : (CliffordAlgebra _)ˣ) :
        CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F))) := by
    apply psiA_injective φ g
    rw [psiA_mul, psiA_mul, hψ, ← coe_psiU, hconj, hyW]
  have hxfix := (bcUnits_commute_ι_iff Q₁ x u').1 hx'
  have htfix : (specP Q₁ (t : GSpin Q₁) : V₁ →ₗ[F] V₁).baseChange (AlgebraicClosure F) u' = u' := by
    refine baseChange_fix_of_fix ((specP Q₁ x : V₁ →ₗ[F] V₁) - LinearMap.id) _
      (fun v hv => ht v hv) u' ?_
    rw [LinearMap.mem_ker, LinearMap.baseChange_sub, LinearMap.sub_apply, LinearMap.baseChange_id,
      LinearMap.id_apply, hxfix, sub_self]
  have htW := (bcUnits_commute_ι_iff Q₁ (t : GSpin Q₁) u').2 htfix
  refine (bcUnits_commute_ι_iff Q₂ (transportHom hg hrat t) (1 ⊗ₜ w)).1 ?_
  rw [bcUnits_transportHom, coe_psiU]
  change _ * W = W * _
  rw [← hψ, ← psiA_mul, htW, psiA_mul]

include hg in
theorem transportHom_mem_centralizer {y : GSpin Q₂}
    (hconj : psiU φ g (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ)) = bcUnits Q₂ (y : (CliffordAlgebra Q₂)ˣ))
    (t : Subgroup.centralizer {x}) :
    transportHom hg hrat t ∈ Subgroup.centralizer {y} := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff.mp hh]
  apply bcUnits_GSpin_injective Q₂
  show bcUnits Q₂ _ = bcUnits Q₂ _
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, bcUnits_transportHom, ← hconj,
    ← map_mul (psiU φ g), ← map_mul (psiU φ g), ← map_mul (bcUnits Q₁), ← map_mul (bcUnits Q₁),
    (commute_of_mem_centralizer t).eq]

end Hom

section Equiv

/-- `Z(x) ∩ Fix(W'_x)`, the subgroup `T_x` of `GSpin(Q)(F)` (`GGPData.torusOf`). -/
def torusSub {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V) (x : GSpin Q) :
    Subgroup (GSpin Q) :=
  Subgroup.centralizer {x} ⊓ fixerOf Q (fixedSub x)

variable {φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F))}
  {g : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ}
  (hg : g ∈ GSpin (Q₂.baseChange (AlgebraicClosure F))) {x : GSpin Q₁} {y : GSpin Q₂}
  (hrat : RatAt φ g (x : (CliffordAlgebra Q₁)ˣ))
  (hconj : psiU φ g (bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ)) = bcUnits Q₂ (y : (CliffordAlgebra Q₂)ˣ))

include hconj in
theorem psiU_symm_bcUnits :
    psiU φ.symm (cliffUnits φ.symm g⁻¹) (bcUnits Q₂ (y : (CliffordAlgebra Q₂)ˣ)) =
      bcUnits Q₁ (x : (CliffordAlgebra Q₁)ˣ) := by
  rw [← hconj, psiU_symm_psiU]

include hg in
theorem mem_GSpin_symm : cliffUnits φ.symm g⁻¹ ∈ GSpin (Q₁.baseChange (AlgebraicClosure F)) :=
  cliffUnits_mem_GSpin φ.symm ((GSpin _).inv_mem hg)

/-- **The torus isomorphism** `T_x(F) ≃ T_y(F)` (Thesis Prop. 6.6.1(ii)): the restriction of
`Ad(g) ∘ C(φ)`, with inverse `Ad(C(φ⁻¹)(g⁻¹)) ∘ C(φ⁻¹)`. -/
def transportEquiv : torusSub Q₁ x ≃* torusSub Q₂ y where
  toFun t := ⟨transportHom hg hrat ⟨t, t.2.1⟩, transportHom_mem_centralizer hg hrat hconj _,
    transportHom_mem_fixerOf hg hrat hconj _ t.2.2⟩
  invFun s := ⟨transportHom (mem_GSpin_symm hg) (ratAt_symm hg hrat hconj) ⟨s, s.2.1⟩,
    transportHom_mem_centralizer _ _ (psiU_symm_bcUnits hconj) _,
    transportHom_mem_fixerOf _ _ (psiU_symm_bcUnits hconj) _ s.2.2⟩
  left_inv t := Subtype.ext (bcUnits_GSpin_injective Q₁ (by
    show bcUnits Q₁ _ = bcUnits Q₁ _
    rw [bcUnits_transportHom]
    erw [bcUnits_transportHom]
    rw [psiU_symm_psiU]))
  right_inv s := Subtype.ext (bcUnits_GSpin_injective Q₂ (by
    show bcUnits Q₂ _ = bcUnits Q₂ _
    rw [bcUnits_transportHom]
    erw [bcUnits_transportHom]
    rw [psiU_psiU_symm]))
  map_mul' s t := by
    apply Subtype.ext
    change transportHom hg hrat ⟨s * t, (s * t).2.1⟩ =
      transportHom hg hrat ⟨s, s.2.1⟩ * transportHom hg hrat ⟨t, t.2.1⟩
    rw [← map_mul]
    rfl

theorem bcUnits_transportEquiv (t : torusSub Q₁ x) :
    bcUnits Q₂ (((transportEquiv hg hrat hconj t : torusSub Q₂ y) : GSpin Q₂) :
      (CliffordAlgebra Q₂)ˣ) = psiU φ g (bcUnits Q₁ ((t : GSpin Q₁) : (CliffordAlgebra Q₁)ˣ)) :=
  bcUnits_transportHom hg hrat ⟨t, t.2.1⟩

/-- `Ad(g) ∘ C(φ)` fixes the scalars `F^×`. -/
theorem psiU_bcUnits_scalar {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂]
    [Module F V₂] {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}
    (φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F)))
    (g : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ) (c : Fˣ) :
    psiU φ g (bcUnits Q₁ ((scalarGSpin Q₁ c : GSpin Q₁) : (CliffordAlgebra Q₁)ˣ)) =
      bcUnits Q₂ ((scalarGSpin Q₂ c : GSpin Q₂) : (CliffordAlgebra Q₂)ˣ) := by
  apply Units.ext
  rw [coe_psiU]
  show psiA φ g (bcHom Q₁ (algebraMap F _ (c : F))) = bcHom Q₂ (algebraMap F _ (c : F))
  rw [bcHom_algebraMap, bcHom_algebraMap, psiA, AlgHom.commutes, ← Algebra.commutes,
    mul_assoc, Units.mul_inv, mul_one]

end Equiv

section Continuity

/-- The base change `C(Q) → C(Q_{F̄})` as an `F`-linear map. -/
def bcHomL {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V) :
    CliffordAlgebra Q →ₗ[F] CliffordAlgebra (Q.baseChange (AlgebraicClosure F)) :=
  ((CliffordAlgebra.ofBaseChange (AlgebraicClosure F) Q).toLinearMap.restrictScalars F) ∘ₗ
    (Algebra.TensorProduct.includeRight (R := F) (A := AlgebraicClosure F)).toLinearMap

theorem bcHomL_apply {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)
    (a : CliffordAlgebra Q) : bcHomL Q a = bcHom Q a := rfl

/-- `Ad(g) ∘ C(φ)` as an `F`-linear map. -/
def psiL (φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F)))
    (g : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ) :
    CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F)) →ₗ[F]
      CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)) :=
  ((LinearMap.mulRight (AlgebraicClosure F) ((g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) ∘ₗ
    LinearMap.mulLeft (AlgebraicClosure F) (g : CliffordAlgebra _) ∘ₗ
      (CliffordAlgebra.map φ.toIsometry).toLinearMap).restrictScalars F)

theorem psiL_apply
    (φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F)))
    (g : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ)
    (a : CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F))) : psiL φ g a = psiA φ g a := rfl

variable [Module.Finite F V₁] [Module.Finite F V₂]

/-- **A map of subgroups given by `t̄ ↦ Ad(g) C(φ)(t̄)` is continuous**: it is the restriction of
the `F`-linear map `r ∘ Ad(g) ∘ C(φ) ∘ (base change)` from `C(Q₁)` to `C(Q₂)`, where `r` is an
`F`-linear left inverse of the base change of `C(Q₂)`. -/
theorem continuous_of_bcUnits_eq
    {φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F))}
    {g : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ}
    {S₁ : Subgroup (GSpin Q₁)} {S₂ : Subgroup (GSpin Q₂)} (f : S₁ →* S₂)
    (hf : ∀ t : S₁, bcUnits Q₂ (((f t : S₂) : GSpin Q₂) : (CliffordAlgebra Q₂)ˣ) =
      psiU φ g (bcUnits Q₁ ((t : GSpin Q₁) : (CliffordAlgebra Q₁)ˣ))) :
    Continuous f := by
  obtain ⟨r, hr⟩ := (bcHomL Q₂).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (bcHom_injective Q₂))
  let Λ : CliffordAlgebra Q₁ →ₗ[F] CliffordAlgebra Q₂ := r ∘ₗ psiL φ g ∘ₗ bcHomL Q₁
  have hΛc : Continuous Λ := IsModuleTopology.continuous_of_linearMap Λ
  have hΛ : ∀ t : S₁, Λ (((t : GSpin Q₁) : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) =
      (((f t : S₂) : GSpin Q₂) : (CliffordAlgebra Q₂)ˣ) := by
    intro t
    have h := congrArg Units.val (hf t)
    show r (psiA φ g ((bcUnits Q₁ ((t : GSpin Q₁) : (CliffordAlgebra Q₁)ˣ) :
      (CliffordAlgebra _)ˣ) : CliffordAlgebra _)) = _
    rw [← coe_psiU, ← h]
    exact LinearMap.congr_fun hr _
  have hc1 : Continuous fun t : S₁ => (((f t : S₂) : GSpin Q₂) : (CliffordAlgebra Q₂)ˣ) := by
    rw [Units.continuous_iff]
    constructor
    · have : (fun t : S₁ => ((((f t : S₂) : GSpin Q₂) : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra Q₂))
          = Λ ∘ fun t : S₁ => (((t : GSpin Q₁) : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) :=
        funext fun t => (hΛ t).symm
      rw [show (Units.val ∘ fun t : S₁ => (((f t : S₂) : GSpin Q₂) : (CliffordAlgebra Q₂)ˣ)) =
        Λ ∘ fun t : S₁ => (((t : GSpin Q₁) : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) from this]
      exact hΛc.comp (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val))
    · refine (hΛc.comp (Units.continuous_val.comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_inv)))).congr ?_
      intro t
      simp only [Function.comp_apply]
      rw [hΛ, map_inv]
      rfl
  exact Continuous.subtype_mk (Continuous.subtype_mk hc1 _) _

end Continuity

end TorusTransfer
end GSpinGGP
