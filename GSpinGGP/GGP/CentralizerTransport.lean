/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TorusTransport
import GSpinGGP.GGP.MovedCentralizer
import GSpinGGP.Foundations.CentralizerIso

/-!
# The transport `Ad(g) ∘ ψ` on centralizers, over `F`

Let `x ∈ GSpin(Q₁)(F)` and `y ∈ GSpin(Q₂)(F)` be strongly stably conjugate through an isometry
`φ : Q₁ ⊗ F̄ ≃ Q₂ ⊗ F̄`, by `g` (Thesis §6.1): `Ψ = Ad(g) ∘ C(φ)` maps `x̄` to `ȳ` and commutes
with the Galois action on the centralizer of `x̄` in `GSpin(Q₁)(F̄)`. This file shows that `Ψ`
restricts to an `F`-linear isomorphism, multiplicative, between the subalgebras of `C(Q₁)`, `C(Q₂)`
of elements whose transport is rational (`ratSub`), and that these contain the centralizers of `x`
and `y` in `GSpin(F)` and in `gspin(F)`, which it matches.

* `ratSub φ g`: the `a ∈ C(Q₁)` with `Ψ(ā)` rational; `transL φ g`: an `F`-linear map
  `C(Q₁) → C(Q₂)` with `transL a = Ψ(ā)` on `ratSub` (`bcHom_transL`).
* `mem_ratSub_of_commute`, `mem_ratSub_of_mem_gspin`: `Z_{GSpin(Q₁)(F)}(x)` and `Z_{gspin(Q₁)}(x)`
  lie in `ratSub` (the latter from the former through `exp`, near `0`, and scaling).
* `transL_mem_GSpin`, `transL_mem_gspin`: they are mapped into `GSpin(Q₂)(F)`, `gspin(Q₂)`.
* `trace_mulLeft_transL`: `tr(L_{transL a}) = tr(L_a)` (compute over `F̄`).

Own work: the thesis states (§6.1) that `ι = Ad(g) ∘ ψ_α` is an isomorphism `G_x ≃ G_{α,y}` defined
over `F`; this file supplies the linear algebra behind it.
-/

noncomputable section

open CliffordAlgebra Filter Topology
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP
namespace TorusTransfer

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
  {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}

section RatSub

variable
  (φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F)))
  (g : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ)

theorem psiA_one : psiA φ g 1 = 1 := by
  simpa using psiA_algebraMap φ g (1 : F)

theorem bcHom_algebraMap' (c : F) : bcHom Q₁ (algebraMap F _ c) = algebraMap F _ c := by
  rw [bcHom_algebraMap, ← IsScalarTower.algebraMap_apply]

/-- The subalgebra of `C(Q₁)` of the elements `a` whose transport `Ad(g) C(φ)(ā)` is rational. -/
def ratSub : Subalgebra F (CliffordAlgebra Q₁) where
  carrier := {a | ∃ b : CliffordAlgebra Q₂, bcHom Q₂ b = psiA φ g (bcHom Q₁ a)}
  mul_mem' := by
    rintro a c ⟨b, hb⟩ ⟨d, hd⟩
    exact ⟨b * d, by rw [map_mul, hb, hd, map_mul, psiA_mul]⟩
  add_mem' := by
    rintro a c ⟨b, hb⟩ ⟨d, hd⟩
    exact ⟨b + d, by rw [map_add, hb, hd, map_add, psiA_add]⟩
  algebraMap_mem' c := ⟨algebraMap F _ c, by
    rw [bcHom_algebraMap', bcHom_algebraMap', psiA_algebraMap]⟩

theorem mem_ratSub {a : CliffordAlgebra Q₁} :
    a ∈ ratSub φ g ↔ ∃ b : CliffordAlgebra Q₂, bcHom Q₂ b = psiA φ g (bcHom Q₁ a) := Iff.rfl

/-- An `F`-linear left inverse of the base change `C(Q₂) → C(Q₂)_{F̄}`. -/
def bcRetract (Q₂ : QuadraticForm F V₂) :
    CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)) →ₗ[F] CliffordAlgebra Q₂ :=
  Classical.choose ((bcHomL Q₂).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (bcHom_injective Q₂)))

theorem bcRetract_bcHom (b : CliffordAlgebra Q₂) : bcRetract Q₂ (bcHom Q₂ b) = b :=
  LinearMap.congr_fun (Classical.choose_spec ((bcHomL Q₂).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (bcHom_injective Q₂)))) b

/-- The transport `a ↦ Ad(g) C(φ)(ā)` as an `F`-linear map `C(Q₁) → C(Q₂)`, correct on `ratSub`
(`bcHom_transL`). -/
def transL : CliffordAlgebra Q₁ →ₗ[F] CliffordAlgebra Q₂ :=
  bcRetract Q₂ ∘ₗ psiL φ g ∘ₗ bcHomL Q₁

variable {φ g}

theorem bcHom_transL {a : CliffordAlgebra Q₁} (ha : a ∈ ratSub φ g) :
    bcHom Q₂ (transL φ g a) = psiA φ g (bcHom Q₁ a) := by
  obtain ⟨b, hb⟩ := ha
  have : transL φ g a = b := by
    change bcRetract Q₂ (psiA φ g (bcHom Q₁ a)) = b
    rw [← hb, bcRetract_bcHom]
  rw [this, hb]

theorem transL_one : transL φ g 1 = 1 :=
  bcHom_injective Q₂ (by rw [bcHom_transL (ratSub φ g).one_mem, map_one, map_one, psiA_one])

theorem transL_mul {a c : CliffordAlgebra Q₁} (ha : a ∈ ratSub φ g) (hc : c ∈ ratSub φ g) :
    transL φ g (a * c) = transL φ g a * transL φ g c :=
  bcHom_injective Q₂ (by
    rw [bcHom_transL ((ratSub φ g).mul_mem ha hc), map_mul, map_mul, bcHom_transL ha,
      bcHom_transL hc, psiA_mul])

variable
  {φ₂ : (Q₂.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₁.baseChange (AlgebraicClosure F))}
  {g₂ : (CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F)))ˣ}

/-- The transport of `ratSub φ g` lies in `ratSub` of an inverse transport. -/
theorem transL_mem_ratSub (h : ∀ a, psiA φ₂ g₂ (psiA φ g a) = a) {a : CliffordAlgebra Q₁}
    (ha : a ∈ ratSub φ g) : transL φ g a ∈ ratSub φ₂ g₂ :=
  ⟨a, by rw [bcHom_transL ha, h]⟩

/-- An inverse transport inverts `transL` on `ratSub`. -/
theorem transL_transL (h : ∀ a, psiA φ₂ g₂ (psiA φ g a) = a) {a : CliffordAlgebra Q₁}
    (ha : a ∈ ratSub φ g) : transL φ₂ g₂ (transL φ g a) = a :=
  bcHom_injective Q₁ (by rw [bcHom_transL (transL_mem_ratSub h ha), bcHom_transL ha, h])

end RatSub

section Centralizer

variable
  {φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F))}
  {g : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ}
  (hg : g ∈ GSpin (Q₂.baseChange (AlgebraicClosure F))) {x : GSpin Q₁}
  (hrat : RatAt φ g (x : (CliffordAlgebra Q₁)ˣ))
include hg hrat

/-- `Z_{GSpin(Q₁)(F)}(x) ⊆ ratSub`, and `transL` maps it into `GSpin(Q₂)(F)`. -/
theorem exists_transL_eq_of_commute (t : GSpin Q₁)
    (ht : Commute (t : (CliffordAlgebra Q₁)ˣ) (x : (CliffordAlgebra Q₁)ˣ)) :
    ((t : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) ∈ ratSub φ g ∧
      ∃ b : GSpin Q₂, ((b : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra Q₂) =
        transL φ g ((t : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) := by
  obtain ⟨b, hb⟩ := exists_transport hg hrat t ht
  have hmem : ((t : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) ∈ ratSub φ g :=
    ⟨((b : (CliffordAlgebra Q₂)ˣ) : CliffordAlgebra Q₂), congrArg Units.val hb⟩
  exact ⟨hmem, b, bcHom_injective Q₂ (by rw [bcHom_transL hmem]; exact congrArg Units.val hb)⟩

/-- `transL` maps an element of `ratSub` commuting with `x` to one commuting with `y`. -/
theorem transL_mul_comm {y : CliffordAlgebra Q₂} (hconj : psiA φ g (bcHom Q₁
    ((x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁)) = bcHom Q₂ y) {X : CliffordAlgebra Q₁}
    (hX : X ∈ ratSub φ g) (hXx : X * ((x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) =
      ((x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) * X) :
    transL φ g X * y = y * transL φ g X :=
  bcHom_injective Q₂ (by
    rw [map_mul, map_mul, bcHom_transL hX, ← hconj, ← psiA_mul, ← psiA_mul, ← map_mul, ← map_mul,
      hXx])

variable [Module.Finite F V₁] [Module.Finite F V₂]

/-- **`Z_{gspin(Q₁)}(x) ⊆ ratSub`, and `transL` maps it into `gspin(Q₂)`.** For `c ≠ 0` small,
`e^{cX} ∈ GSpin(Q₁)(F)` commutes with `x`, so it lies in `ratSub` and is transported into
`GSpin(Q₂)(F)`; hence `cX ∈ ratSub` (`exists_nhds_mem_of_expA_mem`), and
`e^{c transL X} = transL(e^{cX}) ∈ GSpin(Q₂)(F)` gives `c transL X ∈ gspin(Q₂)`
(`eventually_mem_gspin_of_expA_mem`). -/
theorem mem_ratSub_of_mem_gspin {X : CliffordAlgebra Q₁} (hX : X ∈ gspin Q₁)
    (hXx : X * ((x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) =
      ((x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) * X) :
    X ∈ ratSub φ g ∧ transL φ g X ∈ gspin Q₂ := by
  obtain ⟨U₁, hU₁, hexpG⟩ := MovedPart.exists_nhds_expA_mem_GSpin (F := F) Q₁
  obtain ⟨U₂, hU₂, hsub⟩ := exists_nhds_mem_of_expA_mem F (A := CliffordAlgebra Q₁)
  have hU₃ := eventually_mem_gspin_of_expA_mem (F := F) Q₂
  have ht₁ : Tendsto (fun c : F => c • X) (𝓝[≠] 0) (𝓝 0) := by
    have := (tendsto_id (x := 𝓝 (0 : F))).smul_const X
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  have ht₂ : Tendsto (fun c : F => c • transL φ g X) (𝓝[≠] 0) (𝓝 0) := by
    have := (tendsto_id (x := 𝓝 (0 : F))).smul_const (transL φ g X)
    rw [zero_smul] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨c, hc0, ⟨h1, h2⟩, h3⟩ := ((eventually_mem_nhdsWithin (s := ({0}ᶜ : Set F))
    (a := 0)).and (((ht₁.eventually_mem hU₁).and (ht₁.eventually_mem hU₂)).and
      (ht₂.eventually hU₃))).exists
  have hc0 : c ≠ 0 := hc0
  set Y := c • X with hYdef
  have hY : Y ∈ gspin Q₁ := (gspin Q₁).smul_mem c hX
  obtain ⟨t, ht⟩ := hexpG Y h1 hY
  have htx : Commute (t : (CliffordAlgebra Q₁)ˣ) (x : (CliffordAlgebra Q₁)ˣ) := by
    refine Units.ext ?_
    change (t : CliffordAlgebra Q₁) * _ = _ * (t : CliffordAlgebra Q₁)
    have hc : Commute ((x : (CliffordAlgebra Q₁)ˣ) : CliffordAlgebra Q₁) Y := by
      change _ * (c • X) = (c • X) * _
      rw [mul_smul_comm, smul_mul_assoc, hXx]
    rw [ht]
    exact (commute_expA_of_commute hc).eq.symm
  obtain ⟨hmem, b, hb⟩ := exists_transL_eq_of_commute hg hrat t htx
  rw [ht] at hmem hb
  have hYm : Y ∈ ratSub φ g := hsub Y h2 (ratSub φ g) hmem
  have hXm : X ∈ ratSub φ g := by
    have := (ratSub φ g).smul_mem hYm c⁻¹
    rwa [hYdef, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this
  refine ⟨hXm, ?_⟩
  have hexp : transL φ g (expA F Y) = expA F (transL φ g Y) :=
    map_expA_of_leftInverse (transL φ g) (transL φ.symm (cliffUnits φ.symm g⁻¹))
      (map_pow_of_mul transL_one (fun a ha c hc => transL_mul ha hc) hYm)
      (fun n => transL_transL (psiA_symm_psiA φ g) ((ratSub φ g).pow_mem hYm n))
  have hTY : transL φ g Y ∈ gspin Q₂ := by
    rw [hYdef, map_smul]
    exact h3 b (hb.trans (hexp.trans (by rw [hYdef, map_smul])))
  have := (gspin Q₂).smul_mem c⁻¹ hTY
  rwa [hYdef, map_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul] at this

end Centralizer

section Trace

variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]

/-- `tr_{F̄}(L_{ā}) = tr_F(L_a)` on `C(Q)_{F̄} ≅ F̄ ⊗ C(Q)`. -/
theorem trace_mulLeft_bcHom (Q : QuadraticForm F V) (a : CliffordAlgebra Q) :
    LinearMap.trace (AlgebraicClosure F) _ (LinearMap.mulLeft (AlgebraicClosure F) (bcHom Q a)) =
      algebraMap F (AlgebraicClosure F) (LinearMap.trace F _ (LinearMap.mulLeft F a)) := by
  set E := (CliffordAlgebra.equivBaseChange (AlgebraicClosure F) Q).toLinearEquiv
  rw [← LinearMap.trace_conj' _ E, ← LinearMap.trace_baseChange]
  congr 1
  refine LinearMap.ext fun t => ?_
  rw [LinearEquiv.conj_apply_apply, LinearMap.mulLeft_apply]
  change CliffordAlgebra.equivBaseChange _ Q (bcHom Q a * E.symm t) = _
  rw [map_mul]
  change _ * E (E.symm t) = _
  rw [LinearEquiv.apply_symm_apply]
  have h1 : CliffordAlgebra.equivBaseChange (AlgebraicClosure F) Q (bcHom Q a) =
      (1 : AlgebraicClosure F) ⊗ₜ a := by
    change CliffordAlgebra.toBaseChange (AlgebraicClosure F) Q
      (CliffordAlgebra.ofBaseChange (AlgebraicClosure F) Q (1 ⊗ₜ a)) = _
    rw [CliffordAlgebra.toBaseChange_ofBaseChange]
  rw [h1]
  induction t using TensorProduct.inductionOn with
  | tmul z c => simp [Algebra.TensorProduct.tmul_mul_tmul]
  | add t₁ t₂ h₁ h₂ => rw [mul_add, map_add, h₁, h₂]

/-- `Ad(g) ∘ C(φ)` preserves `tr(L_z)` (it is an algebra isomorphism over `F̄`). -/
theorem trace_mulLeft_psiA
    (φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F)))
    (g : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ)
    (z : CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F))) :
    LinearMap.trace (AlgebraicClosure F) _ (LinearMap.mulLeft (AlgebraicClosure F) (psiA φ g z)) =
      LinearMap.trace (AlgebraicClosure F) _ (LinearMap.mulLeft (AlgebraicClosure F) z) := by
  let L : CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F)) →ₗ[AlgebraicClosure F]
      CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)) :=
    LinearMap.mulRight (AlgebraicClosure F) ((g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) ∘ₗ
      LinearMap.mulLeft (AlgebraicClosure F) (g : CliffordAlgebra _) ∘ₗ
        (CliffordAlgebra.map φ.toIsometry).toLinearMap
  have hL : ∀ w, L w = psiA φ g w := fun _ => rfl
  let Ψ := LinearEquiv.ofBijective L ⟨fun a b h => psiA_injective φ g (by rwa [hL, hL] at h),
    fun w => ⟨psiA φ.symm (cliffUnits φ.symm g⁻¹) w, by rw [hL, psiA_psiA_symm]⟩⟩
  rw [← LinearMap.trace_conj' _ Ψ]
  congr 1
  refine LinearMap.ext fun w => ?_
  rw [LinearEquiv.conj_apply_apply, LinearMap.mulLeft_apply, LinearMap.mulLeft_apply]
  change _ = L (z * Ψ.symm w)
  rw [hL, psiA_mul, ← hL (Ψ.symm w)]
  exact (congrArg _ (Ψ.apply_symm_apply w)).symm

/-- **`transL` preserves `tr(L_a)` on `ratSub`.** -/
theorem trace_mulLeft_transL [Module.Finite F V₁] [Module.Finite F V₂]
    {φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F))}
    {g : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ} {a : CliffordAlgebra Q₁}
    (ha : a ∈ ratSub φ g) :
    LinearMap.trace F _ (LinearMap.mulLeft F (transL φ g a)) =
      LinearMap.trace F _ (LinearMap.mulLeft F a) := by
  apply (algebraMap F (AlgebraicClosure F)).injective
  rw [← trace_mulLeft_bcHom, bcHom_transL ha, trace_mulLeft_psiA, trace_mulLeft_bcHom]

end Trace

end TorusTransfer
end GSpinGGP
