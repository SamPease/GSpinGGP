/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TorusCommute
import GSpinGGP.GGP.CentralizerBaseChange
import GSpinGGP.Foundations.GSpinExp
import GSpinGGP.GGP.GSpinSemisimple

/-!
# The moved part of the centralizer of `x ∈ GSpin(W)(F)`

For `x ∈ GSpin(W)(F)`, the *moved part* of the Lie centralizer is
`𝔩_x = {X ∈ gspin(W) : [X, x] = 0, [X, ι(W'_x)] = 0}` (`so(W''_x)_{x̄} ⊕ F`).

* `exists_gspin_commute_iff` (`exists_gspin_expA_commute_iff`, `exists_gspin_commute_iff_trace`):
  an element of `GSpin` with the commutant of a given `Z ∈ gspin` (of nonzero trace);
  `commute_of_commute_specP_of_trace_ne_zero`: `P(h)`, `P(g)` commuting and `tr L_g ≠ 0` force
  `h`, `g` to commute; `mem_torusOf_of_commute`: commuting with `x` and `ι(W'_x)` puts `g` in
  `T_x`; `exists_mem_torusOf_commute_iff`: the moved part of `𝔩_x` has commutants of points of
  `T_x`;
* `movedPartAbelian_of_isGammaElt`: `𝔩_x` is abelian for `x ∈ Γ(G,H)`;
* `GGPData.eq_zero_of_forall_movedCent`: a skew endomorphism of `W_{F̄}` commuting with `P(x)` and
  vanishing on `W'_x ⊗ F̄` is `ad` of an element of `𝔩_x ⊗ F̄` (`exists_movedCent_lift`, in
  `GGP/CentralizerBaseChange.lean`), so the `(ad Z)_{F̄}`, `Z ∈ 𝔩_x`, span all of them; `GGPData.exists_movedCent_forall_ne_zero`:
  some `Z ∈ 𝔩_x` avoids finitely many such hyperplanes (`F` infinite);
* `lieAbelian_specP_baseChange_of_movedPartAbelian`: if `𝔩_x` is abelian, so is the Lie algebra
  of `S_x` over `F̄` (`IsomCent.LieAbelian`; the case `W = W(d)` of
  `lieAbelian_specP_baseChange_of_lie_eq_zero`);
* `GGPData.isSS_of_commute_of_isGammaElt`: for `x ∈ Γ(G,H)`, every `X ∈ gspin(W)` commuting with
  `x` and killing `W'_x` is semisimple.
-/

noncomputable section

open MeasureTheory Filter Topology Module
open CliffordAlgebra (ι_injective)
open scoped Classical

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
/-- `exists_gspin_commute_iff`, with control of the element: `g = e^{cZ}` for some `c ≠ 0` with
`cZ` in a given neighbourhood `U` of `0`. -/
theorem exists_gspin_expA_commute_iff
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (Q : QuadraticForm F V) {Z : CliffordAlgebra Q}
    (hZ : Z ∈ gspin Q) {U : Set (CliffordAlgebra Q)} (hU : U ∈ 𝓝 (0 : CliffordAlgebra Q)) :
    ∃ c : F, c ≠ 0 ∧ c • Z ∈ U ∧ ∃ g : GSpin Q,
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = expA F (c • Z) ∧
      ∀ W : CliffordAlgebra Q,
        Commute W ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ↔ Commute W Z := by
  obtain ⟨U₁, hU₁, hG⟩ := MovedPart.exists_nhds_expA_mem_GSpin (F := F) Q
  obtain ⟨U', hU', hc⟩ := exists_nhds_commute_of_commute_expA F (A := CliffordAlgebra Q)
  have hlim : Tendsto (fun c : F => c • Z) (𝓝[≠] 0) (𝓝 0) := by
    have : Continuous (fun c : F => c • Z) := continuous_id.smul continuous_const
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨c, hcU, hc0⟩ :=
    ((hlim.eventually (inter_mem (inter_mem hU₁ hU') hU)).and self_mem_nhdsWithin).exists
  obtain ⟨g, hg⟩ := hG _ hcU.1.1 ((gspin Q).smul_mem c hZ)
  refine ⟨c, hc0, hcU.2, g, hg, fun W => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hg] at h
    have h2 := (hc _ hcU.1.2 _ h).eq
    rw [mul_smul_comm, smul_mul_assoc] at h2
    exact smul_right_injective _ hc0 h2
  · rw [hg]
    exact commute_expA_of_commute (h.smul_right c)

/-- **A group element with the commutant of `Z`**: for `Z ∈ gspin(Q)` there is `g ∈ GSpin(Q)(F)`
(namely `e^{cZ}` for small `c ≠ 0`, `MovedPart.exists_nhds_expA_mem_GSpin`) commuting with exactly
the elements of `C(Q)` that commute with `Z` (`commute_expA_of_commute`,
`exists_nhds_commute_of_commute_expA`). -/
theorem exists_gspin_commute_iff {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (Q : QuadraticForm F V) {Z : CliffordAlgebra Q} (hZ : Z ∈ gspin Q) :
    ∃ g : GSpin Q, ∀ W : CliffordAlgebra Q,
      Commute W ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ↔ Commute W Z := by
  obtain ⟨-, -, -, g, -, hg⟩ := exists_gspin_expA_commute_iff Q hZ univ_mem
  exact ⟨g, hg⟩

/-- **A group element with the commutant of `Z` and nonzero trace**: for `Z ∈ gspin(Q)` there is
`g ∈ GSpin(Q)(F)` (namely `e^{cZ}` for small `c ≠ 0`) commuting with exactly the elements of `C(Q)`
that commute with `Z`, with `tr L_g ≠ 0` (`tr L_{e^0} = dim C(Q) ≠ 0`), and semisimple if `Z` is
(`exists_nhds_isSS_expA`). -/
theorem exists_gspin_commute_iff_trace
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (Q : QuadraticForm F V) {Z : CliffordAlgebra Q} (hZ : Z ∈ gspin Q) :
    ∃ g : GSpin Q,
      (∀ W : CliffordAlgebra Q,
        Commute W ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ↔ Commute W Z) ∧
      cliffTrace Q ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ≠ 0 ∧
      (IsSS F Z → IsSS F ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) := by
  obtain ⟨Uss, hUss, hss⟩ := exists_nhds_isSS_expA F (A := CliffordAlgebra Q)
  let τ : CliffordAlgebra Q →ₗ[F] F :=
    (LinearMap.trace F (CliffordAlgebra Q)).comp (LinearMap.mul F (CliffordAlgebra Q))
  have hτY : ∀ Y, τ Y = cliffTrace Q Y := fun Y => rfl
  have hτ : Continuous τ := IsModuleTopology.continuous_of_linearMap τ
  have hcont : ContinuousAt (fun Y : CliffordAlgebra Q => τ (expA F Y)) 0 :=
    hτ.continuousAt.comp (continuousAt_expA_at_zero F (A := CliffordAlgebra Q))
  have h0 : τ (expA F (0 : CliffordAlgebra Q)) ≠ 0 := by
    rw [hτY, expA_zero_eq_one, cliffTrace_one]
    exact cast_finrank_cliffordAlgebra_ne_zero Q
  obtain ⟨c, hc0, hcU, g, hg, hcomm⟩ :=
    exists_gspin_expA_commute_iff Q hZ (inter_mem hUss (hcont.eventually_ne h0))
  refine ⟨g, hcomm, ?_, fun hZs => ?_⟩
  · have h2 : τ (expA F (c • Z)) ≠ 0 := hcU.2
    rwa [hτY, ← hg] at h2
  · rw [hg]
    exact hss _ hcU.1 (isSS_smul c hZs)

/-- **Commutation from `P` and the trace**: for `V` nondegenerate (`IsNondeg Q`), if `P(h)`
commutes with `P(g)` in `SO(Q)`, then `hgh⁻¹ = cg` for a scalar `c` (`ker P = F^×`), and `c = 1`
when `tr L_g ≠ 0` (traces of conjugate elements agree). -/
theorem commute_of_commute_specP_of_trace_ne_zero
    {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    {Q : QuadraticForm F V} (hQ : IsNondeg Q) {g h : GSpin Q}
    (hg : cliffTrace Q ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ≠ 0)
    (hc : Commute (specP Q h) (specP Q g)) : Commute h g := by
  set A := CliffordAlgebra Q
  have hP : specP Q (h * g * h⁻¹) = specP Q g := by
    rw [map_mul, map_mul, hc.eq, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  obtain ⟨c, hcg⟩ := exists_eq_mul_scalarGSpin_of_specP_eq hQ hP
  set gA : A := ((g : Aˣ) : A)
  set hA : A := ((h : Aˣ) : A)
  set hiA : A := (((h⁻¹ : GSpin Q) : Aˣ) : A)
  have hhi : hiA * hA = 1 := by
    simp only [hiA, hA, Subgroup.coe_inv, Units.inv_mul]
  have hval : hA * gA * hiA = (c : F) • gA := by
    have := congrArg (fun k : GSpin Q => ((k : Aˣ) : A)) hcg
    simp only [Subgroup.coe_mul, Units.val_mul] at this
    rw [this]
    change gA * algebraMap F A (c : F) = _
    rw [← Algebra.commutes, Algebra.smul_def]
  have htr : cliffTrace Q (hA * gA * hiA) = cliffTrace Q gA := by
    rw [mul_assoc]
    change LinearMap.trace F _ (LinearMap.mulLeft F (hA * (gA * hiA))) = _
    rw [trace_mulLeft_comm Q, mul_assoc, hhi, mul_one]
  rw [hval, cliffTrace_smul] at htr
  have hc1 : (c : F) = 1 := by
    have := sub_eq_zero.mpr htr
    rw [← sub_one_mul] at this
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hg)
  have hc1' : c = 1 := Units.ext hc1
  rw [hc1', map_one, mul_one] at hcg
  exact (mul_inv_eq_iff_eq_mul.mp hcg)

/-- `g ∈ T_x(F)` as soon as `g` commutes with `x` and with `ι(W'_x)`. -/
theorem mem_torusOf_of_commute (d : GGPData F) {x g : ↥(GSpin d.QW)}
    (hx : Commute ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)
      ((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
    (hf : ∀ w ∈ fixedSub x, Commute (CliffordAlgebra.ι d.QW w)
      ((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)) :
    g ∈ d.torusOf x := by
  refine ⟨?_, fun w hw => ?_⟩
  · show g ∈ Subgroup.centralizer {x}
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Units.ext hx.eq.symm)
  · apply CliffordAlgebra.ι_injective d.QW
    rw [ι_specP, ← (hf w hw).eq, mul_assoc, Units.mul_inv, mul_one]

/-- **An element of the moved part of the Lie centralizer has the commutant of a point of the
torus**: for `Z ∈ gspin(W)` commuting with `x` and with `ι(W'_x)`, some `g ∈ T_x(F)` (namely
`e^{cZ}`, `exists_gspin_commute_iff_trace`) commutes with exactly the elements of `C(W)` that
commute with `Z`, and `tr L_g ≠ 0`. -/
theorem exists_mem_torusOf_commute_iff (d : GGPData F) {x : ↥(GSpin d.QW)}
    {Z : CliffordAlgebra d.QW} (hZ : Z ∈ gspin d.QW)
    (hZx : Commute ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) Z)
    (hZf : ∀ v ∈ fixedSub x, ⁅Z, CliffordAlgebra.ι d.QW v⁆ = 0) :
    ∃ g ∈ d.torusOf x, (∀ W : CliffordAlgebra d.QW,
        Commute W ((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) ↔ Commute W Z) ∧
      cliffTrace d.QW ((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) ≠ 0 := by
  obtain ⟨g, hg, htr, -⟩ := exists_gspin_commute_iff_trace d.QW hZ
  refine ⟨g, mem_torusOf_of_commute d ((hg _).mpr hZx) fun w hw => (hg _).mpr ?_, hg, htr⟩
  have hw0 := hZf w hw
  rw [Ring.lie_def, sub_eq_zero] at hw0
  exact hw0.symm

/-- For `x ∈ Γ(G,H)` the moved part `G''_x` is a torus: `T_x(F) = Z(x) ∩ Fix(W'_x)`
is commutative, hence so is its Lie algebra
`so(W''_x)_{x̄} ⊕ F`.  Own work; this is the hypothesis under which
`nilReg_centralizer_nonempty_iff` applies.

Proof (exponential, no Zariski density): `X` and `Y` in the moved part have the commutants of some
`g, h ∈ T_x(F)` (`exists_mem_torusOf_commute_iff`: `e^{cX}`, `e^{cY}` for small `c ≠ 0`), which
commute; hence `X` and `Y` commute.  Only the commutativity of
`T_x(F)` is used, not the semisimplicity of `x` or the compactness of `T_x(F)/A(F)`. -/
theorem movedPartAbelian_of_isGammaElt (d : GGPData F) (x : ↥(GSpin d.QW))
    (hx : d.IsGammaElt x) : MovedPartAbelian d.QW x := by
  intro X hX Y hY hXf hYf
  rw [mem_lieCentralizer] at hX hY
  obtain ⟨g, hgT, hg, -⟩ := exists_mem_torusOf_commute_iff d hX.1 hX.2 hXf
  obtain ⟨h, hhT, hh, -⟩ := exists_mem_torusOf_commute_iff d hY.1 hY.2 hYf
  have h1 : Commute ((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)
      ((h : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) :=
    congrArg (fun k : ↥(GSpin d.QW) => ((k : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
      (hx.2.1 g hgT h hhT).eq
  have h3 : Commute Y X := (hg _).mp ((hh _).mp h1).symm
  rw [Ring.lie_def, sub_eq_zero]
  exact h3.eq.symm


namespace GGPData

section MovedCentLift

open CliffordAlgebra
open scoped TensorProduct

variable (d : GGPData F)

open scoped TensorProduct

local notation "Kb" => AlgebraicClosure F

set_option hygiene false in
local notation "Wb" => AlgebraicClosure F ⊗[F] (Fin d.m → F)

set_option hygiene false in
local notation "Qb" => d.QW.baseChange (AlgebraicClosure F)

/-- `ad` commutes with base change: `ad (1 ⊗ Z) = (ad Z)_{F̄}` for `Z ∈ gspin(W)`. -/
theorem adV_gspinBC_tmul {Z : (gspin d.QW).toSubmodule} :
    adV Qb (gspinBC d.QW (1 ⊗ₜ Z)) = (adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb := by
  refine TensorProduct.AlgebraTensorModule.ext fun z v => ?_
  have e1 : ∀ w : Fin d.m → F, z ⊗ₜ[F] w = z • ((1 : Kb) ⊗ₜ[F] w) := fun w => by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [LinearMap.baseChange_tmul, e1, e1, map_smul]
  congr 1
  rw [adV_apply, gspinBC_tmul, ofBaseChange_tmul_eq, map_one, one_mul, ← bcHom_ι, ← map_mul,
    ← map_mul, ← map_sub, ← ι_adV Z.2, bcHom_ι, ιInv_ι]



end MovedCentLift

end GGPData

/-- **The Lie algebra of `S_x` is abelian over `F̄` if the moved part `𝔩_x` is** (own work):
`lieAbelian_specP_baseChange_of_lie_eq_zero` for `W`.  A skew endomorphism of `W_{F̄}` commuting
with `P(x)_{F̄}` and vanishing on `ker (P(x)_{F̄} − 1) = W'_x ⊗ F̄` is `ad` of an element of the
`F̄`-span of `𝔩_x` (the defining conditions are `F`-linear equations). -/
theorem lieAbelian_specP_baseChange_of_movedPartAbelian {d : GGPData F} (x : ↥(GSpin d.QW))
    (hx : MovedPartAbelian d.QW x) :
    IsomCent.LieAbelian (bform (d.QW.baseChange (AlgebraicClosure F)))
      ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange (AlgebraicClosure F)) :=
  lieAbelian_specP_baseChange_of_lie_eq_zero d.nondeg x hx

/-- **The Lie algebra of `S_x` is abelian over `F̄`** for `x ∈ Γ(G,H)`
(`lieAbelian_specP_baseChange_of_movedPartAbelian`, `movedPartAbelian_of_isGammaElt`). -/
theorem lieAbelian_specP_baseChange {d : GGPData F} (x : ↥(GSpin d.QW)) (hx : d.IsGammaElt x) :
    IsomCent.LieAbelian (bform (d.QW.baseChange (AlgebraicClosure F)))
      ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange (AlgebraicClosure F)) :=
  lieAbelian_specP_baseChange_of_movedPartAbelian x (movedPartAbelian_of_isGammaElt d x hx)

namespace GGPData

open scoped TensorProduct

/-- `ker (P(x)_{F̄} − 1) = W'_x ⊗ F̄`. -/
theorem eigenspace_bc_one {V' : Type*} [AddCommGroup V'] [Module F V']
    (Q : QuadraticForm F V') (x : GSpin Q) :
    Module.End.eigenspace (specP _ (bcGSpin Q x) :
        AlgebraicClosure F ⊗[F] V' →ₗ[AlgebraicClosure F] _) 1 =
      (fixedSub x).baseChange (AlgebraicClosure F) := by
  rw [specP_bcGSpin, Steinberg.fixedSub_eq_eigenspace,
    ← Module.End.eigenspace_baseChange_of_flat, map_one]

/-- `dim_{F̄} E₁(P(x)_{F̄}) = dim_F W'_x`. -/
theorem finrank_eigenspace_bc_one {V' : Type*} [AddCommGroup V'] [Module F V'] [FiniteDimensional F V']
    (Q : QuadraticForm F V') (x : GSpin Q) :
    Module.finrank (AlgebraicClosure F) (Module.End.eigenspace (specP _ (bcGSpin Q x) :
        AlgebraicClosure F ⊗[F] V' →ₗ[AlgebraicClosure F] _) 1) = Module.finrank F (fixedSub x) := by
  rw [eigenspace_bc_one, fixedSub, ← LinearMap.ker_baseChange_of_flat]
  exact (LinearMap.tensorKerEquiv _ _ _).finrank_eq.symm.trans Module.finrank_baseChange


section MovedCentSpan

open CliffordAlgebra

variable (d : GGPData F)

open scoped TensorProduct

local notation "Kb" => AlgebraicClosure F

set_option hygiene false in
local notation "Wb" => AlgebraicClosure F ⊗[F] (Fin d.m → F)

set_option hygiene false in
local notation "Qb" => d.QW.baseChange (AlgebraicClosure F)

/-- The moved part `ad Z`, `Z ∈ 𝔩_x`, over `F̄`: skew, commuting with `P(x)_{F̄}`, and vanishing
on `ker (P(x)_{F̄} − 1)`. -/
theorem movedCent_baseChange_props (x : ↥(GSpin d.QW))
    {Z : (gspin d.QW).toSubmodule} (hZ : Z ∈ LinearMap.ker (movedCentMap d.QW x (fixedSub x))) :
    (bform Qb).IsSkewAdjoint ((adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb) ∧
      Commute ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb)
        ((adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb) ∧
      ∀ z ∈ Module.End.eigenspace
        ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb) 1,
        (adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb z = 0 := by
  obtain ⟨hc, hf⟩ := mem_ker_movedCentMap hZ
  have hbf : bform Qb = (bform d.QW).baseChange Kb := QuadraticForm.associated_baseChange _
  have hk : ∀ v ∈ fixedSub x, adV d.QW (Z : CliffordAlgebra d.QW) v = 0 := fun v hv => by
    rw [adV_apply, hf v hv, sub_self, map_zero]
  refine ⟨?_, ?_, fun z hz => ?_⟩
  · rw [hbf]; exact LinearMap.IsSkewAdjoint.baseChange _ (LinearMap.isSkewAdjoint_iff.2 (bform_adV Z.2))
  · rw [Commute, SemiconjBy, ← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul,
      (commute_iff_adV d.nondeg x Z.2).mp hc]
  · rw [← specP_bcGSpin, eigenspace_bc_one] at hz
    obtain ⟨u, rfl⟩ := Submodule.toBaseChange_surjective' Kb _ hz
    clear hz
    induction u using TensorProduct.inductionOn with
    | tmul k v =>
      rw [Submodule.coe_toBaseChange_tmul, LinearMap.baseChange_tmul, hk v v.2,
        TensorProduct.tmul_zero]
    | add u v hu hv => rw [map_add, Submodule.coe_add, map_add, hu, hv, add_zero]

/-- A `F̄`-linear functional on `End(W_{F̄})` vanishing on `(ad Z)_{F̄}` for all `Z ∈ 𝔩_x` vanishes
on every skew endomorphism commuting with `P(x)_{F̄}` and vanishing on `ker (P(x)_{F̄} − 1)`. -/
theorem eq_zero_of_forall_movedCent (x : ↥(GSpin d.QW)) (γ : Module.End Kb Wb →ₗ[Kb] Kb)
    (hγ : ∀ Z ∈ LinearMap.ker (movedCentMap d.QW x (fixedSub x)),
      γ ((adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb) = 0)
    (Y : Module.End Kb Wb) (hs : (bform Qb).IsSkewAdjoint Y)
    (hc : Commute ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb) Y)
    (hf : ∀ z ∈ Module.End.eigenspace
      ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb) 1, Y z = 0) :
    γ Y = 0 := by
  obtain ⟨u, hu, hY⟩ := exists_movedCent_lift d.nondeg x (fixedSub x) Y hs hc
    fun _ hw => hf _ (tmul_mem_eigenspace_baseChange_one x hw)
  have hYu : Y = adV Qb (gspinBC d.QW u) :=
    LinearMap.ext fun v => by rw [adV_apply, hY, ιInv_ι]
  rw [hYu]
  clear hs hc hf hY hYu
  rw [Submodule.baseChange_eq_span] at hu
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨Z, hZ, rfl⟩ := hy
    rw [TensorProduct.mk_apply, adV_gspinBC_tmul]
    exact hγ Z hZ
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, map_add, map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, map_smul, map_smul, ha, smul_zero]

/-- `Z ↦ (ad Z)_{F̄}` on the moved part `𝔩_x = ker movedCentMap`, as an `F`-linear map. -/
def movedCentAd (x : ↥(GSpin d.QW)) :
    ↥(LinearMap.ker (movedCentMap d.QW x (fixedSub x))) →ₗ[F] Module.End Kb Wb where
  toFun Z := (adV d.QW ((Z : (gspin d.QW).toSubmodule) : CliffordAlgebra d.QW)).baseChange Kb
  map_add' Z Z' := by simp only [Submodule.coe_add, map_add, LinearMap.baseChange_add]
  map_smul' c Z := by
    simp only [SetLike.val_smul, map_smul, LinearMap.baseChange_smul, RingHom.id_apply]

/-- **Avoiding finitely many hyperplanes in `𝔩_x`**: given finitely many `F̄`-linear functionals
on `End(W_{F̄})`, each nonzero at some skew endomorphism commuting with `P(x)_{F̄}` and vanishing on
`ker (P(x)_{F̄} − 1)`, some `Z ∈ 𝔩_x` has `(ad Z)_{F̄}` outside all their kernels (`F` is infinite,
`Submodule.exists_forall_notMem_of_forall_ne_top`; `eq_zero_of_forall_movedCent`). -/
theorem exists_movedCent_forall_ne_zero (x : ↥(GSpin d.QW)) {ι : Type*} [Finite ι]
    (γ : ι → Module.End Kb Wb →ₗ[Kb] Kb)
    (hγ : ∀ k, ∃ Y : Module.End Kb Wb, (bform Qb).IsSkewAdjoint Y ∧
      Commute ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb) Y ∧
      (∀ z ∈ Module.End.eigenspace
        ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb) 1, Y z = 0) ∧
      γ k Y ≠ 0) :
    ∃ Z ∈ LinearMap.ker (movedCentMap d.QW x (fixedSub x)),
      ∀ k, γ k ((adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb) ≠ 0 := by
  let p : ι → Submodule F ↥(LinearMap.ker (movedCentMap d.QW x (fixedSub x))) := fun k =>
    { carrier := {Z | γ k (d.movedCentAd x Z) = 0}
      add_mem' := fun {Z Z'} hZ hZ' => by
        simp only [Set.mem_ofPred_eq, map_add] at hZ hZ' ⊢; rw [hZ, hZ', add_zero]
      zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]
      smul_mem' := fun c Z hZ => by
        simp only [Set.mem_ofPred_eq, map_smul] at hZ ⊢
        rw [LinearMap.map_smul_of_tower, hZ, smul_zero] }
  have hne : ∀ k, p k ≠ ⊤ := by
    intro k htop
    obtain ⟨Y, hs, hc, hf, hY⟩ := hγ k
    refine hY (d.eq_zero_of_forall_movedCent x (γ k) (fun Z hZ => ?_) Y hs hc hf)
    have : (⟨Z, hZ⟩ : ↥(LinearMap.ker (movedCentMap d.QW x (fixedSub x)))) ∈ p k := htop ▸ Submodule.mem_top
    exact this
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  obtain ⟨Z, hZ⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hne
  exact ⟨Z, Z.2, fun k h => hZ k h⟩

end MovedCentSpan

end GGPData

section TorusNat

open CliffordAlgebra Module
open scoped TensorProduct

namespace GGPData

variable (d : GGPData F)

theorem specP_incl_eq_prodMap (a : GSpin d.QW) :
    (specP d.QV (d.incl a) : d.V →ₗ[F] d.V) =
      (specP d.QW a : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).prodMap LinearMap.id := by
  ext ⟨w, z⟩ <;> simp [d.specP_incl_apply]

/-- `W_{F̄} ↪ V_{F̄}`. -/
abbrev inlF : (AlgebraicClosure F ⊗[F] (Fin d.m → F)) →ₗ[AlgebraicClosure F]
    (AlgebraicClosure F ⊗[F] d.V) :=
  (LinearMap.inl F (Fin d.m → F) d.Z).baseChange (AlgebraicClosure F)

theorem inlF_injective : Function.Injective d.inlF := by
  intro a b h
  have := congrArg ((LinearMap.fst F (Fin d.m → F) d.Z).baseChange (AlgebraicClosure F)) h
  rw [inlF, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
    LinearMap.fst_comp_inl, LinearMap.baseChange_id] at this
  exact this

theorem bform_inlF (u v : AlgebraicClosure F ⊗[F] (Fin d.m → F)) :
    bform (d.QV.baseChange (AlgebraicClosure F)) (d.inlF u) (d.inlF v) =
      bform (d.QW.baseChange (AlgebraicClosure F)) u v := by
  simp only [bform, QuadraticForm.associated_baseChange]
  induction u using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]
  | tmul a w =>
    induction v using TensorProduct.inductionOn with
    | add c e hc he => rw [map_add, map_add, map_add, hc, he]
    | tmul b w' =>
      simp [inlF, LinearMap.BilinForm.baseChange_tmul, QuadraticMap.associated_prod]

theorem specP_bc_incl_inlF (a : GSpin d.QW) (u : AlgebraicClosure F ⊗[F] (Fin d.m → F)) :
    (specP d.QV (d.incl a) : d.V →ₗ[F] d.V).baseChange (AlgebraicClosure F) (d.inlF u) =
      d.inlF ((specP d.QW a : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange
        (AlgebraicClosure F) u) := by
  rw [d.specP_incl_eq_prodMap a, inlF, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp,
    ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
  congr 2

theorem eigenspace_le_range_inlF (a : GSpin d.QW) {μ : AlgebraicClosure F} (hμ : μ ≠ 1) :
    Module.End.eigenspace ((specP d.QV (d.incl a) : d.V →ₗ[F] d.V).baseChange
      (AlgebraicClosure F)) μ ≤ LinearMap.range d.inlF := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff] at hv
  set sndF := (LinearMap.snd F (Fin d.m → F) d.Z).baseChange (AlgebraicClosure F)
  set fstF := (LinearMap.fst F (Fin d.m → F) d.Z).baseChange (AlgebraicClosure F)
  have hs : sndF ((specP d.QV (d.incl a) : d.V →ₗ[F] d.V).baseChange (AlgebraicClosure F) v) =
      sndF v := by
    rw [d.specP_incl_eq_prodMap a, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    congr 2
  rw [hv, map_smul] at hs
  have h0 : sndF v = 0 := by
    by_contra hne
    exact hμ (smul_left_injective (AlgebraicClosure F) hne (by simpa using hs))
  refine ⟨fstF v, ?_⟩
  have hid : (LinearMap.inl F (Fin d.m → F) d.Z ∘ₗ LinearMap.fst F _ _ +
      LinearMap.inr F (Fin d.m → F) d.Z ∘ₗ LinearMap.snd F _ _) = LinearMap.id := by
    ext ⟨w, z⟩ <;> simp
  have := congrArg (fun f => (f.baseChange (AlgebraicClosure F)) v) hid
  simp only [LinearMap.baseChange_add, LinearMap.baseChange_comp, LinearMap.add_apply,
    LinearMap.comp_apply, LinearMap.baseChange_id, LinearMap.id_apply] at this
  conv_rhs => rw [← this]
  rw [show (LinearMap.snd F (Fin d.m → F) d.Z).baseChange (AlgebraicClosure F) v = 0 from h0,
    map_zero, add_zero]

/-- **The moved part of `Lie(G_{incl t})` over `F̄` is abelian**, from that of `t` on `W`. -/
theorem lieAbelian_incl (a : GSpin d.QW)
    (hss : Module.End.IsSemisimple ((specP d.QV (d.incl a) : d.V →ₗ[F] d.V).baseChange
      (AlgebraicClosure F)))
    (hL : IsomCent.LieAbelian (bform (d.QW.baseChange (AlgebraicClosure F)))
      ((specP d.QW a : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange (AlgebraicClosure F))) :
    IsomCent.LieAbelian (bform (d.QV.baseChange (AlgebraicClosure F)))
      ((specP d.QV (d.incl a) : d.V →ₗ[F] d.V).baseChange (AlgebraicClosure F)) := by
  have hXU : ∀ u ∈ LinearMap.range d.inlF,
      (specP d.QV (d.incl a) : d.V →ₗ[F] d.V).baseChange (AlgebraicClosure F) u ∈
        LinearMap.range d.inlF := by
    rintro _ ⟨w, rfl⟩
    exact ⟨_, (d.specP_bc_incl_inlF a w).symm⟩
  refine IsomCent.LieAbelian.of_restrict hss _ hXU (fun μ hμ => d.eigenspace_le_range_inlF a hμ) ?_
  let e := LinearEquiv.ofInjective d.inlF d.inlF_injective
  refine IsomCent.LieAbelian.of_equiv e (fun u v => ?_) (fun v => ?_) hL
  · exact d.bform_inlF u v
  · apply Subtype.ext
    exact d.specP_bc_incl_inlF a v

theorem mem_fixedSub_iff {x : GSpin d.QW} {v : Fin d.m → F} :
    v ∈ fixedSub x ↔ specP d.QW x v = v := by
  simp [fixedSub, sub_eq_zero]

theorem self_mem_torusOf (x : GSpin d.QW) : x ∈ d.torusOf x :=
  ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, fun v hv => (d.mem_fixedSub_iff).mp hv⟩

/-- On the regular part `T_{x,♮}` the fixed spaces agree: `W'_t = W'_x`. -/
theorem fixedSub_eq_of_torusOf_eq {x t : GSpin d.QW} (ht : t ∈ d.torusOf x)
    (hT : d.torusOf t = d.torusOf x) : fixedSub t = fixedSub x := by
  apply le_antisymm
  · intro v hv
    have hx : x ∈ d.torusOf t := hT ▸ d.self_mem_torusOf x
    exact (d.mem_fixedSub_iff).mpr (hx.2 v hv)
  · intro v hv
    exact (d.mem_fixedSub_iff).mpr (ht.2 v hv)

/-- **On `T_{x,♮}` the centralizers over `F̄` agree**: for `x ∈ Γ(G,H)` and `t ∈ T_x` with
`t ∈ Γ(G,H)` and `T_t = T_x`, an element of `GSpin(W)(F̄)` commutes with `t̄` iff it commutes with
`x̄` (`Steinberg.commute_of_commute_of_lieAbelian`, both ways). -/
theorem commute_bc_iff_of_torusOf_eq {x t : GSpin d.QW} (hx : d.IsGammaElt x)
    (ht : d.IsGammaElt t) (htx : t ∈ d.torusOf x) (hT : d.torusOf t = d.torusOf x)
    (z : GSpin (d.QW.baseChange (AlgebraicClosure F))) :
    Commute z (bcGSpin d.QW t) ↔ Commute z (bcGSpin d.QW x) := by
  have hQ := isNondeg_baseChange _ d.nondeg
  have hss : ∀ y : GSpin d.QW, d.IsGammaElt y → Module.End.IsSemisimple
      (specP _ (bcGSpin d.QW y) :
        AlgebraicClosure F ⊗[F] (Fin d.m → F) →ₗ[AlgebraicClosure F] _) := fun y hy => by
    rw [specP_bcGSpin]; exact isSemisimple_specP_baseChange y hy.1
  have hL : ∀ y : GSpin d.QW, d.IsGammaElt y → IsomCent.LieAbelian
      (bform (d.QW.baseChange (AlgebraicClosure F)))
      (specP _ (bcGSpin d.QW y) :
        AlgebraicClosure F ⊗[F] (Fin d.m → F) →ₗ[AlgebraicClosure F] _) := fun y hy => by
    rw [specP_bcGSpin]; exact lieAbelian_specP_baseChange y hy
  have hxt : Commute x t := (Subgroup.mem_centralizer_singleton_iff.mp htx.1).symm
  have hxt' : Commute (bcGSpin d.QW x) (bcGSpin d.QW t) := hxt.map _
  have hE : Module.End.eigenspace (specP _ (bcGSpin d.QW x) :
        AlgebraicClosure F ⊗[F] (Fin d.m → F) →ₗ[AlgebraicClosure F] _) 1 =
      Module.End.eigenspace (specP _ (bcGSpin d.QW t) :
        AlgebraicClosure F ⊗[F] (Fin d.m → F) →ₗ[AlgebraicClosure F] _) 1 := by
    rw [eigenspace_bc_one, eigenspace_bc_one, d.fixedSub_eq_of_torusOf_eq htx hT]
  constructor
  · exact Steinberg.commute_of_commute_of_lieAbelian hQ (hss x hx) (hss t ht) (hL t ht) hxt' hE
  · exact Steinberg.commute_of_commute_of_lieAbelian hQ (hss t ht) (hss x hx) (hL x hx)
      hxt'.symm hE.symm

theorem fixedSub_incl_eq {x t : GSpin d.QW} (h : fixedSub t = fixedSub x) :
    fixedSub (d.incl t) = fixedSub (d.incl x) := by
  ext ⟨w, z⟩
  rw [d.mem_fixedSub_incl_iff, d.mem_fixedSub_incl_iff, h]

/-- **On `T_{x,♮}` the centralizers in `GSpin(V)(F̄)` agree** (`V`-version of
`commute_bc_iff_of_torusOf_eq`). -/
theorem commute_bc_incl_iff_of_torusOf_eq {x t : GSpin d.QW} (hx : d.IsGammaElt x)
    (ht : d.IsGammaElt t) (htx : t ∈ d.torusOf x) (hT : d.torusOf t = d.torusOf x)
    (z : GSpin (d.QV.baseChange (AlgebraicClosure F))) :
    Commute z (bcGSpin d.QV (d.incl t)) ↔ Commute z (bcGSpin d.QV (d.incl x)) := by
  have hQ := isNondeg_baseChange _ d.nondeg_QV
  have hss : ∀ y : GSpin d.QW, d.IsGammaElt y → Module.End.IsSemisimple
      (specP _ (bcGSpin d.QV (d.incl y)) :
        AlgebraicClosure F ⊗[F] d.V →ₗ[AlgebraicClosure F] _) := fun y hy => by
    rw [specP_bcGSpin]
    exact isSemisimple_baseChange (isSemisimple_specP_of_isSS d.QV (d.incl y) (d.isSS_incl hy.1))
  have hL : ∀ y : GSpin d.QW, d.IsGammaElt y → IsomCent.LieAbelian
      (bform (d.QV.baseChange (AlgebraicClosure F)))
      (specP _ (bcGSpin d.QV (d.incl y)) :
        AlgebraicClosure F ⊗[F] d.V →ₗ[AlgebraicClosure F] _) := fun y hy => by
    have h := hss y hy
    rw [specP_bcGSpin] at h ⊢
    exact d.lieAbelian_incl y h (lieAbelian_specP_baseChange y hy)
  have hxt : Commute x t := (Subgroup.mem_centralizer_singleton_iff.mp htx.1).symm
  have hxt' : Commute (bcGSpin d.QV (d.incl x)) (bcGSpin d.QV (d.incl t)) :=
    (hxt.map d.incl).map _
  have hE : Module.End.eigenspace (specP _ (bcGSpin d.QV (d.incl x)) :
        AlgebraicClosure F ⊗[F] d.V →ₗ[AlgebraicClosure F] _) 1 =
      Module.End.eigenspace (specP _ (bcGSpin d.QV (d.incl t)) :
        AlgebraicClosure F ⊗[F] d.V →ₗ[AlgebraicClosure F] _) 1 := by
    rw [eigenspace_bc_one, eigenspace_bc_one,
      d.fixedSub_incl_eq (d.fixedSub_eq_of_torusOf_eq htx hT)]
  constructor
  · exact Steinberg.commute_of_commute_of_lieAbelian hQ (hss x hx) (hss t ht) (hL t ht) hxt' hE
  · exact Steinberg.commute_of_commute_of_lieAbelian hQ (hss t ht) (hss x hx) (hL x hx)
      hxt'.symm hE.symm

/-- **Points of the Lie algebra of `T_x` are semisimple** for `x ∈ Γ(G,H)`: an `X ∈ gspin(W)`
commuting with `x` and killing `W'_x` is semisimple.  Over `F̄`, `P(x)` is semisimple with abelian
moved Lie centralizer (`lieAbelian_specP_baseChange`), and `adV X` is skew, commutes with `P(x)`
and vanishes on `ker (P(x) − 1) = W'_x ⊗ F̄`, hence is semisimple
(`IsomCent.isSemisimple_of_isSkewAdjoint_of_commute_of_lieAbelian`); then so is `X`
(`isSemisimple_mulLeft_of_isSemisimple_adV_baseChange`).  Lie-algebra form of
`isSS_of_mem_torusOf`. -/
theorem isSS_of_commute_of_isGammaElt {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    {X : CliffordAlgebra d.QW} (hX : X ∈ gspin d.QW)
    (hc : ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * X =
      X * ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
    (hf : ∀ v ∈ fixedSub x, adV d.QW X v = 0) : IsSS F X := by
  refine isSemisimple_mulLeft_of_isSemisimple_adV_baseChange d.nondeg hX ?_
  have hQ := isNondeg_baseChange _ d.nondeg
  have hB : (bform (d.QW.baseChange (AlgebraicClosure F))).IsSymm :=
    ⟨fun u v => bform_comm _ u v⟩
  have hbf : bform (d.QW.baseChange (AlgebraicClosure F)) =
      (bform d.QW).baseChange (AlgebraicClosure F) := QuadraticForm.associated_baseChange _
  have hxss : Module.End.IsSemisimple ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange
      (AlgebraicClosure F)) :=
    isSemisimple_baseChange (isSemisimple_specP_of_isSS d.QW x hx.1)
  have hXi : LinearMap.IsOrthogonal (bform (d.QW.baseChange (AlgebraicClosure F)))
      ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange (AlgebraicClosure F)) := by
    rw [← specP_bcGSpin]; exact Steinberg.isOrthogonal_specP _
  have hsk : LinearMap.IsSkewAdjoint (bform (d.QW.baseChange (AlgebraicClosure F)))
      ((adV d.QW X).baseChange (AlgebraicClosure F)) := by
    rw [hbf]; exact LinearMap.IsSkewAdjoint.baseChange _
      (LinearMap.isSkewAdjoint_iff.2 (bform_adV hX))
  have hcomm : Commute ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange
      (AlgebraicClosure F)) ((adV d.QW X).baseChange (AlgebraicClosure F)) := by
    rw [Commute, SemiconjBy, ← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul,
      (commute_iff_adV d.nondeg x hX).mp hc]
  refine IsomCent.isSemisimple_of_isSkewAdjoint_of_commute_of_lieAbelian hB hQ hXi hxss
    (lieAbelian_specP_baseChange x hx) hsk hcomm fun z hz => ?_
  have he := eigenspace_bc_one d.QW x
  rw [specP_bcGSpin] at he
  rw [he, Submodule.baseChange_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, hv, rfl⟩ := hy
    simp [hf v hv]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
  | smul c a _ ha => rw [map_smul, ha, smul_zero]

end GGPData

end TorusNat

end GSpinGGP
