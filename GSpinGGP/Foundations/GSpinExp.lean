/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.ExpLocal
import GSpinGGP.Foundations.GSpin
import TauCeti.RingTheory.Adjoin.Unit

/-!
# The logarithm of `GSpin` near `1` lies in `gspin`

* `stabSubalgebra`: the endomorphisms of a module preserving a submodule, as a subalgebra;
* `expA_ad_eq`: `e^{ad Y} = Ad(e^Y)` near `0` (in the algebra of endomorphisms of `A`);
* `eventually_mem_gspin_of_expA_mem`: for `Y` near `0` in `C(Q)`, `e^Y ∈ GSpin(Q)` implies
  `Y ∈ gspin(Q)` (evenness, and `[Y, ι(V)] ⊆ ι(V)` from `Ad(e^Y) ι(V) ⊆ ι(V)`), by
  `exists_nhds_mem_of_expA_mem`;
* `isSS_of_mem_adjoin`, `isSS_coe_inv`, `isSS_mul_of_commute`: semisimplicity of elements of
  `F[u]`, of inverses and of commuting products;
* `isRegularSS_add_iff_of_central`: translation by a central semisimple element preserves
  regularity.
-/

noncomputable section

open Topology Filter

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

/-- The endomorphisms of `M` preserving the submodule `p`, as a subalgebra of `End(M)`. -/
def stabSubalgebra {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (p : Submodule R M) :
    Subalgebra R (Module.End R M) where
  carrier := {f | ∀ v ∈ p, f v ∈ p}
  mul_mem' hf hg v hv := hf _ (hg v hv)
  add_mem' hf hg v hv := p.add_mem (hf v hv) (hg v hv)
  algebraMap_mem' c v hv := by
    simpa [Module.algebraMap_end_apply] using p.smul_mem c hv

theorem mem_stabSubalgebra {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {p : Submodule R M} {f : Module.End R M} : f ∈ stabSubalgebra p ↔ ∀ v ∈ p, f v ∈ p :=
  Iff.rfl

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

section Ad

variable {A : Type*} [Ring A] [Algebra F A]

/-- Right multiplication as a linear map `A → End(A)`. -/
def mulRightₗ : A →ₗ[F] Module.End F A := (LinearMap.mul F A).flip

omit [PAdicField F] in
theorem mulRightₗ_apply (a : A) : mulRightₗ (F := F) a = LinearMap.mulRight F a := rfl

variable [Module.Finite F A] [TopologicalSpace A] [IsModuleTopology F A]

variable (F) in
/-- **`e^{ad Y} = Ad(e^Y)`** for `Y` near `0`, in `End(A)` with its module topology:
`ad Y = L_Y − R_Y` with commuting `L_Y`, `R_Y`, and `e^{L_Y} = L_{e^Y}`, `e^{−R_Y} = R_{e^{−Y}}`. -/
theorem expA_ad_eq [TopologicalSpace (Module.End F A)] [IsModuleTopology F (Module.End F A)] :
    ∀ᶠ Y in 𝓝 (0 : A), expA F (LinearMap.mulLeft F Y - LinearMap.mulRight F Y) =
      LinearMap.mulLeft F (expA F Y) * LinearMap.mulRight F (expA F (-Y)) := by
  letI := isTopologicalRing_of_moduleTopology F A
  letI := isTopologicalRing_of_moduleTopology F (Module.End F A)
  obtain ⟨UB, hUB, hadd⟩ := expA_add_of_commute F (A := Module.End F A)
  have hl := eventually_map_expA (F := F) (A := A) (B := Module.End F A)
    (Algebra.lmul F A).toLinearMap (fun X n => map_pow (Algebra.lmul F A) X n)
  have hr := eventually_map_expA (F := F) (A := A) (B := Module.End F A) mulRightₗ
    (fun X n => by rw [mulRightₗ_apply, mulRightₗ_apply, LinearMap.pow_mulRight])
  have hcl : Continuous ((Algebra.lmul F A).toLinearMap : A → Module.End F A) :=
    IsModuleTopology.continuous_of_linearMap _
  have hcr : Continuous (mulRightₗ (F := F) : A → Module.End F A) :=
    IsModuleTopology.continuous_of_linearMap _
  have h1 : (fun Y : A => (Algebra.lmul F A).toLinearMap Y) ⁻¹' UB ∈ 𝓝 (0 : A) :=
    hcl.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  have h2 : (fun Y : A => -mulRightₗ (F := F) Y) ⁻¹' UB ∈ 𝓝 (0 : A) :=
    hcr.neg.continuousAt.preimage_mem_nhds (by simpa using hUB)
  have hr' : ∀ᶠ Y in 𝓝 (0 : A), mulRightₗ (F := F) (expA F (-Y)) = expA F (mulRightₗ (-Y)) :=
    (continuous_neg.tendsto' (0 : A) 0 neg_zero).eventually hr
  filter_upwards [hl, hr', h1, h2] with Y hlY hrY h1Y h2Y
  have hc : Commute (LinearMap.mulLeft F Y) (-LinearMap.mulRight F Y) :=
    (LinearMap.commute_mulLeft_right Y Y).neg_right
  have h1Y' : LinearMap.mulLeft F Y ∈ UB := h1Y
  have h2Y' : -LinearMap.mulRight F Y ∈ UB := h2Y
  rw [sub_eq_add_neg, hadd _ h1Y' _ h2Y' hc]
  congr 1
  · exact hlY.symm
  · rw [mulRightₗ_apply, map_neg, mulRightₗ_apply] at hrY
    exact hrY.symm

end Ad

section Clifford

open CliffordAlgebra

variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] (Q : QuadraticForm F V)

/-- **The logarithm of `GSpin(Q)` near `1` lies in `gspin(Q)`**: for `Y` near `0` in `C(Q)`, if
`e^Y ∈ GSpin(Q)` then `Y` is even (`e^Y` is, and `exp` detects subalgebras near `0`) and
`[Y, ι(V)] ⊆ ι(V)` (`e^{ad Y} = Ad(e^Y)` preserves `ι(V)`, and `exp` detects the stabilizer of
`ι(V)` in `End(C(Q))`). -/
theorem eventually_mem_gspin_of_expA_mem :
    ∀ᶠ Y in 𝓝 (0 : CliffordAlgebra Q), ∀ g : ↥(GSpin Q),
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = expA F Y → Y ∈ gspin Q := by
  letI : TopologicalSpace (Module.End F (CliffordAlgebra Q)) :=
    moduleTopology F (Module.End F (CliffordAlgebra Q))
  haveI : IsModuleTopology F (Module.End F (CliffordAlgebra Q)) := ⟨rfl⟩
  letI := isTopologicalRing_of_moduleTopology F (Module.End F (CliffordAlgebra Q))
  obtain ⟨U₁, hU₁, hsub⟩ := exists_nhds_mem_of_expA_mem F (A := CliffordAlgebra Q)
  obtain ⟨U₂, hU₂, hneg⟩ := expA_mul_expA_neg F (A := CliffordAlgebra Q)
  obtain ⟨UB, hUB, hsubB⟩ := exists_nhds_mem_of_expA_mem F (A := Module.End F (CliffordAlgebra Q))
  set ad : CliffordAlgebra Q →ₗ[F] Module.End F (CliffordAlgebra Q) :=
    (Algebra.lmul F (CliffordAlgebra Q)).toLinearMap - mulRightₗ with had
  have hadc : Continuous ad := IsModuleTopology.continuous_of_linearMap ad
  have h3 : ad ⁻¹' UB ∈ 𝓝 (0 : CliffordAlgebra Q) :=
    hadc.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  filter_upwards [hU₁, hU₂, h3, expA_ad_eq F (A := CliffordAlgebra Q)] with Y hY₁ hY₂ hY₃ hY₄
  intro g hg
  obtain ⟨hg0, hg1, -⟩ := g.2
  have hginv : (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      expA F (-Y) := Units.inv_eq_of_mul_eq_one_right (by rw [hg]; exact hneg Y hY₂)
  refine ⟨hsub Y hY₁ (CliffordAlgebra.even Q) (hg ▸ hg0), fun v => ?_⟩
  -- `Ad(e^Y) = e^{ad Y}` preserves `ι(V)`
  have hAd : expA F (ad Y) ∈ stabSubalgebra (LinearMap.range (ι Q)) := by
    have : ad Y = LinearMap.mulLeft F Y - LinearMap.mulRight F Y := rfl
    rw [this, hY₄, mem_stabSubalgebra]
    rintro _ ⟨w, rfl⟩
    have := hg1 w
    rw [hg, hginv] at this
    simpa [mul_assoc] using this
  have hmem := hsubB _ hY₃ _ hAd (ι Q v) (LinearMap.mem_range_self _ v)
  have : ad Y (ι Q v) = ⁅Y, ι Q v⁆ := by
    simp [had, mulRightₗ_apply, Ring.lie_def]
  rwa [this] at hmem

end Clifford

section Semisimple

variable {A : Type*} [Ring A] [Algebra F A]

/-- An element of `F[u]` is semisimple if `u` is. -/
theorem isSS_of_mem_adjoin [PerfectField F] [FiniteDimensional F A] {u Y : A} (hu : IsSS F u)
    (hY : Y ∈ Algebra.adjoin F {u}) : IsSS F Y := by
  have hmem : Algebra.lmul F A Y ∈ Algebra.adjoin F {Algebra.lmul F A u} := by
    rw [← AlgHom.map_adjoin_singleton]
    exact Subalgebra.mem_map.mpr ⟨_, hY, rfl⟩
  exact Module.End.IsSemisimple.of_mem_adjoin_singleton hu hmem

/-- The inverse of a semisimple unit is semisimple (it lies in `F[u]`). -/
theorem isSS_coe_inv [PerfectField F] [FiniteDimensional F A] {u : Aˣ} (hu : IsSS F (u : A)) :
    IsSS F ((u⁻¹ : Aˣ) : A) :=
  isSS_of_mem_adjoin hu (TauCeti.Units.coe_inv_mem_adjoin u (IsIntegral.of_finite F (u : A)))

/-- The product of commuting semisimple elements is semisimple. -/
theorem isSS_mul_of_commute [PerfectField F] [FiniteDimensional F A] {a c : A} (h : Commute a c)
    (ha : IsSS F a) (hc : IsSS F c) : IsSS F (a * c) := by
  unfold IsSS at *
  rw [LinearMap.mulLeft_mul]
  have hcomm : Commute (LinearMap.mulLeft F a) (LinearMap.mulLeft F c) := by
    exact LinearMap.ext fun w => by
      simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, ← mul_assoc, h.eq]
  exact Module.End.IsSemisimple.mul_of_commute hcomm ha hc

/-- **Translation by a central semisimple element preserves regularity**: if `Y` is semisimple and
commutes with every element of `𝔥`, then `Z + Y` is regular semisimple in `𝔥` iff `Z` is, for
`Z ∈ 𝔥` (same centralizer in `𝔥`; sums of commuting semisimple elements are semisimple). -/
theorem isRegularSS_add_iff_of_central [PerfectField F] [FiniteDimensional F A]
    {𝔥 : LieSubalgebra F A} {Y : A} (hY : IsSS F Y) (hc : ∀ W ∈ 𝔥, Commute W Y) {Z : A}
    (hZ : Z ∈ 𝔥) : IsRegularSS 𝔥 (Z + Y) ↔ IsRegularSS 𝔥 Z := by
  have hC : lieCentralizer 𝔥 (Z + Y) = lieCentralizer 𝔥 Z := by
    ext W
    rw [mem_lieCentralizer, mem_lieCentralizer]
    refine and_congr_right fun hW => ?_
    rw [add_mul, mul_add, (hc W hW).eq]
    exact add_left_inj _
  have hss : ∀ {a c : A}, Commute a c → IsSS F a → IsSS F c → IsSS F (a + c) := by
    intro a c h ha hc'
    unfold IsSS at *
    rw [show LinearMap.mulLeft F (a + c) = LinearMap.mulLeft F a + LinearMap.mulLeft F c from
      LinearMap.ext fun w => add_mul a c w]
    have hcomm : Commute (LinearMap.mulLeft F a) (LinearMap.mulLeft F c) := by
      exact LinearMap.ext fun w => by
        simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, ← mul_assoc, h.eq]
    exact Module.End.IsSemisimple.add_of_commute hcomm ha hc'
  have hnY : IsSS F (-Y) := by
    unfold IsSS at *
    rw [show LinearMap.mulLeft F (-Y) = (-1 : F) • LinearMap.mulLeft F Y from
      LinearMap.ext fun w => by simp]
    exact Module.End.IsSemisimple_smul _ hY
  have hZY : Commute Z Y := hc Z hZ
  unfold IsRegularSS
  rw [hC]
  refine and_congr_left fun _ => ⟨fun h => ?_, fun h => hss hZY h hY⟩
  have := hss ((hZY.add_left (Commute.refl Y)).neg_right) h hnY
  rwa [add_neg_cancel_right] at this

end Semisimple

end GSpinGGP
