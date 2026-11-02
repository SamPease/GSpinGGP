/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TorusCommute

/-!
# The moved part of the centralizer of `x ∈ GSpin(W)(F)`

For `x ∈ GSpin(W)(F)`, the *moved part* of the Lie centralizer is
`𝔩_x = {X ∈ gspin(W) : [X, x] = 0, [X, ι(W'_x)] = 0}` (`so(W''_x)_{x̄} ⊕ F`).

* `MovedPart.exists_nhds_expA_mem_GSpin`: `e^X ∈ GSpin(W)(F)` for small `X ∈ gspin(W)`;
* `movedPartAbelian_of_isGammaElt`: `𝔩_x` is abelian for `x ∈ Γ(G,H)`;
* `gspinBC`, `movedCentMap`, `gspinBC_commute_of_mem`: `𝔩_x ⊗ F̄` and its commutativity;
* `lieAbelian_specP_baseChange_of_movedPartAbelian`: if `𝔩_x` is abelian, so is the Lie algebra
  of `S_x` over `F̄` (`IsomCent.LieAbelian`).
-/

noncomputable section

open MeasureTheory Filter Topology Module
open CliffordAlgebra (ι_injective)
open scoped Classical

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-! ### The moved part on `Γ(G,H)` (helpers for `movedPartAbelian_of_isGammaElt`)

The exponential of a small element of `gspin(W)` lies in `GSpin(W)(F)`
(`MovedPart.exists_nhds_expA_mem_GSpin`): conjugation by `e^X` is `e^{ad X}` (computed in
`End(F^d)` via left and right multiplication), which preserves the `ad X`-stable closed subspace
`ι(W)`. -/

namespace MovedPart

variable {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A]
  [IsModuleTopology F A]

local notation "VA" => (Fin (Module.finrank F A) → F)

variable (F) in
/-- Right multiplication by `a`, transported to a continuous endomorphism of `F^d`. -/
def rmulPi (a : A) : VA →L[F] VA :=
  LinearMap.toContinuousLinearMap
    ((toPiCLE F A).toLinearEquiv.toLinearMap ∘ₗ LinearMap.mulRight F a ∘ₗ
      (toPiCLE F A).symm.toLinearEquiv.toLinearMap)

lemma rmulPi_apply (a : A) (v : VA) :
    rmulPi F a v = toPiCLE F A ((toPiCLE F A).symm v * a) := rfl

variable (F) in
/-- `a ↦ rmulPi a` as a linear map. -/
def rmulPiₗ : A →ₗ[F] (VA →L[F] VA) where
  toFun := rmulPi F
  map_add' a b := ContinuousLinearMap.ext fun v => by simp [rmulPi_apply, mul_add]
  map_smul' c a := ContinuousLinearMap.ext fun v => by simp [rmulPi_apply]

lemma continuous_rmulPi : Continuous (rmulPi F : A → VA →L[F] VA) :=
  IsModuleTopology.continuous_of_linearMap (rmulPiₗ F)

lemma rmulPi_mul (a b : A) : rmulPi F (a * b) = rmulPi F b * rmulPi F a :=
  ContinuousLinearMap.ext fun v => by simp [rmulPi_apply, mul_assoc]

lemma rmulPi_pow (a : A) (n : ℕ) : rmulPi F (a ^ n) = rmulPi F a ^ n := by
  induction n with
  | zero => ext v; simp [rmulPi_apply]
  | succ n ih => rw [pow_succ', rmulPi_mul, ih, pow_succ]

lemma commute_lmulPi_rmulPi (a b : A) : Commute (lmulPi F a) (rmulPi F b) := by
  ext v
  simp [lmulPi_apply, rmulPi_apply, mul_assoc]

lemma rmulPi_expA_neg_aux {X : A}
    (hs : HasSum (fun n : ℕ ↦ ((n.factorial : F)⁻¹) • (-X) ^ n) (expA F (-X))) :
    rmulPi F (expA F (-X)) = NormedSpace.exp (rmulPi F (-X)) := by
  have h2 := hs.map (rmulPiₗ F) (continuous_rmulPi (F := F))
  have hterm : ((rmulPiₗ F : A →ₗ[F] (VA →L[F] VA)) ∘
      fun n : ℕ ↦ ((n.factorial : F)⁻¹) • (-X) ^ n) =
      fun n ↦ ((n.factorial : F)⁻¹) • rmulPi F (-X) ^ n := by
    funext n
    simp only [Function.comp_apply, map_smul]
    rw [show (rmulPiₗ F) ((-X) ^ n) = rmulPi F ((-X) ^ n) from rfl, rmulPi_pow]
  rw [hterm] at h2
  rw [NormedSpace.exp_eq_tsum F]
  exact h2.tsum_eq.symm

/-- **`e^X r e^{-X}` stays in an `ad X`-stable subspace** for `X` near `0`: in `End(F^d)`,
`L_{e^X} R_{e^{-X}} = e^{L_X} e^{-R_X} = e^{L_X - R_X} = e^{ad X}` (left and right multiplications
commute), and `e^{ad X} r = ∑ (ad X)ⁿ r / n!` lies in the closed subspace `R`. -/
lemma exists_nhds_expA_conj_mem :
    ∃ U ∈ 𝓝 (0 : A), ∀ X ∈ U, ∀ R : Submodule F A, (∀ r ∈ R, X * r - r * X ∈ R) →
      ∀ r ∈ R, expA F X * r * expA F (-X) ∈ R := by
  let _ := isTopologicalRing_of_moduleTopology F A
  have _ := t2Space_of_moduleTopology F A
  obtain ⟨U₀, hU₀, hneg, h⟩ := expA_aux F (A := A)
  set B := Metric.eball (0 : VA →L[F] VA) (NormedSpace.expSeries F (VA →L[F] VA)).radius
  have hB0 : (0 : VA →L[F] VA) ∈ B := by
    rw [Metric.mem_eball, edist_self]
    exact expSeries_radius_pos_of_pAdic F (VA →L[F] VA)
  let adPi : A → (VA →L[F] VA) := fun X => lmulPi F X - rmulPi F X
  have hadc : Continuous adPi := (continuous_lmulPi F).sub (continuous_rmulPi (F := F))
  have hrc : Continuous fun X : A => rmulPi F (-X) := (continuous_rmulPi (F := F)).comp continuous_neg
  refine ⟨U₀ ∩ ((fun X : A => rmulPi F (-X)) ⁻¹' B) ∩ (adPi ⁻¹' B), ?_, ?_⟩
  · refine inter_mem (inter_mem hU₀ ?_) ?_
    · refine (Metric.isOpen_eball.preimage hrc).mem_nhds ?_
      show rmulPi F (-0 : A) ∈ B
      rw [neg_zero, show rmulPi F (0 : A) = 0 from map_zero (rmulPiₗ F)]
      exact hB0
    · refine (Metric.isOpen_eball.preimage hadc).mem_nhds ?_
      show lmulPi F (0 : A) - rmulPi F 0 ∈ B
      rw [show rmulPi F (0 : A) = 0 from map_zero (rmulPiₗ F),
        show lmulPi F (0 : A) = 0 from map_zero (lmulPiₗ F), sub_zero]
      exact hB0
  rintro X ⟨⟨hX0, hXr⟩, hXad⟩ R hR r hr
  obtain ⟨hb, -, he⟩ := h X hX0
  have hρ := rmulPi_expA_neg_aux (h (-X) (hneg X hX0)).2.1
  have hadd : NormedSpace.exp (lmulPi F X) * NormedSpace.exp (rmulPi F (-X)) =
      NormedSpace.exp (adPi X) := by
    rw [← NormedSpace.exp_add_of_commute_of_mem_ball (𝕂 := F) (commute_lmulPi_rmulPi X (-X)) hb hXr]
    congr 1
    simp only [adPi, sub_eq_add_neg]
    rw [show rmulPi F (-X) = -rmulPi F X from map_neg (rmulPiₗ F) X]
  have hsum := NormedSpace.expSeries_hasSum_exp_of_mem_ball' (𝕂 := F) (adPi X) hXad
  have hsv := hsum.map (ContinuousLinearMap.apply F VA (toPiCLE F A r))
    (ContinuousLinearMap.apply F VA (toPiCLE F A r)).continuous
  set S : Submodule F VA := R.map (toPiCLE F A).toLinearEquiv.toLinearMap
  have hclosed : IsClosed (S : Set VA) := S.closed_of_finiteDimensional
  have hpow : ∀ n : ℕ, ∃ z ∈ R, (adPi X ^ n) (toPiCLE F A r) = toPiCLE F A z := by
    intro n
    induction n with
    | zero => exact ⟨r, hr, by simp⟩
    | succ n ih =>
      obtain ⟨z, hz, hzeq⟩ := ih
      refine ⟨X * z - z * X, hR z hz, ?_⟩
      rw [pow_succ', mul_apply_eq_comp, hzeq]
      simp [adPi, lmulPi_apply, rmulPi_apply, map_sub]
  have hmem : NormedSpace.exp (adPi X) (toPiCLE F A r) ∈ S := by
    refine hclosed.mem_of_tendsto hsv (Eventually.of_forall fun s => ?_)
    refine Submodule.sum_mem _ fun n _ => ?_
    simp only [Function.comp_apply, ContinuousLinearMap.apply_apply,
      smul_apply]
    obtain ⟨z, hz, hzeq⟩ := hpow n
    rw [hzeq]
    exact S.smul_mem _ ⟨z, hz, rfl⟩
  rw [← hadd, ← he, ← hρ, mul_apply_eq_comp, rmulPi_apply, lmulPi_apply] at hmem
  obtain ⟨z, hz, hzeq⟩ := hmem
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hzeq
  have := (toPiCLE F A).injective hzeq
  rw [mul_assoc, ← this]
  exact hz

/-- **`e^X ∈ GSpin(V)` for `X ∈ gspin(V)` near `0`**: `e^X` is a unit (inverse `e^{-X}`), even
(`e^X ∈ F[X] ⊆ C⁺(V)`), and conjugation by `e^{±X}` preserves `ι(V)`, which is `ad X`-stable
(`exists_nhds_expA_conj_mem`). -/
lemma exists_nhds_expA_mem_GSpin {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (Q : QuadraticForm F V) :
    ∃ U ∈ 𝓝 (0 : CliffordAlgebra Q), ∀ X ∈ U, X ∈ gspin Q →
      ∃ g : GSpin Q, (((g : (CliffordAlgebra Q)ˣ)) : CliffordAlgebra Q) = expA F X := by
  obtain ⟨U₁, hU₁, hconj⟩ := exists_nhds_expA_conj_mem (F := F) (A := CliffordAlgebra Q)
  obtain ⟨U₂, hU₂, hinv⟩ := expA_mul_expA_neg F (A := CliffordAlgebra Q)
  obtain ⟨U₃, hU₃, hadj⟩ := exists_nhds_expA_mem_adjoin F (A := CliffordAlgebra Q)
  have hneg : (fun X : CliffordAlgebra Q => -X) ⁻¹' (U₁ ∩ U₂) ∈ 𝓝 (0 : CliffordAlgebra Q) := by
    have hc : ContinuousAt (fun X : CliffordAlgebra Q => -X) 0 := continuous_neg.continuousAt
    exact hc.preimage_mem_nhds (by rw [neg_zero]; exact inter_mem hU₁ hU₂)
  refine ⟨U₁ ∩ U₂ ∩ U₃ ∩ (fun X : CliffordAlgebra Q => -X) ⁻¹' (U₁ ∩ U₂),
    inter_mem (inter_mem (inter_mem hU₁ hU₂) hU₃) hneg, ?_⟩
  rintro X ⟨⟨⟨hX1, hX2⟩, hX3⟩, ⟨hXn1, hXn2⟩⟩ hX
  have hXn : -X ∈ gspin Q := neg_mem hX
  have hR : ∀ Z ∈ gspin Q, ∀ r ∈ LinearMap.range (CliffordAlgebra.ι Q), Z * r - r * Z ∈ LinearMap.range (CliffordAlgebra.ι Q) := by
    rintro Z hZ _ ⟨v, rfl⟩
    rw [← Ring.lie_def]
    exact hZ.2 v
  have h1 : expA F X * expA F (-X) = 1 := hinv X hX2
  have h2 : expA F (-X) * expA F X = 1 := by
    simpa using hinv (-X) hXn2
  let u : (CliffordAlgebra Q)ˣ := ⟨expA F X, expA F (-X), h1, h2⟩
  have heven : expA F X ∈ CliffordAlgebra.even Q :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hX.1) (hadj X hX3)
  refine ⟨⟨u, heven, fun v => ?_, fun v => ?_⟩, rfl⟩
  · exact hconj X hX1 _ (hR X hX) _ ⟨v, rfl⟩
  · have := hconj (-X) hXn1 _ (hR (-X) hXn) _ ⟨v, rfl⟩
    rw [neg_neg] at this
    exact this

end MovedPart

/-- For `x ∈ Γ(G,H)` the moved part `G''_x` is a torus: `T_x(F) = Z(x) ∩ Fix(W'_x)`
is commutative, hence so is its Lie algebra
`so(W''_x)_{x̄} ⊕ F`.  Own work; this is the hypothesis under which
`nilReg_centralizer_nonempty_iff` applies.

Proof (exponential, no Zariski density): for `X, Y` in the moved part and `c ≠ 0` small, `e^{cX}`,
`e^{cY}` lie in `GSpin(W)(F)` (`MovedPart.exists_nhds_expA_mem_GSpin`), commute with `x` and fix
`W'_x` pointwise (`X`, `Y` commute with `x` and with `ι(W'_x)`), so they lie in `T_x(F)` and
commute.  Near `0` the centralizer of `e^Z` is that of `Z`
(`exists_nhds_commute_of_commute_expA`), so `cX` and `cY` commute.  Only the commutativity of
`T_x(F)` is used, not the semisimplicity of `x` or the compactness of `T_x(F)/A(F)`. -/
theorem movedPartAbelian_of_isGammaElt (d : GGPData F) (x : ↥(GSpin d.QW))
    (hx : d.IsGammaElt x) : MovedPartAbelian d.QW x := by
  intro X hX Y hY hXf hYf
  obtain ⟨U, hU, hG⟩ := MovedPart.exists_nhds_expA_mem_GSpin (F := F) d.QW
  obtain ⟨U', hU', hc⟩ := exists_nhds_commute_of_commute_expA F (A := CliffordAlgebra d.QW)
  have ht : ∀ Z : CliffordAlgebra d.QW, Tendsto (fun t : F => t • Z) (𝓝[≠] 0) (𝓝 0) := by
    intro Z
    have : Continuous (fun t : F => t • Z) := continuous_id.smul continuous_const
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨c, ⟨hcX, hcY⟩, hc0⟩ := ((((ht X).eventually (inter_mem hU hU')).and
    ((ht Y).eventually (inter_mem hU hU'))).and self_mem_nhdsWithin).exists
  -- `e^{cZ}` lies in `T_x` for `Z` in the moved part
  have key : ∀ Z ∈ lieCentralizer (gspin d.QW) ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
      (∀ v ∈ fixedSub x, ⁅Z, CliffordAlgebra.ι d.QW v⁆ = 0) → c • Z ∈ U →
      ∃ g ∈ d.torusOf x, (((g : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW) =
        expA F (c • Z) := by
    intro Z hZ hZf hcZ
    rw [mem_lieCentralizer] at hZ
    obtain ⟨g, hg⟩ := hG _ hcZ ((gspin d.QW).smul_mem c hZ.1)
    refine ⟨g, ⟨?_, fun w hw => ?_⟩, hg⟩
    · show g ∈ Subgroup.centralizer {x}
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxc : Commute ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) (c • Z) :=
        (Commute.smul_right hZ.2 c)
      have := commute_expA_of_commute (F := F) hxc
      rw [← hg] at this
      exact Subtype.ext (Units.ext this.eq.symm)
    · apply ι_injective d.QW
      rw [ι_specP]
      have hw0 := hZf w hw
      rw [Ring.lie_def, sub_eq_zero] at hw0
      have hwc : Commute (CliffordAlgebra.ι d.QW w) (c • Z) :=
        Commute.smul_right hw0.symm c
      have := (commute_expA_of_commute (F := F) hwc).eq
      rw [← hg] at this
      rw [← this, mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨g, hg, hge⟩ := key X hX hXf hcX.1
  obtain ⟨h, hh, hhe⟩ := key Y hY hYf hcY.1
  have hgh : Commute (expA F (c • X)) (expA F (c • Y)) := by
    have := congrArg (fun k : ↥(GSpin d.QW) =>
      (((k : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW)) (hx.2.1 g hg h hh).eq
    simp only [Subgroup.coe_mul, Units.val_mul] at this
    rw [hge, hhe] at this
    exact this
  have h1 : Commute (expA F (c • X)) (c • Y) := hc _ hcY.2 _ hgh
  have h2 : Commute (c • Y) (c • X) := hc _ hcX.2 _ h1.symm
  have h3 : c • c • (Y * X) = c • c • (X * Y) := by
    have := h2.eq
    rw [smul_mul_smul_comm, smul_mul_smul_comm] at this
    rw [smul_smul, smul_smul]
    exact this
  rw [Ring.lie_def, sub_eq_zero]
  have hc' : c * c ≠ 0 := mul_ne_zero hc0 hc0
  rw [smul_smul, smul_smul] at h3
  exact (smul_right_injective _ hc' h3).symm

section WD

open CliffordAlgebra
open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module F V]

theorem ofBaseChange_tmul_eq (Q : QuadraticForm F V) (z : AlgebraicClosure F)
    (X : CliffordAlgebra Q) :
    ofBaseChange (AlgebraicClosure F) Q (z ⊗ₜ X) = algebraMap _ _ z * bcHom Q X := by
  rw [show z ⊗ₜ[F] X = (z ⊗ₜ[F] (1 : CliffordAlgebra Q)) * (1 ⊗ₜ X) by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul, ofBaseChange_tmul_one]
  rfl

theorem bcHom_mem_even (Q : QuadraticForm F V) {X : CliffordAlgebra Q} (hX : X ∈ even Q) :
    bcHom Q X ∈ even (Q.baseChange (AlgebraicClosure F)) := by
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hX ⊢
  induction X, hX using even_induction with
  | algebraMap r =>
    have : bcHom Q (algebraMap F _ r) = algebraMap (AlgebraicClosure F) _
        (algebraMap F (AlgebraicClosure F) r) := by
      show ofBaseChange (AlgebraicClosure F) Q (1 ⊗ₜ algebraMap F _ r) = _
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, ofBaseChange_tmul_one,
        Algebra.smul_def, mul_one]
    rw [this]
    exact SetLike.algebraMap_mem_graded _ _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul, bcHom_ι, bcHom_ι]
    exact zero_add (0 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero _ _ _) ih

theorem ofBaseChange_mem_gspin (Q : QuadraticForm F V) (z : AlgebraicClosure F)
    {X : CliffordAlgebra Q} (hX : X ∈ gspin Q) :
    ofBaseChange (AlgebraicClosure F) Q (z ⊗ₜ X) ∈ gspin (Q.baseChange (AlgebraicClosure F)) := by
  rw [ofBaseChange_tmul_eq, ← Algebra.smul_def]
  refine (gspin _).smul_mem z ⟨bcHom_mem_even Q hX.1, fun w => ?_⟩
  induction w using TensorProduct.inductionOn with
  | tmul c v =>
    obtain ⟨u, hu⟩ := hX.2 v
    refine ⟨c ⊗ₜ u, ?_⟩
    have hc : ι (Q.baseChange (AlgebraicClosure F)) (c ⊗ₜ v) = c • ι _ (1 ⊗ₜ v) := by
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hc' : ι (Q.baseChange (AlgebraicClosure F)) (c ⊗ₜ u) = c • ι _ (1 ⊗ₜ u) := by
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hc, hc', ← bcHom_ι, ← bcHom_ι, hu, Ring.lie_def, Ring.lie_def, mul_smul_comm,
      smul_mul_assoc, ← smul_sub, map_sub, map_mul, map_mul]
  | add a b ha hb =>
    rw [map_add, lie_add]
    exact Submodule.add_mem _ ha hb


/-- `F̄ ⊗ gspin(Q) → C(Q_{F̄})`. -/
def gspinBC (Q : QuadraticForm F V) :
    AlgebraicClosure F ⊗[F] (gspin Q).toSubmodule →ₗ[AlgebraicClosure F]
      CliffordAlgebra (Q.baseChange (AlgebraicClosure F)) :=
  (ofBaseChange (AlgebraicClosure F) Q).toLinearMap ∘ₗ
    (gspin Q).toSubmodule.subtype.baseChange (AlgebraicClosure F)

theorem gspinBC_tmul (Q : QuadraticForm F V) (z : AlgebraicClosure F) (X : (gspin Q).toSubmodule) :
    gspinBC Q (z ⊗ₜ X) = ofBaseChange (AlgebraicClosure F) Q (z ⊗ₜ (X : CliffordAlgebra Q)) := rfl

theorem ofBaseChange_injective (Q : QuadraticForm F V) :
    Function.Injective (ofBaseChange (AlgebraicClosure F) Q) :=
  Function.LeftInverse.injective (toBaseChange_ofBaseChange (AlgebraicClosure F) Q)

theorem baseChange_subtype_injective {M : Type*} [AddCommGroup M] [Module F M] (p : Submodule F M) :
    Function.Injective (p.subtype.baseChange (AlgebraicClosure F)) := by
  rw [LinearMap.baseChange_eq_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ p.injective_subtype

/-- Over `F̄`, `gspin(Q_{F̄})` is spanned by `gspin(Q)` (via `gspin = span{v w} ⊕ F`,
`gspin_eq_span`, for `Q_{F̄}` nondegenerate). -/
theorem range_gspinBC [Module.Finite F V] (Q : QuadraticForm F V)
    (hQ : IsNondeg (Q.baseChange (AlgebraicClosure F))) :
    LinearMap.range (gspinBC Q) = (gspin (Q.baseChange (AlgebraicClosure F))).toSubmodule := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    induction u using TensorProduct.inductionOn with
    | tmul z X => exact ofBaseChange_mem_gspin Q z X.2
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  · rw [gspin_eq_span hQ, sup_le_iff, Submodule.span_le, Submodule.span_le]
    constructor
    · rintro _ ⟨⟨w₁, w₂⟩, rfl⟩
      dsimp only
      induction w₁ using TensorProduct.inductionOn with
      | tmul a v =>
        induction w₂ using TensorProduct.inductionOn with
        | tmul b v' =>
          refine ⟨(a * b) ⊗ₜ ⟨ι Q v * ι Q v', ι_mul_ι_mem_gspin Q v v'⟩, ?_⟩
          rw [gspinBC_tmul, ← Algebra.TensorProduct.tmul_mul_tmul, map_mul,
            ofBaseChange_tmul_ι, ofBaseChange_tmul_ι]
        | add b c hb hc => rw [map_add, mul_add]; exact add_mem hb hc
      | add b c hb hc => rw [map_add, add_mul]; exact add_mem hb hc
    · rintro _ rfl
      exact ⟨1 ⊗ₜ ⟨1, one_mem_gspin Q⟩, by rw [gspinBC_tmul]; exact map_one _⟩

/-- The `F`-linear conditions cutting out the moved centralizer: commutator with `x` and with
`ι(bᵢ)` for a basis `bᵢ` of `W'_x`. -/
def movedCentMap [Module.Finite F V] (Q : QuadraticForm F V) (x : GSpin Q) :
    (gspin Q).toSubmodule →ₗ[F] (Option (Fin (finrank F (fixedSub x))) → CliffordAlgebra Q) :=
  LinearMap.pi fun j => Option.elim j
    ((LinearMap.mulLeft F ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) -
      LinearMap.mulRight F ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) ∘ₗ
        (gspin Q).toSubmodule.subtype)
    (fun i => (LinearMap.mulRight F (ι Q (Module.finBasis F (fixedSub x) i : V)) -
      LinearMap.mulLeft F (ι Q (Module.finBasis F (fixedSub x) i : V))) ∘ₗ
        (gspin Q).toSubmodule.subtype)

theorem piRight_pi_baseChange {M : Type*} [AddCommGroup M] [Module F M] {n : Type*} [Fintype n]
    [DecidableEq n] {N : Type*} [AddCommGroup N] [Module F N] (f : n → M →ₗ[F] N)
    (u : AlgebraicClosure F ⊗[F] M) (j : n) :
    TensorProduct.piRight F (AlgebraicClosure F) (AlgebraicClosure F) (fun _ : n => N)
      ((LinearMap.pi f).baseChange (AlgebraicClosure F) u) j =
        (f j).baseChange (AlgebraicClosure F) u := by
  induction u using TensorProduct.inductionOn with
  | tmul z m => simp
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

theorem ofBaseChange_commBC (Q : QuadraticForm F V) (c : CliffordAlgebra Q)
    (u : AlgebraicClosure F ⊗[F] (gspin Q).toSubmodule) :
    ofBaseChange (AlgebraicClosure F) Q
      (((LinearMap.mulLeft F c - LinearMap.mulRight F c) ∘ₗ (gspin Q).toSubmodule.subtype).baseChange
        (AlgebraicClosure F) u) = bcHom Q c * gspinBC Q u - gspinBC Q u * bcHom Q c := by
  induction u using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [LinearMap.baseChange_tmul, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      Submodule.coe_subtype, gspinBC_tmul, ofBaseChange_tmul_eq, map_sub, map_mul]
    rw [← mul_assoc (bcHom Q c), ← Algebra.commutes z (bcHom Q c), mul_sub]
    simp only [mul_assoc]
  | add a b ha hb => simp only [map_add, ha, hb]; noncomm_ring

theorem mem_movedCent_baseChange [Module.Finite F V] (Q : QuadraticForm F V) (x : GSpin Q)
    (u : AlgebraicClosure F ⊗[F] (gspin Q).toSubmodule)
    (hc : bcHom Q ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * gspinBC Q u =
      gspinBC Q u * bcHom Q ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
    (hf : ∀ w ∈ fixedSub x, gspinBC Q u * ι _ (1 ⊗ₜ w) = ι _ (1 ⊗ₜ w) * gspinBC Q u) :
    u ∈ (LinearMap.ker (movedCentMap Q x)).baseChange (AlgebraicClosure F) := by
  rw [← LinearMap.ker_baseChange_of_flat, LinearMap.mem_ker]
  apply (TensorProduct.piRight F (AlgebraicClosure F) (AlgebraicClosure F) _).injective
  funext j
  rw [movedCentMap, piRight_pi_baseChange, map_zero, Pi.zero_apply]
  apply ofBaseChange_injective Q
  rw [map_zero]
  cases j with
  | none =>
    simp only [Option.elim]
    rw [ofBaseChange_commBC, hc, sub_self]
  | some i =>
    simp only [Option.elim]
    rw [← neg_sub, LinearMap.neg_comp, LinearMap.baseChange_neg, LinearMap.neg_apply, map_neg,
      ofBaseChange_commBC, bcHom_ι, hf _ (Module.finBasis F (fixedSub x) i).2, sub_self, neg_zero]

theorem mem_ker_movedCentMap [Module.Finite F V] {Q : QuadraticForm F V} {x : GSpin Q} {X : (gspin Q).toSubmodule}
    (hX : X ∈ LinearMap.ker (movedCentMap Q x)) :
    ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * X = X * ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∧
      ∀ v ∈ fixedSub x, (X : CliffordAlgebra Q) * ι Q v = ι Q v * X := by
  rw [LinearMap.mem_ker] at hX
  have h := fun j => congr_fun hX j
  simp only [movedCentMap, LinearMap.pi_apply, Pi.zero_apply] at h
  refine ⟨sub_eq_zero.mp (h none), ?_⟩
  let ℓ : fixedSub x →ₗ[F] CliffordAlgebra Q :=
    (LinearMap.mulLeft F (X : CliffordAlgebra Q) - LinearMap.mulRight F (X : CliffordAlgebra Q)) ∘ₗ
      ι Q ∘ₗ (fixedSub x).subtype
  have hℓ : ℓ = 0 := (Module.finBasis F (fixedSub x)).ext fun i => by
    simpa [ℓ] using h (some i)
  intro v hv
  have := LinearMap.congr_fun hℓ ⟨v, hv⟩
  simpa [ℓ, sub_eq_zero] using this

theorem gspinBC_commute_of_mem {m : ℕ} {Q : QuadraticForm F (Fin m → F)} {x : GSpin Q}
    (hA : MovedPartAbelian Q x) {u u' : AlgebraicClosure F ⊗[F] (gspin Q).toSubmodule}
    (hu : u ∈ (LinearMap.ker (movedCentMap Q x)).baseChange (AlgebraicClosure F))
    (hu' : u' ∈ (LinearMap.ker (movedCentMap Q x)).baseChange (AlgebraicClosure F)) :
    gspinBC Q u * gspinBC Q u' = gspinBC Q u' * gspinBC Q u := by
  have gen : ∀ X ∈ LinearMap.ker (movedCentMap Q x), ∀ X' ∈ LinearMap.ker (movedCentMap Q x),
      gspinBC Q (1 ⊗ₜ X) * gspinBC Q (1 ⊗ₜ X') = gspinBC Q (1 ⊗ₜ X') * gspinBC Q (1 ⊗ₜ X) := by
    intro X hX X' hX'
    obtain ⟨hc, hf⟩ := mem_ker_movedCentMap hX
    obtain ⟨hc', hf'⟩ := mem_ker_movedCentMap hX'
    have := hA X (mem_lieCentralizer.2 ⟨X.2, hc⟩) X' (mem_lieCentralizer.2 ⟨X'.2, hc'⟩)
      (fun v hv => by rw [Ring.lie_def, hf v hv, sub_self])
      (fun v hv => by rw [Ring.lie_def, hf' v hv, sub_self])
    rw [Ring.lie_def, sub_eq_zero] at this
    rw [gspinBC_tmul, gspinBC_tmul, ← map_mul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, this]
  rw [Submodule.baseChange_eq_span] at hu hu'
  induction hu using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨X, hX, rfl⟩ := hy
    induction hu' using Submodule.span_induction with
    | mem y' hy' =>
      obtain ⟨X', hX', rfl⟩ := hy'
      exact gen X hX X' hX'
    | zero => simp
    | add a b _ _ ha hb => rw [map_add, mul_add, add_mul, ha, hb]
    | smul c a _ ha => rw [map_smul, mul_smul_comm, smul_mul_assoc, ha]
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, mul_add, add_mul, ha, hb]
  | smul c a _ ha => rw [map_smul, mul_smul_comm, smul_mul_assoc, ha]

end WD

open CliffordAlgebra in
open scoped TensorProduct in
/-- **The Lie algebra of `S_x` is abelian over `F̄` if the moved part `𝔩_x` is** (own work).  Route: a skew endomorphism `Y`
of `W_{F̄}` commuting with `X = P(x)_{F̄}` and vanishing on `ker (X − 1) = W'_x ⊗ F̄` is `ad`
of an element of `so(W_{F̄}) ⊆ gspin(W_{F̄})` (`gspin = so ⊕ F`) in the centralizer of `x` and
killing `ι(W'_x ⊗ F̄)`.  These conditions are `F`-linear equations, so their solutions over `F̄`
are the `F̄`-span of the solutions over `F` (flatness, `range_gspinBC`), which commute by
hypothesis; hence so do the `Y`. -/
theorem lieAbelian_specP_baseChange_of_movedPartAbelian {d : GGPData F} (x : ↥(GSpin d.QW))
    (hx : MovedPartAbelian d.QW x) :
    IsomCent.LieAbelian (bform (d.QW.baseChange (AlgebraicClosure F)))
      ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange (AlgebraicClosure F)) := by
  intro Y₁ Y₂ hs₁ hs₂ hc₁ hc₂ hf₁ hf₂
  have hQ := isNondeg_baseChange _ d.nondeg
  let xb : GSpin (d.QW.baseChange (AlgebraicClosure F)) :=
    ⟨bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ), TorusTransfer.bcUnits_mem_GSpin d.QW x⟩
  have hX : (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange (AlgebraicClosure F) =
      (specP (d.QW.baseChange (AlgebraicClosure F)) xb : _ →ₗ[AlgebraicClosure F] _) :=
    LinearMap.ext fun w => (GGPData.specP_bcUnits d x w).symm
  have key : ∀ Y : Module.End (AlgebraicClosure F) (AlgebraicClosure F ⊗[F] (Fin d.m → F)),
      IsomCent.IsSkew (bform (d.QW.baseChange (AlgebraicClosure F))) Y →
      Commute ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange
        (AlgebraicClosure F)) Y →
      (∀ z ∈ Module.End.eigenspace ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange
        (AlgebraicClosure F)) 1, Y z = 0) →
      ∃ u ∈ (LinearMap.ker (movedCentMap d.QW x)).baseChange (AlgebraicClosure F),
        ∀ v, gspinBC d.QW u * ι _ v - ι _ v * gspinBC d.QW u = ι _ (Y v) := by
    intro Y hs hc hf
    obtain ⟨Yh, hYh0, hYh⟩ := exists_lift_skew hQ Y hs
    have hYh0' := hYh0
    rw [← LieSubalgebra.mem_toSubmodule, ← range_gspinBC d.QW hQ] at hYh0'
    obtain ⟨u, rfl⟩ := hYh0'
    refine ⟨u, mem_movedCent_baseChange d.QW x u ?_ ?_, hYh⟩
    · rw [hX] at hc
      exact commute_of_lift hQ xb hc hYh0 hYh
    · intro w hw
      have h1 : (1 : AlgebraicClosure F) ⊗ₜ[F] w ∈ Module.End.eigenspace
          ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange (AlgebraicClosure F)) 1 := by
        rw [Module.End.mem_eigenspace_iff, one_smul, LinearMap.baseChange_tmul]
        congr 1
        have := LinearMap.mem_ker.mp hw
        rw [LinearMap.sub_apply, sub_eq_zero] at this
        exact this
      have := hYh (1 ⊗ₜ w)
      rw [hf _ h1, map_zero, sub_eq_zero] at this
      exact this
  obtain ⟨u₁, hu₁, h₁⟩ := key Y₁ hs₁ hc₁ hf₁
  obtain ⟨u₂, hu₂, h₂⟩ := key Y₂ hs₂ hc₂ hf₂
  have h12 := gspinBC_commute_of_mem hx hu₁ hu₂
  refine LinearMap.ext fun v => ι_injective (d.QW.baseChange (AlgebraicClosure F)) ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, ← sub_eq_zero, ← h₁, ← h₂, ← h₂, ← h₁]
  set A := gspinBC d.QW u₁
  set B := gspinBC d.QW u₂
  have e : A * (B * ι _ v - ι _ v * B) - (B * ι _ v - ι _ v * B) * A -
      (B * (A * ι _ v - ι _ v * A) - (A * ι _ v - ι _ v * A) * B) =
      (A * B - B * A) * ι _ v - ι _ v * (A * B - B * A) := by noncomm_ring
  rw [e, h12, sub_self, zero_mul, mul_zero, sub_zero]

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

end GGPData

end GSpinGGP
