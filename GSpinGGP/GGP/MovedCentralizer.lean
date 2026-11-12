/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TorusCommute
import GSpinGGP.Foundations.ExpLocal
import GSpinGGP.GGP.GSpinSemisimple

/-!
# The moved part of the centralizer of `x ∈ GSpin(W)(F)`

For `x ∈ GSpin(W)(F)`, the *moved part* of the Lie centralizer is
`𝔩_x = {X ∈ gspin(W) : [X, x] = 0, [X, ι(W'_x)] = 0}` (`so(W''_x)_{x̄} ⊕ F`).

* `MovedPart.exists_nhds_expA_mem_GSpin`: `e^X ∈ GSpin(W)(F)` for small `X ∈ gspin(W)`, and
  conversely `eventually_mem_gspin_of_expA_mem`;
* `exists_gspin_commute_iff`: an element of `GSpin` with the commutant of a given `Z ∈ gspin`;
  `mem_torusOf_of_commute`: commuting with `x` and `ι(W'_x)` puts `g` in `T_x`;
* `movedPartAbelian_of_isGammaElt`: `𝔩_x` is abelian for `x ∈ Γ(G,H)`;
* `gspinBC`, `movedCentMap`, `gspinBC_commute_of_mem`: `𝔩_x ⊗ F̄` and its commutativity;
* `GGPData.exists_movedCent_lift`, `GGPData.eq_zero_of_forall_movedCent`: a skew endomorphism of
  `W_{F̄}` commuting with `P(x)` and vanishing on `W'_x ⊗ F̄` is `ad` of an element of `𝔩_x ⊗ F̄`,
  so the `(ad Z)_{F̄}`, `Z ∈ 𝔩_x`, span all of them; `GGPData.exists_movedCent_forall_ne_zero`:
  some `Z ∈ 𝔩_x` avoids finitely many such hyperplanes (`F` infinite);
* `lieAbelian_specP_baseChange_of_movedPartAbelian`: if `𝔩_x` is abelian, so is the Lie algebra
  of `S_x` over `F̄` (`IsomCent.LieAbelian`);
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

/-! ### The moved part on `Γ(G,H)` (helpers for `movedPartAbelian_of_isGammaElt`)

The exponential of a small element of `gspin(W)` lies in `GSpin(W)(F)`
(`MovedPart.exists_nhds_expA_mem_GSpin`): conjugation by `e^X` is `e^{ad X}` (`expA_ad_eq`), which
preserves the `ad X`-stable subspace `ι(W)`. -/

namespace MovedPart

variable {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A]
  [IsModuleTopology F A]

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

section Clifford

open CliffordAlgebra

variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] (Q : QuadraticForm F V)

/-- **The logarithm of `GSpin(Q)` near `1` lies in `gspin(Q)`** (converse of
`MovedPart.exists_nhds_expA_mem_GSpin`): for `Y` near `0` in `C(Q)`, if
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
  filter_upwards [hU₁, hU₂, h3, expA_ad_eq F (B := CliffordAlgebra Q)] with Y hY₁ hY₂ hY₃ hY₄
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

/-- **A group element with the commutant of `Z`**: for `Z ∈ gspin(Q)` there is `g ∈ GSpin(Q)(F)`
(namely `e^{cZ}` for small `c ≠ 0`, `MovedPart.exists_nhds_expA_mem_GSpin`) commuting with exactly
the elements of `C(Q)` that commute with `Z` (`commute_expA_of_commute`,
`exists_nhds_commute_of_commute_expA`). -/
theorem exists_gspin_commute_iff {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (Q : QuadraticForm F V) {Z : CliffordAlgebra Q} (hZ : Z ∈ gspin Q) :
    ∃ g : GSpin Q, ∀ W : CliffordAlgebra Q,
      Commute W ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ↔ Commute W Z := by
  obtain ⟨U, hU, hG⟩ := MovedPart.exists_nhds_expA_mem_GSpin (F := F) Q
  obtain ⟨U', hU', hc⟩ := exists_nhds_commute_of_commute_expA F (A := CliffordAlgebra Q)
  have hlim : Tendsto (fun c : F => c • Z) (𝓝[≠] 0) (𝓝 0) := by
    have : Continuous (fun c : F => c • Z) := continuous_id.smul continuous_const
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨c, hcU, hc0⟩ := ((hlim.eventually (inter_mem hU hU')).and self_mem_nhdsWithin).exists
  obtain ⟨g, hg⟩ := hG _ hcU.1 ((gspin Q).smul_mem c hZ)
  refine ⟨g, fun W => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [hg] at h
    have h2 := (hc _ hcU.2 _ h).eq
    rw [mul_smul_comm, smul_mul_assoc] at h2
    exact smul_right_injective _ hc0 h2
  · rw [hg]
    exact commute_expA_of_commute (h.smul_right c)

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

/-- For `x ∈ Γ(G,H)` the moved part `G''_x` is a torus: `T_x(F) = Z(x) ∩ Fix(W'_x)`
is commutative, hence so is its Lie algebra
`so(W''_x)_{x̄} ⊕ F`.  Own work; this is the hypothesis under which
`nilReg_centralizer_nonempty_iff` applies.

Proof (exponential, no Zariski density): `X` and `Y` in the moved part have the commutants of some
`g, h ∈ GSpin(W)(F)` (`exists_gspin_commute_iff`: `e^{cX}`, `e^{cY}` for small `c ≠ 0`), which
commute with `x` and fix `W'_x` pointwise, so lie in `T_x(F)` (`mem_torusOf_of_commute`) and
commute; hence `X` and `Y` commute.  Only the commutativity of
`T_x(F)` is used, not the semisimplicity of `x` or the compactness of `T_x(F)/A(F)`. -/
theorem movedPartAbelian_of_isGammaElt (d : GGPData F) (x : ↥(GSpin d.QW))
    (hx : d.IsGammaElt x) : MovedPartAbelian d.QW x := by
  intro X hX Y hY hXf hYf
  rw [mem_lieCentralizer] at hX hY
  -- `Z` in the moved part has the commutant of some `g ∈ T_x`
  have key : ∀ Z ∈ gspin d.QW,
      Commute ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) Z →
      (∀ v ∈ fixedSub x, ⁅Z, CliffordAlgebra.ι d.QW v⁆ = 0) →
      ∃ g ∈ d.torusOf x, ∀ W : CliffordAlgebra d.QW,
        Commute W ((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) ↔ Commute W Z := by
    intro Z hZ hZx hZf
    obtain ⟨g, hg⟩ := exists_gspin_commute_iff d.QW hZ
    refine ⟨g, mem_torusOf_of_commute d ((hg _).mpr hZx) fun w hw => (hg _).mpr ?_, hg⟩
    have hw0 := hZf w hw
    rw [Ring.lie_def, sub_eq_zero] at hw0
    exact hw0.symm
  obtain ⟨g, hgT, hg⟩ := key X hX.1 hX.2 hXf
  obtain ⟨h, hhT, hh⟩ := key Y hY.1 hY.2 hYf
  have h1 : Commute ((g : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)
      ((h : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) :=
    congrArg (fun k : ↥(GSpin d.QW) => ((k : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
      (hx.2.1 g hgT h hhT).eq
  have h3 : Commute Y X := (hg _).mp ((hh _).mp h1).symm
  rw [Ring.lie_def, sub_eq_zero]
  exact h3.eq.symm

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


/-- **The `F̄`-span of the rational moved centralizer**: a skew endomorphism `Y` of `W_{F̄}`
commuting with `P(x)_{F̄}` and vanishing on `W'_x ⊗ F̄` is `ad u` for some `u` in the base change
of the moved part `𝔩_x = ker movedCentMap` (`exists_lift_skew`, `range_gspinBC`,
`mem_movedCent_baseChange`): `[u, ι v] = ι (Y v)`. -/
theorem exists_movedCent_lift (x : ↥(GSpin d.QW)) (Y : Module.End Kb Wb)
    (hs : (bform Qb).IsSkewAdjoint Y)
    (hc : Commute ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb) Y)
    (hf : ∀ z ∈ Module.End.eigenspace
      ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb) 1, Y z = 0) :
    ∃ u ∈ (LinearMap.ker (movedCentMap d.QW x)).baseChange Kb,
      ∀ v, gspinBC d.QW u * ι Qb v - ι Qb v * gspinBC d.QW u = ι Qb (Y v) := by
  have hQ := isNondeg_baseChange _ d.nondeg
  let xb : GSpin Qb :=
    ⟨bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ), TorusTransfer.bcUnits_mem_GSpin d.QW x⟩
  have hX : (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb =
      (specP Qb xb : _ →ₗ[Kb] _) :=
    LinearMap.ext fun w => (GGPData.specP_bcUnits d x w).symm
  obtain ⟨Yh, hYh0, hYh⟩ := exists_lift_skew hQ Y hs.eq
  have hYh0' := hYh0
  rw [← LieSubalgebra.mem_toSubmodule, ← range_gspinBC d.QW hQ] at hYh0'
  obtain ⟨u, rfl⟩ := hYh0'
  refine ⟨u, mem_movedCent_baseChange d.QW x u ?_ ?_, hYh⟩
  · rw [hX] at hc
    exact commute_of_lift hQ xb hc hYh0 hYh
  · intro w hw
    have h1 : (1 : Kb) ⊗ₜ[F] w ∈ Module.End.eigenspace
        ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb) 1 := by
      rw [Module.End.mem_eigenspace_iff, one_smul, LinearMap.baseChange_tmul]
      congr 1
      have := LinearMap.mem_ker.mp hw
      rw [LinearMap.sub_apply, sub_eq_zero] at this
      exact this
    have := hYh (1 ⊗ₜ w)
    rw [hf _ h1, map_zero, sub_eq_zero] at this
    exact this

end MovedCentLift

end GGPData

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
  obtain ⟨u₁, hu₁, h₁⟩ := d.exists_movedCent_lift x Y₁ hs₁ hc₁ hf₁
  obtain ⟨u₂, hu₂, h₂⟩ := d.exists_movedCent_lift x Y₂ hs₂ hc₂ hf₂
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
    {Z : (gspin d.QW).toSubmodule} (hZ : Z ∈ LinearMap.ker (movedCentMap d.QW x)) :
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
    (hγ : ∀ Z ∈ LinearMap.ker (movedCentMap d.QW x),
      γ ((adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb) = 0)
    (Y : Module.End Kb Wb) (hs : (bform Qb).IsSkewAdjoint Y)
    (hc : Commute ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb) Y)
    (hf : ∀ z ∈ Module.End.eigenspace
      ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb) 1, Y z = 0) :
    γ Y = 0 := by
  obtain ⟨u, hu, hY⟩ := d.exists_movedCent_lift x Y hs hc hf
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
    ↥(LinearMap.ker (movedCentMap d.QW x)) →ₗ[F] Module.End Kb Wb where
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
    ∃ Z ∈ LinearMap.ker (movedCentMap d.QW x),
      ∀ k, γ k ((adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb) ≠ 0 := by
  let p : ι → Submodule F ↥(LinearMap.ker (movedCentMap d.QW x)) := fun k =>
    { carrier := {Z | γ k (d.movedCentAd x Z) = 0}
      add_mem' := fun {Z Z'} hZ hZ' => by
        simp only [Set.mem_setOf_eq, map_add] at hZ hZ' ⊢; rw [hZ, hZ', add_zero]
      zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]
      smul_mem' := fun c Z hZ => by
        simp only [Set.mem_setOf_eq, map_smul] at hZ ⊢
        rw [LinearMap.map_smul_of_tower, hZ, smul_zero] }
  have hne : ∀ k, p k ≠ ⊤ := by
    intro k htop
    obtain ⟨Y, hs, hc, hf, hY⟩ := hγ k
    refine hY (d.eq_zero_of_forall_movedCent x (γ k) (fun Z hZ => ?_) Y hs hc hf)
    have : (⟨Z, hZ⟩ : ↥(LinearMap.ker (movedCentMap d.QW x))) ∈ p k := htop ▸ Submodule.mem_top
    exact this
  haveI : Infinite F := Infinite.of_injective (Nat.cast : ℕ → F) Nat.cast_injective
  obtain ⟨Z, hZ⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hne
  exact ⟨Z, Z.2, fun k h => hZ k h⟩

end MovedCentSpan

end GGPData

section TorusNat

open CliffordAlgebra Module
open scoped TensorProduct

/-- **`P(x)_{F̄}` is semisimple** for semisimple `x ∈ GSpin(W)(F)` (own work, elementary).  Route:
left and right multiplication by `x` are commuting semisimple operators on `C(W)`, so conjugation
`v ↦ x v x⁻¹` is semisimple and so is its restriction to `ι(W)`, which is `P(x)`; semisimplicity
over `F` of characteristic `0` survives base change to `F̄` (squarefree minimal polynomial).
Proved: `isSemisimple_specP_of_isSS` (`GGP/Steinberg.lean`), `isSemisimple_baseChange`
(`GGP/TorusCommute.lean`). -/
theorem isSemisimple_specP_baseChange {d : GGPData F} (x : ↥(GSpin d.QW))
    (hx : IsSS F (((x : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW)) :
    Module.End.IsSemisimple
      ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange (AlgebraicClosure F)) :=
  isSemisimple_baseChange (isSemisimple_specP_of_isSS d.QW x hx)

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
