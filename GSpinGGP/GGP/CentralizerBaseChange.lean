/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TorusCommute

/-!
# Centralizers in `gspin(V)` under base change to `K̄`

For `x ∈ GSpin(V)` over a field `K` (characteristic `≠ 2`) and a subspace `U ⊆ V`, the elements
of `gspin(V)` commuting with `x` and with `ι(U)` are cut out by `K`-linear equations
(`movedCentMap`), so their solutions over `K̄` are the `K̄`-span of the solutions over `K`
(flatness; `gspin(V_{K̄})` is spanned by `gspin(V)`, `range_gspinBC`).  Consequently
(`commute_baseChange_of_lie_eq_zero`): if those elements commute over `K`, then the `b`-skew
endomorphisms of `V_{K̄}` commuting with `P(x)_{K̄}` and vanishing on `U` commute (they are `ad` of
such elements, `exists_movedCent_lift`).  For `U = W'_x = ker (P(x) − 1)` this is the moved part
(`lieAbelian_specP_baseChange_of_lie_eq_zero`); for `U = 0`, the whole Lie centralizer.
Also `isSemisimple_specP_baseChange`: `P(x)_{K̄}` is semisimple for `x` semisimple on `C(V)`.
-/

noncomputable section

open Module
open CliffordAlgebra (ι_injective)

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

variable {K : Type*} [Field K] [Invertible (2 : K)]

section WD

open CliffordAlgebra
open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module K V]

theorem ofBaseChange_tmul_eq (Q : QuadraticForm K V) (z : AlgebraicClosure K)
    (X : CliffordAlgebra Q) :
    ofBaseChange (AlgebraicClosure K) Q (z ⊗ₜ X) = algebraMap _ _ z * bcHom Q X := by
  rw [show z ⊗ₜ[K] X = (z ⊗ₜ[K] (1 : CliffordAlgebra Q)) * (1 ⊗ₜ X) by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul], map_mul, ofBaseChange_tmul_one]
  rfl

theorem bcHom_mem_even (Q : QuadraticForm K V) {X : CliffordAlgebra Q} (hX : X ∈ even Q) :
    bcHom Q X ∈ even (Q.baseChange (AlgebraicClosure K)) := by
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hX ⊢
  induction X, hX using even_induction with
  | algebraMap r =>
    have : bcHom Q (algebraMap K _ r) = algebraMap (AlgebraicClosure K) _
        (algebraMap K (AlgebraicClosure K) r) := by
      show ofBaseChange (AlgebraicClosure K) Q (1 ⊗ₜ algebraMap K _ r) = _
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, ofBaseChange_tmul_one,
        Algebra.smul_def, mul_one]
    rw [this]
    exact SetLike.algebraMap_mem_graded _ _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul, bcHom_ι, bcHom_ι]
    exact zero_add (0 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero _ _ _) ih

theorem ofBaseChange_mem_gspin (Q : QuadraticForm K V) (z : AlgebraicClosure K)
    {X : CliffordAlgebra Q} (hX : X ∈ gspin Q) :
    ofBaseChange (AlgebraicClosure K) Q (z ⊗ₜ X) ∈ gspin (Q.baseChange (AlgebraicClosure K)) := by
  rw [ofBaseChange_tmul_eq, ← Algebra.smul_def]
  refine (gspin _).smul_mem z ⟨bcHom_mem_even Q hX.1, fun w => ?_⟩
  induction w using TensorProduct.inductionOn with
  | tmul c v =>
    obtain ⟨u, hu⟩ := hX.2 v
    refine ⟨c ⊗ₜ u, ?_⟩
    have hc : ι (Q.baseChange (AlgebraicClosure K)) (c ⊗ₜ v) = c • ι _ (1 ⊗ₜ v) := by
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have hc' : ι (Q.baseChange (AlgebraicClosure K)) (c ⊗ₜ u) = c • ι _ (1 ⊗ₜ u) := by
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hc, hc', ← bcHom_ι, ← bcHom_ι, hu, Ring.lie_def, Ring.lie_def, mul_smul_comm,
      smul_mul_assoc, ← smul_sub, map_sub, map_mul, map_mul]
  | add a b ha hb =>
    rw [map_add, lie_add]
    exact Submodule.add_mem _ ha hb


/-- `K̄ ⊗ gspin(Q) → C(Q_{K̄})`. -/
def gspinBC (Q : QuadraticForm K V) :
    AlgebraicClosure K ⊗[K] (gspin Q).toSubmodule →ₗ[AlgebraicClosure K]
      CliffordAlgebra (Q.baseChange (AlgebraicClosure K)) :=
  (ofBaseChange (AlgebraicClosure K) Q).toLinearMap ∘ₗ
    (gspin Q).toSubmodule.subtype.baseChange (AlgebraicClosure K)

theorem gspinBC_tmul (Q : QuadraticForm K V) (z : AlgebraicClosure K) (X : (gspin Q).toSubmodule) :
    gspinBC Q (z ⊗ₜ X) = ofBaseChange (AlgebraicClosure K) Q (z ⊗ₜ (X : CliffordAlgebra Q)) := rfl

theorem ofBaseChange_injective (Q : QuadraticForm K V) :
    Function.Injective (ofBaseChange (AlgebraicClosure K) Q) :=
  Function.LeftInverse.injective (toBaseChange_ofBaseChange (AlgebraicClosure K) Q)

omit [Invertible (2 : K)] in
theorem baseChange_subtype_injective {M : Type*} [AddCommGroup M] [Module K M] (p : Submodule K M) :
    Function.Injective (p.subtype.baseChange (AlgebraicClosure K)) := by
  rw [LinearMap.baseChange_eq_lTensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ p.injective_subtype

/-- Over `K̄`, `gspin(Q_{K̄})` is spanned by `gspin(Q)` (via `gspin = span{v w} ⊕ K`,
`gspin_eq_span`, for `Q_{K̄}` nondegenerate). -/
theorem range_gspinBC [Module.Finite K V] (Q : QuadraticForm K V)
    (hQ : IsNondeg (Q.baseChange (AlgebraicClosure K))) :
    LinearMap.range (gspinBC Q) = (gspin (Q.baseChange (AlgebraicClosure K))).toSubmodule := by
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

/-- The `K`-linear conditions cutting out the elements of `gspin(V)_x` commuting with `ι(U)`:
commutator with `x` and with `ι(bᵢ)` for a basis `bᵢ` of `U` (the moved centralizer for
`U = W'_x`, the whole centralizer for `U = 0`). -/
def movedCentMap [Module.Finite K V] (Q : QuadraticForm K V) (x : GSpin Q)
    (U : Submodule K V) :
    (gspin Q).toSubmodule →ₗ[K] (Option (Fin (finrank K U)) → CliffordAlgebra Q) :=
  LinearMap.pi fun j => Option.elim j
    ((LinearMap.mulLeft K ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) -
      LinearMap.mulRight K ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) ∘ₗ
        (gspin Q).toSubmodule.subtype)
    (fun i => (LinearMap.mulRight K (ι Q (Module.finBasis K U i : V)) -
      LinearMap.mulLeft K (ι Q (Module.finBasis K U i : V))) ∘ₗ
        (gspin Q).toSubmodule.subtype)

omit [Invertible (2 : K)] in
theorem piRight_pi_baseChange {M : Type*} [AddCommGroup M] [Module K M] {n : Type*} [Fintype n]
    [DecidableEq n] {N : Type*} [AddCommGroup N] [Module K N] (f : n → M →ₗ[K] N)
    (u : AlgebraicClosure K ⊗[K] M) (j : n) :
    TensorProduct.piRight K (AlgebraicClosure K) (AlgebraicClosure K) (fun _ : n => N)
      ((LinearMap.pi f).baseChange (AlgebraicClosure K) u) j =
        (f j).baseChange (AlgebraicClosure K) u := by
  induction u using TensorProduct.inductionOn with
  | tmul z m => simp
  | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]

theorem ofBaseChange_commBC (Q : QuadraticForm K V) (c : CliffordAlgebra Q)
    (u : AlgebraicClosure K ⊗[K] (gspin Q).toSubmodule) :
    ofBaseChange (AlgebraicClosure K) Q
      (((LinearMap.mulLeft K c - LinearMap.mulRight K c) ∘ₗ (gspin Q).toSubmodule.subtype).baseChange
        (AlgebraicClosure K) u) = bcHom Q c * gspinBC Q u - gspinBC Q u * bcHom Q c := by
  induction u using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [LinearMap.baseChange_tmul, LinearMap.comp_apply,
      LinearMap.sub_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply,
      Submodule.coe_subtype, gspinBC_tmul, ofBaseChange_tmul_eq, map_sub, map_mul]
    rw [← mul_assoc (bcHom Q c), ← Algebra.commutes z (bcHom Q c), mul_sub]
    simp only [mul_assoc]
  | add a b ha hb => simp only [map_add, ha, hb]; noncomm_ring

theorem mem_movedCent_baseChange [Module.Finite K V] (Q : QuadraticForm K V) (x : GSpin Q)
    (U : Submodule K V)
    (u : AlgebraicClosure K ⊗[K] (gspin Q).toSubmodule)
    (hc : bcHom Q ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * gspinBC Q u =
      gspinBC Q u * bcHom Q ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
    (hf : ∀ w ∈ U, gspinBC Q u * ι _ (1 ⊗ₜ w) = ι _ (1 ⊗ₜ w) * gspinBC Q u) :
    u ∈ (LinearMap.ker (movedCentMap Q x U)).baseChange (AlgebraicClosure K) := by
  rw [← LinearMap.ker_baseChange_of_flat, LinearMap.mem_ker]
  apply (TensorProduct.piRight K (AlgebraicClosure K) (AlgebraicClosure K) _).injective
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
      ofBaseChange_commBC, bcHom_ι, hf _ (Module.finBasis K U i).2, sub_self, neg_zero]

omit [Invertible (2 : K)] in
theorem mem_ker_movedCentMap [Module.Finite K V] {Q : QuadraticForm K V} {x : GSpin Q}
    {U : Submodule K V}
    {X : (gspin Q).toSubmodule}
    (hX : X ∈ LinearMap.ker (movedCentMap Q x U)) :
    ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * X = X * ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∧
      ∀ v ∈ U, (X : CliffordAlgebra Q) * ι Q v = ι Q v * X := by
  rw [LinearMap.mem_ker] at hX
  have h := fun j => congr_fun hX j
  simp only [movedCentMap, LinearMap.pi_apply, Pi.zero_apply] at h
  refine ⟨sub_eq_zero.mp (h none), ?_⟩
  let ℓ : U →ₗ[K] CliffordAlgebra Q :=
    (LinearMap.mulLeft K (X : CliffordAlgebra Q) - LinearMap.mulRight K (X : CliffordAlgebra Q)) ∘ₗ
      ι Q ∘ₗ U.subtype
  have hℓ : ℓ = 0 := (Module.finBasis K U).ext fun i => by
    simpa [ℓ] using h (some i)
  intro v hv
  have := LinearMap.congr_fun hℓ ⟨v, hv⟩
  simpa [ℓ, sub_eq_zero] using this

/-- Elements of the base change of `ker (movedCentMap Q x U)` commute, if the elements of
`gspin(V)_x` commuting with `ι(U)` do. -/
theorem gspinBC_commute_of_mem [Module.Finite K V] {Q : QuadraticForm K V} {x : GSpin Q}
    {U : Submodule K V}
    (hA : ∀ X ∈ lieCentralizer (gspin Q) ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q),
      ∀ Y ∈ lieCentralizer (gspin Q) ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q),
      (∀ v ∈ U, ⁅X, ι Q v⁆ = 0) → (∀ v ∈ U, ⁅Y, ι Q v⁆ = 0) → ⁅X, Y⁆ = 0)
    {u u' : AlgebraicClosure K ⊗[K] (gspin Q).toSubmodule}
    (hu : u ∈ (LinearMap.ker (movedCentMap Q x U)).baseChange (AlgebraicClosure K))
    (hu' : u' ∈ (LinearMap.ker (movedCentMap Q x U)).baseChange (AlgebraicClosure K)) :
    gspinBC Q u * gspinBC Q u' = gspinBC Q u' * gspinBC Q u := by
  have gen : ∀ X ∈ LinearMap.ker (movedCentMap Q x U), ∀ X' ∈ LinearMap.ker (movedCentMap Q x U),
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

section Lift

open CliffordAlgebra
open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

set_option hygiene false in
local notation "Kb" => AlgebraicClosure K

omit [FiniteDimensional K V] in
/-- `1 ⊗ w ∈ ker (P(x)_{K̄} − 1)` for `w ∈ W'_x`. -/
theorem tmul_mem_eigenspace_baseChange_one {Q : QuadraticForm K V} (x : GSpin Q) {w : V}
    (hw : w ∈ fixedSub x) :
    (1 : Kb) ⊗ₜ[K] w ∈ Module.End.eigenspace ((specP Q x : V →ₗ[K] V).baseChange Kb) 1 := by
  rw [Module.End.mem_eigenspace_iff, one_smul, LinearMap.baseChange_tmul]
  congr 1
  have := LinearMap.mem_ker.mp hw
  rw [LinearMap.sub_apply, sub_eq_zero] at this
  exact this

/-- **The `K̄`-span of the rational centralizer**: a skew endomorphism `Y` of `V_{K̄}` commuting
with `P(x)_{K̄}` and vanishing on `U` is `ad u` for some `u` in the base change of
`ker (movedCentMap Q x U)` (`exists_lift_skew`, `range_gspinBC`, `mem_movedCent_baseChange`):
`[u, ι v] = ι (Y v)`. -/
theorem exists_movedCent_lift {Q : QuadraticForm K V} (hQ : IsNondeg Q) (x : GSpin Q)
    (U : Submodule K V) (Y : Module.End Kb (Kb ⊗[K] V))
    (hs : (bform (Q.baseChange Kb)).IsSkewAdjoint Y)
    (hc : Commute ((specP Q x : V →ₗ[K] V).baseChange Kb) Y)
    (hf : ∀ w ∈ U, Y ((1 : Kb) ⊗ₜ[K] w) = 0) :
    ∃ u ∈ (LinearMap.ker (movedCentMap Q x U)).baseChange Kb,
      ∀ v, gspinBC Q u * ι (Q.baseChange Kb) v - ι (Q.baseChange Kb) v * gspinBC Q u =
        ι (Q.baseChange Kb) (Y v) := by
  have hQL := isNondeg_baseChange Q hQ
  obtain ⟨Yh, hYh0, hYh⟩ := exists_lift_skew hQL Y hs.eq
  have hYh0' := hYh0
  rw [← LieSubalgebra.mem_toSubmodule, ← range_gspinBC Q hQL] at hYh0'
  obtain ⟨u, rfl⟩ := hYh0'
  refine ⟨u, mem_movedCent_baseChange Q x U u ?_ ?_, hYh⟩
  · rw [← specP_bcGSpin] at hc
    exact commute_of_lift hQL (bcGSpin Q x) hc hYh0 hYh
  · intro w hw
    have := hYh (1 ⊗ₜ w)
    rw [hf w hw, map_zero, sub_eq_zero] at this
    exact this

/-- **Commutativity survives base change to `K̄`** (own work): if the elements of `gspin(V)_x`
commuting with `ι(U)` commute, then so do the `b`-skew endomorphisms of `V_{K̄}` commuting with
`P(x)_{K̄}` and vanishing on `U`.  They are `ad` of elements of the `K̄`-span of the former
(`exists_movedCent_lift`, `gspinBC_commute_of_mem`).  For `U = 0` this is the base change of the
abelianness of `so(V)_{P(x)}` (`soCent`), which `commute_soCentMat_map` (`GGP/RegularRank.lean`)
does at the matrix level; the route through `gspin` here also covers the moved part (`U = W'_x`). -/
theorem commute_baseChange_of_lie_eq_zero {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (x : GSpin Q) (U : Submodule K V)
    (hA : ∀ X ∈ lieCentralizer (gspin Q) ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q),
      ∀ Y ∈ lieCentralizer (gspin Q) ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q),
      (∀ v ∈ U, ⁅X, ι Q v⁆ = 0) → (∀ v ∈ U, ⁅Y, ι Q v⁆ = 0) → ⁅X, Y⁆ = 0)
    {Y₁ Y₂ : Module.End Kb (Kb ⊗[K] V)}
    (hs₁ : (bform (Q.baseChange Kb)).IsSkewAdjoint Y₁)
    (hs₂ : (bform (Q.baseChange Kb)).IsSkewAdjoint Y₂)
    (hc₁ : Commute ((specP Q x : V →ₗ[K] V).baseChange Kb) Y₁)
    (hc₂ : Commute ((specP Q x : V →ₗ[K] V).baseChange Kb) Y₂)
    (hf₁ : ∀ w ∈ U, Y₁ ((1 : Kb) ⊗ₜ[K] w) = 0) (hf₂ : ∀ w ∈ U, Y₂ ((1 : Kb) ⊗ₜ[K] w) = 0) :
    Commute Y₁ Y₂ := by
  obtain ⟨u₁, hu₁, h₁⟩ := exists_movedCent_lift hQ x U Y₁ hs₁ hc₁ hf₁
  obtain ⟨u₂, hu₂, h₂⟩ := exists_movedCent_lift hQ x U Y₂ hs₂ hc₂ hf₂
  have h12 := gspinBC_commute_of_mem hA hu₁ hu₂
  refine LinearMap.ext fun v => ι_injective (Q.baseChange Kb) ?_
  rw [mul_apply_eq_comp, mul_apply_eq_comp, ← sub_eq_zero, ← h₁, ← h₂, ← h₂, ← h₁]
  set A := gspinBC Q u₁
  set B := gspinBC Q u₂
  have e : A * (B * ι _ v - ι _ v * B) - (B * ι _ v - ι _ v * B) * A -
      (B * (A * ι _ v - ι _ v * A) - (A * ι _ v - ι _ v * A) * B) =
      (A * B - B * A) * ι _ v - ι _ v * (A * B - B * A) := by noncomm_ring
  rw [e, h12, sub_self, zero_mul, mul_zero, sub_zero]

/-- **The moved part of the Lie centralizer of `P(x)` over `K̄` is abelian** if the moved part
`{X ∈ gspin(V)_x : [X, ι(W'_x)] = 0}` is (`commute_baseChange_of_lie_eq_zero` with
`U = W'_x`, whose base change is `ker (P(x)_{K̄} − 1)`). -/
theorem lieAbelian_specP_baseChange_of_lie_eq_zero {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (x : GSpin Q)
    (hA : ∀ X ∈ lieCentralizer (gspin Q) ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q),
      ∀ Y ∈ lieCentralizer (gspin Q) ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q),
      (∀ v ∈ fixedSub x, ⁅X, ι Q v⁆ = 0) → (∀ v ∈ fixedSub x, ⁅Y, ι Q v⁆ = 0) → ⁅X, Y⁆ = 0) :
    IsomCent.LieAbelian (bform (Q.baseChange Kb)) ((specP Q x : V →ₗ[K] V).baseChange Kb) :=
  fun _ _ hs₁ hs₂ hc₁ hc₂ hf₁ hf₂ => commute_baseChange_of_lie_eq_zero hQ x (fixedSub x) hA
    hs₁ hs₂ hc₁ hc₂ (fun _ hw => hf₁ _ (tmul_mem_eigenspace_baseChange_one x hw))
    (fun _ hw => hf₂ _ (tmul_mem_eigenspace_baseChange_one x hw))

/-- **`P(x)_{K̄}` is semisimple** for `x` semisimple on `C(V)` (own work, elementary).  Route: left
and right multiplication by `x` are commuting semisimple operators on `C(V)`, so conjugation
`v ↦ x v x⁻¹` is semisimple and so is its restriction to `ι(V)`, which is `P(x)`
(`isSemisimple_specP_of_isSS`); over a perfect field semisimplicity survives base change to `K̄`
(`IsomCent.isSemisimple_baseChange_algebraicClosure`). -/
theorem isSemisimple_specP_baseChange [PerfectField K] {Q : QuadraticForm K V} (x : GSpin Q)
    (hx : Module.End.IsSemisimple
      (LinearMap.mulLeft K ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))) :
    Module.End.IsSemisimple ((specP Q x : V →ₗ[K] V).baseChange Kb) :=
  IsomCent.isSemisimple_baseChange_algebraicClosure (isSemisimple_specP_of_isSS Q x hx)

end Lift

end GSpinGGP
