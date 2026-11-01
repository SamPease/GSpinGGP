/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.Triple
import GSpinGGP.Literature.Kottwitz

/-!
# Galois descent for the Clifford algebra and the torus transfer

Own work (standard Galois descent), towards Thesis Prop. 6.6.1(ii)
(`Main.exists_torusTransfer_core`).

* `exists_tmul_of_fixed`: an element of `F̄ ⊗ M` fixed by every `σ ⊗ 1` is `1 ⊗ m`
  (coordinates in a basis of `M` are Galois-fixed, hence in `F`).
* `exists_bcHom_of_fixed`: an element of `C(Q_{F̄}) ≅ F̄ ⊗ C(Q)` fixed by the Galois action `galC`
  is rational.
-/

noncomputable section
open scoped TensorProduct
set_option linter.unusedSectionVars false

namespace GSpinGGP
namespace TorusTransfer

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]


section Descent

variable (M : Type*) [AddCommGroup M] [Module F M]

/-- The Galois action `σ ⊗ 1` on `F̄ ⊗ M`. -/
def galT (σ : GalF F) : (AlgebraicClosure F) ⊗[F] M →ₗ[F] (AlgebraicClosure F) ⊗[F] M :=
  LinearMap.rTensor M (σ : (AlgebraicClosure F) →ₐ[F] (AlgebraicClosure F)).toLinearMap

theorem galT_tmul (σ : GalF F) (z : (AlgebraicClosure F)) (m : M) : galT M σ (z ⊗ₜ m) = σ z ⊗ₜ m := rfl

/-- Coordinates of `σ w` in a rational basis are `σ` of those of `w`. -/
theorem repr_galT {ι : Type*} (b : Module.Basis ι F M) (σ : GalF F) (w : (AlgebraicClosure F) ⊗[F] M) (i : ι) :
    (b.baseChange (AlgebraicClosure F)).repr (galT M σ w) i = σ ((b.baseChange (AlgebraicClosure F)).repr w i) := by
  induction w using TensorProduct.inductionOn with
  | tmul z m =>
    rw [galT_tmul, Module.Basis.baseChange_repr_tmul, Module.Basis.baseChange_repr_tmul,
      Algebra.smul_def, Algebra.smul_def, map_mul, AlgEquiv.commutes]
  | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb]

/-- **Galois descent for `F̄ ⊗ M`**: an element fixed by every `σ ⊗ 1` is `1 ⊗ m` for a
rational `m` (the fixed field of `Aut(F̄/F)` is `F`, `F` having characteristic `0`). -/
theorem exists_tmul_of_fixed (w : (AlgebraicClosure F) ⊗[F] M) (h : ∀ σ : GalF F, galT M σ w = w) :
    ∃ m : M, (1 : (AlgebraicClosure F)) ⊗ₜ[F] m = w := by
  classical
  let b := Module.Basis.ofVectorSpace F M
  have hc : ∀ i, ∃ c : F, algebraMap F (AlgebraicClosure F) c = (b.baseChange (AlgebraicClosure F)).repr w i := fun i =>
    (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 fun σ => by
      rw [← repr_galT, h σ]
  choose c hc using hc
  refine ⟨∑ i ∈ ((b.baseChange (AlgebraicClosure F)).repr w).support, c i • b i, ?_⟩
  apply (b.baseChange (AlgebraicClosure F)).repr.injective
  ext i
  rw [Module.Basis.baseChange_repr_tmul, map_sum]
  simp only [map_smul, Module.Basis.repr_self, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finsupp.mem_support_iff]
  split_ifs with hi
  · rw [Algebra.smul_def, mul_one, hc]
  · rw [not_not] at hi
    have := hc i
    rw [hi] at this ⊢
    rw [zero_smul]

end Descent

section Clifford

variable {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)

/-- **Galois descent for the Clifford algebra**: an element of `C(Q_{F̄})` fixed by the Galois
action is the base change of an element of `C(Q)`. -/
theorem exists_bcHom_of_fixed (a : CliffordAlgebra (Q.baseChange (AlgebraicClosure F)))
    (h : ∀ σ : GalF F, galC Q σ a = a) : ∃ b : CliffordAlgebra Q, bcHom Q b = a := by
  set u := CliffordAlgebra.toBaseChange (AlgebraicClosure F) Q a
  have hu : ∀ σ : GalF F, galT (CliffordAlgebra Q) σ u = u := fun σ => by
    have := congrArg (CliffordAlgebra.toBaseChange (AlgebraicClosure F) Q) (h σ)
    simp only [galC, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, CliffordAlgebra.toBaseChange_ofBaseChange] at this
    exact this
  obtain ⟨b, hb⟩ := exists_tmul_of_fixed _ u hu
  refine ⟨b, ?_⟩
  have : bcHom Q b = CliffordAlgebra.ofBaseChange (AlgebraicClosure F) Q ((1 : (AlgebraicClosure F)) ⊗ₜ b) := rfl
  rw [this, hb, CliffordAlgebra.ofBaseChange_toBaseChange]

end Clifford


section CliffordBC

open CliffordAlgebra

variable {V : Type*} [AddCommGroup V] [Module F V] (Q : QuadraticForm F V)

theorem bcHom_mem_evenOdd_zero {X : CliffordAlgebra Q} (hX : X ∈ evenOdd Q 0) :
    bcHom Q X ∈ evenOdd (Q.baseChange (AlgebraicClosure F)) 0 := by
  induction X, hX using even_induction with
  | algebraMap r => rw [bcHom_algebraMap]; exact SetLike.algebraMap_mem_graded _ _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul, bcHom_ι, bcHom_ι]
    exact zero_add (0 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero _ _ _) ih

theorem bcHom_mem_evenOdd_one {X : CliffordAlgebra Q} (hX : X ∈ evenOdd Q 1) :
    bcHom Q X ∈ evenOdd (Q.baseChange (AlgebraicClosure F)) 1 := by
  induction X, hX using odd_induction with
  | ι v => rw [bcHom_ι]; exact ι_mem_evenOdd_one _ _
  | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    rw [map_mul, map_mul, bcHom_ι, bcHom_ι]
    exact zero_add (1 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero _ _ _) ih

/-- Evenness descends along base change. -/
theorem mem_even_of_bcHom {X : CliffordAlgebra Q} (hX : bcHom Q X ∈ even (Q.baseChange (AlgebraicClosure F))) :
    X ∈ even Q := by
  rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at hX ⊢
  have htop : X ∈ evenOdd Q 0 ⊔ evenOdd Q 1 := by
    rw [(evenOdd_isCompl Q).sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 htop
  have hb' : bcHom Q b ∈ evenOdd (Q.baseChange (AlgebraicClosure F)) 0 := by
    have := Submodule.sub_mem _ hX (bcHom_mem_evenOdd_zero Q ha)
    rwa [map_add, add_sub_cancel_left] at this
  have h0 : bcHom Q b = 0 :=
    (Submodule.disjoint_def.1 (evenOdd_isCompl (Q.baseChange (AlgebraicClosure F))).disjoint) _ hb'
      (bcHom_mem_evenOdd_one Q hb)
  rw [show b = 0 from bcHom_injective Q (h0.trans (map_zero _).symm), add_zero]
  exact ha

/-- `σ(ι(w)) = ι((σ ⊗ 1) w)`. -/
theorem galC_ι' (σ : GalF F) (w : (AlgebraicClosure F) ⊗[F] V) :
    galC Q σ (ι (Q.baseChange (AlgebraicClosure F)) w) = ι (Q.baseChange (AlgebraicClosure F)) (galT V σ w) := by
  induction w using TensorProduct.inductionOn with
  | tmul z v =>
    simp only [galC, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, toBaseChange_ι, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq,
      ofBaseChange_tmul_ι, galT_tmul]
    rfl
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/-- `σ` fixes the rational elements. -/
theorem galC_bcHom' (σ : GalF F) (a : CliffordAlgebra Q) : galC Q σ (bcHom Q a) = bcHom Q a := by
  simp only [galC, bcHom, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply, toBaseChange_ofBaseChange,
    Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq]

/-- A rational element of `C(Q_{F̄})` lying in `ι(F̄ ⊗ V)` lies in `ι(V)`. -/
theorem mem_range_ι_of_bcHom {X : CliffordAlgebra Q}
    (hX : bcHom Q X ∈ LinearMap.range (ι (Q.baseChange (AlgebraicClosure F)))) : X ∈ LinearMap.range (ι Q) := by
  obtain ⟨w, hw⟩ := hX
  have hfix : ∀ σ : GalF F, galT V σ w = w := fun σ => by
    apply ι_injective (Q.baseChange (AlgebraicClosure F))
    rw [← galC_ι', hw, galC_bcHom']
  obtain ⟨v, rfl⟩ := exists_tmul_of_fixed V w hfix
  refine ⟨v, bcHom_injective Q ?_⟩
  rw [bcHom_ι, hw]

/-- **`GSpin` descends along base change**: a unit of `C(Q)` whose base change lies in
`GSpin(Q)(F̄)` lies in `GSpin(Q)(F)`. -/
theorem mem_GSpin_of_bcUnits {b : (CliffordAlgebra Q)ˣ}
    (hb : bcUnits Q b ∈ GSpin (Q.baseChange (AlgebraicClosure F))) : b ∈ GSpin Q := by
  obtain ⟨h0, h1, h2⟩ := hb
  have hinv : (((bcUnits Q b)⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
      bcHom Q ((b⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
    rw [← map_inv]; rfl
  refine ⟨mem_even_of_bcHom Q h0, fun v => mem_range_ι_of_bcHom Q ?_,
    fun v => mem_range_ι_of_bcHom Q ?_⟩
  · have := h1 (1 ⊗ₜ v)
    rw [hinv, ← bcHom_ι] at this
    rw [map_mul, map_mul]
    exact this
  · have := h2 (1 ⊗ₜ v)
    rw [hinv, ← bcHom_ι] at this
    rw [map_mul, map_mul]
    exact this

/-- `t ι(w) t⁻¹ = ι(P(t)_{F̄} w)` for `t ∈ GSpin(Q)(F)`. -/
theorem bcUnits_conj_ι' (t : GSpin Q) (w : (AlgebraicClosure F) ⊗[F] V) :
    ((bcUnits Q (t : (CliffordAlgebra Q)ˣ) : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) *
      ι (Q.baseChange (AlgebraicClosure F)) w *
      (((bcUnits Q (t : (CliffordAlgebra Q)ˣ))⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
    ι (Q.baseChange (AlgebraicClosure F)) ((specP Q t : V →ₗ[F] V).baseChange (AlgebraicClosure F) w) := by
  induction w using TensorProduct.inductionOn with
  | tmul z v =>
    rw [LinearMap.baseChange_tmul, ← ofBaseChange_tmul_ι, ← ofBaseChange_tmul_ι,
      LinearEquiv.coe_coe, ι_specP]
    show ofBaseChange (AlgebraicClosure F) Q (1 ⊗ₜ ((t : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) *
      ofBaseChange (AlgebraicClosure F) Q (z ⊗ₜ ι Q v) * ofBaseChange (AlgebraicClosure F) Q
        (1 ⊗ₜ (((t : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) = _
    rw [← map_mul, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  | add a b ha hb => rw [map_add, mul_add, add_mul, ha, hb, map_add, map_add]

/-- Base change maps `GSpin(Q)(F)` into `GSpin(Q)(F̄)`. -/
theorem bcUnits_mem_GSpin (t : GSpin Q) :
    bcUnits Q (t : (CliffordAlgebra Q)ˣ) ∈ GSpin (Q.baseChange (AlgebraicClosure F)) := by
  have h0 : ((t : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ evenOdd Q 0 := by
    rw [← even_toSubmodule]; exact t.2.1
  refine ⟨?_, fun w => ⟨_, (bcUnits_conj_ι' Q t w).symm⟩, fun w => ?_⟩
  · rw [← Subalgebra.mem_toSubmodule, even_toSubmodule]; exact bcHom_mem_evenOdd_zero Q h0
  · have := bcUnits_conj_ι' Q t⁻¹ w
    rw [Subgroup.coe_inv, map_inv, inv_inv] at this
    exact ⟨_, this.symm⟩

end CliffordBC

section KerBC

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- If `B` fixes `ker A` pointwise, then `B_{F̄}` fixes `ker A_{F̄}` pointwise (`F̄` is flat). -/
theorem baseChange_fix_of_fix (A B : V →ₗ[F] V) (h : ∀ v ∈ LinearMap.ker A, B v = v)
    (u : (AlgebraicClosure F) ⊗[F] V) (hu : u ∈ LinearMap.ker (A.baseChange (AlgebraicClosure F))) : B.baseChange (AlgebraicClosure F) u = u := by
  have hk := Module.Flat.ker_lTensor_eq (R := F) (AlgebraicClosure F) (AlgebraicClosure F) A
  have hu' : u ∈ LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor (AlgebraicClosure F) (AlgebraicClosure F) A) := hu
  rw [hk] at hu'
  obtain ⟨u₀, rfl⟩ := hu'
  clear hu
  induction u₀ using TensorProduct.inductionOn with
  | tmul z k =>
    show B.baseChange (AlgebraicClosure F) (z ⊗ₜ (k : V)) = z ⊗ₜ (k : V)
    rw [LinearMap.baseChange_tmul, h k k.2]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

end KerBC

section Transport

open CliffordAlgebra

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
  {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}

/-- A unit of `C(Q_{F̄})` which, with its inverse, is Galois-fixed, is the base change of a unit
of `C(Q)`. -/
theorem exists_bcUnits_of_fixed (U : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ)
    (h : ∀ σ : GalF F, galC Q₂ σ U = U)
    (h' : ∀ σ : GalF F, galC Q₂ σ ((U⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
      ((U⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _)) :
    ∃ b : (CliffordAlgebra Q₂)ˣ, bcUnits Q₂ b = U := by
  obtain ⟨b, hb⟩ := exists_bcHom_of_fixed Q₂ _ h
  obtain ⟨c, hc⟩ := exists_bcHom_of_fixed Q₂ _ h'
  have hbc : b * c = 1 := bcHom_injective Q₂ (by rw [map_mul, hb, hc, map_one, Units.mul_inv])
  have hcb : c * b = 1 := bcHom_injective Q₂ (by rw [map_mul, hb, hc, map_one, Units.inv_mul])
  exact ⟨⟨b, c, hbc, hcb⟩, Units.ext hb⟩

/-- `C(φ)` maps `GSpin(Q₁)(F̄)` into `GSpin(Q₂)(F̄)`. -/
theorem cliffUnits_mem_GSpin
    (φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F)))
    {z : (CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F)))ˣ} (hz : z ∈ GSpin (Q₁.baseChange (AlgebraicClosure F))) :
    cliffUnits φ z ∈ GSpin (Q₂.baseChange (AlgebraicClosure F)) := by
  obtain ⟨h0, h1, h2⟩ := hz
  have hι : ∀ w, ι (Q₂.baseChange (AlgebraicClosure F)) w = CliffordAlgebra.map φ.toIsometry
      (ι (Q₁.baseChange (AlgebraicClosure F)) (φ.symm w)) := fun w => by
    rw [map_apply_ι]; congr 1; exact (φ.apply_symm_apply w).symm
  have hinv : (((cliffUnits φ z)⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
      CliffordAlgebra.map φ.toIsometry ((z⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) := by
    rw [← map_inv]; rfl
  refine ⟨?_, fun w => ?_, fun w => ?_⟩
  · have key : ∀ X ∈ evenOdd (Q₁.baseChange (AlgebraicClosure F)) 0,
        CliffordAlgebra.map φ.toIsometry X ∈ evenOdd (Q₂.baseChange (AlgebraicClosure F)) 0 := by
      intro X hX
      induction X, hX using even_induction with
      | algebraMap r => rw [AlgHom.commutes]; exact SetLike.algebraMap_mem_graded _ _
      | add x y hx hy ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
      | ι_mul_ι_mul m₁ m₂ x hx ih =>
        rw [map_mul, map_mul, map_apply_ι, map_apply_ι]
        exact zero_add (0 : ZMod 2) ▸ SetLike.mul_mem_graded (ι_mul_ι_mem_evenOdd_zero _ _ _) ih
    rw [← Subalgebra.mem_toSubmodule, even_toSubmodule] at h0 ⊢
    exact key _ h0
  · obtain ⟨u, hu⟩ := h1 (φ.symm w)
    refine ⟨φ u, ?_⟩
    rw [hinv, hι w, show ((cliffUnits φ z : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
      CliffordAlgebra.map φ.toIsometry z from rfl, ← map_mul, ← map_mul, ← hu, map_apply_ι]
    rfl
  · obtain ⟨u, hu⟩ := h2 (φ.symm w)
    refine ⟨φ u, ?_⟩
    rw [hinv, hι w, show ((cliffUnits φ z : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
      CliffordAlgebra.map φ.toIsometry z from rfl, ← map_mul, ← map_mul, ← hu, map_apply_ι]
    rfl

end Transport

section Psi

open CliffordAlgebra

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
  {Q₁ : QuadraticForm F V₁} {Q₂ : QuadraticForm F V₂}

/-- `Ψ = Ad(g) ∘ C(φ) : C(Q₁)_{F̄} → C(Q₂)_{F̄}`. -/
def psiA (φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F)))
    (g : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ) (a : CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F))) : CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)) :=
  (g : CliffordAlgebra _) * CliffordAlgebra.map φ.toIsometry a *
    ((g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _)

variable (φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F)))
  (g : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ)

theorem psiA_mul (a b : CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F))) :
    psiA φ g (a * b) = psiA φ g a * psiA φ g b := by
  simp only [psiA, map_mul, mul_assoc, Units.inv_mul_cancel_left]

theorem psiA_injective : Function.Injective (psiA φ g) := by
  intro a b h
  have h' : CliffordAlgebra.map φ.toIsometry a = CliffordAlgebra.map φ.toIsometry b := by
    have := congrArg (fun c => ((g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) * c * (g : CliffordAlgebra _)) h
    simpa only [psiA, mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, mul_one] using this
  exact (CliffordAlgebra.equivOfIsometry φ).injective h'

theorem psiA_ι (w : (AlgebraicClosure F) ⊗[F] V₁) :
    psiA φ g (ι _ w) = (g : CliffordAlgebra _) * ι (Q₂.baseChange (AlgebraicClosure F)) (φ w) *
      ((g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) := by
  rw [psiA, map_apply_ι]; rfl

/-- `Ψ` on units. -/
def psiU (φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F)))
    (g : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ) : (CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F)))ˣ →* (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ :=
  (MulAut.conj g).toMonoidHom.comp (cliffUnits φ)

theorem coe_psiU (z : (CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F)))ˣ) :
    ((psiU φ g z : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) = psiA φ g z := rfl

theorem psiU_eq (z : (CliffordAlgebra (Q₁.baseChange (AlgebraicClosure F)))ˣ) :
    psiU φ g z = g * cliffUnits φ z * g⁻¹ := rfl

/-- The rationality clause of strong stable conjugacy at `x`. -/
def RatAt (φ : (Q₁.baseChange (AlgebraicClosure F)).IsometryEquiv (Q₂.baseChange (AlgebraicClosure F)))
    (g : (CliffordAlgebra (Q₂.baseChange (AlgebraicClosure F)))ˣ) (x : (CliffordAlgebra Q₁)ˣ) : Prop :=
  ∀ σ : GalF F, ∀ z ∈ GSpin (Q₁.baseChange (AlgebraicClosure F)), Commute z (bcUnits Q₁ x) →
    galC Q₂ σ ((g * cliffUnits φ z * g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _) =
      (g : CliffordAlgebra _) * CliffordAlgebra.map φ.toIsometry (galC Q₁ σ (z : CliffordAlgebra _)) *
        ((g⁻¹ : (CliffordAlgebra _)ˣ) : CliffordAlgebra _)

variable {φ g}

/-- **Rationality of the transport**: if `Ad(g) ∘ C(φ)` is defined over `F` on the centralizer of
`x`, it maps every rational `t ∈ GSpin(Q₁)(F)` commuting with `x` to the base change of a
rational element of `GSpin(Q₂)(F)`. -/
theorem exists_transport {x : (CliffordAlgebra Q₁)ˣ} (hg : g ∈ GSpin (Q₂.baseChange (AlgebraicClosure F)))
    (hrat : RatAt φ g x) (t : GSpin Q₁) (ht : Commute (t : (CliffordAlgebra Q₁)ˣ) x) :
    ∃ b : GSpin Q₂, bcUnits Q₂ (b : (CliffordAlgebra Q₂)ˣ) =
      psiU φ g (bcUnits Q₁ (t : (CliffordAlgebra Q₁)ˣ)) := by
  have hfix : ∀ s : GSpin Q₁, Commute (s : (CliffordAlgebra Q₁)ˣ) x → ∀ σ : GalF F,
      galC Q₂ σ ((psiU φ g (bcUnits Q₁ (s : (CliffordAlgebra Q₁)ˣ)) : (CliffordAlgebra _)ˣ) :
        CliffordAlgebra _) = psiU φ g (bcUnits Q₁ (s : (CliffordAlgebra Q₁)ˣ)) := by
    intro s hs σ
    rw [psiU_eq, hrat σ _ (bcUnits_mem_GSpin Q₁ s) (hs.map (bcUnits Q₁))]
    show _ * CliffordAlgebra.map φ.toIsometry (galC Q₁ σ (bcHom Q₁ _)) * _ = _
    rw [galC_bcHom']
    rfl
  obtain ⟨b, hb⟩ := exists_bcUnits_of_fixed _ (hfix t ht) (fun σ => by
    have := hfix t⁻¹ (by rw [Subgroup.coe_inv]; exact ht.inv_left) σ
    rwa [Subgroup.coe_inv, map_inv, map_inv] at this)
  have hmem : b ∈ GSpin Q₂ := by
    apply mem_GSpin_of_bcUnits
    rw [hb, psiU_eq]
    exact (GSpin _).mul_mem ((GSpin _).mul_mem hg (cliffUnits_mem_GSpin φ
      (bcUnits_mem_GSpin Q₁ t))) ((GSpin _).inv_mem hg)
  exact ⟨⟨b, hmem⟩, hb⟩

end Psi

end TorusTransfer
end GSpinGGP
