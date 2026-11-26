/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Basic
import GSpinGGP.TraceFormula.SpinorNorm

/-!
# The regular set under conjugation and under `A_G(F)`

* `conj_mem_regularSet`: `G_reg(F)` is stable under conjugation by `G(F)` (from `Ad(G)`-stability of
  `gspin`, `conj_mem_regularSet_of_ad`).
* `mul_mem_regularSet_of_mem_AG`, `mul_mem_ellRegSet_of_mem_AG`, `conj_mem_ellRegSet`: `G_reg(F)`
  and `G_ell,reg(F)` are stable under `A_G(F)` (elements of `A_G(F)` are semisimple and commute
  with `𝔤`, `splitCentralGSpin_spec`), and `G_ell,reg(F)` under conjugation.
* `lieCentralizer_mul_AG`, `grpCentralizer_mul_AG`: `𝔤_{a x} = 𝔤_x` and `G_{a x} = G_x` for
  `a ∈ A_G(F)`.
-/

noncomputable section

open MeasureTheory Topology Filter

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- The regular semisimple set is stable under conjugation by `G`, provided `𝔤` is
`Ad(G)`-stable (Thesis §2.1): `x ↦ g x g⁻¹` conjugates left multiplication (so preserves
semisimplicity) and carries `𝔤_x` isomorphically onto `𝔤_{g x g⁻¹}`. -/
theorem conj_mem_regularSet_of_ad {A : Type*} [Ring A] [Algebra F A] (G : Subgroup Aˣ)
    (𝔤 : LieSubalgebra F A)
    (hAd : ∀ g : ↥G, ∀ X ∈ 𝔤, ((g : Aˣ) : A) * X * ((g⁻¹ : Aˣ) : A) ∈ 𝔤)
    (g y : ↥G) (hy : y ∈ regularSet G 𝔤) : g * y * g⁻¹ ∈ regularSet G 𝔤 := by
  obtain ⟨hss, hab⟩ := hy
  set u : Aˣ := (g : Aˣ)
  set z : A := ((y : Aˣ) : A)
  have hc : (((g * y * g⁻¹ : ↥G) : Aˣ) : A) = (u : A) * z * ((u⁻¹ : Aˣ) : A) := rfl
  refine ⟨?_, ?_⟩
  · -- semisimplicity is invariant under conjugation by the linear equivalence `L_u`
    let e : A ≃ₗ[F] A := LinearEquiv.ofLinearMap (LinearMap.mulLeft F (u : A))
      (LinearMap.mulLeft F ((u⁻¹ : Aˣ) : A)) (by ext; simp [← mul_assoc]) (by ext; simp [← mul_assoc])
    change IsSS F (((g * y * g⁻¹ : ↥G) : Aˣ) : A)
    rw [hc]
    refine (LinearEquiv.isSemisimple_iff (f := LinearMap.mulLeft F z) _ e ?_).1 hss
    ext w
    simp [e, mul_assoc]
  · refine ⟨fun X Y => ?_⟩
    obtain ⟨X, hX⟩ := X
    obtain ⟨Y, hY⟩ := Y
    rw [mem_lieCentralizer, hc] at hX hY
    have hmem : ∀ W : A, W ∈ 𝔤 → (u : A) * z * ((u⁻¹ : Aˣ) : A) * W =
        W * ((u : A) * z * ((u⁻¹ : Aˣ) : A)) →
        ((u⁻¹ : Aˣ) : A) * W * (u : A) ∈ lieCentralizer 𝔤 z := by
      intro W hW hWc
      rw [mem_lieCentralizer]
      refine ⟨?_, ?_⟩
      · have := hAd g⁻¹ W hW
        simpa using this
      · have h2 := congrArg (fun T => ((u⁻¹ : Aˣ) : A) * T * (u : A)) hWc
        simp only [mul_assoc, Units.inv_mul, mul_one, Units.inv_mul_cancel_left] at h2
        simpa [mul_assoc] using h2
    have h0 := hab.trivial ⟨_, hmem X hX.1 hX.2⟩ ⟨_, hmem Y hY.1 hY.2⟩
    rw [Subtype.ext_iff, LieSubalgebra.coe_bracket] at h0
    apply Subtype.ext
    rw [LieSubalgebra.coe_bracket]
    simp only [Ring.lie_def, ZeroMemClass.coe_zero] at h0 ⊢
    have h3 := congrArg (fun T => (u : A) * T * ((u⁻¹ : Aˣ) : A)) h0
    simp only [mul_sub, sub_mul, mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one,
      mul_zero, zero_mul] at h3
    simpa [mul_assoc] using h3

namespace GGPData

variable (d : GGPData F)

/-- `G(F)` is totally disconnected (`p`-adic `F`; LocalGroups `totallyDisconnectedSpace_subgroup`,
Thesis §2.1). -/
instance totallyDisconnectedSpace_G : TotallyDisconnectedSpace ↥d.G :=
  totallyDisconnectedSpace_subgroup F d.ambient d.G

/-- `A_G(F)` is locally compact (it is closed in `G(F)`), so it carries a Haar measure
(Thesis §7.1). -/
instance locallyCompactSpace_AG : LocallyCompactSpace ↥d.AG :=
  d.isClosed_AG.locallyCompactSpace

end GGPData

/-! ### Conjugation stability of `G_reg` -/

/-- `G_reg(F)` is stable under conjugation by `G(F)` (Thesis §2.1). -/
theorem conj_mem_regularSet (d : GGPData F) (g y : ↥d.G) (hy : y ∈ regularSet d.G d.lie) :
    g * y * g⁻¹ ∈ regularSet d.G d.lie :=
  conj_mem_regularSet_of_ad d.G d.lie (fun g _ hX => d.conj_mem_lie g hX) g y hy

/-! ### `A_G(F)`-stability of the regular set -/

variable (d : GGPData F)

open Classical Polynomial in
/-- An element annihilated by a product of distinct linear factors is semisimple. -/
theorem isSS_of_aeval_prod_eq_zero {A : Type*} [Ring A] [Algebra F A] {x : A} (s : Finset F)
    (h : aeval x (∏ μ ∈ s, (X - C μ)) = 0) : IsSS F x := by
  have hsep : (∏ μ ∈ s, (X - C μ)).Separable :=
    separable_prod_X_sub_C_iff' (f := fun μ : F => μ).mpr fun a _ b _ hab => hab
  unfold IsSS
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsep.squarefree ?_
  have h1 := Polynomial.aeval_algHom_apply (Algebra.lmul F A) x (∏ μ ∈ s, (X - C μ))
  have h2 : Algebra.lmul F A x = LinearMap.mulLeft F x := rfl
  rw [h2] at h1
  rw [h1, h, map_zero]

open Classical Polynomial in
/-- Enlarging the set of roots keeps the annihilation. -/
theorem aeval_prod_eq_zero_of_subset {A : Type*} [Ring A] [Algebra F A] {x : A} {s t : Finset F}
    (hst : s ⊆ t) (h : aeval x (∏ μ ∈ s, (X - C μ)) = 0) :
    aeval x (∏ μ ∈ t, (X - C μ)) = 0 := by
  rw [← Finset.prod_sdiff hst, map_mul, h, mul_zero]

open Classical CliffordAlgebra Polynomial in
/-- **Elements of the split centre `A_{GSpin(V)}` are split semisimple and commute with
`gspin(V)`**: scalars trivially; for a hyperbolic plane, `GSpin(V) ⊆ C⁺(V) = F ⊕ F ω` with
`ω² = r²`, `r ≠ 0`, so `a = α + βω` satisfies `(a - α - βr)(a - α + βr) = 0`, and `C⁺(V) ⊇ gspin(V)` is
commutative. -/
theorem splitCentralGSpin_spec {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V]
    (Q : QuadraticForm F V) {a : GSpin Q} (ha : a ∈ splitCentralGSpin Q) :
    (∃ s : Finset F,
      aeval ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) (∏ μ ∈ s, (X - C μ)) = 0) ∧
    ∀ Y ∈ gspin Q, ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * Y =
      Y * ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) := by
  unfold splitCentralGSpin at ha
  split_ifs at ha with hQ
  · obtain ⟨e, he⟩ := exists_orthogonal_basis_fin_two Q hQ.1
    obtain ⟨r, hr0, hr⟩ := exists_sq_eq_of_isHypPlane hQ e he
    set ω : CliffordAlgebra Q := ι Q (e 0) * ι Q (e 1) with hω
    have h10 : ι Q (e 1) * ι Q (e 0) = -ω := by
      have h1 := ι_mul_ι_add_swap (Q := Q) (e 1) (e 0)
      have hb : bform Q (e 1) (e 0) = 0 := he 1 0 (by decide)
      rw [polar_eq_two_mul_bform, hb, mul_zero, (algebraMap F (CliffordAlgebra Q)).map_zero] at h1
      exact eq_neg_of_add_eq_zero_left h1
    have hsq : ∀ i, ι Q (e i) * ι Q (e i) = Q (e i) • (1 : CliffordAlgebra Q) := fun i => by
      rw [ι_sq_scalar, Algebra.algebraMap_eq_smul_one]
    have hωω : ω * ω = (r ^ 2) • (1 : CliffordAlgebra Q) := by
      calc ω * ω = ι Q (e 0) * (ι Q (e 1) * ι Q (e 0)) * ι Q (e 1) := by
            simp only [ω, mul_assoc]
        _ = -((ι Q (e 0) * ι Q (e 0)) * (ι Q (e 1) * ι Q (e 1))) := by
            rw [h10]; simp only [ω, mul_neg, neg_mul, mul_assoc]
        _ = _ := by rw [hsq, hsq, smul_mul_smul_comm, one_mul, hr, neg_smul]
    have hev : ∀ Y : CliffordAlgebra Q, Y ∈ even Q → ∃ α β : F, Y = α • (1 : CliffordAlgebra Q) + β • ω :=
      fun Y hY => exists_eq_smul_one_add_smul_of_even e he Y (by rw [← even_toSubmodule]; exact hY)
    obtain ⟨α, β, hab⟩ := hev _ a.2.1
    refine ⟨?_, fun Y hY => ?_⟩
    · by_cases hβ : β = 0
      · refine ⟨{α}, ?_⟩
        rw [Finset.prod_singleton, map_sub, aeval_X, aeval_C, hab, hβ,
          Algebra.algebraMap_eq_smul_one]
        module
      · have hne : α + β * r ≠ α - β * r := by
          intro h
          have h2 : (2 : F) * (β * r) = 0 := by linear_combination h
          rcases mul_eq_zero.mp h2 with h2 | h2
          · exact two_ne_zero h2
          · exact mul_ne_zero hβ hr0 h2
        refine ⟨{α + β * r, α - β * r}, ?_⟩
        rw [Finset.prod_pair hne, map_mul, map_sub, map_sub, aeval_X, aeval_C, aeval_C, hab,
          Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        simp only [sub_mul, mul_sub, add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, hωω]
        module
    · obtain ⟨γ, η, hYe⟩ := hev Y hY.1
      rw [hab, hYe]
      simp only [add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one]
      module
  · obtain ⟨c, rfl⟩ := ha
    have hc : ((scalarGSpin Q c : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
        algebraMap F (CliffordAlgebra Q) (c : F) := rfl
    refine ⟨⟨{(c : F)}, ?_⟩, fun Y _ => ?_⟩
    · rw [Finset.prod_singleton, map_sub, aeval_X, aeval_C, hc, sub_self]
    · rw [hc]; exact Algebra.commutes _ _

open Classical Polynomial in
/-- `G_reg(F)` is stable under multiplication by `A_G(F)` (Thesis §2.1).

`a ∈ A_G(F)` is semisimple (annihilated by a product of distinct linear factors: scalars, or on a
hyperbolic-plane factor an element of `C⁺(W) ≅ F × F`, `splitCentralGSpin_spec`) and commutes with
`𝔤` (`C⁺(W) ⊇ gspin(W)` is commutative for a plane) and with `g` (`A_G` is central), so `a g` is
semisimple with `𝔤_{ag} = 𝔤_g`. -/
theorem mul_mem_regularSet_of_mem_AG (a : ↥d.AG) {g : ↥d.G} (hg : g ∈ regularSet d.G d.lie) :
    (a : ↥d.G) * g ∈ regularSet d.G d.lie := by
  obtain ⟨p, ⟨hp1, hp2⟩, hpa⟩ := a.2
  obtain ⟨⟨s₁, hs₁⟩, hc₁⟩ := splitCentralGSpin_spec d.QW hp1
  obtain ⟨⟨s₂, hs₂⟩, hc₂⟩ := splitCentralGSpin_spec d.QV hp2
  set A : d.ambient := (((a : ↥d.G) : d.ambientˣ) : d.ambient) with hAdef
  have hA : A = (((p.1 : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
      ((p.2 : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) := by
    rw [hAdef, ← hpa]; rfl
  have hAss : IsSS F A := by
    refine isSS_of_aeval_prod_eq_zero (s₁ ∪ s₂) ?_
    rw [hA]
    refine Prod.ext ?_ ?_
    · have := Polynomial.aeval_algHom_apply (AlgHom.fst F (CliffordAlgebra d.QW)
        (CliffordAlgebra d.QV)) (((p.1 : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
          ((p.2 : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) (∏ μ ∈ s₁ ∪ s₂, (X - C μ))
      change aeval ((p.1 : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) _ = (aeval (R := F) (A := d.ambient) _ _).1 at this
      rw [← this, Prod.fst_zero]
      exact aeval_prod_eq_zero_of_subset Finset.subset_union_left hs₁
    · have := Polynomial.aeval_algHom_apply (AlgHom.snd F (CliffordAlgebra d.QW)
        (CliffordAlgebra d.QV)) (((p.1 : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
          ((p.2 : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) (∏ μ ∈ s₁ ∪ s₂, (X - C μ))
      change aeval ((p.2 : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) _ = (aeval (R := F) (A := d.ambient) _ _).2 at this
      rw [← this, Prod.snd_zero]
      exact aeval_prod_eq_zero_of_subset Finset.subset_union_right hs₂
  have hAc : ∀ Y ∈ d.lie, A * Y = Y * A := fun Y hY => by
    rw [hA]
    exact Prod.ext (hc₁ Y.1 hY.1) (hc₂ Y.2 hY.2)
  have hAg : A * (((g : ↥d.G) : d.ambientˣ) : d.ambient) =
      (((g : ↥d.G) : d.ambientˣ) : d.ambient) * A := by
    have h := Subgroup.mem_center_iff.mp (d.AG_le_center a.2) g
    have h' := congrArg (fun u : ↥d.G => ((u : d.ambientˣ) : d.ambient)) h
    simpa [hAdef] using h'.symm
  show IsRegularSS d.lie ((((a : ↥d.G) * g : ↥d.G) : d.ambientˣ) : d.ambient)
  rw [Subgroup.coe_mul, Units.val_mul, ← hAdef]
  have hC : lieCentralizer d.lie (A * (((g : ↥d.G) : d.ambientˣ) : d.ambient)) =
      lieCentralizer d.lie (((g : ↥d.G) : d.ambientˣ) : d.ambient) := by
    ext Y
    rw [mem_lieCentralizer, mem_lieCentralizer]
    refine and_congr_right fun hY => ?_
    have hu : IsUnit A := ((a : ↥d.G) : d.ambientˣ).isUnit
    constructor
    · intro h
      refine hu.mul_left_cancel ?_
      rw [← mul_assoc, h, ← mul_assoc, ← hAc Y hY, mul_assoc]
    · intro h
      rw [mul_assoc, h, ← mul_assoc, hAc Y hY, mul_assoc]
  refine ⟨?_, hC ▸ hg.2⟩
  exact isSS_mul_of_commute hAg hAss hg.1

/-- `G_ell,reg(F)` is stable under `A_G(F)`: `a g` is regular, and `a` central gives
`Z_G(a g) = Z_G(g)`. -/
theorem mul_mem_ellRegSet_of_mem_AG (a : ↥d.AG) {g : ↥d.G} (hg : g ∈ d.ellRegSet) :
    (a : ↥d.G) * g ∈ d.ellRegSet := by
  refine ⟨mul_mem_regularSet_of_mem_AG d a hg.1, ?_⟩
  have hc : ∀ y : ↥d.G, y * (a : ↥d.G) = (a : ↥d.G) * y := fun y =>
    Subgroup.mem_center_iff.mp (d.AG_le_center a.2) y
  have he : (Subgroup.centralizer ({(a : ↥d.G) * g} : Set ↥d.G) : Set ↥d.G) =
      Subgroup.centralizer ({g} : Set ↥d.G) := by
    ext y
    simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      calc g * y = (a : ↥d.G)⁻¹ * ((a : ↥d.G) * g * y) := by group
        _ = (a : ↥d.G)⁻¹ * (y * ((a : ↥d.G) * g)) := by rw [h]
        _ = (a : ↥d.G)⁻¹ * ((a : ↥d.G) * (y * g)) := by rw [← mul_assoc y, hc y, mul_assoc]
        _ = y * g := by group
    · intro h
      rw [mul_assoc, h, ← mul_assoc, ← hc y, mul_assoc]
  rw [he]
  exact hg.2

/-- `G_ell,reg(F)` is stable under conjugation: `x g x⁻¹` is regular, and the image of
`Z_G(x g x⁻¹) = x Z_G(g) x⁻¹` in `G(F)/A_G(F)` is the conjugate of that of `Z_G(g)`. -/
theorem conj_mem_ellRegSet (x : ↥d.G) {g : ↥d.G} (hg : g ∈ d.ellRegSet) :
    x * g * x⁻¹ ∈ d.ellRegSet := by
  refine ⟨conj_mem_regularSet d x g hg.1, ?_⟩
  set φ : ↥d.G ⧸ d.AG → ↥d.G ⧸ d.AG := fun q =>
    (QuotientGroup.mk x : ↥d.G ⧸ d.AG) * q * (QuotientGroup.mk x : ↥d.G ⧸ d.AG)⁻¹
  have hφ : Continuous φ := (continuous_const.mul continuous_id).mul continuous_const
  have hmem : ∀ z : ↥d.G, z ∈ Subgroup.centralizer ({x * g * x⁻¹} : Set ↥d.G) ↔
      x⁻¹ * z * x ∈ Subgroup.centralizer ({g} : Set ↥d.G) := by
    intro z
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
    constructor
    · intro h
      calc g * (x⁻¹ * z * x) = x⁻¹ * ((x * g * x⁻¹) * z) * x := by group
        _ = x⁻¹ * (z * (x * g * x⁻¹)) * x := by rw [h]
        _ = x⁻¹ * z * x * g := by group
    · intro h
      calc x * g * x⁻¹ * z = x * (g * (x⁻¹ * z * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * z * x) * g) * x⁻¹ := by rw [h]
        _ = z * (x * g * x⁻¹) := by group
  have he : (QuotientGroup.mk '' (Subgroup.centralizer ({x * g * x⁻¹} : Set ↥d.G) : Set ↥d.G) :
      Set (↥d.G ⧸ d.AG)) = φ '' (QuotientGroup.mk ''
        (Subgroup.centralizer ({g} : Set ↥d.G) : Set ↥d.G)) := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨QuotientGroup.mk (x⁻¹ * z * x), ⟨_, (hmem z).1 hz, rfl⟩, ?_⟩
      simp only [φ, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1; group
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨x * w * x⁻¹, (hmem _).2 (by simpa [mul_assoc] using hw), ?_⟩
      simp only [φ, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  show IsCompact (QuotientGroup.mk '' (Subgroup.centralizer ({x * g * x⁻¹} : Set ↥d.G) :
    Set ↥d.G) : Set (↥d.G ⧸ d.AG))
  rw [he]
  exact hg.2.image hφ

open Classical Polynomial in
/-- An element of `A_G(F)` is semisimple in `C(W) × C(V)` and commutes with `𝔤` (the first half of
`mul_mem_regularSet_of_mem_AG`). -/
theorem coe_AG_spec (a : ↥d.AG) :
    IsSS F (((a : ↥d.G) : d.ambientˣ) : d.ambient) ∧
      ∀ Y ∈ d.lie, (((a : ↥d.G) : d.ambientˣ) : d.ambient) * Y =
        Y * (((a : ↥d.G) : d.ambientˣ) : d.ambient) := by
  obtain ⟨p, ⟨hp1, hp2⟩, hpa⟩ := a.2
  obtain ⟨⟨s₁, hs₁⟩, hc₁⟩ := splitCentralGSpin_spec d.QW hp1
  obtain ⟨⟨s₂, hs₂⟩, hc₂⟩ := splitCentralGSpin_spec d.QV hp2
  set A : d.ambient := (((a : ↥d.G) : d.ambientˣ) : d.ambient) with hAdef
  have hA : A = (((p.1 : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
      ((p.2 : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) := by
    rw [hAdef, ← hpa]; rfl
  refine ⟨?_, fun Y hY => ?_⟩
  · refine isSS_of_aeval_prod_eq_zero (s₁ ∪ s₂) ?_
    rw [hA]
    refine Prod.ext ?_ ?_
    · have := Polynomial.aeval_algHom_apply (AlgHom.fst F (CliffordAlgebra d.QW)
        (CliffordAlgebra d.QV)) (((p.1 : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
          ((p.2 : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) (∏ μ ∈ s₁ ∪ s₂, (X - C μ))
      change aeval ((p.1 : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) _ = (aeval (R := F) (A := d.ambient) _ _).1 at this
      rw [← this, Prod.fst_zero]
      exact aeval_prod_eq_zero_of_subset Finset.subset_union_left hs₁
    · have := Polynomial.aeval_algHom_apply (AlgHom.snd F (CliffordAlgebra d.QW)
        (CliffordAlgebra d.QV)) (((p.1 : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
          ((p.2 : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) (∏ μ ∈ s₁ ∪ s₂, (X - C μ))
      change aeval ((p.2 : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) _ = (aeval (R := F) (A := d.ambient) _ _).2 at this
      rw [← this, Prod.snd_zero]
      exact aeval_prod_eq_zero_of_subset Finset.subset_union_right hs₂
  · rw [hA]
    exact Prod.ext (hc₁ Y.1 hY.1) (hc₂ Y.2 hY.2)

/-- `a ∈ A_G(F)` commutes with every `g ∈ G(F)` in `C(W) × C(V)`. -/
theorem coe_AG_commute (a : ↥d.AG) (g : ↥d.G) :
    (((a : ↥d.G) : d.ambientˣ) : d.ambient) * ((g : d.ambientˣ) : d.ambient) =
      ((g : d.ambientˣ) : d.ambient) * (((a : ↥d.G) : d.ambientˣ) : d.ambient) := by
  have h := Subgroup.mem_center_iff.mp (d.AG_le_center a.2) g
  have h' := congrArg (fun u : ↥d.G => ((u : d.ambientˣ) : d.ambient)) h
  simpa using h'.symm

/-- `a x` is semisimple for `a ∈ A_G(F)` and semisimple `x`. -/
theorem isSS_mul_AG (a : ↥d.AG) {x : ↥d.G} (hx : IsSS F ((x : d.ambientˣ) : d.ambient)) :
    IsSS F ((((a : ↥d.G) * x : ↥d.G) : d.ambientˣ) : d.ambient) := by
  rw [Subgroup.coe_mul, Units.val_mul]
  exact isSS_mul_of_commute (coe_AG_commute d a x) (coe_AG_spec d a).1 hx

/-- `𝔤_{a x} = 𝔤_x` for `a ∈ A_G(F)`. -/
theorem lieCentralizer_mul_AG (a : ↥d.AG) (x : ↥d.G) :
    lieCentralizer d.lie ((((a : ↥d.G) * x : ↥d.G) : d.ambientˣ) : d.ambient) =
      lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient) := by
  set A : d.ambient := (((a : ↥d.G) : d.ambientˣ) : d.ambient)
  have hAc := (coe_AG_spec d a).2
  have hu : IsUnit A := ((a : ↥d.G) : d.ambientˣ).isUnit
  rw [Subgroup.coe_mul, Units.val_mul]
  ext Y
  rw [mem_lieCentralizer, mem_lieCentralizer]
  refine and_congr_right fun hY => ?_
  constructor
  · intro h
    refine hu.mul_left_cancel ?_
    rw [← mul_assoc, h, ← mul_assoc, ← hAc Y hY, mul_assoc]
  · intro h
    rw [mul_assoc, h, ← mul_assoc, hAc Y hY, mul_assoc]

/-- `G_{a x} = G_x` for `a ∈ A_G(F)` (as subgroups of `(C(W) × C(V))^×`). -/
theorem grpCentralizer_mul_AG (a : ↥d.AG) (x : ↥d.G) :
    grpCentralizer d.G (((a : ↥d.G) * x : ↥d.G) : d.ambientˣ) =
      grpCentralizer d.G (x : d.ambientˣ) := by
  ext z
  simp only [grpCentralizer, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun hz => ?_
  have hc : ((a : ↥d.G) : d.ambientˣ) * z = z * ((a : ↥d.G) : d.ambientˣ) := by
    have h := Subgroup.mem_center_iff.mp (d.AG_le_center a.2) ⟨z, hz⟩
    exact (congrArg Subtype.val h).symm
  set u : d.ambientˣ := ((a : ↥d.G) : d.ambientˣ)
  set v : d.ambientˣ := ((x : ↥d.G) : d.ambientˣ)
  change z * (u * v) = u * v * z ↔ z * v = v * z
  constructor
  · intro h
    refine mul_left_cancel (a := u) ?_
    calc u * (z * v) = z * (u * v) := by rw [← mul_assoc, hc, mul_assoc]
      _ = u * v * z := h
      _ = u * (v * z) := mul_assoc _ _ _
  · intro h
    calc z * (u * v) = u * (z * v) := by rw [← mul_assoc, ← hc, mul_assoc]
      _ = u * (v * z) := by rw [h]
      _ = u * v * z := (mul_assoc _ _ _).symm

end GSpinGGP
