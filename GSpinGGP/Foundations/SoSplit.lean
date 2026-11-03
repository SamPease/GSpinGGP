/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.SoCentralizer

/-!
# Splitting `so(V)_X` along orthogonal decompositions

For `V = U ⊥ U'` with `U`, `U'` stable under `X` and under every element of `so(V)_X`,
`so(V)_X ≅ so(U)_X × so(U')_X` (`finrank_soCent_eq_add`); more generally for the joint centralizer
`so(V)_X ⊓ so(V)_Y` (`finrank_soCent_inf_eq_add`). `exists_lieCentralizer_fixed_swap`: the
component of `Y ∈ gspin(V)_y` on the fixed space `W'_y` can be replaced by any skew map.
-/

noncomputable section

open Module LinearMap

namespace GSpinGGP

section Split

variable {K : Type*} [Field K]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {U U' : Submodule K V}

/-- The endomorphism of `V = U ⊕ U'` acting by `A` on `U` and `A'` on `U'`. -/
def sumEnd (h : IsCompl U U') (A : Module.End K U) (A' : Module.End K U') : Module.End K V :=
  LinearMap.ofIsCompl h (U.subtype ∘ₗ A) (U'.subtype ∘ₗ A')

theorem sumEnd_left (h : IsCompl U U') (A : Module.End K U) (A' : Module.End K U') (u : U) :
    sumEnd h A A' u = A u := by
  simp [sumEnd]

theorem sumEnd_right (h : IsCompl U U') (A : Module.End K U) (A' : Module.End K U') (u : U') :
    sumEnd h A A' u = A' u := by
  simp [sumEnd]

variable [Invertible (2 : K)]

variable {Q : QuadraticForm K V} {X : Module.End K V}
variable (horth : ∀ u ∈ U, ∀ w ∈ U', bform Q u w = 0)
include horth

theorem bform_orth' (u : U') (w : U) : bform Q u w = 0 := by
  rw [show bform Q u w = bform Q w u from QuadraticMap.associated_isSymm K Q _ _]
  exact horth _ w.2 _ u.2

theorem sumEnd_mem_soCent (h : IsCompl U U') (hXU : Set.MapsTo X U U) (hXU' : Set.MapsTo X U' U')
    {A : Module.End K U} {A' : Module.End K U'}
    (hA : A ∈ soCent (Q.comp U.subtype) (X.restrict hXU))
    (hA' : A' ∈ soCent (Q.comp U'.subtype) (X.restrict hXU')) :
    sumEnd h A A' ∈ soCent Q X := by
  rw [mem_soCent] at hA hA' ⊢
  refine ⟨fun v w => ?_, LinearMap.ext fun v => ?_⟩
  · obtain ⟨a, a', rfl, -⟩ := Submodule.existsUnique_add_of_isCompl h v
    obtain ⟨b, b', rfl, -⟩ := Submodule.existsUnique_add_of_isCompl h w
    have h1 := hA.1 a b
    have h2 := hA'.1 a' b'
    simp only [bform_comp_subtype] at h1 h2
    simp only [map_add, LinearMap.add_apply, sumEnd_left, sumEnd_right,
      horth _ (A a).2 _ b'.2, horth _ a.2 _ (A' b').2, bform_orth' horth (A' a') b,
      bform_orth' horth a' (A b)]
    linear_combination h1 + h2
  · obtain ⟨a, a', rfl, -⟩ := Submodule.existsUnique_add_of_isCompl h v
    have e1 : X a = (X.restrict hXU a : V) := rfl
    have e2 : X a' = (X.restrict hXU' a' : V) := rfl
    have h1 : (A (X.restrict hXU a) : V) = X (A a) :=
      congrArg (fun F : Module.End K U => (F a : V)) hA.2
    have h2 : (A' (X.restrict hXU' a') : V) = X (A' a') :=
      congrArg (fun F : Module.End K U' => (F a' : V)) hA'.2
    simp only [Module.End.mul_apply]
    rw [LinearMap.map_add X, e1, e2, LinearMap.map_add (sumEnd h A A'), sumEnd_left, sumEnd_right,
      h1, h2, LinearMap.map_add (sumEnd h A A'), sumEnd_left, sumEnd_right, LinearMap.map_add]

omit horth in
/-- A skew endomorphism preserving `U` preserves `U^⊥`. -/
theorem mapsTo_orthogonal_of_skew {M : Module.End K V}
    (hM : ∀ u w, bform Q (M u) w = -bform Q u (M w)) (hMU : Set.MapsTo M U U) :
    Set.MapsTo M ((bform Q).orthogonal U) ((bform Q).orthogonal U) := fun w hw =>
  LinearMap.BilinForm.mem_orthogonal_iff.2 fun x hx => by
    have h0 : bform Q (M x) w = 0 := (LinearMap.BilinForm.mem_orthogonal_iff.1 hw) _ (hMU hx)
    rw [hM, bform_comm Q x, neg_eq_zero] at h0
    rwa [bform_comm Q x]

omit horth in
/-- An isometry preserving `U` preserves `U^⊥`. -/
theorem mapsTo_orthogonal_of_isometry [FiniteDimensional K V] (hQ : IsNondeg Q)
    {g : Module.End K V} (hg : ∀ u v, bform Q (g u) (g v) = bform Q u v)
    (hgU : Set.MapsTo g U U) :
    Set.MapsTo g ((bform Q).orthogonal U) ((bform Q).orthogonal U) := by
  have hginj : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine hQ.1 x fun y => ?_
    rw [← hg, hx, map_zero, LinearMap.zero_apply]
  have hinj : Function.Injective (g.restrict hgU) := fun x y hxy =>
    Subtype.ext (hginj (congrArg Subtype.val hxy))
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  intro y hy
  refine LinearMap.BilinForm.mem_orthogonal_iff.2 fun x hx => ?_
  obtain ⟨x', hx'⟩ := hsurj ⟨x, hx⟩
  have hx'' : g x' = x := congrArg Subtype.val hx'
  change bform Q x (g y) = 0
  rw [← hx'', hg]
  exact (LinearMap.BilinForm.mem_orthogonal_iff.1 hy) _ x'.2

omit horth in
theorem restrict_mem_soCent (hXU : Set.MapsTo X U U) {M : Module.End K V} (hM : M ∈ soCent Q X)
    (hMU : Set.MapsTo M U U) : M.restrict hMU ∈ soCent (Q.comp U.subtype) (X.restrict hXU) := by
  rw [mem_soCent] at hM ⊢
  refine ⟨fun u w => by rw [bform_comp_subtype, bform_comp_subtype]; exact hM.1 u w,
    LinearMap.ext fun u => ?_⟩
  exact Subtype.ext (congrArg (fun F : Module.End K V => F u) hM.2)

/-- **Splitting the joint centralizer** `so(V)_{X,Y} = so(V)_X ⊓ so(V)_Y` along `V = U ⊥ U'`
preserved by `X`, `Y` and every element of `so(V)_{X,Y}`. -/
theorem finrank_soCent_inf_eq_add [FiniteDimensional K V] {Y : Module.End K V} (h : IsCompl U U')
    (hXU : Set.MapsTo X U U) (hXU' : Set.MapsTo X U' U') (hYU : Set.MapsTo Y U U)
    (hYU' : Set.MapsTo Y U' U') (hM : ∀ M ∈ soCent Q X ⊓ soCent Q Y, Set.MapsTo M U U)
    (hM' : ∀ M ∈ soCent Q X ⊓ soCent Q Y, Set.MapsTo M U' U') :
    finrank K ↥(soCent Q X ⊓ soCent Q Y) =
      finrank K ↥(soCent (Q.comp U.subtype) (X.restrict hXU) ⊓
        soCent (Q.comp U.subtype) (Y.restrict hYU)) +
      finrank K ↥(soCent (Q.comp U'.subtype) (X.restrict hXU') ⊓
        soCent (Q.comp U'.subtype) (Y.restrict hYU')) := by
  let e : ↥(soCent Q X ⊓ soCent Q Y) ≃ₗ[K]
      ↥(soCent (Q.comp U.subtype) (X.restrict hXU) ⊓ soCent (Q.comp U.subtype) (Y.restrict hYU)) ×
      ↥(soCent (Q.comp U'.subtype) (X.restrict hXU') ⊓
        soCent (Q.comp U'.subtype) (Y.restrict hYU')) :=
    { toFun := fun M => (⟨_, restrict_mem_soCent hXU M.2.1 (hM M M.2),
          restrict_mem_soCent hYU M.2.2 (hM M M.2)⟩,
        ⟨_, restrict_mem_soCent hXU' M.2.1 (hM' M M.2),
          restrict_mem_soCent hYU' M.2.2 (hM' M M.2)⟩)
      invFun := fun p => ⟨sumEnd h p.1 p.2, sumEnd_mem_soCent horth h hXU hXU' p.1.2.1 p.2.2.1,
        sumEnd_mem_soCent horth h hYU hYU' p.1.2.2 p.2.2.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun M => by
        refine Subtype.ext (LinearMap.ext fun v => ?_)
        obtain ⟨a, a', rfl, -⟩ := Submodule.existsUnique_add_of_isCompl h v
        simp only [map_add, sumEnd_left, sumEnd_right]
        rfl
      right_inv := fun p => by
        refine Prod.ext (Subtype.ext (LinearMap.ext fun u => Subtype.ext ?_))
          (Subtype.ext (LinearMap.ext fun u => Subtype.ext ?_))
        · exact sumEnd_left h _ _ u
        · exact sumEnd_right h _ _ u }
  rw [e.finrank_eq, Module.finrank_prod]

/-- **Splitting `so(V)_X` along an orthogonal decomposition** `V = U ⊥ U'` preserved by `X` and by
every element of `so(V)_X`: `dim so(V)_X = dim so(U)_X + dim so(U')_X`. -/
theorem finrank_soCent_eq_add [FiniteDimensional K V] (h : IsCompl U U')
    (hXU : Set.MapsTo X U U) (hXU' : Set.MapsTo X U' U')
    (hM : ∀ M ∈ soCent Q X, Set.MapsTo M U U) (hM' : ∀ M ∈ soCent Q X, Set.MapsTo M U' U') :
    finrank K (soCent Q X) = finrank K (soCent (Q.comp U.subtype) (X.restrict hXU)) +
      finrank K (soCent (Q.comp U'.subtype) (X.restrict hXU')) := by
  have := finrank_soCent_inf_eq_add horth h hXU hXU' hXU hXU'
    (by simpa only [inf_idem] using hM) (by simpa only [inf_idem] using hM')
  rwa [inf_idem, inf_idem, inf_idem] at this

theorem isNondeg_comp_subtype (hQ : IsNondeg Q) (h : IsCompl U U') :
    IsNondeg (Q.comp U.subtype) := by
  rw [isNondeg_iff] at hQ ⊢
  intro x hx
  refine Subtype.ext (hQ _ fun v => ?_)
  obtain ⟨a, a', rfl, -⟩ := Submodule.existsUnique_add_of_isCompl h v
  rw [map_add, horth _ x.2 _ a'.2, add_zero, ← bform_comp_subtype]
  exact hx a

/-- If `so(V)_X` is abelian, so is `so(U)_X`. -/
theorem commute_of_restrict (h : IsCompl U U') (hXU : Set.MapsTo X U U)
    (hXU' : Set.MapsTo X U' U') (hab : ∀ M₁ ∈ soCent Q X, ∀ M₂ ∈ soCent Q X, Commute M₁ M₂) :
    ∀ A₁ ∈ soCent (Q.comp U.subtype) (X.restrict hXU),
      ∀ A₂ ∈ soCent (Q.comp U.subtype) (X.restrict hXU), Commute A₁ A₂ := by
  intro A₁ h₁ A₂ h₂
  have z : (0 : Module.End K U') ∈ soCent (Q.comp U'.subtype) (X.restrict hXU') := zero_mem _
  have hc := (hab _ (sumEnd_mem_soCent horth h hXU hXU' h₁ z) _
    (sumEnd_mem_soCent horth h hXU hXU' h₂ z)).eq
  refine LinearMap.ext fun u => Subtype.ext ?_
  have := congrArg (fun F : Module.End K V => F u) hc
  simpa only [Module.End.mul_apply, sumEnd_left] using this

end Split

section Small

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {X : Module.End K V}

/-- `so(V)_X = so(V)` when `X` is a scalar. -/
theorem soCent_of_scalar {c : K} (hX : ∀ v, X v = c • v) : soCent Q X = soCent Q 1 := by
  have : X = c • (1 : Module.End K V) := LinearMap.ext fun v => by simp [hX]
  ext M
  simp only [mem_soCent, this, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]


end Small

section FixedSwap

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Changing the fixed-space component of `Y ∈ gspin(V)_y`**: for any skew `M` on `A = W'_y`
there is `Y' ∈ gspin(V)_y` with `dim gspin(V)_{y,Y'} − dim so(A)_M = dim gspin(V)_{y,Y} −
dim so(A)_{adV Y|_A}`. It is constructed as a lift of `adV Y' = M ⊕ adV Y|_{A^⊥}` (`sumEnd`), so
the part killing `A` is unchanged (`finrank_lieCentralizer_fixed`, `soCent_inf_killSub_congr`). -/
theorem exists_lieCentralizer_fixed_swap {Q : QuadraticForm K V} (hQ : IsNondeg Q) (y : GSpin Q)
    (hc : IsCompl (fixedSub y) ((bform Q).orthogonal (fixedSub y))) {Y : CliffordAlgebra Q}
    (hY : Y ∈ lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
    (h : ∀ a ∈ fixedSub y, adV Q Y a ∈ fixedSub y) {M : Module.End K (fixedSub y)}
    (hM : ∀ u w, bform (Q.comp (fixedSub y).subtype) (M u) w =
      -bform (Q.comp (fixedSub y).subtype) u (M w)) :
    ∃ Y' ∈ lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q),
      finrank K (lieCentralizer (lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q)) Y') +
        finrank K (soCent (Q.comp (fixedSub y).subtype) ((adV Q Y).restrict h)) =
      finrank K (lieCentralizer (lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q)) Y) +
        finrank K (soCent (Q.comp (fixedSub y).subtype) M) := by
  obtain ⟨hYg, hYc⟩ := mem_lieCentralizer.mp hY
  have hNs := bform_adV hYg
  have hNg : adV Q Y * (specP Q y : Module.End K V) = (specP Q y : Module.End K V) * adV Q Y :=
    ((commute_iff_adV hQ y hYg).mp hYc).symm
  have horth : ∀ u ∈ fixedSub y, ∀ w ∈ (bform Q).orthogonal (fixedSub y), bform Q u w = 0 :=
    fun u hu w hw => hw u hu
  have hgA : Set.MapsTo (specP Q y : Module.End K V) (fixedSub y) (fixedSub y) := fun a ha => by
    rw [SetLike.mem_coe, (mem_fixedSub_iff y a).1 ha]; exact ha
  have hgB : Set.MapsTo (specP Q y : Module.End K V) ((bform Q).orthogonal (fixedSub y))
      ((bform Q).orthogonal (fixedSub y)) := fun b hb => specP_mem_orthogonal_fixedSub y hb
  have hNB := mapsTo_orthogonal_of_skew hNs (fun a ha => h a ha)
  have hMmem : M ∈ soCent (Q.comp (fixedSub y).subtype)
      ((specP Q y : Module.End K V).restrict hgA) := by
    have hr : (specP Q y : Module.End K V).restrict hgA = 1 :=
      LinearMap.ext fun a => Subtype.ext ((mem_fixedSub_iff y a).1 a.2)
    exact mem_soCent.2 ⟨hM, by rw [hr, mul_one, one_mul]⟩
  have hNmem : (adV Q Y).restrict hNB ∈ soCent (Q.comp ((bform Q).orthogonal (fixedSub y)).subtype)
      ((specP Q y : Module.End K V).restrict hgB) := by
    refine mem_soCent.2 ⟨fun u w => ?_, LinearMap.ext fun b => Subtype.ext ?_⟩
    · simp only [bform_comp_subtype, LinearMap.restrict_coe_apply]; exact hNs _ _
    · exact congrArg (fun T : Module.End K V => T (b : V)) hNg
  set N' := sumEnd hc M ((adV Q Y).restrict hNB)
  obtain ⟨Y', hY'm, hY'⟩ := exists_mem_lieCentralizer_adV_eq hQ y
    (sumEnd_mem_soCent horth hc hgA hgB hMmem hNmem)
  obtain ⟨h1, e1⟩ := finrank_lieCentralizer_fixed hQ y hc hY'm
  obtain ⟨h0, e0⟩ := finrank_lieCentralizer_fixed hQ y hc hY
  have hres : (adV Q Y').restrict h1 = M := by
    ext a; simp only [LinearMap.restrict_coe_apply, hY', N', sumEnd_left]
  have hkill : soCent Q (specP Q y : Module.End K V) ⊓ soCent Q (adV Q Y') ⊓ killSub (fixedSub y) =
      soCent Q (specP Q y : Module.End K V) ⊓ soCent Q (adV Q Y) ⊓ killSub (fixedSub y) :=
    soCent_inf_killSub_congr hc (fun a ha => h1 a ha) (fun a ha => h a ha) fun b hb => by
      rw [hY', show b = ((⟨b, hb⟩ : (bform Q).orthogonal (fixedSub y)) : V) from rfl, sumEnd_right]
      rfl
  have hr0 : (adV Q Y).restrict h0 = (adV Q Y).restrict h := rfl
  refine ⟨Y', hY'm, ?_⟩
  rw [e1, e0, hres, hkill, hr0]
  omega

end FixedSwap

end GSpinGGP
