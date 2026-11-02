/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.SoCentralizer
import GSpinGGP.GGP.IsometryCentralizer

/-!
# `dim so(V)_X = ⌊dim V / 2⌋` for a regular semisimple isometry

Let `Q` be a nondegenerate quadratic form on a finite-dimensional space `V` over an algebraically
closed field `K` of characteristic `0`, and `X` a semisimple isometry of `Q` of determinant `1`
whose centralizer `so(V)_X` in `so(V)` is abelian. Then `dim so(V)_X = ⌊dim V / 2⌋`
(`finrank_soCent_of_isAbelian`), the rank of `so(V)`.

Proof. Induction on `dim V`, splitting off orthogonal summands `U` that are stable under `X` and
under every element of `so(V)_X`; then `so(V)_X ≅ so(U)_X × so(U^⊥)_X` (`finrank_soCent_eq_add`).
If `X` has an eigenvalue `μ ≠ ±1`, take `U = E_μ ⊕ E_{μ⁻¹}`: both are lines (`so(V)_X` abelian), so
`so(U)_X` is spanned by `diag(1, -1)` and has dimension `1`. Otherwise `V = E_1 ⊥ E_{-1}`, each
of dimension `≤ 2` (`so(V)_X` abelian), `dim E_{-1}` even (`det X = 1`), and `so(E)` has
dimension `⌊dim E / 2⌋` for `dim E ≤ 2`.
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

theorem exists_add_of_isCompl (h : IsCompl U U') (v : V) :
    ∃ a : U, ∃ a' : U', (a : V) + a' = v := by
  obtain ⟨a, ha, a', ha', e⟩ := Submodule.mem_sup.1 (h.sup_eq_top ▸ Submodule.mem_top (x := v))
  exact ⟨⟨a, ha⟩, ⟨a', ha'⟩, e⟩

variable [Invertible (2 : K)]

theorem bform_comp_subtype (Q : QuadraticForm K V) (U : Submodule K V) (u w : U) :
    bform (Q.comp U.subtype) u w = bform Q u w := by
  simp [bform]

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
  · obtain ⟨a, a', rfl⟩ := exists_add_of_isCompl h v
    obtain ⟨b, b', rfl⟩ := exists_add_of_isCompl h w
    have h1 := hA.1 a b
    have h2 := hA'.1 a' b'
    simp only [bform_comp_subtype] at h1 h2
    simp only [map_add, LinearMap.add_apply, sumEnd_left, sumEnd_right,
      horth _ (A a).2 _ b'.2, horth _ a.2 _ (A' b').2, bform_orth' horth (A' a') b,
      bform_orth' horth a' (A b)]
    linear_combination h1 + h2
  · obtain ⟨a, a', rfl⟩ := exists_add_of_isCompl h v
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
theorem restrict_mem_soCent (hXU : Set.MapsTo X U U) {M : Module.End K V} (hM : M ∈ soCent Q X)
    (hMU : Set.MapsTo M U U) : M.restrict hMU ∈ soCent (Q.comp U.subtype) (X.restrict hXU) := by
  rw [mem_soCent] at hM ⊢
  refine ⟨fun u w => by rw [bform_comp_subtype, bform_comp_subtype]; exact hM.1 u w,
    LinearMap.ext fun u => ?_⟩
  exact Subtype.ext (congrArg (fun F : Module.End K V => F u) hM.2)

/-- A skew endomorphism preserving `U` preserves the orthogonal complement `U'`. -/
theorem mapsTo_right_of_skew (hQ : IsNondeg Q) (h : IsCompl U U') {M : Module.End K V}
    (hM : ∀ u w, bform Q (M u) w = -bform Q u (M w)) (hMU : Set.MapsTo M U U) :
    Set.MapsTo M U' U' := by
  intro w hw
  obtain ⟨a, a', e⟩ := exists_add_of_isCompl h (M w)
  suffices ha : (a : V) = 0 by rw [← e, ha, zero_add]; exact a'.2
  refine hQ.1 _ fun v => ?_
  obtain ⟨b, b', rfl⟩ := exists_add_of_isCompl h v
  have hab : bform Q a b = bform Q (M w) b - bform Q a' b := by
    rw [← e, map_add, LinearMap.add_apply, add_sub_cancel_right]
  rw [map_add, horth _ a.2 _ b'.2, add_zero, hab, hM, bform_orth' horth ⟨w, hw⟩ ⟨_, hMU b.2⟩,
    bform_orth' horth a' b, neg_zero, sub_zero]

/-- **Splitting `so(V)_X` along an orthogonal decomposition** `V = U ⊥ U'` preserved by `X` and by
every element of `so(V)_X`: `dim so(V)_X = dim so(U)_X + dim so(U')_X`. -/
theorem finrank_soCent_eq_add [FiniteDimensional K V] (hQ : IsNondeg Q) (h : IsCompl U U')
    (hXU : Set.MapsTo X U U) (hXU' : Set.MapsTo X U' U')
    (hM : ∀ M ∈ soCent Q X, Set.MapsTo M U U) :
    finrank K (soCent Q X) = finrank K (soCent (Q.comp U.subtype) (X.restrict hXU)) +
      finrank K (soCent (Q.comp U'.subtype) (X.restrict hXU')) := by
  have hM' : ∀ M ∈ soCent Q X, Set.MapsTo M U' U' := fun M hMm =>
    mapsTo_right_of_skew horth hQ h (mem_soCent.1 hMm).1 (hM M hMm)
  let e : soCent Q X ≃ₗ[K] soCent (Q.comp U.subtype) (X.restrict hXU) ×
      soCent (Q.comp U'.subtype) (X.restrict hXU') :=
    { toFun := fun M => (⟨_, restrict_mem_soCent hXU M.2 (hM M M.2)⟩,
        ⟨_, restrict_mem_soCent hXU' M.2 (hM' M M.2)⟩)
      invFun := fun p => ⟨sumEnd h p.1 p.2, sumEnd_mem_soCent horth h hXU hXU' p.1.2 p.2.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun M => by
        refine Subtype.ext (LinearMap.ext fun v => ?_)
        obtain ⟨a, a', rfl⟩ := exists_add_of_isCompl h v
        simp only [map_add, sumEnd_left, sumEnd_right]
        rfl
      right_inv := fun p => by
        refine Prod.ext (Subtype.ext (LinearMap.ext fun u => Subtype.ext ?_))
          (Subtype.ext (LinearMap.ext fun u => Subtype.ext ?_))
        · exact sumEnd_left h _ _ u
        · exact sumEnd_right h _ _ u }
  rw [e.finrank_eq, Module.finrank_prod]

theorem isNondeg_comp_subtype (hQ : IsNondeg Q) (h : IsCompl U U') :
    IsNondeg (Q.comp U.subtype) := by
  rw [isNondeg_iff] at hQ ⊢
  intro x hx
  refine Subtype.ext (hQ _ fun v => ?_)
  obtain ⟨a, a', rfl⟩ := exists_add_of_isCompl h v
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

section Pieces

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {X : Module.End K V}

open IsomCent

/-- An eigenvector of an isometry with eigenvalue `ν`, `ν² ≠ 1`, is isotropic. -/
theorem bform_self_eq_zero_of_eigen (hX : IsIsom (bform Q) X) {x : V} {ν : K} (hν : ν * ν ≠ 1)
    (hx : X x = ν • x) : bform Q x x = 0 := by
  have e := hX x x
  simp only [hx, map_smul, LinearMap.smul_apply, smul_eq_mul] at e
  have e' : (ν * ν - 1) * bform Q x x = 0 := by linear_combination e
  exact (mul_eq_zero.1 e').resolve_left (sub_ne_zero.2 hν)

/-- **A hyperbolic pair of eigenvectors.** If `V` is spanned by `u, w` with `X u = μ u`,
`X w = μ⁻¹ w`, `μ² ≠ 1` and `b(u, w) ≠ 0`, then `so(V)_X` is the line spanned by
`z ↦ b(w, z) u − b(u, z) w` (acting by `b(u,w)` on `u` and `−b(u,w)` on `w`). -/
theorem soCent_eq_span_wedge (hX : IsIsom (bform Q) X) {μ : K} (hμ0 : μ ≠ 0) (hμ : μ * μ ≠ 1)
    {u w : V} (hu : X u = μ • u) (hw : X w = μ⁻¹ • w) (huw : bform Q u w ≠ 0)
    (hspan : Submodule.span K {u, w} = ⊤) :
    soCent Q X = K ∙ wedge (bform Q) u w := by
  have hsym : ∀ x y, bform Q x y = bform Q y x := bform_comm Q
  have hB : (bform Q).IsSymm := ⟨hsym⟩
  have hμi : μ⁻¹ * μ⁻¹ ≠ 1 := by rw [← mul_inv]; exact fun h => hμ (inv_eq_one.1 h)
  have hμμ : μ⁻¹ ≠ μ := fun e => hμ (calc μ * μ = μ * μ⁻¹ := by rw [e]
    _ = 1 := mul_inv_cancel₀ hμ0)
  have huu := bform_self_eq_zero_of_eigen hX hμ hu
  have hww := bform_self_eq_zero_of_eigen hX hμi hw
  have hw0 : w ≠ 0 := fun h => huw (by rw [h, map_zero])
  have hu0 : u ≠ 0 := fun h => huw (by rw [h, map_zero, LinearMap.zero_apply])
  have hmem : ∀ x : V, ∃ a b : K, a • u + b • w = x := fun x =>
    Submodule.mem_span_pair.1 (hspan ▸ Submodule.mem_top)
  -- the eigenspaces of `X` are the lines `K u`, `K w`
  have lineu : ∀ x, X x = μ • x → ∃ t : K, x = t • u := by
    intro x hx
    obtain ⟨a, b, rfl⟩ := hmem x
    simp only [map_add, map_smul, hu, hw] at hx
    have e : (b * (μ⁻¹ - μ)) • w = 0 := by linear_combination (norm := module) hx
    have hb : b = 0 := by
      rcases smul_eq_zero.1 e with h | h
      · exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hμμ)
      · exact absurd h hw0
    exact ⟨a, by rw [hb, zero_smul, add_zero]⟩
  have linew : ∀ x, X x = μ⁻¹ • x → ∃ t : K, x = t • w := by
    intro x hx
    obtain ⟨a, b, rfl⟩ := hmem x
    simp only [map_add, map_smul, hu, hw] at hx
    have e : (a * (μ - μ⁻¹)) • u = 0 := by linear_combination (norm := module) hx
    have ha : a = 0 := by
      rcases smul_eq_zero.1 e with h | h
      · exact (mul_eq_zero.1 h).resolve_right (sub_ne_zero.2 hμμ.symm)
      · exact absurd h hu0
    exact ⟨b, by rw [ha, zero_smul, zero_add]⟩
  have hJ : wedge (bform Q) u w ∈ soCent Q X := mem_soCent.2 ⟨isSkew_wedge hB u w,
    (commute_wedge hB hX (mul_inv_cancel₀ hμ0) (Module.End.mem_eigenspace_iff.2 hu)
      (Module.End.mem_eigenspace_iff.2 hw)).eq.symm⟩
  ext M
  rw [Submodule.mem_span_singleton]
  constructor
  · intro hM
    obtain ⟨hsk, hc⟩ := mem_soCent.1 hM
    have hXM : ∀ x, X (M x) = M (X x) := fun x => (congrArg (fun F : Module.End K V => F x) hc).symm
    obtain ⟨t, ht⟩ := lineu (M u) (by rw [hXM, hu, map_smul])
    obtain ⟨s, hs⟩ := linew (M w) (by rw [hXM, hw, map_smul])
    have hst : (t + s) * bform Q u w = 0 := by
      have := hsk u w
      rw [ht, hs, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at this
      linear_combination this
    have hs' : s = -t := by
      have := (mul_eq_zero.1 hst).resolve_right huw
      linear_combination this
    have hc' : bform Q w u ≠ 0 := by rwa [hsym]
    refine ⟨t / bform Q w u, LinearMap.ext fun x => ?_⟩
    obtain ⟨a, b, rfl⟩ := hmem x
    simp only [LinearMap.smul_apply, map_add, map_smul, wedge_apply, ht, hs, hs', huu, hww,
      hsym u w]
    match_scalars <;> field_simp <;> ring
  · rintro ⟨r, rfl⟩
    exact Submodule.smul_mem _ r hJ

theorem finrank_soCent_pair (hX : IsIsom (bform Q) X) {μ : K} (hμ0 : μ ≠ 0) (hμ : μ * μ ≠ 1)
    {u w : V} (hu : X u = μ • u) (hw : X w = μ⁻¹ • w) (huw : bform Q u w ≠ 0)
    (hspan : Submodule.span K {u, w} = ⊤) : finrank K (soCent Q X) = 1 := by
  rw [soCent_eq_span_wedge hX hμ0 hμ hu hw huw hspan]
  refine finrank_span_singleton fun h => huw ?_
  have := congrArg (fun F : Module.End K V => bform Q (F u) w) h
  simp only [IsomCent.wedge_apply, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, bform_self_eq_zero_of_eigen hX hμ hu, bform_comm Q w u, zero_mul, sub_zero,
    LinearMap.zero_apply, map_zero] at this
  exact mul_self_eq_zero.1 this

/-- In an orthogonal basis, `b(v, e_i) = v_i b(e_i, e_i)`. -/
theorem bform_basis_right {ι : Type*} [Finite ι] {e : Basis ι K V} (he : (bform Q).IsOrthoᵢ e)
    (v : V) (i : ι) : bform Q v (e i) = e.repr v i * bform Q (e i) (e i) := by
  classical
  have := Fintype.ofFinite ι
  conv_lhs => rw [← e.sum_repr v]
  rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single i]
  · rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
  · intro j _ hj
    rw [map_smul, LinearMap.smul_apply, he hj, smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- A skew endomorphism has zero diagonal in an orthogonal basis. -/
theorem repr_skew_self {ι : Type*} [Finite ι] {e : Basis ι K V} (he : (bform Q).IsOrthoᵢ e)
    (hani : ∀ i, bform Q (e i) (e i) ≠ 0) {M : Module.End K V}
    (hsk : ∀ u w, bform Q (M u) w = -bform Q u (M w)) (i : ι) : e.repr (M (e i)) i = 0 := by
  have h1 := hsk (e i) (e i)
  rw [bform_comm Q (e i) (M (e i)), bform_basis_right he] at h1
  have h2 : (2 : K) * e.repr (M (e i)) i * bform Q (e i) (e i) = 0 := by linear_combination h1
  exact (mul_eq_zero.1 ((mul_eq_zero.1 h2).resolve_right (hani i))).resolve_left
    (Invertible.ne_zero 2)

/-- **`dim so(V) = ⌊dim V / 2⌋` for `dim V ≤ 2`.** -/
theorem finrank_soCent_one_of_le_two [FiniteDimensional K V] (hQ : IsNondeg Q)
    (h2 : finrank K V ≤ 2) : finrank K (soCent Q 1) = finrank K V / 2 := by
  obtain ⟨e, he⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm (S := K) Q)
  have hani := LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate he hQ
  generalize finrank K V = n at e he hani h2 ⊢
  have hzero : ∀ M ∈ soCent Q 1, ∀ i, e.repr (M (e i)) i = 0 := fun M hM =>
    repr_skew_self he hani (mem_soCent.1 hM).1
  interval_cases n
  · have : soCent Q 1 = ⊥ := eq_bot_iff.2 fun M _ =>
      (Submodule.mem_bot K).2 (e.ext fun i => i.elim0)
    rw [this, finrank_bot]
  · have : soCent Q 1 = ⊥ := by
      refine eq_bot_iff.2 fun M hM => (Submodule.mem_bot K).2 (e.ext fun i => ?_)
      obtain rfl : i = 0 := Subsingleton.elim _ _
      rw [← e.sum_repr (M (e 0)), Fin.sum_univ_one]
      simp [hzero M hM 0]
    rw [this, finrank_bot]
  · set J := IsomCent.wedge (bform Q) (e 0) (e 1)
    have hJ : J ∈ soCent Q 1 :=
      mem_soCent.2 ⟨IsomCent.isSkew_wedge ⟨bform_comm Q⟩ _ _, by rw [mul_one, one_mul]⟩
    have h01 : bform Q (e 0) (e 1) = 0 := he (by decide)
    have h10 : bform Q (e 1) (e 0) = 0 := he (by decide)
    have hJ0 : J (e 0) = -bform Q (e 0) (e 0) • e 1 := by
      simp [J, IsomCent.wedge_apply, h10]
    have hJ1 : J (e 1) = bform Q (e 1) (e 1) • e 0 := by
      simp [J, IsomCent.wedge_apply, h01]
    have hJne : J ≠ 0 := fun h => by
      have := congrArg (fun F : Module.End K V => e.repr (F (e 0)) 1) h
      simp [hJ0, hani 0] at this
    have : soCent Q 1 = K ∙ J := by
      ext M
      rw [Submodule.mem_span_singleton]
      constructor
      · intro hM
        have hsk := (mem_soCent.1 hM).1
        obtain ⟨q, hM0⟩ : ∃ q : K, M (e 0) = q • e 1 := ⟨e.repr (M (e 0)) 1, by
          rw [← e.sum_repr (M (e 0)), Fin.sum_univ_two]
          simp [hzero M hM 0]⟩
        obtain ⟨p, hM1⟩ : ∃ p : K, M (e 1) = p • e 0 := ⟨e.repr (M (e 1)) 0, by
          rw [← e.sum_repr (M (e 1)), Fin.sum_univ_two]
          simp [hzero M hM 1]⟩
        have hk := hsk (e 0) (e 1)
        rw [hM0, hM1, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at hk
        refine ⟨-q / bform Q (e 0) (e 0), e.ext fun i => ?_⟩
        fin_cases i
        · simp only [Fin.zero_eta, Fin.isValue, LinearMap.smul_apply, hJ0, smul_smul]
          rw [hM0]
          congr 1
          field_simp [hani 0]
        · simp only [Fin.mk_one, Fin.isValue, LinearMap.smul_apply, hJ1, smul_smul]
          rw [hM1]
          congr 1
          field_simp [hani 0]
          linear_combination -hk
      · rintro ⟨r, rfl⟩
        exact Submodule.smul_mem _ r hJ
    rw [this, finrank_span_singleton hJne]

/-- If `so(V)` is abelian, `dim V ≤ 2`. -/
theorem finrank_le_two_of_commute [CharZero K] [IsAlgClosed K] [FiniteDimensional K V]
    (hQ : IsNondeg Q) (hab : ∀ M₁ ∈ soCent Q 1, ∀ M₂ ∈ soCent Q 1, Commute M₁ M₂) :
    finrank K V ≤ 2 := by
  have hB : (bform Q).IsSymm := ⟨bform_comm Q⟩
  have h := IsomCent.finrank_eigenspace_neg_one_le_two (B := bform Q) hB hQ (X := -1)
    (fun u v => by simp [LinearMap.neg_apply])
    (Module.End.isSemisimple_neg.2 Module.End.isSemisimple_id)
    (fun Y₁ Y₂ h₁ h₂ _ _ _ _ => hab Y₁ (mem_soCent.2 ⟨h₁, by simp⟩) Y₂ (mem_soCent.2 ⟨h₂, by simp⟩))
  have : (-1 : Module.End K V).eigenspace (-1) = ⊤ := by
    ext x; simp
  rwa [this, finrank_top] at h

/-- `so(V)_X = so(V)` when `X` is a scalar. -/
theorem soCent_of_scalar {c : K} (hX : ∀ v, X v = c • v) : soCent Q X = soCent Q 1 := by
  have : X = c • (1 : Module.End K V) := LinearMap.ext fun v => by simp [hX]
  ext M
  simp only [mem_soCent, this, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]

omit [Invertible (2 : K)] in
theorem exists_smul_of_finrank_le_one [FiniteDimensional K V] {E : Submodule K V}
    (h : finrank K E ≤ 1) {u x : V} (hu : u ∈ E) (hu0 : u ≠ 0) (hx : x ∈ E) :
    ∃ c : K, x = c • u := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.1 h
  obtain ⟨a, ha⟩ := hv ⟨u, hu⟩
  obtain ⟨b, hb⟩ := hv ⟨x, hx⟩
  have e1 : a • (v : V) = u := congrArg Subtype.val ha
  have e2 : b • (v : V) = x := congrArg Subtype.val hb
  have ha0 : a ≠ 0 := by rintro rfl; exact hu0 (by rw [← e1, zero_smul])
  exact ⟨b / a, by rw [← e1, ← e2, smul_smul, div_mul_cancel₀ _ ha0]⟩

omit [Invertible (2 : K)] in
/-- If `E_c(X) ≤ U`, restricting `X` to `U` does not change `dim E_c`. -/
theorem finrank_eigenspace_restrict {U : Submodule K V} (hXU : Set.MapsTo X U U) (c : K)
    (hle : X.eigenspace c ≤ U) :
    finrank K (Module.End.eigenspace (X.restrict hXU) c) = finrank K (X.eigenspace c) := by
  have : Module.End.eigenspace (X.restrict hXU) c = (X.eigenspace c).comap U.subtype := by
    ext x
    simp only [Module.End.mem_eigenspace_iff, Submodule.mem_comap, Submodule.subtype_apply,
      Subtype.ext_iff, Submodule.coe_smul]
    rfl
  rw [this]
  exact (Submodule.comapSubtypeEquivOfLe hle).finrank_eq

end Pieces

section Main

universe u

variable {K : Type*} [Field K] [Invertible (2 : K)] [CharZero K] [IsAlgClosed K]

open IsomCent

theorem finrank_soCent_aux (n : ℕ) : ∀ {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (X : Module.End K V), finrank K V = n →
    IsNondeg Q → IsIsom (bform Q) X → X.IsSemisimple → Even (finrank K (X.eigenspace (-1))) →
    (∀ M₁ ∈ soCent Q X, ∀ M₂ ∈ soCent Q X, Commute M₁ M₂) → finrank K (soCent Q X) = n / 2 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ Q X hn hQ hX hss hev hab
  have hB : (bform Q).IsSymm := ⟨bform_comm Q⟩
  have hL : LieAbelian (bform Q) X := fun Y₁ Y₂ h₁ h₂ c₁ c₂ _ _ =>
    hab Y₁ (mem_soCent.2 ⟨h₁, c₁.eq.symm⟩) Y₂ (mem_soCent.2 ⟨h₂, c₂.eq.symm⟩)
  have hcM : ∀ M ∈ soCent Q X, Commute X M := fun M hM => (mem_soCent.1 hM).2.symm
  by_cases hA : ∃ μ, X.HasEigenvalue μ ∧ μ * μ ≠ 1
  · -- split off `U = span {u, w}`, `u ∈ E_μ`, `w ∈ E_{μ⁻¹}`, `μ ≠ ±1`
    obtain ⟨μ, hμ, hμ1⟩ := hA
    have hμ0 : μ ≠ 0 := ne_zero_of_hasEigenvalue (B := bform Q) hQ hX hμ
    have hμ1' : μ ≠ 1 := fun h => hμ1 (by rw [h, one_mul])
    have hμm : μ ≠ -1 := fun h => hμ1 (by rw [h]; norm_num)
    have hμi : μ⁻¹ * μ⁻¹ ≠ 1 := by rw [← mul_inv]; exact fun h => hμ1 (inv_eq_one.1 h)
    have hμi1 : μ⁻¹ ≠ 1 := fun h => hμ1' (inv_eq_one.1 h)
    obtain ⟨u, hu, hu0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (Module.End.hasEigenvalue_iff.1 hμ)
    obtain ⟨w, hw, huw⟩ := exists_eigen_pair_ne_zero (B := bform Q) hQ hX hss hu hu0
    have hu' : X u = μ • u := Module.End.mem_eigenspace_iff.1 hu
    have hw' : X w = μ⁻¹ • w := Module.End.mem_eigenspace_iff.1 hw
    have huu := bform_self_eq_zero_of_eigen hX hμ1 hu'
    have hww := bform_self_eq_zero_of_eigen hX hμi hw'
    have hwu : bform Q w u ≠ 0 := by rwa [bform_comm]
    set U := Submodule.span K {u, w}
    set U' := (bform Q).orthogonal U
    have horth : ∀ x ∈ U, ∀ y ∈ U', bform Q x y = 0 := fun x hx y hy =>
      (LinearMap.BilinForm.mem_orthogonal_iff.1 hy) x hx
    have horth' : ∀ y ∈ U', ∀ x ∈ U, bform Q y x = 0 := fun y hy x hx =>
      bform_orth' horth ⟨y, hy⟩ ⟨x, hx⟩
    have huU : u ∈ U := Submodule.subset_span (by simp)
    have hwU : w ∈ U := Submodule.subset_span (by simp)
    have hdisj : Disjoint U U' := by
      rw [Submodule.disjoint_def]
      intro x hx hx'
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
      have h1 := horth u huU _ hx'
      have h2 := horth w hwU _ hx'
      simp only [map_add, map_smul, smul_eq_mul, huu, hww, mul_zero, zero_add, add_zero] at h1 h2
      rw [(mul_eq_zero.1 h1).resolve_right huw, (mul_eq_zero.1 h2).resolve_right hwu, zero_smul,
        zero_smul, add_zero]
    have hcompl : IsCompl U U' :=
      LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl
        (LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal _ hB.isRefl hdisj)
    have hXU : Set.MapsTo X U U := by
      intro x hx
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
      exact Submodule.mem_span_pair.2 ⟨a * μ, b * μ⁻¹, by simp [hu', hw', smul_smul]⟩
    have hXU' : Set.MapsTo X U' U' := by
      intro y hy
      refine LinearMap.BilinForm.mem_orthogonal_iff.2 fun x hx => ?_
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
      have hx' : a • u + b • w = X ((a * μ⁻¹) • u + (b * μ) • w) := by
        simp only [map_add, map_smul, hu', hw', smul_smul]
        rw [mul_assoc, inv_mul_cancel₀ hμ0, mul_assoc, mul_inv_cancel₀ hμ0, mul_one, mul_one]
      change bform Q _ _ = 0
      rw [hx', hX]
      exact horth _ (Submodule.mem_span_pair.2 ⟨_, _, rfl⟩) _ hy
    have hM : ∀ M ∈ soCent Q X, Set.MapsTo M U U := by
      intro M hM' x hx
      have hc := hcM M hM'
      obtain ⟨c, hc1⟩ := exists_smul_of_finrank_le_one
        (finrank_eigenspace_le_one (B := bform Q) hB hQ hX hss hL hμ1' hμ1) hu hu0
        (mapsTo_eigenspace_of_commute hc μ u hu)
      have hw0 : w ≠ 0 := fun h => huw (by rw [h, map_zero])
      obtain ⟨d, hd1⟩ := exists_smul_of_finrank_le_one
        (finrank_eigenspace_le_one (B := bform Q) hB hQ hX hss hL hμi1 hμi) hw hw0
        (mapsTo_eigenspace_of_commute hc μ⁻¹ w hw)
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
      exact Submodule.mem_span_pair.2 ⟨a * c, b * d, by simp [hc1, hd1, smul_smul]⟩
    -- the summand `U`
    have hU1 : finrank K (soCent (Q.comp U.subtype) (X.restrict hXU)) = 1 := by
      refine finrank_soCent_pair (u := ⟨u, huU⟩) (w := ⟨w, hwU⟩) (μ := μ)
        (fun x y => by simp only [bform_comp_subtype]; exact hX x y) hμ0 hμ1
        (Subtype.ext hu') (Subtype.ext hw') (by rw [bform_comp_subtype]; exact huw) ?_
      rw [eq_top_iff]
      rintro ⟨x, hx⟩ -
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
      exact Submodule.mem_span_pair.2 ⟨a, b, rfl⟩
    have hU2 : finrank K U = 2 := by
      have hli : LinearIndependent K ![u, w] := LinearIndependent.pair_iff.2 fun s t hst => by
        have h1 := congrArg (bform Q u) hst
        have h2 := congrArg (bform Q w) hst
        exact ⟨by simpa [huu, hww, hwu] using h2, by simpa [huu, hww, huw] using h1⟩
      have := finrank_span_eq_card hli
      rwa [Matrix.range_cons_cons_empty u w ![], Fintype.card_fin] at this
    -- the summand `U'`, by induction
    have hd := Submodule.finrank_add_eq_of_isCompl hcompl
    have hev' : Even (finrank K (Module.End.eigenspace (X.restrict hXU') (-1))) := by
      rw [finrank_eigenspace_restrict hXU' (-1) fun z hz =>
        LinearMap.BilinForm.mem_orthogonal_iff.2 fun x hx => ?_]
      · exact hev
      obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hx
      change bform Q _ _ = 0
      rw [map_add, map_smul, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.smul_apply, bform_eigen_eq_zero (B := bform Q) hX (by
          rw [mul_neg_one]; exact fun h => hμm (neg_eq_iff_eq_neg.1 h)) hu hz,
        bform_eigen_eq_zero (B := bform Q) hX (by
          rw [mul_neg_one]
          exact fun h => hμm (by rw [← inv_inv μ, neg_eq_iff_eq_neg.1 h, inv_neg, inv_one])) hw hz,
        smul_zero, smul_zero, add_zero]
    have hrec := ih (finrank K U') (by omega) (Q.comp U'.subtype) (X.restrict hXU') rfl
      (isNondeg_comp_subtype horth' hQ hcompl.symm)
      (fun x y => by simp only [bform_comp_subtype]; exact hX x y)
      (hss.restrict ((Module.End.mem_invtSubmodule _).2 hXU')) hev'
      (commute_of_restrict horth' hcompl.symm hXU' hXU hab)
    rw [finrank_soCent_eq_add horth hQ hcompl hXU hXU' hM, hU1, hrec]
    omega
  · -- all eigenvalues are `±1`: `V = E₁ ⊥ E₋₁`
    push Not at hA
    set E₁ := X.eigenspace 1
    set E₂ := X.eigenspace (-1)
    have horth : ∀ x ∈ E₁, ∀ y ∈ E₂, bform Q x y = 0 := fun x hx y hy =>
      bform_eigen_eq_zero (B := bform Q) hX (by norm_num) hx hy
    have horth' : ∀ y ∈ E₂, ∀ x ∈ E₁, bform Q y x = 0 := fun y hy x hx =>
      bform_orth' horth ⟨y, hy⟩ ⟨x, hx⟩
    have hcompl : IsCompl E₁ E₂ := by
      constructor
      · rw [Submodule.disjoint_def]
        intro x h1 h2
        have h : (1 : K) • x = (-1 : K) • x :=
          (Module.End.mem_eigenspace_iff.1 h1).symm.trans (Module.End.mem_eigenspace_iff.1 h2)
        have h' : (2 : K) • x = 0 := by linear_combination (norm := module) h
        exact (smul_eq_zero.1 h').resolve_left two_ne_zero
      · rw [codisjoint_iff, eq_top_iff, ← hss.iSup_eigenspace_eq_top]
        refine iSup_le fun ν => ?_
        by_cases hν : X.HasEigenvalue ν
        · rcases mul_self_eq_one_iff.1 (hA ν hν) with rfl | rfl
          · exact le_sup_left
          · exact le_sup_right
        · rw [Module.End.hasEigenvalue_iff, not_not] at hν
          rw [hν]
          exact bot_le
    have hX1 : Set.MapsTo X E₁ E₁ := mapsTo_eigenspace_of_commute (Commute.refl X) 1
    have hX2 : Set.MapsTo X E₂ E₂ := mapsTo_eigenspace_of_commute (Commute.refl X) (-1)
    have hM : ∀ M ∈ soCent Q X, Set.MapsTo M E₁ E₁ := fun M hM' =>
      mapsTo_eigenspace_of_commute (hcM M hM') 1
    have hs1 : soCent (Q.comp E₁.subtype) (X.restrict hX1) = soCent (Q.comp E₁.subtype) 1 :=
      soCent_of_scalar (c := 1) fun v => Subtype.ext (Module.End.mem_eigenspace_iff.1 v.2)
    have hs2 : soCent (Q.comp E₂.subtype) (X.restrict hX2) = soCent (Q.comp E₂.subtype) 1 :=
      soCent_of_scalar (c := -1) fun v => Subtype.ext (Module.End.mem_eigenspace_iff.1 v.2)
    have hab1 := commute_of_restrict horth hcompl hX1 hX2 hab
    have hab2 := commute_of_restrict horth' hcompl.symm hX2 hX1 hab
    rw [hs1] at hab1
    rw [hs2] at hab2
    have hQ1 := isNondeg_comp_subtype horth hQ hcompl
    have hQ2 := isNondeg_comp_subtype horth' hQ hcompl.symm
    have hd := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [finrank_soCent_eq_add horth hQ hcompl hX1 hX2 hM, hs1, hs2,
      finrank_soCent_one_of_le_two hQ1 (finrank_le_two_of_commute hQ1 hab1),
      finrank_soCent_one_of_le_two hQ2 (finrank_le_two_of_commute hQ2 hab2)]
    obtain ⟨k, hk⟩ := hev
    omega

/-- **`dim so(V)_X = ⌊dim V / 2⌋` for a regular semisimple isometry.** Over an algebraically closed
field of characteristic `0`, if `X` is a semisimple isometry of the nondegenerate form `Q` with
`det X = 1` and `so(V)_X` is abelian, then `dim so(V)_X = ⌊dim V / 2⌋`. -/
theorem finrank_soCent_of_commute {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {X : Module.End K V} (hQ : IsNondeg Q)
    (hX : IsIsom (bform Q) X) (hss : X.IsSemisimple) (hdet : LinearMap.det X = 1)
    (hab : ∀ M₁ ∈ soCent Q X, ∀ M₂ ∈ soCent Q X, Commute M₁ M₂) :
    finrank K (soCent Q X) = finrank K V / 2 := by
  have hB : (bform Q).IsSymm := ⟨bform_comm Q⟩
  have hL : LieAbelian (bform Q) X := fun Y₁ Y₂ h₁ h₂ c₁ c₂ _ _ =>
    hab Y₁ (mem_soCent.2 ⟨h₁, c₁.eq.symm⟩) Y₂ (mem_soCent.2 ⟨h₂, c₂.eq.symm⟩)
  have hd := det_restrict_neg_one (B := bform Q) hB hQ hX hss hL hX hdet (Commute.refl X)
    fun z hz => by rw [Module.End.mem_eigenspace_iff.1 hz, one_smul]
  have hneg : X.restrict (mapsTo_eigenspace_of_commute (Commute.refl X) (-1)) =
      (-1 : K) • LinearMap.id :=
    LinearMap.ext fun z => Subtype.ext (Module.End.mem_eigenspace_iff.1 z.2)
  rw [hneg, LinearMap.det_smul, LinearMap.det_id, mul_one] at hd
  exact finrank_soCent_aux _ Q X rfl hQ hX hss
    ((neg_one_pow_eq_one_iff_even (by norm_num)).1 hd) hab

end Main

end GSpinGGP
