/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.Descent

/-!
# Classification arguments for quadratic spaces (the GGP case of Thesis (6.1.1))

Own work, from the cited classical results of `Literature/GSpin.lean` only (Witt cancellation,
Witt decomposition, the classification of quadratic forms over `p`-adic fields).

* Discriminants in bases (`gdet`, `DiscRel`): change of basis, isometries and orthogonal sums;
  `SameDisc` is `DiscRel` in the standard basis.
* Witt indices: attained, isometry-invariant, superadditive on orthogonal sums
  (`wittIndex_prod_ge`); adding a split space keeps quasi-splitness.
* `nonempty_isometryEquiv_of_odd`: odd-dimensional quasi-split forms are determined by their
  discriminant (`H^w ⊥ ⟨a⟩`).
* `nonempty_isometryEquiv_of_quasiSplit`: a quasi-split inner form of a quasi-split GGP datum is
  trivial.
* `finrank_movedSub_ne_one`: `dim W''_y ≠ 1` (else `det P(y) ≠ 1`).
* `exists_isometry_fixedSub`: `W'_y` embeds in `W`, the GGP case of Thesis (6.1.1), proved
  here by the classification of quadratic forms instead of Kottwitz's theorem.  The cases
  `W''_y = 0` and `W''_y` a hyperbolic plane are handled by the quasi-split hypotheses alone; no
  anisotropy of `W''_y` is used.
-/

noncomputable section
open scoped Classical
open Module Matrix
set_option linter.unusedSectionVars false

namespace GSpinGGP
namespace QuadClassify

variable {K : Type*} [Field K] [Invertible (2 : K)]

section Disc

variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁]
  [AddCommGroup V₂] [Module K V₂]

/-- The Gram determinant of `Q` in a basis. -/
def gdet {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : QuadraticForm K V) (b : Basis ι K V) : K :=
  (QuadraticForm.toMatrix b Q).det

theorem gdet_reindex {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (Q : QuadraticForm K V) (b : Basis ι K V) (e : ι ≃ ι') :
    gdet Q (b.reindex e) = gdet Q b := by
  unfold gdet
  have : QuadraticForm.toMatrix (b.reindex e) Q = Matrix.reindex e e (QuadraticForm.toMatrix b Q) := by
    ext i j
    simp [QuadraticForm.toMatrix, LinearMap.toMatrix₂_apply, Basis.reindex_apply]
  rw [this, Matrix.det_reindex_self]

theorem gdet_change {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : QuadraticForm K V)
    (b b' : Basis ι K V) : gdet Q b' = (b.toMatrix b').det ^ 2 * gdet Q b := by
  unfold gdet QuadraticForm.toMatrix
  rw [← LinearMap.toMatrix₂_mul_basis_toMatrix b b b' b', Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose]
  ring

theorem det_basis_toMatrix_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (b b' : Basis ι K V) :
    (b.toMatrix b').det ≠ 0 := by
  intro h
  have := congrArg Matrix.det (Basis.toMatrix_mul_toMatrix_flip b b')
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

/-- Two forms have the same discriminant (in `K^×/K^×²`), compared in bases with the same index
type. -/
def DiscRel (Q₁ : QuadraticForm K V₁) (Q₂ : QuadraticForm K V₂) : Prop :=
  ∃ (n : ℕ) (b₁ : Basis (Fin n) K V₁) (b₂ : Basis (Fin n) K V₂) (c : K), c ≠ 0 ∧
    gdet Q₂ b₂ = c ^ 2 * gdet Q₁ b₁

/-- `DiscRel` holds in *any* pair of bases (with a common index type). -/
theorem DiscRel.bases {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (h : DiscRel Q₁ Q₂)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b₁' : Basis ι K V₁) (b₂' : Basis ι K V₂) :
    ∃ c : K, c ≠ 0 ∧ gdet Q₂ b₂' = c ^ 2 * gdet Q₁ b₁' := by
  obtain ⟨n, b₁, b₂, c, hc, h⟩ := h
  set B₁ := b₁.reindex (b₁.indexEquiv b₁')
  set B₂ := b₂.reindex (b₂.indexEquiv b₂')
  have h1 := gdet_change Q₁ B₁ b₁'
  have h2 := gdet_change Q₂ B₂ b₂'
  rw [gdet_reindex] at h1 h2
  have d1 := det_basis_toMatrix_ne_zero B₁ b₁'
  have d2 := det_basis_toMatrix_ne_zero B₂ b₂'
  have hne : (B₂.toMatrix b₂').det * c / (B₁.toMatrix b₁').det ≠ 0 :=
    div_ne_zero (mul_ne_zero d2 hc) d1
  refine ⟨(B₂.toMatrix b₂').det * c / (B₁.toMatrix b₁').det, hne, ?_⟩
  rw [h2, h1, h]
  field_simp

theorem DiscRel.refl' (Q : QuadraticForm K V) [FiniteDimensional K V] : DiscRel Q Q :=
  ⟨_, Module.finBasis K V, Module.finBasis K V, 1, one_ne_zero, by ring⟩

theorem DiscRel.symm {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (h : DiscRel Q₁ Q₂) :
    DiscRel Q₂ Q₁ := by
  obtain ⟨n, b₁, b₂, c, hc, h⟩ := h
  exact ⟨n, b₂, b₁, c⁻¹, inv_ne_zero hc, by rw [h]; field_simp⟩

theorem DiscRel.trans {V₃ : Type*} [AddCommGroup V₃] [Module K V₃] {Q₁ : QuadraticForm K V₁}
    {Q₂ : QuadraticForm K V₂} {Q₃ : QuadraticForm K V₃} (h₁ : DiscRel Q₁ Q₂)
    (h₂ : DiscRel Q₂ Q₃) : DiscRel Q₁ Q₃ := by
  obtain ⟨n, b₁, b₂, c, hc, h⟩ := h₁
  obtain ⟨n', b₂', b₃, c', hc', h'⟩ := h₂
  set B₃ := b₃.reindex (b₂'.indexEquiv b₂)
  obtain ⟨c'', hc'', h''⟩ := DiscRel.bases ⟨n', b₂', b₃, c', hc', h'⟩ b₂ B₃
  exact ⟨n, b₁, B₃, c'' * c, mul_ne_zero hc'' hc, by rw [h'', h]; ring⟩

/-- Isometric forms have the same discriminant. -/
theorem gdet_map_isometry {ι : Type*} [Fintype ι] [DecidableEq ι] {Q₁ : QuadraticForm K V₁}
    {Q₂ : QuadraticForm K V₂} (e : Q₁.IsometryEquiv Q₂) (b : Basis ι K V₁) :
    gdet Q₂ (b.map e.toLinearEquiv) = gdet Q₁ b := by
  unfold gdet
  congr 1
  ext i j
  simp only [QuadraticForm.toMatrix, LinearMap.toMatrix₂_apply, Basis.map_apply]
  have : Q₂.comp e.toLinearEquiv.toLinearMap = Q₁ := by ext v; exact e.map_app v
  have h2 := congrArg (fun q : QuadraticForm K V₁ => QuadraticMap.associated (R := K) q (b i) (b j))
    this
  simp only [QuadraticMap.associated_comp] at h2
  exact h2

theorem DiscRel.of_isometryEquiv [FiniteDimensional K V₁] {Q₁ : QuadraticForm K V₁}
    {Q₂ : QuadraticForm K V₂} (e : Q₁.IsometryEquiv Q₂) : DiscRel Q₁ Q₂ :=
  ⟨_, Module.finBasis K V₁, (Module.finBasis K V₁).map e.toLinearEquiv, 1, one_ne_zero, by
    rw [gdet_map_isometry]; ring⟩

/-- The Gram determinant of an orthogonal sum is the product. -/
theorem gdet_prod {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (Q₁ : QuadraticForm K V₁) (Q₂ : QuadraticForm K V₂) (b₁ : Basis ι₁ K V₁)
    (b₂ : Basis ι₂ K V₂) : gdet (Q₁.prod Q₂) (b₁.prod b₂) = gdet Q₁ b₁ * gdet Q₂ b₂ := by
  unfold gdet
  have : QuadraticForm.toMatrix (b₁.prod b₂) (Q₁.prod Q₂) =
      Matrix.fromBlocks (QuadraticForm.toMatrix b₁ Q₁) 0 0 (QuadraticForm.toMatrix b₂ Q₂) := by
    ext (i | i) (j | j) <;>
      simp [QuadraticForm.toMatrix, LinearMap.toMatrix₂_apply]
  rw [this, Matrix.det_fromBlocks_zero₂₁]

theorem DiscRel.prod {V₃ V₄ : Type*} [AddCommGroup V₃] [Module K V₃] [AddCommGroup V₄]
    [Module K V₄] [FiniteDimensional K V₁] [FiniteDimensional K V₂]
    {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} {Q₃ : QuadraticForm K V₃}
    {Q₄ : QuadraticForm K V₄} (h₁ : DiscRel Q₁ Q₃) (h₂ : DiscRel Q₂ Q₄) :
    DiscRel (Q₁.prod Q₂) (Q₃.prod Q₄) := by
  obtain ⟨n, b₁, b₃, c, hc, h⟩ := h₁
  obtain ⟨n', b₂, b₄, c', hc', h'⟩ := h₂
  set e := finSumFinEquiv (m := n) (n := n')
  refine ⟨n + n', (b₁.prod b₂).reindex e, (b₃.prod b₄).reindex e, c * c', mul_ne_zero hc hc', ?_⟩
  rw [gdet_reindex, gdet_reindex, gdet_prod, gdet_prod, h, h']
  ring

/-- `SameDisc` is `DiscRel` for forms on `K^m`. -/
theorem sameDisc_iff_discRel {m : ℕ} (Q Q' : QuadraticForm K (Fin m → K)) :
    SameDisc Q Q' ↔ DiscRel Q Q' := by
  have hb : ∀ q : QuadraticForm K (Fin m → K), gdet q (Pi.basisFun K (Fin m)) = q.discr' := by
    intro q
    rw [gdet, QuadraticForm.toMatrix_eq_toMatrix']
    rfl
  constructor
  · rintro ⟨c, hc, h⟩
    exact ⟨m, Pi.basisFun K (Fin m), Pi.basisFun K (Fin m), c, hc, by rw [hb, hb, h]⟩
  · intro h
    obtain ⟨c, hc, h⟩ := h.bases (Pi.basisFun K (Fin m)) (Pi.basisFun K (Fin m))
    rw [hb, hb] at h
    exact ⟨c, hc, h⟩

/-- Nondegeneracy in terms of a Gram determinant. -/
theorem isNondeg_iff_gdet_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : QuadraticForm K V)
    (b : Basis ι K V) : IsNondeg Q ↔ gdet Q b ≠ 0 := by
  rw [IsNondeg, LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b]
  rfl

theorem DiscRel.isNondeg {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (h : DiscRel Q₁ Q₂) (h₁ : IsNondeg Q₁) : IsNondeg Q₂ := by
  obtain ⟨n, b₁, b₂, c, hc, h⟩ := h
  rw [isNondeg_iff_gdet_ne_zero _ b₁] at h₁
  rw [isNondeg_iff_gdet_ne_zero _ b₂, h]
  exact mul_ne_zero (pow_ne_zero 2 hc) h₁

end Disc


section Witt

variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁]
  [AddCommGroup V₂] [Module K V₂]

theorem wittIndex_bdd [FiniteDimensional K V] (Q : QuadraticForm K V) :
    BddAbove {n | ∃ U : Submodule K V, IsTotallyIsotropic Q U ∧ finrank K U = n} :=
  ⟨finrank K V, by rintro _ ⟨U, -, rfl⟩; exact Submodule.finrank_le U⟩

theorem le_wittIndex [FiniteDimensional K V] {Q : QuadraticForm K V} {U : Submodule K V}
    (hU : IsTotallyIsotropic Q U) : finrank K U ≤ wittIndex Q :=
  le_csSup (wittIndex_bdd Q) ⟨U, hU, rfl⟩

theorem exists_wittIndex [FiniteDimensional K V] (Q : QuadraticForm K V) :
    ∃ U : Submodule K V, IsTotallyIsotropic Q U ∧ finrank K U = wittIndex Q := by
  have hne : ({n | ∃ U : Submodule K V, IsTotallyIsotropic Q U ∧ finrank K U = n} : Set ℕ).Nonempty :=
    ⟨0, ⊥, fun u hu => by rw [(Submodule.mem_bot K).1 hu, map_zero], finrank_bot K V⟩
  exact Nat.sSup_mem hne (wittIndex_bdd Q)

/-- `w(Q₁ ⊥ Q₂) ≥ w(Q₁) + w(Q₂)`. -/
theorem wittIndex_prod_ge [FiniteDimensional K V₁] [FiniteDimensional K V₂]
    (Q₁ : QuadraticForm K V₁) (Q₂ : QuadraticForm K V₂) :
    wittIndex Q₁ + wittIndex Q₂ ≤ wittIndex (Q₁.prod Q₂) := by
  obtain ⟨U₁, h₁, e₁⟩ := exists_wittIndex Q₁
  obtain ⟨U₂, h₂, e₂⟩ := exists_wittIndex Q₂
  set f : (U₁ × U₂) →ₗ[K] (V₁ × V₂) := U₁.subtype.prodMap U₂.subtype
  have hf : Function.Injective f := fun a b h => by
    simp only [f, LinearMap.prodMap_apply, Submodule.coe_subtype, Prod.mk.injEq] at h
    exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
  have hiso : IsTotallyIsotropic (Q₁.prod Q₂) (LinearMap.range f) := by
    rintro _ ⟨⟨a, b⟩, rfl⟩
    simp [f, QuadraticMap.prod_apply, h₁ _ a.2, h₂ _ b.2]
  have := le_wittIndex hiso
  rwa [LinearMap.finrank_range_of_inj hf, Module.finrank_prod, e₁, e₂] at this

/-- Adding a split even-dimensional space keeps quasi-splitness. -/
theorem isQuasiSplitQF_prod [FiniteDimensional K V₁] [FiniteDimensional K V₂]
    {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (h₁ : IsQuasiSplitQF Q₁)
    (h₂ : finrank K V₂ ≤ 2 * wittIndex Q₂) : IsQuasiSplitQF (Q₁.prod Q₂) := by
  unfold IsQuasiSplitQF at h₁ ⊢
  rw [Module.finrank_prod]
  have := wittIndex_prod_ge Q₁ Q₂
  omega

end Witt

section Odd

variable {V₁ V₂ : Type*} [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]

theorem finrank_eq_of_discRel {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    (h : DiscRel Q₁ Q₂) : finrank K V₁ = finrank K V₂ := by
  obtain ⟨n, b₁, b₂, -⟩ := h
  rw [Module.finrank_eq_card_basis b₁, Module.finrank_eq_card_basis b₂]

/-- A form on `K¹` is `v ↦ Q(e₀) v₀²`. -/
theorem apply_fin_one (Q : QuadraticForm K (Fin 1 → K)) (v : Fin 1 → K) :
    Q v = v 0 * v 0 * Q (Pi.single 0 1) := by
  have : v = v 0 • (Pi.single 0 1 : Fin 1 → K) := by
    ext i; fin_cases i; simp
  conv_lhs => rw [this]
  rw [QuadraticMap.map_smul, smul_eq_mul]

theorem gdet_fin_one (Q : QuadraticForm K (Fin 1 → K)) :
    gdet Q (Pi.basisFun K (Fin 1)) = Q (Pi.single 0 1) := by
  rw [gdet, Matrix.det_unique, QuadraticForm.toMatrix, LinearMap.toMatrix₂_apply]
  simp [QuadraticMap.associated_eq_self_apply]

/-- **Odd-dimensional quasi-split forms are determined by their discriminant** (own work, from
the Witt decomposition `witt_decomposition`): if `Q₁, Q₂` are nondegenerate of the same odd
dimension `2w+1` and both quasi-split, then `Q_i ≅ H^w ⊥ ⟨a_i⟩`, and equal discriminants force
`a₂ = c² a₁`. -/
theorem nonempty_isometryEquiv_of_odd [FiniteDimensional K V₁] [FiniteDimensional K V₂]
    {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (h₁ : IsNondeg Q₁) (h₂ : IsNondeg Q₂)
    (hodd : Odd (finrank K V₁)) (hq₁ : IsQuasiSplitQF Q₁) (hq₂ : IsQuasiSplitQF Q₂)
    (hd : DiscRel Q₁ Q₂) : Nonempty (Q₁.IsometryEquiv Q₂) := by
  have hdim := finrank_eq_of_discRel hd
  obtain ⟨k₁, Qa₁, -, ⟨I₁⟩, hk₁⟩ := witt_decomposition Q₁ h₁
  obtain ⟨k₂, Qa₂, -, ⟨I₂⟩, hk₂⟩ := witt_decomposition Q₂ h₂
  unfold IsQuasiSplitQF at hq₁ hq₂
  obtain ⟨t, ht⟩ := hodd
  have hk₁1 : k₁ = 1 := by omega
  have hk₂1 : k₂ = 1 := by omega
  have hw : wittIndex Q₂ = wittIndex Q₁ := by omega
  subst hk₁1 hk₂1
  rw [hw] at I₂
  set H := hypForm K (wittIndex Q₁)
  have hd' : DiscRel (H.prod Qa₁) (H.prod Qa₂) :=
    ((DiscRel.of_isometryEquiv I₁).symm.trans hd).trans (DiscRel.of_isometryEquiv I₂)
  have hnd : IsNondeg (H.prod Qa₁) := (DiscRel.of_isometryEquiv I₁).isNondeg h₁
  obtain ⟨c, hc, hcd⟩ := hd'.bases ((Pi.basisFun K _).prod (Pi.basisFun K (Fin 1)))
    ((Pi.basisFun K _).prod (Pi.basisFun K (Fin 1)))
  rw [isNondeg_iff_gdet_ne_zero _ ((Pi.basisFun K _).prod (Pi.basisFun K (Fin 1))),
    gdet_prod] at hnd
  rw [gdet_prod, gdet_prod, gdet_fin_one, gdet_fin_one] at hcd
  have hH : gdet H (Pi.basisFun K (Fin (2 * wittIndex Q₁))) ≠ 0 := left_ne_zero_of_mul hnd
  have ha : Qa₂ (Pi.single 0 1) = c ^ 2 * Qa₁ (Pi.single 0 1) := by
    apply mul_left_cancel₀ hH
    rw [hcd]; ring
  let e : (Fin 1 → K) ≃ₗ[K] (Fin 1 → K) := LinearEquiv.smulOfUnit (Units.mk0 c⁻¹ (inv_ne_zero hc))
  have he : ∀ v, Qa₂ (e v) = Qa₁ v := by
    intro v
    show Qa₂ (c⁻¹ • v) = _
    rw [QuadraticMap.map_smul, apply_fin_one Qa₂ v, ha, apply_fin_one Qa₁ v, smul_eq_mul]
    field_simp
  let J : Qa₁.IsometryEquiv Qa₂ := { toLinearEquiv := e, map_app' := he }
  exact ⟨(I₁.trans ((QuadraticMap.IsometryEquiv.refl H).prod J)).trans I₂.symm⟩

end Odd


/-- **A quasi-split inner form of a quasi-split GGP datum is trivial** (own work): if `W, V` and `W_α, V_α = W_α ⊕ Z` are all
quasi-split (and `W_α` has the dimension and discriminant of `W`), then `W_α ≅ W`.  The
odd-dimensional one of `W`, `V` is determined by quasi-splitness
(`nonempty_isometryEquiv_of_odd`); if it is `V`, cancel `Z` (`witt_cancellation`). -/
theorem nonempty_isometryEquiv_of_quasiSplit (d : GGPData K) {Q' : QuadraticForm K (Fin d.m → K)}
    (hnd : IsNondeg Q') (hdisc : SameDisc d.QW Q') (hW : IsQuasiSplitQF d.QW)
    (hV : IsQuasiSplitQF d.QV) (hW' : IsQuasiSplitQF Q') (hV' : IsQuasiSplitQF (Q'.prod d.QZ)) :
    Nonempty (Q'.IsometryEquiv d.QW) := by
  have hd : DiscRel d.QW Q' := (sameDisc_iff_discRel _ _).1 hdisc
  rcases Nat.even_or_odd d.m with hm | hm
  · have hdV : DiscRel d.QV (Q'.prod d.QZ) := hd.prod (DiscRel.refl' d.QZ)
    have hodd : Odd (finrank K d.V) := by
      rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]
      obtain ⟨t, ht⟩ := hm
      exact ⟨t + d.r, by omega⟩
    obtain ⟨I⟩ := nonempty_isometryEquiv_of_odd d.nondeg_QV (hdV.isNondeg d.nondeg_QV) hodd hV hV'
      hdV
    exact witt_cancellation d.QZ Q' d.QW
      ⟨((QuadraticMap.IsometryEquiv.prodComm d.QZ Q').trans I.symm).trans
        (QuadraticMap.IsometryEquiv.prodComm d.QW d.QZ)⟩
  · have hodd : Odd (finrank K (Fin d.m → K)) := by rwa [Module.finrank_fin_fun]
    obtain ⟨I⟩ := nonempty_isometryEquiv_of_odd d.nondeg hnd hodd hW hW' hd
    exact ⟨I.symm⟩


section Decomp

variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁]
  [AddCommGroup V₂] [Module K V₂]

/-- The Witt index is an isometry invariant. -/
theorem wittIndex_le_of_isometryEquiv {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂}
    [FiniteDimensional K V₂] (e : Q₁.IsometryEquiv Q₂) {U : Submodule K V₁}
    (hU : IsTotallyIsotropic Q₁ U) : finrank K U ≤ wittIndex Q₂ := by
  have h : IsTotallyIsotropic Q₂ (U.map (e.toLinearEquiv : V₁ →ₗ[K] V₂)) := by
    rintro _ ⟨u, hu, rfl⟩
    rw [LinearEquiv.coe_coe, show e.toLinearEquiv u = e u from rfl, e.map_app]
    exact hU u hu
  have := le_wittIndex h
  rwa [LinearEquiv.finrank_map_eq] at this

theorem wittIndex_eq_of_isometryEquiv [FiniteDimensional K V₁] [FiniteDimensional K V₂]
    {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (e : Q₁.IsometryEquiv Q₂) :
    wittIndex Q₁ = wittIndex Q₂ := by
  obtain ⟨U₁, h₁, e₁⟩ := exists_wittIndex Q₁
  obtain ⟨U₂, h₂, e₂⟩ := exists_wittIndex Q₂
  have a := wittIndex_le_of_isometryEquiv e h₁
  have b := wittIndex_le_of_isometryEquiv e.symm h₂
  omega

theorem isQuasiSplitQF_of_isometryEquiv [FiniteDimensional K V₁] [FiniteDimensional K V₂]
    {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (e : Q₁.IsometryEquiv Q₂)
    (h : IsQuasiSplitQF Q₁) : IsQuasiSplitQF Q₂ := by
  unfold IsQuasiSplitQF at h ⊢
  rw [← LinearEquiv.finrank_eq e.toLinearEquiv, ← wittIndex_eq_of_isometryEquiv e]
  exact h

/-- An orthogonal decomposition `V = A ⊕ B` gives `Q ≅ Q|_A ⊥ Q|_B`. -/
def orthIso {Q : QuadraticForm K V} {A B : Submodule K V} (hc : IsCompl A B)
    (horth : ∀ a ∈ A, ∀ b ∈ B, bform Q a b = 0) :
    ((Q.comp A.subtype).prod (Q.comp B.subtype)).IsometryEquiv Q where
  toLinearEquiv := Submodule.prodEquivOfIsCompl A B hc
  map_app' p := by
    show Q ((p.1 : V) + (p.2 : V)) = Q p.1 + Q p.2
    rw [QuadraticMap.map_add Q, polar_eq_two_mul_bform, horth _ p.1.2 _ p.2.2, mul_zero, add_zero]

/-- The swap `(A ⊥ C) ⊥ B ≅ (A ⊥ B) ⊥ C`. -/
def swapIso {V₃ : Type*} [AddCommGroup V₃] [Module K V₃] (Q₁ : QuadraticForm K V₁)
    (Q₂ : QuadraticForm K V₂) (Q₃ : QuadraticForm K V₃) :
    ((Q₁.prod Q₃).prod Q₂).IsometryEquiv ((Q₁.prod Q₂).prod Q₃) where
  toFun p := ((p.1.1, p.2), p.1.2)
  invFun p := ((p.1.1, p.2), p.1.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  map_app' p := by
    simp only [QuadraticMap.prod_apply]
    abel

theorem isNondeg_of_prod_right [FiniteDimensional K V₁] [FiniteDimensional K V₂]
    {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (h : IsNondeg (Q₁.prod Q₂)) :
    IsNondeg Q₂ := by
  rw [isNondeg_iff_gdet_ne_zero _ ((Module.finBasis K V₁).prod (Module.finBasis K V₂)),
    gdet_prod] at h
  rw [isNondeg_iff_gdet_ne_zero _ (Module.finBasis K V₂)]
  exact right_ne_zero_of_mul h

variable [FiniteDimensional K V]

/-- `W = W'_y ⊕ W''_y` for semisimple `y`. -/
theorem isCompl_fixedSub_movedSub {F : Type*} [Field F] [Invertible (2 : F)] {V : Type*}
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] {Q : QuadraticForm F V} (y : GSpin Q)
    (hdisj : fixedSub y ⊓ movedSub y = ⊥) : IsCompl (fixedSub y) (movedSub y) := by
  refine (Submodule.isCompl_iff_disjoint _ _ ?_).2 (disjoint_iff.2 hdisj)
  have := LinearMap.finrank_range_add_finrank_ker ((specP Q y : V →ₗ[F] V) - LinearMap.id)
  unfold fixedSub movedSub
  omega

/-- **`dim W''_y ≠ 1`**: on a line `W''_y` the isometry `P(y)` would act by a scalar `c`, so
`det P(y) = c`; `det P(y) = 1` then forces `c = 1`, i.e. `W''_y ⊆ W'_y`. -/
theorem finrank_movedSub_ne_one {Q : QuadraticForm K V} (y : GSpin Q)
    (hc : IsCompl (fixedSub y) (movedSub y)) : finrank K (movedSub y) ≠ 1 := by
  intro h1
  set g : V →ₗ[K] V := (specP Q y : V →ₗ[K] V) with hg
  have hmaps : ∀ u ∈ movedSub y, g u ∈ movedSub y := by
    rintro _ ⟨v, rfl⟩
    refine ⟨g v, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.id_apply, map_sub, g]
  have hfix : ∀ a ∈ fixedSub y, g a = a := by
    intro a ha
    have := LinearMap.mem_ker.mp ha
    simpa [sub_eq_zero, g] using this
  obtain ⟨v, hv0, hspan⟩ := finrank_eq_one_iff'.1 h1
  obtain ⟨c, hcv⟩ := hspan ⟨g v, hmaps v v.2⟩
  have hgU : ∀ u ∈ movedSub y, g u = c • u := by
    intro u hu
    obtain ⟨a, ha⟩ := hspan ⟨u, hu⟩
    have ha' : u = a • (v : V) := by
      have := congrArg Subtype.val ha
      simpa using this.symm
    have hcv' : g v = c • (v : V) := by
      have := congrArg Subtype.val hcv
      simpa using this.symm
    rw [ha', map_smul, hcv', smul_comm]
  set e := Submodule.prodEquivOfIsCompl (fixedSub y) (movedSub y) hc
  have hconj : e.symm.toLinearMap ∘ₗ g ∘ₗ e.toLinearMap =
      LinearMap.prodMap LinearMap.id (c • LinearMap.id) := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    apply e.injective
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.smul_apply,
      Submodule.coe_prodEquivOfIsCompl', e, map_add, hfix _ a.2, hgU _ b.2]
    rfl
  have hdet := LinearMap.det_conj g e.symm
  rw [LinearEquiv.symm_symm, hconj, LinearMap.det_prodMap, LinearMap.det_id, LinearMap.det_smul,
    LinearMap.det_id, h1, hg, det_specP] at hdet
  have hc1 : c = 1 := by simpa using hdet
  have hvfix : (v : V) ∈ fixedSub y := by
    show (v : V) ∈ LinearMap.ker ((specP Q y : V →ₗ[K] V) - LinearMap.id)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    have := hgU v v.2
    rw [hc1, one_smul] at this
    exact this
  have : (v : V) ∈ fixedSub y ⊓ movedSub y := ⟨hvfix, v.2⟩
  rw [hc.inf_eq_bot, Submodule.mem_bot] at this
  exact hv0 (Subtype.ext this)

end Decomp


section Binary

/-- A binary form in coordinates. -/
theorem eval_fin_two (Q : QuadraticForm K (Fin 2 → K)) (v : Fin 2 → K) :
    Q v = v 0 * v 0 * Q.toMatrix' 0 0 + 2 * (v 0 * v 1 * Q.toMatrix' 0 1) +
      v 1 * v 1 * Q.toMatrix' 1 1 := by
  have h1 : Q v = QuadraticMap.associated (R := K) Q v v :=
    (QuadraticMap.associated_eq_self_apply K Q v).symm
  have h2 : QuadraticMap.associated (R := K) Q = Matrix.toLinearMap₂' K Q.toMatrix' :=
    (Matrix.toLinearMap₂'_toMatrix' (R := K) _).symm
  have hs : Q.toMatrix' 1 0 = Q.toMatrix' 0 1 := (QuadraticForm.isSymm_toMatrix' Q).apply 0 1
  rw [h1, h2, Matrix.toLinearMap₂'_apply]
  simp only [Fin.sum_univ_two, smul_eq_mul, hs]
  ring

/-- A binary form whose `-disc` is a square is isotropic. -/
theorem exists_isotropic_of_isSquare (Q : QuadraticForm K (Fin 2 → K))
    (h : IsSquare (-Q.discr')) : ∃ v : Fin 2 → K, v ≠ 0 ∧ Q v = 0 := by
  obtain ⟨s, hs⟩ := h
  have hdet : Q.discr' = Q.toMatrix' 0 0 * Q.toMatrix' 1 1 - Q.toMatrix' 0 1 * Q.toMatrix' 0 1 := by
    rw [QuadraticForm.discr', Matrix.det_fin_two, (QuadraticForm.isSymm_toMatrix' Q).apply 0 1]
  by_cases ha : Q.toMatrix' 0 0 = 0
  · refine ⟨Pi.single 0 1, fun h0 => by simpa using congrFun h0 0, ?_⟩
    rw [eval_fin_two]
    simp [ha]
  · refine ⟨![-Q.toMatrix' 0 1 + s, Q.toMatrix' 0 0], fun h0 => ha (by simpa using congrFun h0 1), ?_⟩
    rw [eval_fin_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination -(Q.toMatrix' 0 0) * hs - (Q.toMatrix' 0 0) * hdet

theorem one_le_wittIndex_of_isotropic {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} {v : V} (hv : v ≠ 0) (hQ : Q v = 0) :
    1 ≤ wittIndex Q := by
  have h : IsTotallyIsotropic Q (K ∙ v) := by
    intro u hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hu
    rw [QuadraticMap.map_smul, hQ, smul_zero]
  have := le_wittIndex h
  rwa [finrank_span_singleton hv] at this

end Binary


section Padic

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- **`W'_y` embeds in `W`** (own work; GGP case of Thesis (6.1.1), via the `p`-adic classification
of quadratic forms).
Let `G` be quasi-split, `W_α` a form of the dimension and discriminant of `W`, and `y ∈ GSpin(W_α)`
semisimple with `W'_y` and `W'_y ⊕ Z` quasi-split.  Then `W'_y` embeds isometrically in `W`.

Proof.  If `W_α ≅ W` this is clear.  Otherwise write `W_α = W'_y ⊥ W''_y`.
* If `W''_y` is split (`0` or a hyperbolic plane), `W_α` and `V_α` are quasi-split, so
  `W_α ≅ W` (`nonempty_isometryEquiv_of_quasiSplit`): excluded.
* `dim W''_y ≠ 1` (`finrank_movedSub_ne_one`).
* Otherwise there are two classes `U ≇ W''_y` of the dimension and discriminant of `W''_y`
  (`padic_quadratic_classes`: `dim ≥ 3`, or a non-hyperbolic plane).  Then `W'_y ⊥ U` has the
  dimension and discriminant of `W`, and is `≇ W_α` by Witt cancellation; as there are at most two
  classes and `W ≇ W_α`, `W'_y ⊥ U ≅ W`. -/
theorem exists_isometry_fixedSub (d : GGPData F) (hqs : d.IsQuasiSplit)
    {Q : QuadraticForm F (Fin d.m → F)} (hQ : IsNondeg Q) (hdisc : SameDisc d.QW Q) (y : GSpin Q)
    (hss : IsSS F ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
    (hq1 : IsQuasiSplitQF (Q.comp (fixedSub y).subtype))
    (hq2 : IsQuasiSplitQF ((Q.comp (fixedSub y).subtype).prod d.QZ)) :
    ∃ ι : Q.comp (fixedSub y).subtype →qᵢ d.QW, Function.Injective ι := by
  set A := fixedSub y
  set B := movedSub y
  set QA := Q.comp A.subtype
  set QB := Q.comp B.subtype
  by_cases hA : Nonempty (Q.IsometryEquiv d.QW)
  · obtain ⟨e⟩ := hA
    exact ⟨e.toIsometry.comp ⟨A.subtype, fun _ => rfl⟩, fun a b h => Subtype.ext (e.injective h)⟩
  have hc : IsCompl A B := isCompl_fixedSub_movedSub y (fixedSub_inf_movedSub_of_isSS y hss)
  let I : (QA.prod QB).IsometryEquiv Q := orthIso hc (fixedSub_orthogonal_movedSub y)
  have hQB : IsNondeg QB := isNondeg_of_prod_right ((DiscRel.of_isometryEquiv I.symm).isNondeg hQ)
  -- (i) `W''_y` is not split
  have hsplit : finrank F B ≤ 2 * wittIndex QB → False := by
    intro hB
    have h1 : IsQuasiSplitQF Q := isQuasiSplitQF_of_isometryEquiv I (isQuasiSplitQF_prod hq1 hB)
    have h2 : IsQuasiSplitQF (Q.prod d.QZ) :=
      isQuasiSplitQF_of_isometryEquiv ((swapIso QA QB d.QZ).trans
        (I.prod (QuadraticMap.IsometryEquiv.refl d.QZ))) (isQuasiSplitQF_prod hq2 hB)
    exact hA (nonempty_isometryEquiv_of_quasiSplit d hQ hdisc hqs.1 hqs.2 h1 h2)
  -- (ii) a second class `U'` in the dimension and discriminant of `W''_y` gives the embedding
  have htwo : ∀ (k : ℕ) (eB : B ≃ₗ[F] (Fin k → F)) (U' : QuadraticForm F (Fin k → F)),
      IsNondeg U' → SameDisc (QB.comp eB.symm.toLinearMap) U' →
      ¬ Nonempty (U'.IsometryEquiv (QB.comp eB.symm.toLinearMap)) →
      ∃ ι : QA →qᵢ d.QW, Function.Injective ι := by
    intro k eB U' hU' hU'd hne
    set QBf := QB.comp eB.symm.toLinearMap
    let JB : QBf.IsometryEquiv QB := { toLinearEquiv := eB.symm, map_app' := fun _ => rfl }
    have hdimX : finrank F (A × (Fin k → F)) = finrank F (Fin d.m → F) := by
      have hkB : finrank F B = k := by rw [LinearEquiv.finrank_eq eB, Module.finrank_fin_fun]
      rw [Module.finrank_prod, Module.finrank_fin_fun, ← hkB, Submodule.finrank_add_eq_of_isCompl hc]
    let E := LinearEquiv.ofFinrankEq _ _ hdimX
    set Xf := (QA.prod U').comp E.symm.toLinearMap
    let JX : (QA.prod U').IsometryEquiv Xf :=
      { toLinearEquiv := E, map_app' := fun p => by simp [Xf] }
    have hdX : DiscRel d.QW Xf :=
      ((((sameDisc_iff_discRel _ _).1 hdisc).trans (DiscRel.of_isometryEquiv I.symm)).trans
        ((DiscRel.refl' QA).prod ((DiscRel.of_isometryEquiv JB.symm).trans
          ((sameDisc_iff_discRel _ _).1 hU'd)))).trans (DiscRel.of_isometryEquiv JX)
    have hXnd : IsNondeg Xf := hdX.isNondeg d.nondeg
    obtain ⟨n, R, -, -, -, huniq, -, -, -, hn2⟩ := padic_quadratic_classes d.QW d.nondeg
    obtain ⟨iW, ⟨eW⟩, -⟩ := huniq d.QW d.nondeg ⟨1, one_ne_zero, by ring⟩
    obtain ⟨iQ, ⟨eQ⟩, -⟩ := huniq Q hQ hdisc
    obtain ⟨iX, ⟨eX⟩, -⟩ := huniq Xf hXnd ((sameDisc_iff_discRel _ _).2 hdX)
    have hQW : iQ ≠ iW := by
      rintro rfl
      exact hA ⟨eQ.trans eW.symm⟩
    have hXQ : iX ≠ iQ := by
      rintro rfl
      exact hne (witt_cancellation QA U' QBf
        ⟨((JX.trans (eX.trans eQ.symm)).trans I.symm).trans
          ((QuadraticMap.IsometryEquiv.refl QA).prod JB.symm)⟩)
    have hXW : iX = iW := by
      apply Fin.ext
      have h1 := Fin.val_ne_of_ne hQW
      have h2 := Fin.val_ne_of_ne hXQ
      have := iX.2
      have := iQ.2
      have := iW.2
      omega
    subst hXW
    refine ⟨(eX.trans eW.symm).toIsometry.comp (JX.toIsometry.comp
      (QuadraticMap.Isometry.inl QA U')), fun a b h => ?_⟩
    have h' := JX.toLinearEquiv.injective ((eX.trans eW.symm).toLinearEquiv.injective h)
    exact (Prod.mk.inj h').1
  -- (iii) case analysis on `dim W''_y`
  obtain ⟨k, eB, hk⟩ : ∃ k, ∃ _ : B ≃ₗ[F] (Fin k → F), k = finrank F B :=
    ⟨_, LinearEquiv.ofFinrankEq _ _ (by simp), rfl⟩
  set QBf := QB.comp eB.symm.toLinearMap
  let JB : QBf.IsometryEquiv QB := { toLinearEquiv := eB.symm, map_app' := fun _ => rfl }
  have hQBf : IsNondeg QBf := (DiscRel.of_isometryEquiv JB.symm).isNondeg hQB
  have hk1 : k ≠ 1 := hk ▸ finrank_movedSub_ne_one y hc
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · exact (hsplit (by omega)).elim
  obtain ⟨n, R, i₀, hR0, hR, huniq, h3, -, h2, hn2⟩ := padic_quadratic_classes QBf hQBf
  by_cases hn : n = 2
  · subst hn
    set j : Fin 2 := if i₀ = 0 then 1 else 0 with hjdef
    have hj : j ≠ i₀ := by fin_cases i₀ <;> simp [hjdef]
    refine htwo k eB (R j) (hR j).1 (hR j).2 fun ⟨e⟩ => hj ?_
    obtain ⟨i, -, hi⟩ := huniq (R j) (hR j).1 (hR j).2
    have hRe : Nonempty ((R j).IsometryEquiv (R i₀)) := ⟨hR0 ▸ e⟩
    exact (hi j ⟨QuadraticMap.IsometryEquiv.refl _⟩).trans (hi i₀ hRe).symm
  · have hk2' : k = 2 := by
      by_contra h
      exact hn (h3 (by omega))
    have hn1 : n = 1 := by
      have := i₀.2
      omega
    have hsq : IsSquare (-QuadraticForm.discr' QBf) := (h2 hk2').1 hn1
    subst hk2'
    obtain ⟨v, hv, hQv⟩ := exists_isotropic_of_isSquare QBf hsq
    have hw : 1 ≤ wittIndex QB := by
      rw [← wittIndex_eq_of_isometryEquiv JB]
      exact one_le_wittIndex_of_isotropic hv hQv
    exact (hsplit (by omega)).elim

end Padic

end QuadClassify
end GSpinGGP
