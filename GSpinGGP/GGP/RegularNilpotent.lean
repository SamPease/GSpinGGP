/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.RegularNilpotent
import GSpinGGP.GGP.LieRank
import GSpinGGP.GGP.QuadClassify
import GSpinGGP.GGP.WittParity
import GSpinGGP.GGP.Levi

/-!
# Regular nilpotent elements of `gspin(V)`

The rank of `gspin(V)` is in `GGP/LieRank.lean` (`lieRank_gspin`).

* `isRegularNil_regNil`: the explicit element `regNil` is regular nilpotent.
* Witt theory: split families of maximal size in quasi-split spaces
  (`exists_isSplitFamily_of_quasiSplit`, `exists_hyp_of_quasiSplit_odd`, `exists_wittData_W`).
* Regular nilpotent orbits (Thesis §5.1.4): `nilReg_nonempty_of_quasiSplit`,
  `exists_regularNil_inOrbitNu` (Luo's orbit `O_ν`, via `isInOrbitNu_regNil`),
  `nilReg_centralizer_nonempty_of_quasiSplit`. The `⇒` directions and the
  iff statements are in `GGP.RegularNilpotentConverse`.
-/

noncomputable section

open CliffordAlgebra Module

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

section Rank

variable {K : Type*} [NontriviallyNormedField K] [CharZero K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The explicit element `regNil` is regular nilpotent** in `gspin(V)` when
`dim V ≤ 2k + 2`: its centralizer has dimension `≤ dim V − k`
(`finrank_lieCentralizer_regNil_le`), which is `⌊dim V/2⌋ + 1 ≤ lieRank` as `dim V ∈ {2k+1, 2k+2}`. -/
theorem isRegularNil_regNil {Q : QuadraticForm K V} (hQ : IsNondeg Q) {w : ℤ → V} {ν : K} {k : ℕ}
    (hw : IsSplitFamily Q w ν k) (hν : ν ≠ 0) (hdim : finrank K V ≤ 2 * k + 2) :
    IsRegularNil (gspin Q) (regNil Q w ν k) := by
  have hr : lieRank (gspin Q) ≤ finrank K (lieCentralizer (gspin Q) (regNil Q w ν k)) := by
    unfold lieRank
    exact ciInf_le (OrderBot.bddBelow _) (⟨regNil Q w ν k, regNil_mem_gspin⟩ : gspin Q)
  refine ⟨regNil_mem_gspin, isNilpotent_regNil hw hν, le_antisymm ?_ hr⟩
  have h1 := finrank_lieCentralizer_regNil_le hQ hw hν hdim
  have hge : 2 * k + 1 ≤ finrank K V := by
    have := (linearIndependent_isSplitFamily hw hν).fintype_card_le_finrank
    rwa [Fintype.card_fin] at this
  have h2 := le_lieRank_gspin (F := K) hQ
  omega

end Rank

section Witt

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **A quasi-split space contains a split family of maximal size** (Witt decomposition): if
`dim V > 0` and the anisotropic kernel has dimension `≤ 2`, there are `w_{-k..k}` with
`b(w_i, w_j) = ν δ_{i+j,0}`, `ν ≠ 0`, and `dim V ≤ 2k + 2`. From `V ≅ H^s ⊥ V_an`: the hyperbolic
pairs of `H^s` around an anisotropic vector of `V_an` (`k = s`), or (for `V_an = 0`) around
`h₀ + h_{2s-1}` with the remaining `s − 1` pairs (`k = s − 1`). -/
theorem exists_isSplitFamily_of_quasiSplit {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (hqs : IsQuasiSplitQF Q) (hpos : 0 < finrank K V) :
    ∃ (w : ℤ → V) (ν : K) (k : ℕ), ν ≠ 0 ∧ IsSplitFamily Q w ν k ∧ finrank K V ≤ 2 * k + 2 := by
  obtain ⟨ka, Qa, hani, ⟨I⟩, hdim⟩ := witt_decomposition Q hQ
  set s := wittIndex Q
  unfold IsQuasiSplitQF at hqs
  let J := I.symm
  have hJ : ∀ x y, bform Q (J x) (J y) = bform (hypForm K s) x.1 y.1 + bform Qa x.2 y.2 :=
    fun x y => (bform_isometry J.toIsometry x y).trans (bform_prod _ _ x y)
  let h : ℕ → V := fun a => if ha : a < 2 * s then J (Pi.single ⟨a, ha⟩ 1, 0) else 0
  have hh : ∀ a b : ℕ, a < 2 * s → b < 2 * s →
      bform Q (h a) (h b) = if a + b + 1 = 2 * s then 1 else 0 := by
    intro a b ha hb
    simp only [h, dite_eq_left ha, dite_eq_left hb]
    rw [hJ, bform_hypForm_single]
    simp
  have hsymm : ∀ x y, bform Q x y = bform Q y x := fun x y => QuadraticMap.associated_isSymm K Q x y
  have hQb : ∀ x, bform Q x x = Q x := fun x => QuadraticMap.associated_eq_self_apply K Q x
  by_cases hka : 1 ≤ ka
  · let g : Fin ka → K := Pi.single ⟨0, hka⟩ 1
    let u : V := J (0, g)
    have hQu : Q u = Qa g := by
      simp only [u, QuadraticMap.IsometryEquiv.map_app, QuadraticMap.prod_apply, map_zero,
        zero_add]
    have hν : Q u ≠ 0 := by
      rw [hQu]; intro h0
      have := hani g h0
      simpa [g] using congrFun this ⟨0, hka⟩
    refine ⟨extFamily (fun _ => u) h (Q u) 0 s, Q u, 0 + s, hν, ?_, by omega⟩
    refine isSplitFamily_extFamily (fun i j hi hj => ?_) hh (fun j _ a ha => ?_)
    · have hi0 : i = 0 := by rw [abs_le] at hi; omega
      have hj0 : j = 0 := by rw [abs_le] at hj; omega
      subst hi0 hj0
      simp [hQb]
    · simp only [u, h, dite_eq_left ha]
      rw [hJ]
      simp
  · have hka0 : ka = 0 := by omega
    have hs : 1 ≤ s := by omega
    let u : V := h 0 + h (2 * s - 1)
    have hbu : bform Q u u = 2 := by
      simp only [u, map_add, LinearMap.add_apply]
      rw [hh _ _ (by omega) (by omega), hh _ _ (by omega) (by omega), hh _ _ (by omega) (by omega),
        hh _ _ (by omega) (by omega), ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
        ite_eq_right (by omega)]
      norm_num
    refine ⟨extFamily (fun _ => u) (fun a => h (a + 1)) (2 : K) 0 (s - 1), (2 : K), 0 + (s - 1),
      Invertible.ne_zero 2, ?_, by omega⟩
    refine isSplitFamily_extFamily (fun i j hi hj => ?_) (fun a b ha hb => ?_) (fun j _ a ha => ?_)
    · have hi0 : i = 0 := by rw [abs_le] at hi; omega
      have hj0 : j = 0 := by rw [abs_le] at hj; omega
      subst hi0 hj0
      simp [hbu]
    · rw [hh _ _ (by omega) (by omega)]
      congr 1; apply propext; omega
    · simp only [u, map_add, LinearMap.add_apply]
      rw [hh _ _ (by omega) (by omega), hh _ _ (by omega) (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega), add_zero]

/-- **An odd-dimensional quasi-split space is `H^s ⊥ ⟨a⟩`** (Witt decomposition): hyperbolic
pairs `h_0, …, h_{2s-1}` (`b(h_i, h_j) = δ_{i+j+1, 2s}`) and an anisotropic `a ⊥ h`, with
`dim V = 2s + 1`. -/
theorem exists_hyp_of_quasiSplit_odd {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (hqs : IsQuasiSplitQF Q) (hodd : Odd (finrank K V)) :
    ∃ (s : ℕ) (h : ℕ → V) (a : V), (∀ i j : ℕ, i < 2 * s → j < 2 * s →
      bform Q (h i) (h j) = if i + j + 1 = 2 * s then 1 else 0) ∧ Q a ≠ 0 ∧
      (∀ j : ℕ, j < 2 * s → bform Q a (h j) = 0) ∧ finrank K V = 2 * s + 1 := by
  obtain ⟨ka, Qa, hani, ⟨I⟩, hdim⟩ := witt_decomposition Q hQ
  set s := wittIndex Q
  unfold IsQuasiSplitQF at hqs
  obtain ⟨t, ht⟩ := hodd
  have hka : ka = 1 := by omega
  let J := I.symm
  have hJ : ∀ x y, bform Q (J x) (J y) = bform (hypForm K s) x.1 y.1 + bform Qa x.2 y.2 :=
    fun x y => (bform_isometry J.toIsometry x y).trans (bform_prod _ _ x y)
  let h : ℕ → V := fun a => if ha : a < 2 * s then J (Pi.single ⟨a, ha⟩ 1, 0) else 0
  let g : Fin ka → K := Pi.single ⟨0, by omega⟩ 1
  refine ⟨s, h, J (0, g), fun i j hi hj => ?_, ?_, fun j hj => ?_, by omega⟩
  · simp only [h, dite_eq_left hi, dite_eq_left hj]
    rw [hJ, bform_hypForm_single]
    simp
  · simp only [QuadraticMap.IsometryEquiv.map_app, QuadraticMap.prod_apply, map_zero, zero_add]
    intro h0
    have := hani g h0
    simpa [g] using congrFun this ⟨0, by omega⟩
  · simp only [h, dite_eq_left hj]
    rw [hJ]
    simp

end Witt

/-! ## Centralizers of `Y ∈ gspin(V)_y`: the fixed part and the moved part -/

section Side

variable {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Lower bound** for `dim gspin(V)_{y,Y}` when the moved part is abelian (the elements of
`so(V)_{P y}` killing `A` commute): `≥ ⌊dim A/2⌋ + dim (so(V)_{P y} killing A) + 1`. -/
theorem le_finrank_lieCentralizer_fixed {Q : QuadraticForm K V} (hQ : IsNondeg Q) (y : GSpin Q)
    (hc : IsCompl (fixedSub y) ((bform Q).orthogonal (fixedSub y)))
    (hab : ∀ M₁ ∈ soCent Q (specP Q y : Module.End K V) ⊓ killSub (fixedSub y),
      ∀ M₂ ∈ soCent Q (specP Q y : Module.End K V) ⊓ killSub (fixedSub y), M₁ * M₂ = M₂ * M₁)
    {Y : CliffordAlgebra Q}
    (hY : Y ∈ lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) :
    finrank K (fixedSub y) / 2 +
        finrank K ↥(soCent Q (specP Q y : Module.End K V) ⊓ killSub (fixedSub y)) + 1 ≤
      finrank K (lieCentralizer (lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q)) Y) := by
  obtain ⟨h, e⟩ := finrank_lieCentralizer_fixed hQ y hc hY
  obtain ⟨hYg, hYc⟩ := mem_lieCentralizer.mp hY
  have hNg : adV Q Y * (specP Q y : Module.End K V) = (specP Q y : Module.End K V) * adV Q Y :=
    ((commute_iff_adV hQ y hYg).mp hYc).symm
  have hgB : ∀ b ∈ (bform Q).orthogonal (fixedSub y),
      (specP Q y : Module.End K V) b ∈ (bform Q).orthogonal (fixedSub y) :=
    fun b hb => specP_mem_orthogonal_fixedSub y hb
  rw [e, soCent_inf_killSub_eq hc (mem_fixedSub_iff y) hgB (bform_adV hYg) hNg hab]
  have hNs : ∀ a b, bform (Q.comp (fixedSub y).subtype) ((adV Q Y).restrict h a) b =
      -bform (Q.comp (fixedSub y).subtype) a ((adV Q Y).restrict h b) := by
    intro a b
    rw [bform_comp_subtype, bform_comp_subtype]
    exact bform_adV hYg a b
  have := le_finrank_soCent (isNondeg_comp_subtype_of_isCompl hc) hNs
  omega


end Side

/-! ## The two sides of `G_x`: `W'_x ⊂ W` and `V'_x = W'_x ⊕ Z ⊂ V` -/

section GGPSides

variable {K : Type*} [Field K] [Invertible (2 : K)] (d : GGPData K)

theorem fixedSub_inf_movedSub_incl (x : GSpin d.QW) (h : fixedSub x ⊓ movedSub x = ⊥) :
    fixedSub (d.incl x) ⊓ movedSub (d.incl x) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hf, hm⟩ := Submodule.mem_inf.mp hv
  obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hm
  rw [Submodule.mem_bot]
  set m : Fin d.m → K := specP d.QW x u.1 - u.1
  have hu : (((specP d.QV (d.incl x) : d.V →ₗ[K] d.V) - LinearMap.id : d.V →ₗ[K] d.V) u) =
      (m, 0) := by
    obtain ⟨w, z⟩ := u
    simp [d.specP_incl_apply, m]
  rw [hu] at hf ⊢
  have h1 : m ∈ fixedSub x ⊓ movedSub x :=
    ⟨(d.mem_fixedSub_incl_iff x m 0).mp hf, LinearMap.mem_range.mpr ⟨u.1, by simp [m]⟩⟩
  rw [h, Submodule.mem_bot] at h1
  simp [h1]

/-- **The moved part of `V` is that of `W`**: an element of `so(V)_{P(x)}` killing `V'_x` is
`(w, z) ↦ (M' w, 0)` with `M' ∈ so(W)_{P(x)}` killing `W'_x`. So if the latter commute, so do the
former. -/
theorem commute_movedPart_incl (x : GSpin d.QW)
    (hW : ∀ M₁ ∈ soCent d.QW (specP d.QW x : Module.End K (Fin d.m → K)) ⊓ killSub (fixedSub x),
      ∀ M₂ ∈ soCent d.QW (specP d.QW x : Module.End K (Fin d.m → K)) ⊓ killSub (fixedSub x),
        M₁ * M₂ = M₂ * M₁) :
    ∀ M₁ ∈ soCent d.QV (specP d.QV (d.incl x) : Module.End K d.V) ⊓ killSub (fixedSub (d.incl x)),
      ∀ M₂ ∈ soCent d.QV (specP d.QV (d.incl x) : Module.End K d.V) ⊓
        killSub (fixedSub (d.incl x)), M₁ * M₂ = M₂ * M₁ := by
  have hZnd := isNondeg_splitOddForm d.r d.ν.ne_zero
  -- the restriction to `W`
  have key : ∀ M ∈ soCent d.QV (specP d.QV (d.incl x) : Module.End K d.V) ⊓
      killSub (fixedSub (d.incl x)),
      (∀ v, M v = ((M (v.1, 0)).1, 0)) ∧
      (LinearMap.fst K _ _ ∘ₗ M ∘ₗ LinearMap.inl K _ _) ∈
        soCent d.QW (specP d.QW x : Module.End K (Fin d.m → K)) ⊓ killSub (fixedSub x) := by
    intro M hM
    obtain ⟨hMg, hMk⟩ := Submodule.mem_inf.mp hM
    obtain ⟨hMs, hMc⟩ := mem_soCent.mp hMg
    have hz : ∀ z : d.Z, ((0 : Fin d.m → K), z) ∈ fixedSub (d.incl x) := fun z =>
      (d.mem_fixedSub_incl_iff x 0 z).mpr (Submodule.zero_mem _)
    have h2 : ∀ v, (M v).2 = 0 := by
      intro v
      refine (isNondeg_iff _).mp hZnd _ fun z => ?_
      have := hMs (0, z) v
      rw [hMk _ (hz z), map_zero, LinearMap.zero_apply, bform_prod] at this
      simp only [map_zero, LinearMap.zero_apply, zero_add] at this
      rw [bform_comm]; linear_combination this
    have hv : ∀ v, M v = ((M (v.1, 0)).1, 0) := by
      intro v
      have e : v = (v.1, 0) + (0, v.2) := by simp
      conv_lhs => rw [e, map_add, hMk _ (hz _), add_zero]
      exact Prod.ext rfl (h2 _)
    refine ⟨hv, Submodule.mem_inf.mpr ⟨mem_soCent.2 ⟨fun a b => ?_, ?_⟩, fun a ha => ?_⟩⟩
    · have := hMs (a, 0) (b, 0)
      rw [hv (a, 0), hv (b, 0), bform_prod, bform_prod] at this
      simpa using this
    · refine LinearMap.ext fun w => ?_
      show (M (specP d.QW x w, 0)).1 = specP d.QW x ((M (w, 0)).1)
      have := congrArg (fun T : Module.End K d.V => T (w, 0)) hMc
      simp only [Module.End.mul_apply, LinearEquiv.coe_coe] at this
      rw [d.specP_incl_apply] at this
      conv_rhs at this => rw [hv (w, 0)]
      rw [d.specP_incl_apply] at this
      exact congrArg Prod.fst this
    · show (M (a, 0)).1 = 0
      rw [hMk _ ((d.mem_fixedSub_incl_iff x a 0).mpr ha), Prod.fst_zero]
  intro M₁ hM₁ M₂ hM₂
  obtain ⟨hv₁, h₁⟩ := key M₁ hM₁
  obtain ⟨hv₂, h₂⟩ := key M₂ hM₂
  have hc := hW _ h₁ _ h₂
  refine LinearMap.ext fun v => ?_
  have := congrArg (fun T : Module.End K (Fin d.m → K) => T v.1) hc
  simp only [Module.End.mul_apply, LinearMap.comp_apply, LinearMap.inl_apply,
    LinearMap.fst_apply] at this
  simp only [Module.End.mul_apply]
  rw [hv₂ v, hv₁, hv₁ v, hv₂]
  simp only [this]
  exact (hv₂ ((M₁ (v.1, 0)).1, 0)).symm

end GGPSides

/-! ## Regular nilpotent elements of `𝔤_x` -/

section CentralizerNilReg

variable {K : Type*} [Field K] [Invertible (2 : K)]

/-- `𝔤_{a,Y} = gspin(W)_{a₁,Y₁} × gspin(V)_{a₂,Y₂}`. -/
theorem mem_lieCentralizer_lieCentralizer_lie (d : GGPData K) {a Y X : d.ambient} :
    X ∈ lieCentralizer (lieCentralizer d.lie a) Y ↔
      X.1 ∈ lieCentralizer (lieCentralizer (gspin d.QW) a.1) Y.1 ∧
        X.2 ∈ lieCentralizer (lieCentralizer (gspin d.QV) a.2) Y.2 := by
  have hl : ∀ Z : d.ambient, Z ∈ d.lie ↔ Z.1 ∈ gspin d.QW ∧ Z.2 ∈ gspin d.QV := fun Z => Iff.rfl
  simp only [mem_lieCentralizer, hl, Prod.ext_iff, Prod.fst_mul, Prod.snd_mul]
  tauto

/-- `𝔤_{a,Y}` is abelian iff both factors are. -/
theorem isLieAbelian_lieCentralizer_lieCentralizer_lie_iff (d : GGPData K) {a Y : d.ambient} :
    IsLieAbelian (lieCentralizer (lieCentralizer d.lie a) Y) ↔
      IsLieAbelian (lieCentralizer (lieCentralizer (gspin d.QW) a.1) Y.1) ∧
        IsLieAbelian (lieCentralizer (lieCentralizer (gspin d.QV) a.2) Y.2) := by
  rw [isLieAbelian_iff_forall_commute, isLieAbelian_iff_forall_commute,
    isLieAbelian_iff_forall_commute]
  have h0W : (0 : CliffordAlgebra d.QW) ∈ lieCentralizer (lieCentralizer (gspin d.QW) a.1) Y.1 :=
    zero_mem _
  have h0V : (0 : CliffordAlgebra d.QV) ∈ lieCentralizer (lieCentralizer (gspin d.QV) a.2) Y.2 :=
    zero_mem _
  constructor
  · intro h
    refine ⟨fun X₁ h₁ X₂ h₂ => ?_, fun X₁ h₁ X₂ h₂ => ?_⟩
    · have := h (X₁, 0) ((mem_lieCentralizer_lieCentralizer_lie d).2 ⟨h₁, h0V⟩) (X₂, 0)
        ((mem_lieCentralizer_lieCentralizer_lie d).2 ⟨h₂, h0V⟩)
      exact congrArg Prod.fst this
    · have := h (0, X₁) ((mem_lieCentralizer_lieCentralizer_lie d).2 ⟨h0W, h₁⟩) (0, X₂)
        ((mem_lieCentralizer_lieCentralizer_lie d).2 ⟨h0W, h₂⟩)
      exact congrArg Prod.snd this
  · rintro ⟨hW, hV⟩ X₁ h₁ X₂ h₂
    rw [mem_lieCentralizer_lieCentralizer_lie] at h₁ h₂
    exact Prod.ext (hW _ h₁.1 _ h₂.1) (hV _ h₁.2 _ h₂.2)

/-- `𝔤_{a,Y} = gspin(W)_{a₁,Y₁} × gspin(V)_{a₂,Y₂}`. -/
theorem finrank_lieCentralizer_lieCentralizer_lie (d : GGPData K) (a Y : d.ambient) :
    finrank K (lieCentralizer (lieCentralizer d.lie a) Y) =
      finrank K (lieCentralizer (lieCentralizer (gspin d.QW) a.1) Y.1) +
        finrank K (lieCentralizer (lieCentralizer (gspin d.QV) a.2) Y.2) := by
  have h : (lieCentralizer (lieCentralizer d.lie a) Y).toSubmodule =
      (lieCentralizer (lieCentralizer (gspin d.QW) a.1) Y.1).toSubmodule.prod
        (lieCentralizer (lieCentralizer (gspin d.QV) a.2) Y.2).toSubmodule := by
    ext Z
    exact mem_lieCentralizer_lieCentralizer_lie d
  show finrank K ↥(lieCentralizer (lieCentralizer d.lie a) Y).toSubmodule =
    finrank K ↥(lieCentralizer (lieCentralizer (gspin d.QW) a.1) Y.1).toSubmodule +
      finrank K ↥(lieCentralizer (lieCentralizer (gspin d.QV) a.2) Y.2).toSubmodule
  rw [h, (Submodule.prodEquiv _ _).finrank_eq, Module.finrank_prod]

/-- **A regular element of one side**: if `(A, q|_A)` (`A = W'_y`) is quasi-split, some nilpotent
`X ∈ gspin(V)_y` (an explicit `regNil` on `A`, or `0` if `A = 0`) has
`dim gspin(V)_{y,X} ≤ ⌊dim A/2⌋ + dim (so(V)_{P y} killing A) + 1`. -/
theorem exists_side_regNil [CharZero K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : IsNondeg Q) (y : GSpin Q)
    (hc : IsCompl (fixedSub y) ((bform Q).orthogonal (fixedSub y)))
    (hqs : IsQuasiSplitQF (Q.comp (fixedSub y).subtype)) :
    ∃ X ∈ lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q),
      IsNilpotent X ∧
      finrank K (lieCentralizer (lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) :
        CliffordAlgebra Q)) X) ≤ finrank K (fixedSub y) / 2 +
          finrank K ↥(soCent Q (specP Q y : Module.End K V) ⊓ killSub (fixedSub y)) + 1 := by
  have hQA : IsNondeg (Q.comp (fixedSub y).subtype) := isNondeg_comp_subtype_of_isCompl hc
  by_cases hpos : 0 < finrank K (fixedSub y)
  · obtain ⟨w, ν, k, hν, hw, hdim⟩ := exists_isSplitFamily_of_quasiSplit hQA hqs hpos
    set X := regNil Q (fun j => (w j : V)) ν k
    have hw' : IsSplitFamily Q (fun j => (w j : V)) ν k := fun i j hi hj => by
      rw [← bform_comp_subtype]; exact hw i j hi hj
    have hXm : X ∈ lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) :=
      mem_lieCentralizer.mpr ⟨regNil_mem_gspin, commute_regNil y (fun j => (w j).2) ν k⟩
    have h : ∀ a ∈ (fixedSub y), adV Q X a ∈ (fixedSub y) := fun a ha => by
      rw [show a = ((⟨a, ha⟩ : (fixedSub y)) : V) from rfl, adV_regNil_subtype w ν k ⟨a, ha⟩]
      exact Submodule.coe_mem _
    have hr : (adV Q X).restrict h = adV (Q.comp (fixedSub y).subtype) (regNil (Q.comp (fixedSub y).subtype) w ν k) :=
      LinearMap.ext fun a => Subtype.ext (adV_regNil_subtype w ν k a)
    have h1 := finrank_lieCentralizer_fixed_le hQ y hc hXm h
    rw [hr] at h1
    have h2 := finrank_soCent_regNil_le hQA hw hν hdim
    have h3 := (linearIndependent_isSplitFamily hw hν).fintype_card_le_finrank
    rw [Fintype.card_fin] at h3
    exact ⟨X, hXm, isNilpotent_regNil hw' hν, by omega⟩
  · have h0 : finrank K (fixedSub y) = 0 := by omega
    have hXm : (0 : CliffordAlgebra Q) ∈
        lieCentralizer (gspin Q) ((y : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) :=
      Submodule.zero_mem (lieCentralizer (gspin Q) _).toSubmodule
    have h : ∀ a ∈ (fixedSub y), adV Q 0 a ∈ (fixedSub y) := fun a _ => by rw [map_zero]; exact Submodule.zero_mem _
    have h1 := finrank_lieCentralizer_fixed_le hQ y hc hXm h
    have h2 := Submodule.finrank_le (soCent (Q.comp (fixedSub y).subtype) ((adV Q 0).restrict h))
    rw [Module.finrank_linearMap, h0, mul_zero] at h2
    exact ⟨0, hXm, IsNilpotent.zero, by omega⟩

end CentralizerNilReg

/-! ## Regular nilpotent orbits and quasi-splitness -/

section NilReg

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- **A quasi-split `GSpin(V)` has a regular nilpotent orbit** (Thesis §5.1.4 "Regular Nilpotent
Orbits"). Proved: a split family `w_{-k..k}` with `dim V ≤ 2k + 2`
(`exists_isSplitFamily_of_quasiSplit`) gives the regular nilpotent element `regNil`
(`isRegularNil_regNil`, which rests on Jantzen's bound `jantzen_finrank_soCentMat_ge`); for
`V = 0`, `X = 0`. -/
theorem nilReg_nonempty_of_quasiSplit {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (Q : QuadraticForm F V) (hQ : IsNondeg Q) (hqs : IsQuasiSplitQF Q) :
    (NilReg (GSpin Q) (gspin Q)).Nonempty := by
  have hconj : ∀ g ∈ GSpin Q, ∀ Y ∈ gspin Q,
      (g : CliffordAlgebra Q) * Y * (↑g⁻¹ : CliffordAlgebra Q) ∈ gspin Q :=
    fun g hg Y hY => conj_mem_gspin Q ⟨g, hg⟩ hY
  obtain ⟨X, hX⟩ : ∃ X, IsRegularNil (gspin Q) X := by
    by_cases hpos : 0 < finrank F V
    · obtain ⟨w, ν, k, hν, hw, hdim⟩ := exists_isSplitFamily_of_quasiSplit hQ hqs hpos
      exact ⟨_, isRegularNil_regNil hQ hw hν hdim⟩
    · -- `V = 0`: every centralizer is `gspin(V) = F`
      have h0 : finrank F V = 0 := by omega
      refine ⟨0, (gspin Q).zero_mem, IsNilpotent.zero, le_antisymm ?_ ?_⟩
      · rw [finrank_lieCentralizer_gspin hQ (gspin Q).zero_mem]
        have : finrank F (soCent Q (adV Q 0)) = 0 := by
          have h1 := Submodule.finrank_le (soCent Q (adV Q 0))
          rw [Module.finrank_linearMap, h0, mul_zero] at h1
          omega
        have h2 := le_lieRank_gspin hQ
        rw [h0] at h2
        omega
      · unfold lieRank
        exact ciInf_le (OrderBot.bddBelow _) (⟨0, (gspin Q).zero_mem⟩ : gspin Q)
  exact ⟨_, mk_mem_nilReg_of_isRegularNil _ _ hconj ⟨X, hX.1, hX.2.1⟩ hX⟩

/-- **`regNil` lies in Luo's orbit `O_ν`** when `V = ⟨d₀⟩ ⊥ ⟨w_{-k..k}⟩` with `d₀` anisotropic
(`IsInOrbitNu`): `adV X` kills `d₀`, is one Jordan block on `U₁ = ⟨w⟩`, and `U₁ = ⟨w_0⟩ ⊥ ⟨w_j : j ≠ 0⟩`
with `q(w_0) = ν` and `⟨w_j : j ≠ 0⟩` hyperbolic (`⟨w_1, …, w_k⟩` totally isotropic). -/
theorem isInOrbitNu_regNil {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    {Q : QuadraticForm F V} {w : ℤ → V} {ν : F} {k : ℕ} (hw : IsSplitFamily Q w ν k) (hν : ν ≠ 0)
    {d₀ : V} (hd₀ : Q d₀ ≠ 0) (hd₀w : ∀ j : ℤ, |j| ≤ k → bform Q (w j) d₀ = 0)
    (hdim : finrank F V = 2 * k + 2) :
    IsInOrbitNu Q ⊤ ν (adV Q (regNil Q w ν k)) := by
  have hsymm : ∀ x y, bform Q x y = bform Q y x := fun x y => QuadraticMap.associated_isSymm F Q x y
  have hQb : ∀ x, bform Q x x = Q x := fun x => QuadraticMap.associated_eq_self_apply F Q x
  set U₁ := Submodule.span F (Set.range fun i : Fin (2 * k + 1) => w ((i : ℤ) - k))
  have hwU : ∀ j : ℤ, |j| ≤ k → w j ∈ U₁ := fun j hj => Submodule.subset_span
    ⟨⟨(j + k).toNat, by rw [abs_le] at hj; omega⟩, by
      simp only; congr 1; rw [abs_le] at hj; omega⟩
  have hU : finrank F U₁ = 2 * k + 1 := by
    rw [finrank_span_eq_card (linearIndependent_isSplitFamily hw hν), Fintype.card_fin]
  have hd₀U : ∀ u ∈ U₁, bform Q d₀ u = 0 := by
    have hle : U₁ ≤ LinearMap.ker (bform Q d₀) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have hi := i.2
      simp only [SetLike.mem_coe, LinearMap.mem_ker]
      rw [hsymm]; exact hd₀w _ (abs_le.2 ⟨by omega, by omega⟩)
    exact fun u hu => hle hu
  have hd₀0 : d₀ ≠ 0 := fun h => hd₀ (by rw [h, map_zero])
  refine ⟨d₀, U₁, Submodule.mem_top, hd₀, le_top, hd₀U, ?_, adV_regNil_of_orthogonal hd₀w,
    fun u hu => adV_regNil_mem_span hw hν hu, ?_, w 0, hwU 0 (by simp), ?_, ?_⟩
  · -- `⟨d₀⟩ ⊔ U₁ = V`
    have hinf : Submodule.span F {d₀} ⊓ U₁ = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hx1, hx2⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx1
      have := hd₀U _ hx2
      rw [map_smul, smul_eq_mul, hQb] at this
      rw [(mul_eq_zero.mp this).resolve_right hd₀, zero_smul]
      exact Submodule.zero_mem _
    apply Submodule.eq_top_of_finrank_eq
    have := Submodule.finrank_sup_add_finrank_inf_eq (Submodule.span F {d₀}) U₁
    rw [hinf, finrank_bot, add_zero, finrank_span_singleton hd₀0, hU] at this
    omega
  · -- one Jordan block
    obtain ⟨ε, hε, he⟩ := adV_regNil_pow_w hw hν (j := 2 * k) le_rfl
    refine ⟨w (-k), hwU _ (by simp), ?_⟩
    rw [hU, show 2 * k + 1 - 1 = 2 * k by omega, he]
    refine smul_ne_zero hε fun h0 => hν ?_
    have := hw ((2 * k : ℕ) - k) (-k) (by rw [abs_le]; push_cast; omega) (by simp)
    rw [h0, map_zero, LinearMap.zero_apply, ite_eq_left (by push_cast; ring)] at this
    exact this.symm
  · rw [← hQb, hw 0 0 (by simp) (by simp), ite_eq_left (by ring)]
  · -- `U₁ ∩ w_0^⊥` is split
    set S := U₁ ⊓ (bform Q).orthogonal (Submodule.span F {w 0})
    have hSlt : S < U₁ := by
      refine lt_of_le_of_ne inf_le_left fun hSU => ?_
      have h0 : w 0 ∈ S := hSU ▸ hwU 0 (by simp)
      have := (Submodule.mem_inf.mp h0).2 (w 0) (Submodule.mem_span_singleton_self _)
      change bform Q (w 0) (w 0) = 0 at this
      rw [hw 0 0 (by simp) (by simp), ite_eq_left (by ring)] at this
      exact hν this
    have hS : finrank F S ≤ 2 * k := by
      have := Submodule.finrank_lt_finrank_of_lt hSlt; omega
    set T := Submodule.span F (Set.range fun i : Fin k => w ((i : ℤ) + 1))
    have hTS : T ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have hi := i.2
      refine ⟨hwU _ (abs_le.2 ⟨by omega, by omega⟩), fun x hx => ?_⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      change bform Q (c • w 0) (w ((i : ℤ) + 1)) = 0
      rw [map_smul, LinearMap.smul_apply, hw 0 _ (by simp) (abs_le.2 ⟨by omega, by omega⟩),
        ite_eq_right (by omega), smul_zero]
    have hTiso : ∀ y ∈ T, ∀ z ∈ T, bform Q y z = 0 := by
      have hgen : ∀ i j : Fin k, bform Q (w ((i : ℤ) + 1)) (w ((j : ℤ) + 1)) = 0 := by
        intro i j
        have := i.2; have := j.2
        rw [hw _ _ (abs_le.2 ⟨by omega, by omega⟩) (abs_le.2 ⟨by omega, by omega⟩),
          ite_eq_right (by omega)]
      have h1 : ∀ i : Fin k, T ≤ LinearMap.ker (bform Q (w ((i : ℤ) + 1))) := fun i => by
        rw [Submodule.span_le]; rintro _ ⟨j, rfl⟩; exact hgen i j
      intro y hy z hz
      induction hy using Submodule.span_induction with
      | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h1 i hz
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, LinearMap.add_apply, ha, hb, add_zero]
      | smul c a _ ha => rw [map_smul, LinearMap.smul_apply, ha, smul_zero]
    have hTk : finrank F T = k := by
      let f : Fin k → Fin (2 * k + 1) := fun i => ⟨i + 1 + k, by omega⟩
      have hf : Function.Injective f := fun a b h => Fin.ext (by
        have := congrArg Fin.val h; simp only [f] at this; omega)
      have hli := (linearIndependent_isSplitFamily hw hν).comp f hf
      have e : ((fun i : Fin (2 * k + 1) => w ((i : ℤ) - k)) ∘ f) =
          fun i : Fin k => w ((i : ℤ) + 1) := by
        funext i; simp only [Function.comp, f]; congr 1; push_cast; ring
      rw [e] at hli
      rw [finrank_span_eq_card hli, Fintype.card_fin]
    set T' := T.comap S.subtype
    have hT' : finrank F T' = k := by
      rw [(Submodule.comapSubtypeEquivOfLe hTS).finrank_eq, hTk]
    have hiso : IsTotallyIsotropic (Q.comp S.subtype) T' := by
      intro u hu
      have huT : (u : V) ∈ T := hu
      change Q (u : V) = 0
      rw [← hQb]; exact hTiso _ huT _ huT
    have := QuadClassify.le_wittIndex hiso
    unfold IsSplitQF
    omega

/-- `V'_x = W'_x ⊕ Z` (`QVfix`) is the fixed space of `P(incl x)` in `V`, with the restricted form. -/
def QVfixIso (d : GGPData F) (x : GSpin d.QW) :
    (d.QVfix x).IsometryEquiv (d.QV.comp (fixedSub (d.incl x)).subtype) where
  toFun p := ⟨((p.1 : Fin d.m → F), p.2), (d.mem_fixedSub_incl_iff x _ _).mpr p.1.2⟩
  invFun v := (⟨(v : d.V).1, (d.mem_fixedSub_incl_iff x (v : d.V).1 (v : d.V).2).mp v.2⟩, (v : d.V).2)
  map_add' p q := rfl
  map_smul' c p := rfl
  left_inv p := rfl
  right_inv v := rfl
  map_app' p := by
    simp [GGPData.QVfix, GGPData.QWfix, QuadraticMap.prod_apply]

/-- **Existence of regular nilpotent orbits of `𝔤_x`** (the direction `⇐` of
`nilReg_centralizer_nonempty_iff`). For semisimple `x` with abelian moved part and `W'_x`, `V'_x`
quasi-split: `X = (regNil on W'_x, regNil on V'_x)` is regular nilpotent in `𝔤_x`. Indeed
`dim 𝔤_{x,Y} = dim so(W'_x)_{Y} + dim so(V'_x)_{Y} + (moved parts, constant) + 2` for `Y ∈ 𝔤_x`
(`finrank_lieCentralizer_lieCentralizer_lie`, `finrank_lieCentralizer_fixed`,
`soCent_inf_killSub_eq`), and the `so(W'_x)`, `so(V'_x)` terms are minimal at `X`
(`le_finrank_soCent`, `finrank_soCent_regNil_le`). -/
theorem nilReg_centralizer_nonempty_of_quasiSplit (d : GGPData F) (x : GSpin d.QW)
    (hx : IsSS F ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW))
    (hmoved : MovedPartAbelian d.QW x) (hW : IsQuasiSplitQF (d.QWfix x))
    (hV : IsQuasiSplitQF (d.QVfix x)) :
    (NilReg (grpCentralizer d.G ((d.diag x : d.G) : d.ambientˣ))
      (lieCentralizer d.lie (((d.diag x : d.G) : d.ambientˣ) : d.ambient))).Nonempty := by
  set dx : d.ambient := (((d.diag x : d.G) : d.ambientˣ) : d.ambient)
  have hdx : dx = (((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW),
      ((d.incl x : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV)) := rfl
  have hdisj := fixedSub_inf_movedSub_of_isSS x hx
  have hcW := isCompl_fixedSub_orthogonal d.nondeg x hdisj
  have hcV := isCompl_fixedSub_orthogonal d.nondeg_QV (d.incl x)
    (fixedSub_inf_movedSub_incl d x hdisj)
  have habW := commute_of_movedPart d.nondeg x hmoved
  have habV := commute_movedPart_incl d x habW
  have hV' : IsQuasiSplitQF (d.QV.comp (fixedSub (d.incl x)).subtype) :=
    QuadClassify.isQuasiSplitQF_of_isometryEquiv (QVfixIso d x) hV
  obtain ⟨XW, hXWm, hXWn, hXWb⟩ := exists_side_regNil d.nondeg x hcW hW
  obtain ⟨XV, hXVm, hXVn, hXVb⟩ := exists_side_regNil d.nondeg_QV (d.incl x) hcV hV'
  set X : d.ambient := (XW, XV)
  have hXm : X ∈ lieCentralizer d.lie dx := by
    obtain ⟨h1, h2⟩ := mem_lieCentralizer.mp hXWm
    obtain ⟨h3, h4⟩ := mem_lieCentralizer.mp hXVm
    exact mem_lieCentralizer.mpr ⟨⟨h1, h3⟩, by rw [hdx]; exact Prod.ext h2 h4⟩
  have hXn : IsNilpotent X := by
    obtain ⟨n, hn⟩ := hXWn
    obtain ⟨k, hk⟩ := hXVn
    refine ⟨n + k, ?_⟩
    rw [Prod.pow_mk, pow_eq_zero_of_le (Nat.le_add_right n k) hn,
      pow_eq_zero_of_le (Nat.le_add_left k n) hk]; rfl
  have hreg : IsRegularNil (lieCentralizer d.lie dx) X := by
    refine ⟨hXm, hXn, le_antisymm ?_ ?_⟩
    · have : Nonempty ↥(lieCentralizer d.lie dx) := ⟨0⟩
      refine le_ciInf fun Y => ?_
      obtain ⟨⟨hY1, hY2⟩, hYc⟩ := mem_lieCentralizer.mp Y.2
      have hYc1 : ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * (Y : d.ambient).1 =
          (Y : d.ambient).1 * ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) :=
        congrArg Prod.fst hYc
      have hYc2 : ((d.incl x : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) * (Y : d.ambient).2 =
          (Y : d.ambient).2 * ((d.incl x : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) :=
        congrArg Prod.snd hYc
      have hY1m : (Y : d.ambient).1 ∈ lieCentralizer (gspin d.QW)
          ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) :=
        mem_lieCentralizer.mpr ⟨hY1, hYc1⟩
      have hY2m : (Y : d.ambient).2 ∈ lieCentralizer (gspin d.QV)
          ((d.incl x : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) :=
        mem_lieCentralizer.mpr ⟨hY2, hYc2⟩
      have l1 := le_finrank_lieCentralizer_fixed d.nondeg x hcW habW hY1m
      have l2 := le_finrank_lieCentralizer_fixed d.nondeg_QV (d.incl x) hcV habV hY2m
      rw [finrank_lieCentralizer_lieCentralizer_lie, finrank_lieCentralizer_lieCentralizer_lie]
      exact Nat.add_le_add (hXWb.trans l1) (hXVb.trans l2)
    · unfold lieRank
      exact ciInf_le (OrderBot.bddBelow _) (⟨X, hXm⟩ : lieCentralizer d.lie dx)
  have hG : ∀ g ∈ grpCentralizer d.G ((d.diag x : d.G) : d.ambientˣ), ∀ Y ∈ lieCentralizer d.lie dx,
      (g : d.ambient) * Y * (↑g⁻¹ : d.ambient) ∈ lieCentralizer d.lie dx := by
    intro g hg Y hY
    obtain ⟨hgG, hgc⟩ := Subgroup.mem_inf.mp hg
    have hgc' : (g : d.ambient) * dx = dx * g := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hgc
      exact congrArg Units.val this
    obtain ⟨hYl, hYc⟩ := mem_lieCentralizer.mp hY
    refine mem_lieCentralizer.mpr ⟨⟨conj_mem_gspin d.QW (d.fst ⟨g, hgG⟩) hYl.1,
      conj_mem_gspin d.QV (d.snd ⟨g, hgG⟩) hYl.2⟩, ?_⟩
    have hc1 : Commute dx (g : d.ambient) := hgc'.symm
    have hc3 : Commute dx (↑g⁻¹ : d.ambient) := hc1.units_inv_right
    exact ((hc1.mul_right hYc).mul_right hc3)
  exact ⟨_, mk_mem_nilReg_of_isRegularNil _ _ hG ⟨X, hXm, hXn⟩ hreg⟩

/-- **Witt data for `O_{−ν}` in `W`** (the second Witt-theory step in the docstring of
`exists_regularNil_inOrbitNu`): for a quasi-split GGP datum with `dim W = 2s + 2` even, `W` contains
hyperbolic pairs `h_0, …, h_{2s-1}`, a vector `u` with `q(u) = −ν` and an anisotropic `d₀`, all
mutually orthogonal (`W ≅ ⟨b⟩ ⊥ ⟨−ν⟩ ⊥ H^s`).

Proof: `W ≅ H^t ⊥ A` with `A` anisotropic of dimension `0` or `2`. If `A = 0`, take
`u = h₀ − (ν/2) h_{2t-1}`, `d₀ = h₀ + (ν/2) h_{2t-1}`. If `A` is a plane: `V = W ⊥ Z` is odd and
quasi-split, so `V ≅ H^{s+r+1} ⊥ ⟨b⟩`; also `V ≅ H^{s+r} ⊥ (A ⊥ ⟨ν⟩)` (`Z ≅ H^r ⊥ ⟨ν⟩`,
`splitOddIso`), so Witt cancellation gives `A ⊥ ⟨ν⟩ ≅ H ⊥ ⟨b⟩`, which is isotropic; as `A` is
anisotropic, `A` represents `−ν`, and `d₀` spans the orthogonal of `u` in `A`. -/
theorem exists_wittData_W (d : GGPData F) (hqs : d.IsQuasiSplit) (s : ℕ) (hm : d.m = 2 * s + 2) :
    ∃ (h : ℕ → Fin d.m → F) (u d₀ : Fin d.m → F), (∀ i j : ℕ, i < 2 * s → j < 2 * s →
      bform d.QW (h i) (h j) = if i + j + 1 = 2 * s then 1 else 0) ∧
      d.QW u = -(d.ν : F) ∧ d.QW d₀ ≠ 0 ∧ bform d.QW u d₀ = 0 ∧
      (∀ j : ℕ, j < 2 * s → bform d.QW u (h j) = 0) ∧
      (∀ j : ℕ, j < 2 * s → bform d.QW d₀ (h j) = 0) := by
  have hν : (d.ν : F) ≠ 0 := d.ν.ne_zero
  obtain ⟨ka, Qa, hani, ⟨I⟩, hdimW⟩ := witt_decomposition d.QW d.nondeg
  set t := wittIndex d.QW with ht
  have hqW := hqs.1
  unfold IsQuasiSplitQF at hqW
  rw [Module.finrank_fin_fun] at hdimW hqW
  let J := I.symm
  have hJ : ∀ x y, bform d.QW (J x) (J y) = bform (hypForm F t) x.1 y.1 + bform Qa x.2 y.2 :=
    fun x y => (bform_isometry J.toIsometry x y).trans (bform_prod _ _ x y)
  have hJQ : ∀ x, d.QW (J x) = hypForm F t x.1 + Qa x.2 := fun x => by
    rw [QuadraticMap.IsometryEquiv.map_app, QuadraticMap.prod_apply]
  let h' : ℕ → Fin d.m → F := fun a => if ha : a < 2 * t then J (Pi.single ⟨a, ha⟩ 1, 0) else 0
  have hh' : ∀ a b : ℕ, a < 2 * t → b < 2 * t →
      bform d.QW (h' a) (h' b) = if a + b + 1 = 2 * t then 1 else 0 := by
    intro a b ha hb
    simp only [h', dite_eq_left ha, dite_eq_left hb]
    rw [hJ, bform_hypForm_single]
    simp
  rcases (by omega : ka = 0 ∨ ka = 2) with hka | hka
  · -- `W` hyperbolic: use the pair `h'_0, h'_{2t-1}`
    have hts : t = s + 1 := by omega
    set c : F := -(d.ν : F) / 2
    let u := h' 0 + c • h' (2 * t - 1)
    let d₀ := h' 0 - c • h' (2 * t - 1)
    have hQb : ∀ x, bform d.QW x x = d.QW x := fun x => QuadraticMap.associated_eq_self_apply F d.QW x
    have hsymm : ∀ x y, bform d.QW x y = bform d.QW y x :=
      fun x y => QuadraticMap.associated_isSymm F d.QW x y
    have b00 := hh' 0 0 (by omega) (by omega)
    have b01 := hh' 0 (2 * t - 1) (by omega) (by omega)
    have b10 := hh' (2 * t - 1) 0 (by omega) (by omega)
    have b11 := hh' (2 * t - 1) (2 * t - 1) (by omega) (by omega)
    rw [ite_eq_right (by omega)] at b00 b11
    rw [ite_eq_left (by omega)] at b01 b10
    refine ⟨fun a => h' (a + 1), u, d₀, fun i j hi hj => ?_, ?_, ?_, ?_, fun j hj => ?_,
      fun j hj => ?_⟩
    · rw [hh' _ _ (by omega) (by omega)]; congr 1; apply propext; omega
    · rw [← hQb]
      simp only [u, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        b00, b01, b10, b11, c]
      field_simp; ring
    · rw [← hQb]
      simp only [d₀, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        b00, b01, b10, b11, c]
      intro h0; apply hν; linear_combination h0
    · simp only [u, d₀, map_add, map_sub, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, b00, b01, b10, b11]
      ring
    · simp only [u, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hh' _ _ (by omega) (by omega), hh' _ _ (by omega) (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]; ring
    · simp only [d₀, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hh' _ _ (by omega) (by omega), hh' _ _ (by omega) (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]; ring
  · -- `W = H^s ⊥ A`, `A` an anisotropic plane; `A` represents `−ν` because `V` is split
    have hts : t = s := by omega
    subst hka
    have hQb : ∀ x, bform Qa x x = Qa x := fun x => QuadraticMap.associated_eq_self_apply F Qa x
    -- `A ⊥ ⟨ν⟩` is isotropic: Witt cancellation against `V ≅ H^{s+r+1} ⊥ ⟨b⟩`
    obtain ⟨kb, Qb, -, ⟨IV⟩, hdimV⟩ := witt_decomposition d.QV d.nondeg_QV
    have hqV := hqs.2
    unfold IsQuasiSplitQF at hqV
    have hn : finrank F d.V = 2 * s + 2 + (2 * d.r + 1) := by
      rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun, hm]
    have hwV : wittIndex d.QV = s + d.r + 1 := by omega
    let Qν : QuadraticForm F (Fin (2 * 0 + 1) → F) := splitOddForm 0 (d.ν : F)
    let I' : ((hypForm F s).prod Qa).IsometryEquiv d.QW := hts ▸ I.symm
    let L1 : ((hypForm F (s + d.r)).prod (Qa.prod Qν)).IsometryEquiv d.QV :=
      (((LeviAux.hypAddEquiv s d.r).symm.prod (QuadraticMap.IsometryEquiv.refl _)).trans
        (QuadraticMap.IsometryEquiv.prodProdProdComm _ _ _ _)).trans
        (I'.prod (LeviAux.splitOddIso d.r hν))
    let IV' : d.QV.IsometryEquiv ((hypForm F (s + d.r + 1)).prod Qb) := hwV ▸ IV
    let L2 : d.QV.IsometryEquiv ((hypForm F (s + d.r)).prod ((hypForm F 1).prod Qb)) :=
      (IV'.trans ((LeviAux.hypAddEquiv (s + d.r) 1).symm.prod (QuadraticMap.IsometryEquiv.refl Qb))).trans
        (WittParity.assocIso _ _ _)
    obtain ⟨E⟩ := witt_cancellation _ _ _ ⟨L1.trans L2⟩
    set y := E.symm (Pi.single 0 1, 0)
    have hy0 : y ≠ 0 := fun h0 => by
      have := congrArg E h0
      rw [QuadraticMap.IsometryEquiv.apply_symm_apply, map_zero, Prod.mk_eq_zero] at this
      simpa using congrFun this.1 0
    have hyQ : (Qa.prod Qν) y = 0 := by
      rw [QuadraticMap.IsometryEquiv.map_app, QuadraticMap.prod_apply, map_zero, add_zero,
        ← QuadraticMap.associated_eq_self_apply F, ← bform, bform_hypForm_single]
      simp
    rcases hyd : y with ⟨x, τ⟩
    rw [hyd] at hy0 hyQ
    rw [QuadraticMap.prod_apply] at hyQ
    have hτQ : Qν τ = (d.ν : F) * τ 0 ^ 2 := by
      simp only [Qν, LeviAux.splitOddForm_apply, sq]
      rw [Finset.sum_eq_single 0 (fun i _ hi => absurd (Fin.ext (by have := i.2; omega)) hi)
        (by simp)]
      rw [show (0 : Fin (2 * 0 + 1)).rev = 0 from Fin.ext (by simp)]
    have hτ0 : τ 0 ≠ 0 := by
      intro h0
      have hτ : τ = 0 := funext fun i => by
        rw [show i = 0 from Fin.ext (by have := i.2; omega), h0]; rfl
      rw [hτ, map_zero, add_zero] at hyQ
      exact hy0 (by rw [hani x hyQ, hτ]; rfl)
    set x' := (τ 0)⁻¹ • x
    have hx' : Qa x' = -(d.ν : F) := by
      rw [hτQ] at hyQ
      have hx : Qa x = -(d.ν : F) * τ 0 ^ 2 := by linear_combination hyQ
      rw [QuadraticMap.map_smul, smul_eq_mul, hx]
      field_simp
    have hQa : IsNondeg Qa := QuadClassify.isNondeg_of_prod_right
      ((QuadClassify.DiscRel.of_isometryEquiv I).isNondeg d.nondeg)
    have hx'0 : x' ≠ 0 := fun h0 => by
      rw [h0, map_zero] at hx'; exact hν (neg_eq_zero.mp hx'.symm)
    have hperp : finrank F ((bform Qa).orthogonal (F ∙ x')) = 1 := by
      rw [LinearMap.BilinForm.finrank_orthogonal hQa, finrank_span_singleton hx'0,
        Module.finrank_fin_fun]
    obtain ⟨y0, hy0mem, hy0ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (p := (bform Qa).orthogonal (F ∙ x')) (fun hb => by
      rw [hb, finrank_bot] at hperp; exact zero_ne_one hperp)
    have hxy : bform Qa x' y0 = 0 := hy0mem x' (Submodule.mem_span_singleton_self _)
    refine ⟨h', J (0, x'), J (0, y0), fun i j hi hj => ?_, ?_, ?_, ?_, fun j hj => ?_,
      fun j hj => ?_⟩
    · rw [hh' _ _ (by omega) (by omega), hts]
    · rw [hJQ]; simp [hx']
    · rw [hJQ]; simp only [map_zero, zero_add]; exact fun h0 => hy0ne (hani y0 h0)
    · rw [hJ]; simp [hxy]
    · simp only [h', dite_eq_left (show j < 2 * t by omega)]; rw [hJ]; simp
    · simp only [h', dite_eq_left (show j < 2 * t by omega)]; rw [hJ]; simp

/-- **Luo's orbit `O_ν` exists in the GGP situation** (Waldspurger, *Compositio* 146 (2010),
§7.1; Luo, *A local trace formula for the local Gan–Gross–Prasad conjecture for special
orthogonal groups*, §2.1 and §7.1; classification of regular nilpotent orbits: Waldspurger,
*Astérisque* 269 (2001), Ch. I; Thesis §5.1.4 "Regular Nilpotent Orbits").

For a quasi-split GGP datum (`V = W ⊕^⊥ Z`, `Z = ⟨ν⟩ ⊕ H^r` with `q(z₀) = ν`):
* if `dim V` is even and `≥ 4`, some regular nilpotent `X ∈ gspin(V)` has image `ad X ∈ so(V)` in
  `O_ν` (`IsInOrbitNu`: `V = F d₀ ⊕^⊥ U₁`, `d₀` anisotropic, `U₁ ≅ ⟨ν⟩ ⊕ H^k`, `ad X` kills `d₀`
  and is one Jordan block on `U₁`);
* if `dim W` is even and `≥ 4`, some regular nilpotent `X ∈ gspin(W)` has `ad X ∈ O_{−ν}`.

What the sources give, and what is packaged here. The sources classify `Nil_reg(so(U))` for a
quasi-split even-dimensional `U` by the classes `ν' ∈ 𝒩^U` such that `U ≅ ⟨a⟩ ⊕ ⟨ν'⟩ ⊕ H^{k}`,
the orbit `O_{ν'}` being the orbit of a regular nilpotent of `so(U₁)`, `U₁ = ⟨ν'⟩ ⊕ H^k`, extended
by `0` on `⟨a⟩`; it is a regular orbit of `so(U)` (Jordan type `(dim U − 1, 1)`), and lifts to
`gspin(U) = so(U) ⊕ F` with centralizer of dimension `rank so(U) + 1 = rank gspin(U)`. The proof
also uses the elementary (Witt-theory) fact that the relevant class is in `𝒩`:
`dim V` even ⇒ `W` odd and quasi-split, hence split, `W = ⟨a⟩ ⊕ W₁` with `W₁` hyperbolic, so
`V = ⟨a⟩ ⊕ (W₁ ⊕ Z)` and `W₁ ⊕ Z ≅ ⟨ν⟩ ⊕ H^{k+r}`; `dim W = 2m' ≥ 4` ⇒ `V` odd quasi-split,
hence `V ≅ ⟨b⟩ ⊕ H^{m'+r}`, and Witt cancellation of `H^r ⊕ ⟨ν⟩` against `⟨ν⟩ ⊕ ⟨−ν⟩ ≅ H` gives
`W ≅ ⟨b⟩ ⊕ ⟨−ν⟩ ⊕ H^{m'−1}`. These are the classes `ν₀ = q(z₀)` (for `V`) and `−ν₀` (for `W`)
used by Luo §7.1.

All hypotheses are explicit binders; for `toyData`
(`dim W = 0`, `dim V = 1`) both conjuncts are vacuous; the smallest non-vacuous cases
(`dim W = 1`, `r = 1`, `dim V = 4`; `dim W = 4`, `r = 0`, `dim V = 5`) agree with the
classification. `ν ≠ 0` (it is a unit) is what makes `U₁ ≠ 0`, so the clause
`(ad X)^{dim U₁ − 1} ≠ 0` on `U₁` is satisfiable.

**Status: proved.** The element is
`regNil` on a split family built from `Z` and the hyperbolic part of `W` (first case) or from
`exists_wittData_W` (second case); it is regular nilpotent (`isRegularNil_regNil`) and lies in `O_ν`
(`isInOrbitNu_regNil`). -/
theorem exists_regularNil_inOrbitNu {F : Type*} [NontriviallyNormedField F] [PAdicField F]
    (d : GGPData F) (hqs : d.IsQuasiSplit) :
    (Even (finrank F d.V) → 4 ≤ finrank F d.V →
      ∃ X : CliffordAlgebra d.QV, IsRegularNil (gspin d.QV) X ∧
        IsInOrbitNu d.QV ⊤ (d.ν : F) (adV d.QV X)) ∧
    (Even d.m → 4 ≤ d.m →
      ∃ X : CliffordAlgebra d.QW, IsRegularNil (gspin d.QW) X ∧
        IsInOrbitNu d.QW ⊤ (-(d.ν : F)) (adV d.QW X)) := by
  have hν : (d.ν : F) ≠ 0 := d.ν.ne_zero
  have hsymmW : ∀ x y, bform d.QW x y = bform d.QW y x :=
    fun x y => QuadraticMap.associated_isSymm F d.QW x y
  have hQbW : ∀ x, bform d.QW x x = d.QW x := fun x => QuadraticMap.associated_eq_self_apply F d.QW x
  constructor
  · intro hev h4
    have hdimV : finrank F d.V = d.m + (2 * d.r + 1) := by
      rw [Module.finrank_prod, Module.finrank_fin_fun, Module.finrank_fin_fun]
    have hodd : Odd (finrank F (Fin d.m → F)) := by
      rw [Module.finrank_fin_fun]; rw [hdimV] at hev
      obtain ⟨t, ht⟩ := hev; exact ⟨t - d.r - 1, by omega⟩
    obtain ⟨s, h, a, hh, ha, hah, hm⟩ := exists_hyp_of_quasiSplit_odd d.nondeg hqs.1 hodd
    rw [Module.finrank_fin_fun] at hm
    let wZ : ℤ → d.V := fun j => (0, zvec d.r j)
    have hwZ : IsSplitFamily d.QV wZ (d.ν : F) d.r := by
      intro i j hi hj
      rw [bform_prod]
      simp only [wZ, map_zero, zero_add]
      exact bform_splitOddForm_zvec d.r _ hi hj
    let hV : ℕ → d.V := fun b => (h b, 0)
    have hw : IsSplitFamily d.QV (extFamily wZ hV (d.ν : F) d.r s) (d.ν : F) (d.r + s) :=
      isSplitFamily_extFamily hwZ (fun i j hi hj => by
        rw [bform_prod]; simp only [hV, map_zero, add_zero]; exact hh i j hi hj)
        (fun j _ b _ => by rw [bform_prod]; simp [wZ, hV])
    have hdim : finrank F d.V = 2 * (d.r + s) + 2 := by omega
    refine ⟨_, isRegularNil_regNil d.nondeg_QV hw hν hdim.le, isInOrbitNu_regNil hw hν
      (d₀ := (a, 0)) ?_ (fun j hj => ?_) hdim⟩
    · simpa using ha
    · have hj' := abs_le.mp hj
      push_cast at hj'
      simp only [extFamily]
      split_ifs with h1 h2
      · rw [bform_prod]; simp [wZ]
      · rw [bform_prod]
        simp only [hV, Prod.smul_fst, Prod.smul_snd, smul_zero, map_smul, LinearMap.smul_apply,
          map_zero, add_zero]
        rw [hsymmW, hah _ (by rw [abs_le] at h1; omega), smul_zero]
      · rw [bform_prod]; simp only [hV, map_zero, add_zero]
        rw [hsymmW, hah _ (by rw [abs_le] at h1; omega)]
  · intro hev h4
    obtain ⟨s, hs⟩ : ∃ s, d.m = 2 * s + 2 := by
      obtain ⟨t, ht⟩ := hev; exact ⟨t - 1, by omega⟩
    obtain ⟨h, u, d₀, hh, hu, hd₀, hud, huh, hdh⟩ := exists_wittData_W d hqs s hs
    have hw : IsSplitFamily d.QW (extFamily (fun _ => u) h (-(d.ν : F)) 0 s) (-(d.ν : F)) (0 + s) :=
      isSplitFamily_extFamily (fun i j hi hj => by
        have hi0 : i = 0 := by rw [abs_le] at hi; omega
        have hj0 : j = 0 := by rw [abs_le] at hj; omega
        subst hi0 hj0; simp [hQbW, hu]) hh (fun j _ b hb => huh b hb)
    have hdim : finrank F (Fin d.m → F) = 2 * (0 + s) + 2 := by rw [Module.finrank_fin_fun]; omega
    refine ⟨_, isRegularNil_regNil d.nondeg hw (neg_ne_zero.2 hν) hdim.le,
      isInOrbitNu_regNil hw (neg_ne_zero.2 hν) hd₀ (fun j hj => ?_) hdim⟩
    have hj' := abs_le.mp hj
    push_cast at hj'
    simp only [extFamily]
    split_ifs with h1 h2
    · exact hud
    · rw [map_smul, LinearMap.smul_apply, hsymmW, hdh _ (by rw [abs_le] at h1; omega), smul_zero]
    · rw [hsymmW, hdh _ (by rw [abs_le] at h1; omega)]

end NilReg

end GSpinGGP
