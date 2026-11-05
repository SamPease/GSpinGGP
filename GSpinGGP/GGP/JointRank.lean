/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.JointCentralizer
import GSpinGGP.GGP.SemisimpleRank
import GSpinGGP.Foundations.IsometrySemisimple
import GSpinGGP.Foundations.IsometryDet

/-!
# The joint centralizer of a commuting semisimple isometry and skew map

Over an algebraically closed field of characteristic `0`, let `P` be a semisimple isometry of a
nondegenerate quadratic form and `N` a semisimple skew map commuting with `P`, and
`C = so(V)_P ⊓ so(V)_N`. Then `dim C ≥ ⌊dim V/2⌋`, with equality iff `C` is abelian, and then `C`
has no nonzero nilpotent element and the only unipotent isometry commuting with `P` and `N` is `1`.
-/

noncomputable section

open Module LinearMap

namespace GSpinGGP

open IsomCent

section Pieces

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {P N : Module.End K V}

/-- Wedges of dual families in paired joint eigenspaces lie in the joint centralizer. -/
theorem wedge_mem_soCent_inf (hP : IsIsom (bform Q) P) (hN : IsSkew (bform Q) N) {μ c : K}
    (hμ : μ ≠ 0) {u w : V} (hu : u ∈ P.eigenspace μ) (hu' : u ∈ N.eigenspace c)
    (hw : w ∈ P.eigenspace μ⁻¹) (hw' : w ∈ N.eigenspace (-c)) :
    wedge (bform Q) u w ∈ soCent Q P ⊓ soCent Q N :=
  ⟨mem_soCent.2 ⟨isSkew_wedge ⟨bform_comm Q⟩ u w,
      (commute_wedge ⟨bform_comm Q⟩ hP (mul_inv_cancel₀ hμ) hu hw).eq.symm⟩,
    mem_soCent.2 ⟨isSkew_wedge ⟨bform_comm Q⟩ u w,
      (commute_wedge_of_skew hN hu' hw').eq.symm⟩⟩

/-- For dual families with `d ≥ 2`, the wedges `u₀ ∧ w₁` and `u₁ ∧ w₀` do not commute. -/
theorem not_commute_wedge_dual {d : ℕ} (hd : 2 ≤ d) (u w : Fin d → V)
    (huu : ∀ i k, bform Q (u i) (u k) = 0)
    (hwu : ∀ j k, bform Q (w j) (u k) = if j = k then 1 else 0) (hu1 : u ⟨1, by omega⟩ ≠ 0) :
    ¬ Commute (wedge (bform Q) (u ⟨0, by omega⟩) (w ⟨1, by omega⟩))
      (wedge (bform Q) (u ⟨1, by omega⟩) (w ⟨0, by omega⟩)) := by
  intro h
  have h1 := LinearMap.congr_fun h.eq (u ⟨1, by omega⟩)
  simp only [Module.End.mul_apply, wedge_apply, map_smul, huu, hwu, Fin.mk.injEq,
    zero_smul, sub_zero, ite_true, one_smul] at h1
  simp at h1
  exact hu1 h1.symm

variable (hP : IsIsom (bform Q) P) (hN : IsSkew (bform Q) N) {μ c : K} (hμ0 : μ ≠ 0)
  (hne : μ⁻¹ ≠ μ ∨ c ≠ 0) {u w : V} (hu : P u = μ • u) (hu' : N u = c • u) (hw : P w = μ⁻¹ • w)
  (hw' : N w = (-c) • w) (huw : bform Q u w ≠ 0) (hspan : Submodule.span K {u, w} = ⊤)
include hP hN hμ0 hne hu hu' hw hw' huw hspan

/-- On a hyperbolic pair of joint eigenvectors `u`, `w` spanning `V` (`P u = μ u`, `N u = c u`,
`P w = μ⁻¹ w`, `N w = −c w`, `(μ, c) ≠ (μ⁻¹, −c)`, `b(u, w) ≠ 0`): `u`, `w` are isotropic and the
joint eigenspaces for `(μ, c)`, `(μ⁻¹, −c)` are the lines `K u`, `K w`. -/
private theorem pair_facts :
    bform Q u u = 0 ∧ bform Q w w = 0 ∧
    (∀ x, P x = μ • x → N x = c • x → ∃ t : K, x = t • u) ∧
    (∀ x, P x = μ⁻¹ • x → N x = (-c) • x → ∃ t : K, x = t • w) := by
  have h2 : (2 : K) ≠ 0 := Invertible.ne_zero 2
  have hiso : ∀ {x : V} {ν e : K}, (ν⁻¹ ≠ ν ∨ e ≠ 0) → P x = ν • x → N x = e • x →
      bform Q x x = 0 := by
    intro x ν e hνe hx hx'
    rcases hνe with h | h
    · have hνν : ν * ν ≠ 1 := fun h1 => h (by rw [inv_eq_of_mul_eq_one_right h1])
      exact bform_eigen_eq_zero (B := bform Q) hP hνν (Module.End.mem_eigenspace_iff.2 hx)
        (Module.End.mem_eigenspace_iff.2 hx)
    · exact bform_eigen_eq_zero_of_skew hN (c := e) (c' := e) (by
        rw [← two_mul]; exact mul_ne_zero h2 h) (Module.End.mem_eigenspace_iff.2 hx')
        (Module.End.mem_eigenspace_iff.2 hx')
  have hw0 : w ≠ 0 := fun h => huw (by rw [h, map_zero])
  have hu0 : u ≠ 0 := fun h => huw (by rw [h, map_zero, LinearMap.zero_apply])
  have hmem : ∀ x : V, ∃ a b : K, a • u + b • w = x := fun x =>
    Submodule.mem_span_pair.1 (hspan ▸ Submodule.mem_top)
  have key : ∀ a : K, a * (μ - μ⁻¹) = 0 → a * (c + c) = 0 → a = 0 := by
    intro a ha ha'
    rcases hne with h | h
    · exact (mul_eq_zero.1 ha).resolve_right (sub_ne_zero.2 h.symm)
    · exact (mul_eq_zero.1 ha').resolve_right (by rw [← two_mul]; exact mul_ne_zero h2 h)
  refine ⟨hiso hne hu hu', hiso (ν := μ⁻¹) (e := -c) ?_ hw hw', fun x hx hx' => ?_,
    fun x hx hx' => ?_⟩
  · rcases hne with h | h
    · exact Or.inl (by rw [inv_inv]; exact h.symm)
    · exact Or.inr (neg_ne_zero.2 h)
  · obtain ⟨a, b, rfl⟩ := hmem x
    simp only [map_add, map_smul, hu, hu', hw, hw'] at hx hx'
    have e1 : (b * (μ⁻¹ - μ)) • w = 0 := by linear_combination (norm := module) hx
    have e2 : (b * (-c - c)) • w = 0 := by linear_combination (norm := module) hx'
    have hb : b = 0 := key b
      (by have := (smul_eq_zero.1 e1).resolve_right hw0; linear_combination -this)
      (by have := (smul_eq_zero.1 e2).resolve_right hw0; linear_combination -this)
    exact ⟨a, by rw [hb, zero_smul, add_zero]⟩
  · obtain ⟨a, b, rfl⟩ := hmem x
    simp only [map_add, map_smul, hu, hu', hw, hw'] at hx hx'
    have e1 : (a * (μ - μ⁻¹)) • u = 0 := by linear_combination (norm := module) hx
    have e2 : (a * (c + c)) • u = 0 := by linear_combination (norm := module) hx'
    have ha : a = 0 := key a ((smul_eq_zero.1 e1).resolve_right hu0)
      ((smul_eq_zero.1 e2).resolve_right hu0)
    exact ⟨b, by rw [ha, zero_smul, zero_add]⟩

/-- **A hyperbolic pair of joint eigenvectors**: the joint centralizer is the line spanned by
`u ∧ w`. -/
theorem soCent_inf_eq_span_wedge :
    soCent Q P ⊓ soCent Q N = K ∙ wedge (bform Q) u w := by
  obtain ⟨huu, hww, lineu, linew⟩ := pair_facts hP hN hμ0 hne hu hu' hw hw' huw hspan
  have hsym : ∀ x y, bform Q x y = bform Q y x := bform_comm Q
  have hmem : ∀ x : V, ∃ a b : K, a • u + b • w = x := fun x =>
    Submodule.mem_span_pair.1 (hspan ▸ Submodule.mem_top)
  have hJ : wedge (bform Q) u w ∈ soCent Q P ⊓ soCent Q N :=
    wedge_mem_soCent_inf hP hN hμ0 (Module.End.mem_eigenspace_iff.2 hu)
      (Module.End.mem_eigenspace_iff.2 hu') (Module.End.mem_eigenspace_iff.2 hw)
      (Module.End.mem_eigenspace_iff.2 hw')
  ext M
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨hMP, hMN⟩
    obtain ⟨hsk, hc⟩ := mem_soCent.1 hMP
    have hcN := (mem_soCent.1 hMN).2
    have hXM : ∀ x, P (M x) = M (P x) := fun x =>
      (congrArg (fun F : Module.End K V => F x) hc).symm
    have hNM : ∀ x, N (M x) = M (N x) := fun x =>
      (congrArg (fun F : Module.End K V => F x) hcN).symm
    obtain ⟨t, ht⟩ := lineu (M u) (by rw [hXM, hu, map_smul]) (by rw [hNM, hu', map_smul])
    obtain ⟨s, hs⟩ := linew (M w) (by rw [hXM, hw, map_smul]) (by rw [hNM, hw', map_smul])
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

omit hP hN hμ0 hne hu hu' hw hw' huw hspan in
omit [Invertible (2 : K)] in
private theorem pow_apply_of_eq_smul {f : Module.End K V} {x : V} {r : K} (hx : f x = r • x) (k : ℕ) :
    (f ^ k) x = r ^ k • x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, hx, smul_smul, pow_succ]

/-- On a hyperbolic pair of joint eigenvectors, the joint centralizer has no nonzero nilpotent
element, and the only unipotent isometry commuting with `P` and `N` is `1`. -/
theorem pair_nilpotent_unipotent :
    (∀ M ∈ soCent Q P ⊓ soCent Q N, IsNilpotent M → M = 0) ∧
    (∀ h : Module.End K V, IsIsom (bform Q) h → IsNilpotent (h - 1) → Commute P h →
      Commute N h → h = 1) := by
  obtain ⟨huu, hww, lineu, linew⟩ := pair_facts hP hN hμ0 hne hu hu' hw hw' huw hspan
  have hC := soCent_inf_eq_span_wedge hP hN hμ0 hne hu hu' hw hw' huw hspan
  have hwu : bform Q w u ≠ 0 := by rwa [bform_comm Q]
  have hu0 : u ≠ 0 := fun h => huw (by rw [h, map_zero, LinearMap.zero_apply])
  have hw0 : w ≠ 0 := fun h => huw (by rw [h, map_zero])
  refine ⟨fun M hM hnil => ?_, fun h hi hnil hPh hNh => ?_⟩
  · rw [hC, Submodule.mem_span_singleton] at hM
    obtain ⟨r, rfl⟩ := hM
    obtain ⟨k, hk⟩ := hnil
    have hJu : wedge (bform Q) u w u = bform Q w u • u := by
      rw [wedge_apply, huu, zero_smul, sub_zero]
    have hru : (r • wedge (bform Q) u w) u = (r * bform Q w u) • u := by
      rw [LinearMap.smul_apply, hJu, smul_smul]
    have := pow_apply_of_eq_smul hru k
    rw [hk, LinearMap.zero_apply, eq_comm, smul_eq_zero] at this
    have hr : r = 0 := by
      rcases this with h | h
      · exact (mul_eq_zero.1 (pow_eq_zero_iff'.1 h).1).resolve_right hwu
      · exact absurd h hu0
    rw [hr, zero_smul]
  · have hPh' : ∀ x, P (h x) = h (P x) := fun x => (LinearMap.congr_fun hPh.eq x)
    have hNh' : ∀ x, N (h x) = h (N x) := fun x => (LinearMap.congr_fun hNh.eq x)
    obtain ⟨a, ha⟩ := lineu (h u) (by rw [hPh', hu, map_smul]) (by rw [hNh', hu', map_smul])
    obtain ⟨a', ha'⟩ := linew (h w) (by rw [hPh', hw, map_smul]) (by rw [hNh', hw', map_smul])
    have haa : a * a' = 1 := by
      have := hi u w
      simp only [ha, ha', map_smul, LinearMap.smul_apply, smul_eq_mul] at this
      have h' : (a * a' - 1) * bform Q u w = 0 := by linear_combination this
      linear_combination (mul_eq_zero.1 h').resolve_right huw
    obtain ⟨k, hk⟩ := hnil
    have hsub : (h - 1) u = (a - 1) • u := by
      rw [LinearMap.sub_apply, ha, Module.End.one_apply, sub_smul, one_smul]
    have := pow_apply_of_eq_smul hsub k
    rw [hk, LinearMap.zero_apply, eq_comm, smul_eq_zero] at this
    have ha1 : a = 1 := by
      rcases this with h0 | h0
      · exact sub_eq_zero.1 (pow_eq_zero_iff'.1 h0).1
      · exact absurd h0 hu0
    have ha'1 : a' = 1 := by rw [ha1, one_mul] at haa; exact haa
    have hmem : ∀ x : V, ∃ a b : K, a • u + b • w = x := fun x =>
      Submodule.mem_span_pair.1 (hspan ▸ Submodule.mem_top)
    refine LinearMap.ext fun x => ?_
    obtain ⟨s, t, rfl⟩ := hmem x
    rw [map_add, map_smul, map_smul, ha, ha', ha1, ha'1, one_smul, one_smul, Module.End.one_apply]

end Pieces

section Clauses

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The four clauses for the joint centralizer `C = so(V)_P ⊓ so(V)_N` with bound `ℓ`:
`ℓ ≤ dim C`; `dim C = ℓ ↔ C` abelian; if `dim C = ℓ`, `C` has no nonzero nilpotent element and the
only unipotent isometry commuting with `P` and `N` is `1`. -/
def JointClauses (Q : QuadraticForm K V) (P N : Module.End K V) (ℓ : ℕ) : Prop :=
  ℓ ≤ finrank K ↥(soCent Q P ⊓ soCent Q N) ∧
  (finrank K ↥(soCent Q P ⊓ soCent Q N) = ℓ ↔
    ∀ M₁ ∈ soCent Q P ⊓ soCent Q N, ∀ M₂ ∈ soCent Q P ⊓ soCent Q N, Commute M₁ M₂) ∧
  (finrank K ↥(soCent Q P ⊓ soCent Q N) = ℓ →
    ∀ M ∈ soCent Q P ⊓ soCent Q N, IsNilpotent M → M = 0) ∧
  (finrank K ↥(soCent Q P ⊓ soCent Q N) = ℓ → ∀ h : Module.End K V, IsomCent.IsIsom (bform Q) h →
    IsNilpotent (h - 1) → Commute P h → Commute N h → h = 1)

end Clauses

section Transfer

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V} {X Y : Module.End K V} {U U' : Submodule K V}
variable (horth : ∀ u ∈ U, ∀ w ∈ U', bform Q u w = 0) (h : IsCompl U U')
  (hXU : Set.MapsTo X U U) (hXU' : Set.MapsTo X U' U') (hYU : Set.MapsTo Y U U)
  (hYU' : Set.MapsTo Y U' U')
include horth h

include hXU' hYU' in
/-- `so(V)_{X,Y}` abelian ⇒ `so(U)_{X,Y}` abelian. -/
theorem commute_of_restrict_inf
    (hab : ∀ M₁ ∈ soCent Q X ⊓ soCent Q Y, ∀ M₂ ∈ soCent Q X ⊓ soCent Q Y, Commute M₁ M₂) :
    ∀ A₁ ∈ soCent (Q.comp U.subtype) (X.restrict hXU) ⊓ soCent (Q.comp U.subtype) (Y.restrict hYU),
      ∀ A₂ ∈ soCent (Q.comp U.subtype) (X.restrict hXU) ⊓
        soCent (Q.comp U.subtype) (Y.restrict hYU), Commute A₁ A₂ := by
  intro A₁ h₁ A₂ h₂
  have z : ∀ (Z : Module.End K V) (hZ : Set.MapsTo Z U' U'),
      (0 : Module.End K U') ∈ soCent (Q.comp U'.subtype) (Z.restrict hZ) := fun _ _ => zero_mem _
  have m : ∀ A ∈ soCent (Q.comp U.subtype) (X.restrict hXU) ⊓
      soCent (Q.comp U.subtype) (Y.restrict hYU), sumEnd h A 0 ∈ soCent Q X ⊓ soCent Q Y :=
    fun A hA => ⟨sumEnd_mem_soCent horth h hXU hXU' hA.1 (z X hXU'),
      sumEnd_mem_soCent horth h hYU hYU' hA.2 (z Y hYU')⟩
  have hc := (hab _ (m A₁ h₁) _ (m A₂ h₂)).eq
  refine LinearMap.ext fun u => Subtype.ext ?_
  have := congrArg (fun F : Module.End K V => F u) hc
  simpa only [Module.End.mul_apply, sumEnd_left] using this

omit horth in
/-- An endomorphism preserving `U` and `U'` is determined by its restrictions. -/
private theorem ext_of_restrict {A B : Module.End K V} (hAU : Set.MapsTo A U U) (hAU' : Set.MapsTo A U' U')
    (hBU : Set.MapsTo B U U) (hBU' : Set.MapsTo B U' U')
    (h1 : A.restrict hAU = B.restrict hBU) (h2 : A.restrict hAU' = B.restrict hBU') : A = B := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨a, a', rfl, -⟩ := Submodule.existsUnique_add_of_isCompl h v
  rw [map_add, map_add]
  congr 1
  · exact congrArg Subtype.val (LinearMap.congr_fun h1 a)
  · exact congrArg Subtype.val (LinearMap.congr_fun h2 a')

include hXU' hYU' in
/-- **Combining the clauses over `V = U ⊥ U'`.** -/
theorem jointClauses_of_split [FiniteDimensional K V]
    (hM : ∀ M ∈ soCent Q X ⊓ soCent Q Y, Set.MapsTo M U U)
    (hM' : ∀ M ∈ soCent Q X ⊓ soCent Q Y, Set.MapsTo M U' U')
    (hH : ∀ g : Module.End K V, IsomCent.IsIsom (bform Q) g → Commute X g → Commute Y g →
      Set.MapsTo g U U ∧ Set.MapsTo g U' U')
    {ℓ₁ ℓ₂ : ℕ} (h₁ : JointClauses (Q.comp U.subtype) (X.restrict hXU) (Y.restrict hYU) ℓ₁)
    (h₂ : JointClauses (Q.comp U'.subtype) (X.restrict hXU') (Y.restrict hYU') ℓ₂) :
    JointClauses Q X Y (ℓ₁ + ℓ₂) := by
  have hsplit := finrank_soCent_inf_eq_add horth h hXU hXU' hYU hYU' hM hM'
  have horth' : ∀ y ∈ U', ∀ x ∈ U, bform Q y x = 0 := fun y hy x hx =>
    bform_orth' horth ⟨y, hy⟩ ⟨x, hx⟩
  obtain ⟨l₁, ab₁, nil₁, uni₁⟩ := h₁
  obtain ⟨l₂, ab₂, nil₂, uni₂⟩ := h₂
  have heq : finrank K ↥(soCent Q X ⊓ soCent Q Y) = ℓ₁ + ℓ₂ →
      finrank K ↥(soCent (Q.comp U.subtype) (X.restrict hXU) ⊓
        soCent (Q.comp U.subtype) (Y.restrict hYU)) = ℓ₁ ∧
      finrank K ↥(soCent (Q.comp U'.subtype) (X.restrict hXU') ⊓
        soCent (Q.comp U'.subtype) (Y.restrict hYU')) = ℓ₂ := fun he => by omega
  have hres : ∀ M (hMC : M ∈ soCent Q X ⊓ soCent Q Y),
      M.restrict (hM M hMC) ∈ soCent (Q.comp U.subtype) (X.restrict hXU) ⊓
        soCent (Q.comp U.subtype) (Y.restrict hYU) ∧
      M.restrict (hM' M hMC) ∈ soCent (Q.comp U'.subtype) (X.restrict hXU') ⊓
        soCent (Q.comp U'.subtype) (Y.restrict hYU') := fun M hMC =>
    ⟨⟨restrict_mem_soCent hXU hMC.1 _, restrict_mem_soCent hYU hMC.2 _⟩,
      ⟨restrict_mem_soCent hXU' hMC.1 _, restrict_mem_soCent hYU' hMC.2 _⟩⟩
  refine ⟨by omega, ⟨fun he M₁ hM₁ M₂ hM₂ => ?_, fun hab => ?_⟩, fun he M hMC hnil => ?_,
    fun he g hg hnil hXg hYg => ?_⟩
  · obtain ⟨e₁, e₂⟩ := heq he
    have c₁ := ab₁.1 e₁ _ (hres M₁ hM₁).1 _ (hres M₂ hM₂).1
    have c₂ := ab₂.1 e₂ _ (hres M₁ hM₁).2 _ (hres M₂ hM₂).2
    refine ext_of_restrict h (fun x hx => hM M₁ hM₁ (hM M₂ hM₂ hx))
      (fun x hx => hM' M₁ hM₁ (hM' M₂ hM₂ hx)) (fun x hx => hM M₂ hM₂ (hM M₁ hM₁ hx))
      (fun x hx => hM' M₂ hM₂ (hM' M₁ hM₁ hx)) ?_ ?_
    · exact LinearMap.ext fun x => congrArg (fun F : Module.End K U => F x) c₁.eq
    · exact LinearMap.ext fun x => congrArg (fun F : Module.End K U' => F x) c₂.eq
  · rw [hsplit, (ab₁.2 (commute_of_restrict_inf horth h hXU hXU' hYU hYU' hab)),
      (ab₂.2 (commute_of_restrict_inf horth' h.symm hXU' hXU hYU' hYU hab))]
  · obtain ⟨e₁, e₂⟩ := heq he
    have n₁ := nil₁ e₁ _ (hres M hMC).1 (Module.End.isNilpotent.restrict _ hnil)
    have n₂ := nil₂ e₂ _ (hres M hMC).2 (Module.End.isNilpotent.restrict _ hnil)
    refine ext_of_restrict h (hM M hMC) (hM' M hMC) (fun x _ => zero_mem _) (fun x _ => zero_mem _)
      (n₁.trans ?_) (n₂.trans ?_) <;> rfl
  · obtain ⟨e₁, e₂⟩ := heq he
    obtain ⟨gU, gU'⟩ := hH g hg hXg hYg
    have hsU : Set.MapsTo ⇑(g - 1 : Module.End K V) U U := fun x hx => sub_mem (gU hx) hx
    have hsU' : Set.MapsTo ⇑(g - 1 : Module.End K V) U' U' := fun x hx => sub_mem (gU' hx) hx
    have hnilU : IsNilpotent (g.restrict gU - 1) := by
      rw [show g.restrict gU - 1 = (g - 1).restrict hsU from LinearMap.ext fun _ => rfl]
      exact Module.End.isNilpotent.restrict hsU hnil
    have hnilU' : IsNilpotent (g.restrict gU' - 1) := by
      rw [show g.restrict gU' - 1 = (g - 1).restrict hsU' from LinearMap.ext fun _ => rfl]
      exact Module.End.isNilpotent.restrict hsU' hnil
    have g₁ := uni₁ e₁ _ (fun x y => by simp only [bform_comp_subtype]; exact hg x y) hnilU
      (LinearMap.restrict_commute hXg _ _) (LinearMap.restrict_commute hYg _ _)
    have g₂ := uni₂ e₂ _ (fun x y => by simp only [bform_comp_subtype]; exact hg x y) hnilU'
      (LinearMap.restrict_commute hXg _ _) (LinearMap.restrict_commute hYg _ _)
    refine ext_of_restrict h gU gU' (fun x hx => hx) (fun x hx => hx) (g₁.trans ?_) (g₂.trans ?_)
      <;> rfl

end Transfer

section Base

variable {K : Type*} [Field K] [Invertible (2 : K)] [IsAlgClosed K]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {Q : QuadraticForm K V}

/-- A nondegenerate plane over an algebraically closed field has an isotropic basis `u, w` with
`b(u, w) ≠ 0`. -/
theorem exists_isotropic_pair (hQ : IsNondeg Q) (h2 : finrank K V = 2) :
    ∃ u w : V, bform Q u u = 0 ∧ bform Q w w = 0 ∧ bform Q u w ≠ 0 ∧
      Submodule.span K {u, w} = ⊤ := by
  obtain ⟨e, he⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (QuadraticForm.associated_isSymm (S := K) Q)
  have hani := LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate he hQ
  set e₀ := e ⟨0, by omega⟩
  set e₁ := e ⟨1, by omega⟩
  have h01 : bform Q e₀ e₁ = 0 := he (by simp [Fin.ext_iff])
  have h10 : bform Q e₁ e₀ = 0 := he (by simp [Fin.ext_iff])
  have ha : bform Q e₀ e₀ ≠ 0 := hani _
  have hb : bform Q e₁ e₁ ≠ 0 := hani _
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (-(bform Q e₀ e₀) / bform Q e₁ e₁) two_pos
  have ht' : t ^ 2 * bform Q e₁ e₁ = -bform Q e₀ e₀ := by rw [ht]; field_simp
  have ht0 : t ≠ 0 := by
    intro h; apply ha; rw [h] at ht'; linear_combination ht'
  have h2K : (2 : K) ≠ 0 := Invertible.ne_zero 2
  refine ⟨e₀ + t • e₁, e₀ - t • e₁, ?_, ?_, ?_, ?_⟩
  · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h01,
      h10]; linear_combination ht'
  · simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, h01,
      h10]; linear_combination ht'
  · simp only [map_add, map_sub, map_smul, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul, h01, h10]
    intro h
    exact mul_ne_zero h2K ha (by linear_combination h + ht')
  · rw [eq_top_iff, ← e.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h0 : e₀ ∈ Submodule.span K {e₀ + t • e₁, e₀ - t • e₁} := by
      have hm := add_mem (Submodule.smul_mem _ (2 : K)⁻¹ (Submodule.subset_span
        (show e₀ + t • e₁ ∈ ({e₀ + t • e₁, e₀ - t • e₁} : Set V) by simp)))
        (Submodule.smul_mem _ (2 : K)⁻¹ (Submodule.subset_span
        (show e₀ - t • e₁ ∈ ({e₀ + t • e₁, e₀ - t • e₁} : Set V) by simp)))
      have : (2 : K)⁻¹ • (e₀ + t • e₁) + (2 : K)⁻¹ • (e₀ - t • e₁) = e₀ := by
        match_scalars <;> field_simp <;> ring
      rwa [this] at hm
    have h1 : e₁ ∈ Submodule.span K {e₀ + t • e₁, e₀ - t • e₁} := by
      have hm := sub_mem (Submodule.smul_mem _ (2 * t)⁻¹ (Submodule.subset_span
        (show e₀ + t • e₁ ∈ ({e₀ + t • e₁, e₀ - t • e₁} : Set V) by simp)))
        (Submodule.smul_mem _ (2 * t)⁻¹ (Submodule.subset_span
        (show e₀ - t • e₁ ∈ ({e₀ + t • e₁, e₀ - t • e₁} : Set V) by simp)))
      have : (2 * t)⁻¹ • (e₀ + t • e₁) - (2 * t)⁻¹ • (e₀ - t • e₁) = e₁ := by
        match_scalars <;> field_simp <;> ring
      rwa [this] at hm
    obtain ⟨i, hi⟩ := i
    have hi' : i < 2 := h2 ▸ hi
    interval_cases i
    · exact h0
    · exact h1

/-- An isometry of a nondegenerate space of dimension `≤ 2` is semisimple. -/
theorem isSemisimple_of_isIsom_of_finrank_le_two (hQ : IsNondeg Q) (hn : finrank K V ≤ 2)
    {h : Module.End K V} (hi : IsIsom (bform Q) h) : h.IsSemisimple := by
  rcases Nat.lt_or_ge (finrank K V) 2 with h1 | h2
  · exact isSemisimple_of_finrank_le_one (by omega) h
  · have h2' : finrank K V = 2 := by omega
    refine TauCeti.isSemisimple_of_iSup_eigenspace_eq_top (eq_top_iff.2 ?_)
    have := le_iSup_eigenspace_of_finrank_eq_two (B := bform Q) (Invertible.ne_zero 2)
      ⟨bform_comm Q⟩ hi (E := ⊤) (fun v _ => trivial) (by rw [finrank_top]; exact h2')
      (fun e _ he => by
        by_contra hcon; push Not at hcon
        exact he (hQ.1 e fun y => hcon y trivial))
    exact this

omit [Invertible (2 : K)] in
/-- A unipotent semisimple endomorphism is `1`. -/
private theorem eq_one_of_isNilpotent_sub_one {h : Module.End K V} (hss : h.IsSemisimple)
    (hnil : IsNilpotent (h - 1)) : h = 1 := by
  have : (h - 1).IsSemisimple :=
    Module.End.IsSemisimple.sub_of_commute (Commute.one_right h) hss Module.End.isSemisimple_id
  exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple hnil this)

omit [Invertible (2 : K)] [IsAlgClosed K] in
/-- Elements of a subspace of dimension `≤ 1` commute. -/
private theorem commute_of_mem_finrank_le_one {S : Submodule K (Module.End K V)}
    (h1 : finrank K S ≤ 1) {M₁ M₂ : Module.End K V} (h₁ : M₁ ∈ S) (h₂ : M₂ ∈ S) :
    Commute M₁ M₂ := by
  by_cases h0 : M₁ = 0
  · rw [h0]; exact Commute.zero_left _
  · obtain ⟨c, rfl⟩ := exists_smul_of_finrank_le_one h1 h₁ h0 h₂
    exact (Commute.refl M₁).smul_right c

/-- **The four clauses for `so(V)`** (`P = ±1`, `N = 0`): `dim so(V) ≥ ⌊n/2⌋`, with equality iff
`so(V)` is abelian (iff `n ≤ 2`); then `so(V)` has no nonzero nilpotent element and the only
unipotent isometry is `1`. -/
private theorem so_clauses [CharZero K] (hQ : IsNondeg Q) :
    finrank K V / 2 ≤ finrank K (soCent Q 1) ∧
    (finrank K (soCent Q 1) = finrank K V / 2 ↔
      ∀ M₁ ∈ soCent Q 1, ∀ M₂ ∈ soCent Q 1, Commute M₁ M₂) ∧
    (finrank K (soCent Q 1) = finrank K V / 2 → ∀ M ∈ soCent Q 1, IsNilpotent M → M = 0) ∧
    (finrank K (soCent Q 1) = finrank K V / 2 →
      ∀ h : Module.End K V, IsIsom (bform Q) h → IsNilpotent (h - 1) → h = 1) := by
  have hlow := le_finrank_soCent_one hQ
  have hn2 : finrank K (soCent Q 1) = finrank K V / 2 → finrank K V ≤ 2 := fun h => by omega
  refine ⟨by omega, ⟨fun h M₁ h₁ M₂ h₂ => commute_of_mem_finrank_le_one (by omega) h₁ h₂,
    fun hab => finrank_soCent_one_of_le_two hQ (finrank_le_two_of_commute hQ hab)⟩,
    fun h M hM hnil => ?_, fun h g hg hnil =>
      eq_one_of_isNilpotent_sub_one (isSemisimple_of_isIsom_of_finrank_le_two hQ (hn2 h) hg) hnil⟩
  have hle := hn2 h
  rcases Nat.lt_or_ge (finrank K V) 2 with h1 | h2
  · have h0 : finrank K (soCent Q 1) = 0 := by omega
    exact (Submodule.finrank_eq_zero.1 h0 ▸ hM : M ∈ (⊥ : Submodule K _))
      |> (Submodule.mem_bot K).1
  · obtain ⟨u, w, huu, hww, huw, hspan⟩ := exists_isotropic_pair hQ (by omega)
    have hsk := (mem_soCent.1 hM).1
    have hsym : ∀ x y, bform Q x y = bform Q y x := bform_comm Q
    have hwu : bform Q w u ≠ 0 := by rwa [hsym]
    have hmem : ∀ x : V, ∃ a b : K, a • u + b • w = x := fun x =>
      Submodule.mem_span_pair.1 (hspan ▸ Submodule.mem_top)
    have h2K : (2 : K) ≠ 0 := Invertible.ne_zero 2
    -- `M` preserves the isotropic lines
    have hline : ∀ {x y : V}, bform Q x x = 0 → bform Q y y = 0 → bform Q x y ≠ 0 →
        Submodule.span K {x, y} = ⊤ → ∃ t : K, M x = t • x := by
      intro x y hxx hyy hxy hsp
      obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 (hsp ▸ Submodule.mem_top (x := M x))
      have h1 : bform Q (M x) x = 0 := by
        have := hsk x x
        rw [hsym x (M x)] at this
        have h' : (2 : K) * bform Q (M x) x = 0 := by linear_combination this
        exact (mul_eq_zero.1 h').resolve_left h2K
      rw [← hab] at h1
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hxx,
        mul_zero, zero_add] at h1
      have hb : b = 0 := (mul_eq_zero.1 h1).resolve_right (by rwa [hsym])
      exact ⟨a, by rw [← hab, hb, zero_smul, add_zero]⟩
    obtain ⟨a, ha⟩ := hline huu hww huw hspan
    obtain ⟨a', ha'⟩ := hline hww huu hwu (by rw [Set.pair_comm]; exact hspan)
    have haa : a' = -a := by
      have := hsk u w
      rw [ha, ha', map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul] at this
      have h' : (a + a') * bform Q u w = 0 := by linear_combination this
      linear_combination (mul_eq_zero.1 h').resolve_right huw
    obtain ⟨k, hk⟩ := hnil
    have := pow_apply_of_eq_smul ha k
    rw [hk, LinearMap.zero_apply, eq_comm, smul_eq_zero] at this
    have hu0 : u ≠ 0 := fun h => huw (by rw [h, map_zero, LinearMap.zero_apply])
    have ha0 : a = 0 := by
      rcases this with h0 | h0
      · exact (pow_eq_zero_iff'.1 h0).1
      · exact absurd h0 hu0
    refine LinearMap.ext fun x => ?_
    obtain ⟨s, t, rfl⟩ := hmem x
    rw [map_add, map_smul, map_smul, ha, ha', haa, ha0, neg_zero, zero_smul, zero_smul,
      smul_zero, smul_zero, add_zero, LinearMap.zero_apply]

/-- **The four clauses on a paired piece**: `V` spanned by `u_i` (joint eigenvectors for `(μ, c)`)
and `w_j` (for `(μ⁻¹, −c)`), `w_j` for `(μ⁻¹, −c)`, `(μ, c) ≠ (μ⁻¹, −c)`, `b(w_j, u_k) = δ_{jk}`: bound `d`. -/
theorem jointClauses_pair {P N : Module.End K V} (hP : IsIsom (bform Q) P)
    (hN : IsSkew (bform Q) N) {μ c : K} (hμ0 : μ ≠ 0) (hne : μ⁻¹ ≠ μ ∨ c ≠ 0) {d : ℕ}
    (hd : 1 ≤ d) (u w : Fin d → V) (hu : ∀ i, P (u i) = μ • u i) (hu' : ∀ i, N (u i) = c • u i)
    (hw : ∀ j, P (w j) = μ⁻¹ • w j) (hw' : ∀ j, N (w j) = (-c) • w j)
    (huu : ∀ i k, bform Q (u i) (u k) = 0)
    (hwu : ∀ j k, bform Q (w j) (u k) = if j = k then 1 else 0)
    (hspan : Submodule.span K (Set.range u ∪ Set.range w) = ⊤) :
    JointClauses Q P N d := by
  have hmemC : ∀ i j, wedge (bform Q) (u i) (w j) ∈ soCent Q P ⊓ soCent Q N := fun i j =>
    wedge_mem_soCent_inf hP hN hμ0 (Module.End.mem_eigenspace_iff.2 (hu i))
      (Module.End.mem_eigenspace_iff.2 (hu' i)) (Module.End.mem_eigenspace_iff.2 (hw j))
      (Module.End.mem_eigenspace_iff.2 (hw' j))
  have hlow := le_finrank_of_wedge_dual u w huu hwu hmemC
  have hu0 : ∀ i, u i ≠ 0 := fun i h => by
    have := hwu i i; rw [h, map_zero, ite_eq_left_iff.mpr (fun h => absurd rfl h)] at this; exact zero_ne_one this
  -- `d = 1`: the hyperbolic pair
  have hone : d = 1 → soCent Q P ⊓ soCent Q N = K ∙ wedge (bform Q) (u ⟨0, by omega⟩)
      (w ⟨0, by omega⟩) ∧ _ := fun hd1 => by
    subst hd1
    have hsp : Submodule.span K {u 0, w 0} = ⊤ := by
      rw [← hspan]; congr 1; ext x; simp [Set.mem_range, eq_comm]
    have huw : bform Q (u 0) (w 0) ≠ 0 := by
      rw [bform_comm Q, hwu 0 0]; simp
    exact ⟨soCent_inf_eq_span_wedge hP hN hμ0 hne (hu 0) (hu' 0) (hw 0) (hw' 0) huw hsp,
      pair_nilpotent_unipotent hP hN hμ0 hne (hu 0) (hu' 0) (hw 0) (hw' 0) huw hsp⟩
  refine ⟨le_trans (Nat.le_mul_self d) hlow, ⟨fun he => ?_, fun hab => ?_⟩, fun he => ?_,
    fun he => ?_⟩
  · intro M₁ h₁ M₂ h₂
    exact commute_of_mem_finrank_le_one (by nlinarith) h₁ h₂
  · have hd1 : d = 1 := by
      by_contra hne1
      exact not_commute_wedge_dual (Q := Q) (by omega) u w huu hwu (hu0 _)
        (hab _ (hmemC _ _) _ (hmemC _ _))
    obtain ⟨hC, -⟩ := hone hd1
    subst hd1
    rw [hC, finrank_span_singleton]
    intro h0
    have := LinearMap.congr_fun h0 (u 0)
    rw [wedge_apply, huu, zero_smul, sub_zero, LinearMap.zero_apply, smul_eq_zero] at this
    rcases this with h | h
    · rw [hwu] at h; simp at h
    · exact hu0 _ h
  · have hd1 : d = 1 := by nlinarith
    exact (hone hd1).2.1
  · have hd1 : d = 1 := by nlinarith
    exact (hone hd1).2.2

/-- **The four clauses when `P` and `N` are scalars** (`P = ε`, `N = c`): the joint centralizer is
`so(V)`, with bound `⌊dim V/2⌋`. -/
theorem jointClauses_scalar [CharZero K] (hQ : IsNondeg Q) {P N : Module.End K V} {ε c : K}
    (hP : ∀ v, P v = ε • v) (hN : ∀ v, N v = c • v) :
    JointClauses Q P N (finrank K V / 2) := by
  have e : soCent Q P ⊓ soCent Q N = soCent Q 1 := by
    rw [soCent_of_scalar hP, soCent_of_scalar hN, inf_idem]
  obtain ⟨l, ab, nil, uni⟩ := so_clauses hQ
  unfold JointClauses
  rw [e]
  exact ⟨l, ab, nil, fun he h hi hnil _ _ => uni he h hi hnil⟩

end Base

section Main

universe u

variable {K : Type*} [Field K] [Invertible (2 : K)] [CharZero K] [IsAlgClosed K]

/-- Induction form of `jointClauses`, with `dim E₋₁(P)` even in place of `det P = 1`. -/
private theorem jointClauses_aux (n : ℕ) : ∀ {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (P N : Module.End K V), finrank K V = n →
    IsNondeg Q → IsIsom (bform Q) P → P.IsSemisimple → IsSkew (bform Q) N → N.IsSemisimple →
    Commute N P → Even (finrank K ↥(P.eigenspace (-1))) →
    JointClauses Q P N (n / 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ Q P N hn hQ hP hssP hN hssN hc hev
  by_cases hA : ∃ μ c : K, P.eigenspace μ ⊓ N.eigenspace c ≠ ⊥ ∧ (μ⁻¹ ≠ μ ∨ c ≠ 0)
  · -- split off `U = E ⊕ E'`, `E = E_{(μ,c)}`, `E' = E_{(μ⁻¹,−c)}`
    obtain ⟨μ, c, hE0, hne⟩ := hA
    set E := P.eigenspace μ ⊓ N.eigenspace c
    set E' := P.eigenspace μ⁻¹ ⊓ N.eigenspace (-c)
    have hsym : ∀ x y, bform Q x y = bform Q y x := bform_comm Q
    have hB : (bform Q).IsSymm := ⟨hsym⟩
    have h2K : (2 : K) ≠ 0 := two_ne_zero
    have hμ0 : μ ≠ 0 := ne_zero_of_hasEigenvalue (B := bform Q) hQ hP
      (Module.End.hasEigenvalue_iff.2 fun h => hE0 (by simp only [E, h, bot_inf_eq]))
    have hμμ : μ⁻¹ ≠ μ → μ * μ ≠ 1 := fun h h1 => h (inv_eq_of_mul_eq_one_right h1)
    have hisoE : ∀ x ∈ E, ∀ y ∈ E, bform Q x y = 0 := by
      intro x hx y hy
      rcases hne with h | h
      · exact bform_eigen_eq_zero (B := bform Q) hP (hμμ h) hx.1 hy.1
      · exact bform_eigen_eq_zero_of_skew hN (by rw [← two_mul]; exact mul_ne_zero h2K h) hx.2 hy.2
    have hisoE' : ∀ x ∈ E', ∀ y ∈ E', bform Q x y = 0 := by
      intro x hx y hy
      rcases hne with h | h
      · have hii : μ⁻¹ * μ⁻¹ ≠ 1 := by
          rw [← mul_inv]; exact fun h1 => hμμ h (inv_eq_one.1 h1)
        exact bform_eigen_eq_zero (B := bform Q) hP hii hx.1 hy.1
      · have hcc : -c + -c ≠ 0 := by
          rw [← two_mul]; exact mul_ne_zero h2K (neg_ne_zero.2 h)
        exact bform_eigen_eq_zero_of_skew hN hcc hx.2 hy.2
    have hexv : ∀ x : V, x ≠ 0 → ∃ v, bform Q x v ≠ 0 := fun x hx0 => by
      by_contra h; push Not at h; exact hx0 (hQ.1 x h)
    have h1 : ∀ x ∈ E, x ≠ 0 → ∃ y ∈ E', bform Q y x ≠ 0 := by
      intro x hx hx0
      obtain ⟨v, hv⟩ := hexv x hx0
      obtain ⟨y, hy, hyv⟩ := exists_joint_eigen_pair hP hssP hN hssN hc hx.1 hx.2 v
      exact ⟨y, hy, by rw [hsym, hyv]; exact hv⟩
    have h2 : ∀ y ∈ E', y ≠ 0 → ∃ x ∈ E, bform Q y x ≠ 0 := by
      intro y hy hy0
      obtain ⟨v, hv⟩ := hexv y hy0
      obtain ⟨x, hx, hxv⟩ := exists_joint_eigen_pair hP hssP hN hssN hc hy.1 hy.2 v
      rw [inv_inv, neg_neg] at hx
      exact ⟨x, hx, by rw [hxv]; exact hv⟩
    obtain ⟨hdim, u, w, huE, hwE', hwu⟩ := exists_dual_family (B := bform Q) h1 h2
    have hd1 : 1 ≤ finrank K E := Submodule.one_le_finrank_iff.2 hE0
    have hli : ∀ v : Fin (finrank K E) → V, (∀ j k, bform Q (w j) (v k) = if j = k then 1 else 0) ∨
        (∀ j k, bform Q (u j) (v k) = if j = k then 1 else 0) → LinearIndependent K v := by
      intro v hv
      rw [Fintype.linearIndependent_iff]
      intro a ha j
      rcases hv with hv | hv
      · have := congrArg (bform Q (w j)) ha
        simpa [map_sum, map_smul, hv, Finset.sum_ite_eq] using this
      · have := congrArg (bform Q (u j)) ha
        simpa [map_sum, map_smul, hv, Finset.sum_ite_eq] using this
    have hwu' : ∀ j k, bform Q (u j) (w k) = if j = k then 1 else 0 := fun j k => by
      rw [hsym, hwu]; exact if_congr eq_comm rfl rfl
    have hspanE : Submodule.span K (Set.range u) = E := by
      refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
      · rintro _ ⟨i, rfl⟩; exact huE i
      · rw [finrank_span_eq_card (hli u (Or.inl hwu)), Fintype.card_fin]
    have hspanE' : Submodule.span K (Set.range w) = E' := by
      refine Submodule.eq_of_le_of_finrank_eq (Submodule.span_le.2 ?_) ?_
      · rintro _ ⟨i, rfl⟩; exact hwE' i
      · rw [finrank_span_eq_card (hli w (Or.inr hwu')), Fintype.card_fin, hdim]
    set U := E ⊔ E'
    have hUspan : Submodule.span K (Set.range u ∪ Set.range w) = U := by
      rw [Submodule.span_union, hspanE, hspanE']
    set U' := (bform Q).orthogonal U
    have horth : ∀ x ∈ U, ∀ y ∈ U', bform Q x y = 0 := fun x hx y hy =>
      (LinearMap.BilinForm.mem_orthogonal_iff.1 hy) x hx
    have horth' : ∀ y ∈ U', ∀ x ∈ U, bform Q y x = 0 := fun y hy x hx =>
      bform_orth' horth ⟨y, hy⟩ ⟨x, hx⟩
    have hdisj : Disjoint U U' := by
      rw [Submodule.disjoint_def]
      intro z hz hz'
      obtain ⟨e, he, e', he', rfl⟩ := Submodule.mem_sup.1 hz
      have he0 : e = 0 := by
        by_contra hne0
        obtain ⟨y, hy, hyb⟩ := h1 e he hne0
        apply hyb
        have := horth' _ hz' y (Submodule.mem_sup_right hy)
        rw [hsym, map_add, hisoE' y hy e' he', add_zero] at this
        exact this
      have he0' : e' = 0 := by
        by_contra hne0
        obtain ⟨x, hx, hxb⟩ := h2 e' he' hne0
        apply hxb
        have := horth' _ hz' x (Submodule.mem_sup_left hx)
        rw [hsym, map_add, hisoE x hx e he, zero_add] at this
        rwa [hsym]
      rw [he0, he0', add_zero]
    have hcompl : IsCompl U U' :=
      LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl
        (LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal _ hB.isRefl hdisj)
    have hUmaps : ∀ g : Module.End K V, Commute P g → Commute N g → Set.MapsTo g U U := by
      intro g hPg hNg x hx
      obtain ⟨e, he, e', he', rfl⟩ := Submodule.mem_sup.1 hx
      rw [map_add]
      exact add_mem (Submodule.mem_sup_left ⟨mapsTo_eigenspace_of_commute hPg μ e he.1,
          mapsTo_eigenspace_of_commute hNg c e he.2⟩)
        (Submodule.mem_sup_right ⟨mapsTo_eigenspace_of_commute hPg μ⁻¹ e' he'.1,
          mapsTo_eigenspace_of_commute hNg (-c) e' he'.2⟩)
    have hPU := hUmaps P (Commute.refl P) hc
    have hNU := hUmaps N hc.symm (Commute.refl N)
    have hPU' := mapsTo_orthogonal_of_isometry hQ hP hPU
    have hNU' := mapsTo_orthogonal_of_skew hN hNU
    have hpair := jointClauses_pair (Q := Q.comp U.subtype) (P := P.restrict hPU)
      (N := N.restrict hNU) (fun x y => by simp only [bform_comp_subtype]; exact hP x y)
      (fun x y => by simp only [bform_comp_subtype]; exact hN x y) hμ0 hne hd1
      (fun i => ⟨u i, Submodule.mem_sup_left (huE i)⟩)
      (fun j => ⟨w j, Submodule.mem_sup_right (hwE' j)⟩)
      (fun i => Subtype.ext (Module.End.mem_eigenspace_iff.1 (huE i).1))
      (fun i => Subtype.ext (Module.End.mem_eigenspace_iff.1 (huE i).2))
      (fun j => Subtype.ext (Module.End.mem_eigenspace_iff.1 (hwE' j).1))
      (fun j => Subtype.ext (Module.End.mem_eigenspace_iff.1 (hwE' j).2))
      (fun i k => by rw [bform_comp_subtype]; exact hisoE _ (huE i) _ (huE k))
      (fun j k => by rw [bform_comp_subtype]; exact hwu j k) (by
        apply Submodule.map_injective_of_injective U.injective_subtype
        rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, Set.image_union,
          ← Set.range_comp, ← Set.range_comp]
        exact hUspan)
    -- the complement, by induction
    have hinf : E ⊓ E' = ⊥ := by
      rw [eq_bot_iff]
      intro x ⟨hx, hx'⟩
      rw [Submodule.mem_bot]
      by_contra hx0
      obtain ⟨y, hy, hyb⟩ := h2 x hx' hx0
      exact hyb (hisoE x hx y hy)
    have hdU : finrank K U = finrank K E + finrank K E := by
      have := Submodule.finrank_sup_add_finrank_inf_eq E E'
      rw [hinf, finrank_bot, add_zero, hdim] at this
      exact this
    have hd := Submodule.finrank_add_eq_of_isCompl hcompl
    have hev' : Even (finrank K ↥(Module.End.eigenspace (P.restrict hPU') (-1))) := by
      set F := P.eigenspace (-1)
      -- `F = (F ⊓ U) ⊕ (F ⊓ U')`
      have hFsplit : finrank K ↥(F ⊓ U) + finrank K ↥(F ⊓ U') = finrank K F := by
        have hsup : (F ⊓ U) ⊔ (F ⊓ U') = F := by
          refine le_antisymm (sup_le inf_le_left inf_le_left) fun x hx => ?_
          obtain ⟨y, y', rfl, -⟩ := Submodule.existsUnique_add_of_isCompl hcompl x
          have hPx := Module.End.mem_eigenspace_iff.1 hx
          rw [map_add] at hPx
          have hy : P y = (-1 : K) • (y : V) ∧ P y' = (-1 : K) • (y' : V) := by
            have e1 : (P y : V) - (-1 : K) • (y : V) ∈ U := sub_mem (hPU y.2) (U.smul_mem _ y.2)
            have e2 : (P y' : V) - (-1 : K) • (y' : V) ∈ U' :=
              sub_mem (hPU' y'.2) (U'.smul_mem _ y'.2)
            have e3 : ((P y : V) - (-1 : K) • (y : V)) +
                ((P y' : V) - (-1 : K) • (y' : V)) = 0 := by
              linear_combination (norm := module) hPx
            have := Submodule.disjoint_def.1 hcompl.1 _ e1 (by
              rw [eq_neg_of_add_eq_zero_left e3]; exact neg_mem e2)
            refine ⟨sub_eq_zero.1 this, sub_eq_zero.1 ?_⟩
            rw [this, zero_add] at e3; exact e3
          exact Submodule.mem_sup.2 ⟨y, ⟨Module.End.mem_eigenspace_iff.2 hy.1, y.2⟩, y',
            ⟨Module.End.mem_eigenspace_iff.2 hy.2, y'.2⟩, rfl⟩
        have hdis : (F ⊓ U) ⊓ (F ⊓ U') = ⊥ := by
          rw [eq_bot_iff]
          exact fun x hx => Submodule.disjoint_def.1 hcompl.1 x hx.1.2 hx.2.2 ▸ zero_mem _
        have := Submodule.finrank_sup_add_finrank_inf_eq (F ⊓ U) (F ⊓ U')
        rw [hsup, hdis, finrank_bot, add_zero] at this
        exact this.symm
      have hFU' : finrank K ↥(Module.End.eigenspace (P.restrict hPU') (-1)) =
          finrank K ↥(F ⊓ U') := by
        have heq : Module.End.eigenspace (P.restrict hPU') (-1) = F.comap U'.subtype :=
          Module.End.genEigenspace_restrict P U' 1 (-1) hPU'
        have h2' : F.comap U'.subtype = (F ⊓ U').comap U'.subtype := by
          ext x; simp
        rw [heq, h2']
        exact (Submodule.comapSubtypeEquivOfLe inf_le_right).finrank_eq
      have hFU : Even (finrank K ↥(F ⊓ U)) := by
        by_cases hm : μ = -1
        · have hle : U ≤ F := sup_le (fun x hx => by have := hx.1; rwa [hm] at this)
            (fun x hx => by have := hx.1; rwa [hm, inv_neg, inv_one] at this)
          rw [inf_eq_right.2 hle, hdU]
          exact ⟨_, rfl⟩
        · have hbot : F ⊓ U = ⊥ := by
            rw [eq_bot_iff]
            intro x ⟨hxF, hxU⟩
            obtain ⟨e, he, e', he', rfl⟩ := Submodule.mem_sup.1 hxU
            have hPx := Module.End.mem_eigenspace_iff.1 hxF
            rw [map_add, Module.End.mem_eigenspace_iff.1 he.1,
              Module.End.mem_eigenspace_iff.1 he'.1] at hPx
            have hmem : (μ + 1) • e ∈ E ⊓ E' := by
              have h' : (μ + 1) • e = -((μ⁻¹ + 1) • e') := by
                linear_combination (norm := module) hPx
              exact ⟨E.smul_mem _ he, h' ▸ E'.neg_mem (E'.smul_mem _ he')⟩
            rw [hinf, Submodule.mem_bot, smul_eq_zero] at hmem
            have he0 : e = 0 := hmem.resolve_left fun h => hm (by linear_combination h)
            have hmi : μ⁻¹ ≠ -1 := fun h => hm (by rw [← inv_inv μ, h, inv_neg, inv_one])
            rw [he0] at hPx
            have h3 : (μ⁻¹ + 1) • e' = 0 := by linear_combination (norm := module) hPx
            have he0' : e' = 0 := (smul_eq_zero.1 h3).resolve_left fun h => hmi (by
              linear_combination h)
            rw [he0, he0', add_zero]
            exact zero_mem _
          rw [hbot, finrank_bot]; exact ⟨0, rfl⟩
      rw [hFU']
      have := hFsplit ▸ hev
      exact (Nat.even_add.1 this).1 hFU
    have hrec := ih (finrank K U') (by omega) (Q.comp U'.subtype) (P.restrict hPU')
      (N.restrict hNU') rfl (isNondeg_comp_subtype horth' hQ hcompl.symm)
      (fun x y => by simp only [bform_comp_subtype]; exact hP x y)
      (hssP.restrict ((Module.End.mem_invtSubmodule _).2 hPU'))
      (fun x y => by simp only [bform_comp_subtype]; exact hN x y)
      (hssN.restrict ((Module.End.mem_invtSubmodule _).2 hNU'))
      (LinearMap.restrict_commute hc _ _) hev'
    have hcomb := jointClauses_of_split horth hcompl hPU hPU' hNU hNU'
      (fun M hM => hUmaps M (mem_soCent.1 hM.1).2.symm (mem_soCent.1 hM.2).2.symm)
      (fun M hM => mapsTo_orthogonal_of_skew (mem_soCent.1 hM.1).1
        (hUmaps M (mem_soCent.1 hM.1).2.symm (mem_soCent.1 hM.2).2.symm))
      (fun g hg hPg hNg => ⟨hUmaps g hPg hNg,
        mapsTo_orthogonal_of_isometry hQ hg (hUmaps g hPg hNg)⟩) hpair hrec
    have : finrank K E + finrank K U' / 2 = n / 2 := by omega
    rwa [this] at hcomb
  · -- only self-paired joint eigenvalues: `N = 0` and `P = ±1` on its eigenspaces
    push Not at hA
    have hjoint : ∀ c : K, N.eigenspace c ≠ ⊥ → ∃ μ, P.eigenspace μ ⊓ N.eigenspace c ≠ ⊥ := by
      intro c hcne
      set E := N.eigenspace c
      have hE : ∀ x ∈ E, P x ∈ E := mapsTo_eigenspace_of_commute hc c
      have : Nontrivial E := Submodule.nontrivial_iff_ne_bot.2 hcne
      obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (P.restrict hE)
      obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
        (Module.End.hasEigenvalue_iff.1 hμ)
      refine ⟨μ, fun hbot => hz0 (Subtype.ext ?_)⟩
      have : (z : V) ∈ P.eigenspace μ ⊓ N.eigenspace c :=
        ⟨Module.End.eigenspace_restrict_le_eigenspace P hE μ ⟨z, hz, rfl⟩, z.2⟩
      rw [hbot] at this
      exact (Submodule.mem_bot K).1 this
    have hN0 : N.eigenspace 0 = ⊤ := by
      rw [eq_top_iff, ← hssN.iSup_eigenspace_eq_top]
      refine iSup_le fun c => ?_
      by_cases hc0 : N.eigenspace c = ⊥
      · rw [hc0]; exact bot_le
      · obtain ⟨μ, hμ⟩ := hjoint c hc0
        rw [(hA μ c hμ).2]
    have hNv : ∀ v, N v = (0 : K) • v := fun v =>
      Module.End.mem_eigenspace_iff.1 (hN0 ▸ Submodule.mem_top)
    have hPpm : ∀ μ, P.HasEigenvalue μ → μ = 1 ∨ μ = -1 := by
      intro μ hμ
      have h1 := (hA μ 0 (by rw [hN0, inf_top_eq]; exact Module.End.hasEigenvalue_iff.1 hμ)).1
      have hμ0 : μ ≠ 0 := ne_zero_of_hasEigenvalue (B := bform Q) hQ hP hμ
      have : μ * μ = 1 := by
        calc μ * μ = μ * μ⁻¹ := by rw [h1]
          _ = 1 := mul_inv_cancel₀ hμ0
      exact mul_self_eq_one_iff.1 this
    set E₁ := P.eigenspace 1
    set E₂ := P.eigenspace (-1)
    have horth : ∀ x ∈ E₁, ∀ y ∈ E₂, bform Q x y = 0 := fun x hx y hy =>
      bform_eigen_eq_zero (B := bform Q) hP (by norm_num) hx hy
    have hcompl : IsCompl E₁ E₂ := by
      constructor
      · rw [Submodule.disjoint_def]
        intro x h1 h2
        have h : (1 : K) • x = (-1 : K) • x :=
          (Module.End.mem_eigenspace_iff.1 h1).symm.trans (Module.End.mem_eigenspace_iff.1 h2)
        have h' : (2 : K) • x = 0 := by linear_combination (norm := module) h
        exact (smul_eq_zero.1 h').resolve_left two_ne_zero
      · rw [codisjoint_iff, eq_top_iff, ← hssP.iSup_eigenspace_eq_top]
        refine iSup_le fun ν => ?_
        by_cases hν : P.HasEigenvalue ν
        · rcases hPpm ν hν with rfl | rfl
          · exact le_sup_left
          · exact le_sup_right
        · rw [Module.End.hasEigenvalue_iff, not_not] at hν
          rw [hν]
          exact bot_le
    have hmaps : ∀ g : Module.End K V, Commute P g → Set.MapsTo g E₁ E₁ ∧ Set.MapsTo g E₂ E₂ :=
      fun g hg => ⟨mapsTo_eigenspace_of_commute hg 1, mapsTo_eigenspace_of_commute hg (-1)⟩
    have hP1 := (hmaps P (Commute.refl P)).1
    have hP2 := (hmaps P (Commute.refl P)).2
    have hN1 := (hmaps N hc.symm).1
    have hN2 := (hmaps N hc.symm).2
    have horth' : ∀ y ∈ E₂, ∀ x ∈ E₁, bform Q y x = 0 := fun y hy x hx =>
      bform_orth' horth ⟨y, hy⟩ ⟨x, hx⟩
    have c₁ := jointClauses_scalar (isNondeg_comp_subtype horth hQ hcompl) (P := P.restrict hP1)
      (N := N.restrict hN1) (ε := 1) (c := 0)
      (fun v => Subtype.ext (Module.End.mem_eigenspace_iff.1 v.2)) (fun v => Subtype.ext (hNv v))
    have c₂ := jointClauses_scalar (isNondeg_comp_subtype horth' hQ hcompl.symm)
      (P := P.restrict hP2) (N := N.restrict hN2) (ε := -1) (c := 0)
      (fun v => Subtype.ext (Module.End.mem_eigenspace_iff.1 v.2)) (fun v => Subtype.ext (hNv v))
    have hcomb := jointClauses_of_split horth hcompl hP1 hP2 hN1 hN2
      (fun M hM => (hmaps M (mem_soCent.1 hM.1).2.symm).1)
      (fun M hM => (hmaps M (mem_soCent.1 hM.1).2.symm).2)
      (fun g _ hg _ => hmaps g hg) c₁ c₂
    have hd := Submodule.finrank_add_eq_of_isCompl hcompl
    obtain ⟨k, hk⟩ := hev
    have : finrank K E₁ / 2 + finrank K E₂ / 2 = n / 2 := by omega
    rwa [this] at hcomb

/-- **The joint centralizer of a commuting semisimple isometry and skew map.** Over an algebraically
closed field of characteristic `0`, let `P` be a semisimple isometry of the nondegenerate form `Q`
with `det P = 1` and `N` a semisimple skew map commuting with `P`. Then
`C = so(V)_P ⊓ so(V)_N` has `dim C ≥ ⌊dim V/2⌋`, with equality iff `C` is abelian; and then `C` has
no nonzero nilpotent element and the only unipotent isometry commuting with `P` and `N` is `1`. -/
theorem jointClauses {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Q : QuadraticForm K V} {P N : Module.End K V} (hQ : IsNondeg Q) (hP : IsIsom (bform Q) P)
    (hssP : P.IsSemisimple) (hN : IsSkew (bform Q) N) (hssN : N.IsSemisimple) (hc : Commute N P)
    (hdet : LinearMap.det P = 1) : JointClauses Q P N (finrank K V / 2) := by
  refine jointClauses_aux _ Q P N rfl hQ hP hssP hN hssN hc ?_
  have hd := IsomCent.det_eq_det_one_mul_det_neg_one (B := bform Q) ⟨bform_comm Q⟩ hQ hP hssP hP
    (Commute.refl P)
  have h1 : P.restrict (mapsTo_eigenspace_of_commute (Commute.refl P) 1) = LinearMap.id :=
    LinearMap.ext fun z => Subtype.ext (by
      rw [LinearMap.coe_restrict_apply, Module.End.mem_eigenspace_iff.1 z.2, one_smul]; rfl)
  have h2 : P.restrict (mapsTo_eigenspace_of_commute (Commute.refl P) (-1)) =
      (-1 : K) • LinearMap.id :=
    LinearMap.ext fun z => Subtype.ext (Module.End.mem_eigenspace_iff.1 z.2)
  rw [h1, h2, LinearMap.det_id, LinearMap.det_smul, LinearMap.det_id, one_mul, mul_one, hdet] at hd
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).1 hd.symm

end Main

end GSpinGGP
