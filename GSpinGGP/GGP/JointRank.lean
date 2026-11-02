/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.JointCentralizer
import GSpinGGP.GGP.SemisimpleRank
import GSpinGGP.GGP.IsometrySemisimple

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
  simp only [Module.End.mul_apply, wedge_apply, map_sub, map_smul, huu, hwu, Fin.mk.injEq,
    zero_smul, sub_zero, if_true, one_smul, smul_zero] at h1
  simp at h1
  exact hu1 h1.symm

variable (hP : IsIsom (bform Q) P) (hN : IsSkew (bform Q) N) {μ c : K} (hμ0 : μ ≠ 0)
  (hne : μ⁻¹ ≠ μ ∨ c ≠ 0) {u w : V} (hu : P u = μ • u) (hu' : N u = c • u) (hw : P w = μ⁻¹ • w)
  (hw' : N w = (-c) • w) (huw : bform Q u w ≠ 0) (hspan : Submodule.span K {u, w} = ⊤)
include hP hN hμ0 hne hu hu' hw hw' huw hspan

/-- On a hyperbolic pair of joint eigenvectors `u`, `w` spanning `V` (`P u = μ u`, `N u = c u`,
`P w = μ⁻¹ w`, `N w = −c w`, `(μ, c) ≠ (μ⁻¹, −c)`, `b(u, w) ≠ 0`): `u`, `w` are isotropic and the joint
eigenspaces for `(μ, c)`, `(μ⁻¹, −c)` are the lines `K u`, `K w`. -/
theorem pair_facts :
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
theorem pow_apply_of_eq_smul {f : Module.End K V} {x : V} {r : K} (hx : f x = r • x) (k : ℕ) :
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

omit [Invertible (2 : K)] in
theorem isNilpotent_restrict {U : Submodule K V} {M : Module.End K V} (hM : IsNilpotent M)
    (hMU : Set.MapsTo M U U) : IsNilpotent (M.restrict hMU) := by
  obtain ⟨k, hk⟩ := hM
  have key : ∀ (n : ℕ) (x : U), (((M.restrict hMU) ^ n) x : V) = (M ^ n) x := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih => intro x; rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]; rfl
  exact ⟨k, LinearMap.ext fun x => Subtype.ext (by rw [key, hk]; rfl)⟩

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
theorem ext_of_restrict {A B : Module.End K V} (hAU : Set.MapsTo A U U) (hAU' : Set.MapsTo A U' U')
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
    have n₁ := nil₁ e₁ _ (hres M hMC).1 (isNilpotent_restrict hnil _)
    have n₂ := nil₂ e₂ _ (hres M hMC).2 (isNilpotent_restrict hnil _)
    refine ext_of_restrict h (hM M hMC) (hM' M hMC) (fun x _ => zero_mem _) (fun x _ => zero_mem _)
      (n₁.trans ?_) (n₂.trans ?_) <;> rfl
  · obtain ⟨e₁, e₂⟩ := heq he
    obtain ⟨gU, gU'⟩ := hH g hg hXg hYg
    have hsU : Set.MapsTo ⇑(g - 1 : Module.End K V) U U := fun x hx => sub_mem (gU hx) hx
    have hsU' : Set.MapsTo ⇑(g - 1 : Module.End K V) U' U' := fun x hx => sub_mem (gU' hx) hx
    have hnilU : IsNilpotent (g.restrict gU - 1) := by
      rw [show g.restrict gU - 1 = (g - 1).restrict hsU from LinearMap.ext fun _ => rfl]
      exact isNilpotent_restrict hnil hsU
    have hnilU' : IsNilpotent (g.restrict gU' - 1) := by
      rw [show g.restrict gU' - 1 = (g - 1).restrict hsU' from LinearMap.ext fun _ => rfl]
      exact isNilpotent_restrict hnil hsU'
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
  · simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
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

/-- A unipotent semisimple endomorphism is `1`. -/
theorem eq_one_of_isNilpotent_sub_one {h : Module.End K V} (hss : h.IsSemisimple)
    (hnil : IsNilpotent (h - 1)) : h = 1 := by
  have : (h - 1).IsSemisimple :=
    Module.End.IsSemisimple.sub_of_commute (Commute.one_right h) hss Module.End.isSemisimple_id
  exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple hnil this)

/-- Elements of a subspace of dimension `≤ 1` commute. -/
theorem commute_of_mem_finrank_le_one {S : Submodule K (Module.End K V)}
    (h1 : finrank K S ≤ 1) {M₁ M₂ : Module.End K V} (h₁ : M₁ ∈ S) (h₂ : M₂ ∈ S) :
    Commute M₁ M₂ := by
  by_cases h0 : M₁ = 0
  · rw [h0]; exact Commute.zero_left _
  · obtain ⟨c, rfl⟩ := exists_smul_of_finrank_le_one h1 h₁ h0 h₂
    exact (Commute.refl M₁).smul_right c

/-- **The four clauses for `so(V)`** (`P = ±1`, `N = 0`): `dim so(V) ≥ ⌊n/2⌋`, with equality iff
`so(V)` is abelian (iff `n ≤ 2`); then `so(V)` has no nonzero nilpotent element and the only
unipotent isometry is `1`. -/
theorem so_clauses [CharZero K] (hQ : IsNondeg Q) :
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

/-- **The four clauses on a paired piece** `V = span(u) ⊕ span(w)`, with `u_i` joint eigenvectors for
`(μ, c)`, `w_j` for `(μ⁻¹, −c)`, `(μ, c) ≠ (μ⁻¹, −c)`, `b(w_j, u_k) = δ_{jk}`: bound `d`. -/
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
    have := hwu i i; rw [h, map_zero, if_pos rfl] at this; exact zero_ne_one this
  -- `d = 1`: the hyperbolic pair
  have hone : d = 1 → soCent Q P ⊓ soCent Q N = K ∙ wedge (bform Q) (u ⟨0, by omega⟩)
      (w ⟨0, by omega⟩) ∧ _ := fun hd1 => by
    subst hd1
    have hsp : Submodule.span K {u 0, w 0} = ⊤ := by
      rw [← hspan]; congr 1; ext x; simp [Fin.forall_fin_one, Set.mem_range, eq_comm]
    have huw : bform Q (u 0) (w 0) ≠ 0 := by
      rw [bform_comm Q, hwu 0 0, if_pos rfl]; exact one_ne_zero
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

omit [IsAlgClosed K] in
/-- An isometry preserving `U` preserves `U^⊥`. -/
theorem mapsTo_orthogonal_of_isIsom (hQ : IsNondeg Q) {g : Module.End K V}
    (hg : IsIsom (bform Q) g) {U : Submodule K V} (hgU : Set.MapsTo g U U) :
    Set.MapsTo g ((bform Q).orthogonal U) ((bform Q).orthogonal U) := by
  have hinj : Function.Injective (g.restrict hgU) := fun x y hxy =>
    Subtype.ext (IsIsom.injective hQ hg (congrArg Subtype.val hxy))
  have hsurj := LinearMap.injective_iff_surjective.1 hinj
  intro y hy
  refine LinearMap.BilinForm.mem_orthogonal_iff.2 fun x hx => ?_
  obtain ⟨x', hx'⟩ := hsurj ⟨x, hx⟩
  have hx'' : g x' = x := congrArg Subtype.val hx'
  change bform Q x (g y) = 0
  rw [← hx'', hg]
  exact (LinearMap.BilinForm.mem_orthogonal_iff.1 hy) _ x'.2

end Base

section Main

universe u

variable {K : Type*} [Field K] [Invertible (2 : K)] [CharZero K] [IsAlgClosed K]

/-- Induction form of `jointClauses`, with `dim (E₋₁(P) ∩ ker N)` even in place of `det P = 1`. -/
private theorem jointClauses_aux (n : ℕ) : ∀ {V : Type u} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Q : QuadraticForm K V) (P N : Module.End K V), finrank K V = n →
    IsNondeg Q → IsIsom (bform Q) P → P.IsSemisimple → IsSkew (bform Q) N → N.IsSemisimple →
    Commute N P → Even (finrank K ↥(P.eigenspace (-1) ⊓ N.eigenspace 0)) →
    JointClauses Q P N (n / 2) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ Q P N hn hQ hP hssP hN hssN hc hev
  by_cases hA : ∃ μ c : K, P.eigenspace μ ⊓ N.eigenspace c ≠ ⊥ ∧ (μ⁻¹ ≠ μ ∨ c ≠ 0)
  · sorry
  · -- only self-paired joint eigenvalues: `N = 0` and `P = ±1` on its eigenspaces
    push Not at hA
    have hjoint : ∀ c : K, N.eigenspace c ≠ ⊥ → ∃ μ, P.eigenspace μ ⊓ N.eigenspace c ≠ ⊥ := by
      intro c hcne
      set E := N.eigenspace c
      have hE : ∀ x ∈ E, P x ∈ E := mapsTo_eigenspace_of_commute hc c
      haveI : Nontrivial E := Submodule.nontrivial_iff_ne_bot.2 hcne
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
    rw [hN0, inf_top_eq] at hev
    obtain ⟨k, hk⟩ := hev
    have : finrank K E₁ / 2 + finrank K E₂ / 2 = n / 2 := by omega
    rwa [this] at hcomb

end Main

end GSpinGGP
