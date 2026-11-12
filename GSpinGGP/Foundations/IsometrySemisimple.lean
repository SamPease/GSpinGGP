/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.IsometryCentralizer
import TauCeti.LinearAlgebra.Eigenspace.Semisimple

/-!
# Isometries commuting with a regular semisimple isometry are semisimple

Let `B` be a nondegenerate symmetric bilinear form on a finite-dimensional space `V` over an
algebraically closed field of characteristic `0`, and `X` a semisimple isometry whose moved Lie
centralizer is abelian (`LieAbelian B X`).  Then every isometry `h` commuting with `X` and fixing
`ker (X − 1)` pointwise is semisimple (`isSemisimple_of_commute_of_lieAbelian`).

Proof.  `V` is the sum of the eigenspaces `E_μ` of `X`, each preserved by `h`.  On `E₁`, `h = 1`;
for `μ ≠ ±1`, `dim E_μ ≤ 1` (`finrank_eigenspace_le_one`); and `dim E₋₁ ≤ 2`
(`finrank_eigenspace_neg_one_le_two`), with `B` nondegenerate on `E₋₁`.  An isometry of a
nondegenerate plane over an algebraically closed field of characteristic `≠ 2` is diagonalizable
(`le_iSup_eigenspace_of_finrank_eq_two`): with `h e = a e`, `e ≠ 0`, either `B(e,e) ≠ 0` and
`e^⊥` is a second eigenline, or `e` is isotropic, `B(e,f) ≠ 0`, `h f = α e + β f` with `aβ = 1`,
and `f + γ e` is an eigenvector for a suitable `γ` (`α = 0` if `β = a`, since then `β² = 1` and
`B(hf,hf) = B(f,f)` gives `2αβ B(e,f) = 0`).

The same holds for skew-adjoint `h` vanishing on `ker (X − 1)`
(`isSemisimple_of_isSkewAdjoint_of_commute_of_lieAbelian`): a skew-adjoint endomorphism of a
nondegenerate plane is diagonalizable (`le_iSup_eigenspace_of_finrank_eq_two_of_isSkewAdjoint`;
with `h e = a e`, `e` isotropic and `h f = α e + β f`, skewness gives `β = −a`, and `α = 0` when
`a = 0`).  Both share the skeletons `le_iSup_eigenspace_of_finrank_eq_two_of_forall` and
`isSemisimple_of_commute_of_lieAbelian_of_forall`.
-/

noncomputable section

open Module Module.End LinearMap

namespace GSpinGGP

namespace IsomCent

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable (B : LinearMap.BilinForm K V)

/-- An endomorphism of a space of dimension `≤ 1` is semisimple. -/
theorem isSemisimple_of_finrank_le_one {E : Type*} [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (h1 : finrank K E ≤ 1) (f : Module.End K E) : f.IsSemisimple := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 h1 with h0 | h1
  · have : Subsingleton E := Module.finrank_zero_iff.1 h0
    have : f = 0 := LinearMap.ext fun x => Subsingleton.elim _ _
    rw [this]
    exact isSemisimple_zero
  · obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1 f
    rw [hc]
    exact IsSemisimple_smul c isSemisimple_id

/-- An invariant subspace on which `h` is semisimple lies in the span of the eigenspaces of `h`
(over an algebraically closed field). -/
theorem le_iSup_eigenspace_of_restrict [IsAlgClosed K] [FiniteDimensional K V]
    {h : Module.End K V} {E : Submodule K V} (hE : ∀ v ∈ E, h v ∈ E)
    (hs : Module.End.IsSemisimple (h.restrict hE)) : E ≤ ⨆ μ : K, h.eigenspace μ := by
  intro v hv
  have hmem : (⟨v, hv⟩ : E) ∈ ⨆ μ : K, Module.End.eigenspace (h.restrict hE) μ := by
    rw [hs.iSup_eigenspace_eq_top]; trivial
  suffices ∀ w : E, w ∈ ⨆ μ : K, Module.End.eigenspace (h.restrict hE) μ →
      (w : V) ∈ ⨆ μ : K, h.eigenspace μ from this _ hmem
  intro w hw
  induction hw using Submodule.iSup_induction' with
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | mem μ x hx =>
    refine Submodule.mem_iSup_of_mem μ ?_
    rw [mem_eigenspace_iff] at hx ⊢
    have := congrArg Subtype.val hx
    simpa [LinearMap.restrict_apply] using this

variable {B}

/-- Two vectors `e, g` of a plane `E` that are linearly independent span it. -/
theorem le_span_pair_of_finrank_eq_two {E : Submodule K V} [FiniteDimensional K E]
    (h2 : finrank K E = 2) {e g : V} (he : e ∈ E) (hg : g ∈ E)
    (hind : ∀ s t : K, s • e + t • g = 0 → s = 0 ∧ t = 0) :
    E ≤ Submodule.span K {e, g} := by
  have hli : LinearIndependent K ![e, g] := LinearIndependent.pair_iff.2 hind
  have hle : Submodule.span K {e, g} ≤ E := by
    rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨he, hg⟩
  have hfr : finrank K (Submodule.span K ({e, g} : Set V)) = 2 := by
    have := finrank_span_eq_card hli
    rw [Matrix.range_cons_cons_empty] at this
    simpa using this
  exact (Submodule.eq_of_le_of_finrank_eq hle (hfr.trans h2.symm)).ge

/-- **Diagonalizing an endomorphism of a nondegenerate plane** (common skeleton of
`le_iSup_eigenspace_of_finrank_eq_two` and its skew-adjoint form).  Let `h` preserve a plane `E`
on which `B` is nondegenerate, over an algebraically closed field.  Take an eigenvector `e ∈ E`,
`h e = a e`, and complete it to a basis `e, f` of `E`, with `h f = α e + β f`.  Then `E` lies in
the span of the eigenspaces of `h` provided that
* (`hiso`) when `e` is isotropic and `B(e,f) ≠ 0`: `α = γ (β − a)` for some `γ` (then `f + γ e`
  is an eigenvector);
* (`haniso`) when `B(e,e) ≠ 0` and `B(e,f) = 0`: `α = 0` (then `f` is an eigenvector). -/
theorem le_iSup_eigenspace_of_finrank_eq_two_of_forall [IsAlgClosed K] {h : Module.End K V}
    {E : Submodule K V} (hE : ∀ v ∈ E, h v ∈ E) (h2 : finrank K E = 2)
    (hndE : ∀ e ∈ E, e ≠ 0 → ∃ e' ∈ E, B e e' ≠ 0)
    (hiso : ∀ {a α β : K} {e f : V}, e ≠ 0 → h e = a • e → h f = α • e + β • f → B e e = 0 →
      B e f ≠ 0 → ∃ γ, α = γ * (β - a))
    (haniso : ∀ {a α β : K} {e g : V}, e ≠ 0 → h e = a • e → h g = α • e + β • g → B e g = 0 →
      B e e ≠ 0 → α = 0) :
    E ≤ ⨆ μ : K, h.eigenspace μ := by
  classical
  have : FiniteDimensional K E := Module.finite_of_finrank_pos (by omega)
  have hmemE : ∀ {u μ}, u ∈ h.eigenspace μ → u ∈ ⨆ μ : K, h.eigenspace μ :=
    fun hu => Submodule.mem_iSup_of_mem _ hu
  -- an eigenvector `e ∈ E`
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (h.restrict hE)
  obtain ⟨e₀, he₀, he₀0⟩ := ha.exists_hasEigenvector
  set e : V := (e₀ : V) with hedef
  have heE : e ∈ E := e₀.2
  have he0 : e ≠ 0 := fun h0 => he₀0 (Subtype.ext h0)
  have hhe : h e = a • e := by
    have := congrArg Subtype.val (mem_eigenspace_iff.mp he₀)
    simpa [LinearMap.restrict_apply] using this
  have heig : e ∈ h.eigenspace a := mem_eigenspace_iff.mpr hhe
  obtain ⟨e', he'E, hee'⟩ := hndE e heE he0
  -- a second eigenvector `g ∈ E`, independent of `e`
  suffices ∃ g ∈ E, (∃ β, h g = β • g) ∧ ∀ s t : K, s • e + t • g = 0 → s = 0 ∧ t = 0 by
    obtain ⟨g, hgE, ⟨β, hhg⟩, hind⟩ := this
    refine (le_span_pair_of_finrank_eq_two h2 heE hgE hind).trans ?_
    rw [Submodule.span_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨hmemE heig, hmemE (mem_eigenspace_iff.mpr hhg)⟩
  by_cases hee : B e e = 0
  · -- `e` isotropic: `f = e'` with `B(e,f) ≠ 0`
    set f := e' with hfdef
    have hind : ∀ s t : K, s • e + t • f = 0 → s = 0 ∧ t = 0 := by
      intro s t hst
      have h1 := congrArg (B e) hst
      rw [map_add, map_smul, map_smul, hee, map_zero, smul_zero, zero_add, smul_eq_mul] at h1
      have ht : t = 0 := (mul_eq_zero.mp h1).resolve_right hee'
      rw [ht, zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right he0, ht⟩
    obtain ⟨α, β, hab⟩ := Submodule.mem_span_pair.mp
      (le_span_pair_of_finrank_eq_two h2 heE he'E hind (hE f he'E))
    obtain ⟨γ, hαγ⟩ := hiso he0 hhe hab.symm hee hee'
    refine ⟨f + γ • e, add_mem he'E (E.smul_mem γ heE), ⟨β, ?_⟩, fun s t hst => ?_⟩
    · rw [map_add, map_smul, ← hab, hhe, hαγ, smul_add, smul_smul, smul_smul]
      module
    · have h' : (s + t * γ) • e + t • f = 0 := by rw [← hst]; module
      obtain ⟨h1, ht⟩ := hind _ _ h'
      rw [ht, zero_mul, add_zero] at h1
      exact ⟨h1, ht⟩
  · -- `e` anisotropic: a vector `g ∈ E ∩ e^⊥` not on the line `K e`
    obtain ⟨w, hwE, hw⟩ : ∃ w ∈ E, w ∉ Submodule.span K {e} := by
      by_contra hcon
      push Not at hcon
      have hle : E ≤ Submodule.span K {e} := fun w hw => hcon w hw
      have := Submodule.finrank_mono hle
      rw [finrank_span_singleton he0] at this
      omega
    set g := w - (B e w / B e e) • e with hgdef
    have hgE : g ∈ E := sub_mem hwE (E.smul_mem _ heE)
    have heg : B e g = 0 := by
      rw [hgdef, map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hee, sub_self]
    have hg0 : g ≠ 0 := by
      intro hg
      apply hw
      rw [hgdef, sub_eq_zero] at hg
      rw [hg]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e)
    have hind : ∀ s t : K, s • e + t • g = 0 → s = 0 ∧ t = 0 := by
      intro s t hst
      have h1 := congrArg (B e) hst
      rw [map_add, map_smul, map_smul, heg, smul_zero, add_zero, map_zero, smul_eq_mul] at h1
      have hs : s = 0 := (mul_eq_zero.mp h1).resolve_right hee
      rw [hs, zero_smul, zero_add] at hst
      exact ⟨hs, (smul_eq_zero.mp hst).resolve_right hg0⟩
    obtain ⟨α, β, hab⟩ := Submodule.mem_span_pair.mp
      (le_span_pair_of_finrank_eq_two h2 heE hgE hind (hE g hgE))
    have hα : α = 0 := haniso he0 hhe hab.symm heg hee
    refine ⟨g, hgE, ⟨β, ?_⟩, hind⟩
    rw [← hab, hα, zero_smul, zero_add]

/-- **An isometry of a nondegenerate plane is diagonalizable** (over an algebraically closed field
of characteristic `≠ 2`): an `h`-stable plane `E` on which `B` is nondegenerate lies in the span
of the eigenspaces of the isometry `h`. -/
theorem le_iSup_eigenspace_of_finrank_eq_two [IsAlgClosed K] (h2K : (2 : K) ≠ 0)
    (hB : B.IsSymm) {h : Module.End K V} (hi : IsIsom B h) {E : Submodule K V}
    (hE : ∀ v ∈ E, h v ∈ E) (h2 : finrank K E = 2)
    (hndE : ∀ e ∈ E, e ≠ 0 → ∃ e' ∈ E, B e e' ≠ 0) : E ≤ ⨆ μ : K, h.eigenspace μ := by
  refine le_iSup_eigenspace_of_finrank_eq_two_of_forall hE h2 hndE
    (fun {a α β e f} _ hhe hhf hee hee' => ?_) (fun {a α β e g} _ hhe hhg heg hee => ?_)
  · have hfe : B f e = B e f := hB.eq f e
    -- `aβ = 1`
    have haβ : a * β = 1 := by
      have h1 := hi e f
      rw [hhe, hhf] at h1
      simp only [map_add, map_smul, LinearMap.smul_apply, smul_eq_mul,
        hee, mul_zero, zero_add] at h1
      have : (a * β - 1) * B e f = 0 := by linear_combination h1
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right hee')
    have hβ0 : β ≠ 0 := right_ne_zero_of_mul_eq_one haβ
    -- `2αβ B(e,f) + (β² − 1) B(f,f) = 0`
    have hff : 2 * α * β * B e f + (β * β - 1) * B f f = 0 := by
      have h1 := hi f f
      rw [hhf] at h1
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hee, hfe] at h1
      linear_combination h1
    by_cases hβa : β = a
    · refine ⟨0, ?_⟩
      have hββ : β * β = 1 := by rw [hβa] at haβ ⊢; exact haβ
      rw [hββ, sub_self, zero_mul, add_zero] at hff
      have : α * (2 * β * B e f) = 0 := by linear_combination hff
      rw [zero_mul]
      exact (mul_eq_zero.mp this).resolve_right (mul_ne_zero (mul_ne_zero h2K hβ0) hee')
    · exact ⟨α / (β - a), (div_mul_cancel₀ _ (sub_ne_zero.mpr hβa)).symm⟩
  · have ha0 : a ≠ 0 := by
      rintro rfl
      apply hee
      rw [← hi e e, hhe, zero_smul, map_zero]
    have h1 := hi e g
    rw [hhe, hhg, heg] at h1
    simp only [map_add, map_smul, LinearMap.smul_apply, smul_eq_mul, heg, mul_zero,
      add_zero] at h1
    have : α * (a * B e e) = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_right (mul_ne_zero ha0 hee)

/-- **A skew-adjoint endomorphism of a nondegenerate plane is diagonalizable** (over an
algebraically closed field of characteristic `≠ 2`). -/
theorem le_iSup_eigenspace_of_finrank_eq_two_of_isSkewAdjoint [IsAlgClosed K]
    (h2K : (2 : K) ≠ 0) (hB : B.IsSymm) {h : Module.End K V} (hi : B.IsSkewAdjoint h)
    {E : Submodule K V} (hE : ∀ v ∈ E, h v ∈ E) (h2 : finrank K E = 2)
    (hndE : ∀ e ∈ E, e ≠ 0 → ∃ e' ∈ E, B e e' ≠ 0) : E ≤ ⨆ μ : K, h.eigenspace μ := by
  refine le_iSup_eigenspace_of_finrank_eq_two_of_forall hE h2 hndE
    (fun {a α β e f} _ hhe hhf hee hee' => ?_) (fun {a α β e g} _ hhe hhg heg hee => ?_)
  · have hfe : B f e = B e f := hB.eq f e
    -- `β = −a`
    have hβ : β = -a := by
      have h1 := hi.eq e f
      rw [hhe, hhf] at h1
      simp only [map_add, map_smul, LinearMap.smul_apply, smul_eq_mul, hee, mul_zero,
        zero_add] at h1
      have : (β + a) * B e f = 0 := by linear_combination h1
      exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp this).resolve_right hee')
    -- `α B(e,f) + β B(f,f) = 0`
    have hff : α * B e f + β * B f f = 0 := by
      have h1 := hi.eq f f
      rw [hhf] at h1
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
        hfe] at h1
      have : (2 : K) * (α * B e f + β * B f f) = 0 := by linear_combination h1
      exact (mul_eq_zero.mp this).resolve_left h2K
    by_cases hβa : β = a
    · refine ⟨0, ?_⟩
      have ha0 : a = 0 := by
        have : (2 : K) * a = 0 := by linear_combination hβ - hβa
        exact (mul_eq_zero.mp this).resolve_left h2K
      have hβ0 : β = 0 := by rw [hβ, ha0, neg_zero]
      rw [hβ0, zero_mul, add_zero] at hff
      rw [zero_mul]
      exact (mul_eq_zero.mp hff).resolve_right hee'
    · exact ⟨α / (β - a), (div_mul_cancel₀ _ (sub_ne_zero.mpr hβa)).symm⟩
  · have h1 := hi.eq e g
    rw [hhe, hhg] at h1
    simp only [map_add, map_smul, LinearMap.smul_apply, smul_eq_mul, heg, mul_zero,
      add_zero] at h1
    have : α * B e e = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_right hee

variable [CharZero K] [IsAlgClosed K] [FiniteDimensional K V] {X : Module.End K V}

/-- **Common skeleton** of `isSemisimple_of_commute_of_lieAbelian` and its skew-adjoint form: if
`X` is a semisimple isometry with `LieAbelian B X`, an endomorphism `h` commuting with `X`, acting
on `ker (X − 1)` by a scalar `c`, and diagonalizable on every `h`-stable plane on which `B` is
nondegenerate, is semisimple. -/
theorem isSemisimple_of_commute_of_lieAbelian_of_forall (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (hX : IsIsom B X) (hss : X.IsSemisimple) (hL : LieAbelian B X) {h : Module.End K V}
    (hc : Commute X h) (c : K) (hf : ∀ z ∈ X.eigenspace 1, h z = c • z)
    (hplane : ∀ {E : Submodule K V}, (∀ v ∈ E, h v ∈ E) → finrank K E = 2 →
      (∀ e ∈ E, e ≠ 0 → ∃ e' ∈ E, B e e' ≠ 0) → E ≤ ⨆ μ : K, h.eigenspace μ) :
    h.IsSemisimple := by
  apply TauCeti.isSemisimple_of_iSup_eigenspace_eq_top
  rw [eq_top_iff, ← hss.iSup_eigenspace_eq_top]
  refine iSup_le fun μ => ?_
  have hmaps := mapsTo_eigenspace_of_commute hc μ
  by_cases hμ1 : μ = 1
  · subst hμ1
    intro v hv
    exact Submodule.mem_iSup_of_mem c (mem_eigenspace_iff.mpr (hf v hv))
  by_cases hμ2 : μ * μ ≠ 1
  · exact le_iSup_eigenspace_of_restrict hmaps (isSemisimple_of_finrank_le_one
      (finrank_eigenspace_le_one hB hnd hX hss hL hμ1 hμ2) _)
  push Not at hμ2
  have hμ : μ = -1 := by
    have : (μ - 1) * (μ + 1) = 0 := by linear_combination hμ2
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hμ1
    · exact eq_neg_of_add_eq_zero_left h0
  subst hμ
  have hle2 := finrank_eigenspace_neg_one_le_two hB hnd hX hss hL
  rcases Nat.lt_or_ge (finrank K (X.eigenspace (-1))) 2 with hlt | hge
  · exact le_iSup_eigenspace_of_restrict hmaps (isSemisimple_of_finrank_le_one (by omega) _)
  · refine hplane hmaps (by omega) ?_
    intro e he he0
    obtain ⟨w, hw, hew⟩ := exists_eigen_pair_ne_zero hnd hX hss he he0
    rw [inv_neg, inv_one] at hw
    exact ⟨w, hw, hew⟩

/-- **Isometries commuting with a regular semisimple isometry are semisimple**: if `X` is a
semisimple isometry with `LieAbelian B X`, every isometry `h` commuting with `X` and fixing
`ker (X − 1)` pointwise is semisimple. -/
theorem isSemisimple_of_commute_of_lieAbelian (hB : B.IsSymm) (hnd : B.Nondegenerate)
    (hX : IsIsom B X) (hss : X.IsSemisimple) (hL : LieAbelian B X) {h : Module.End K V}
    (hi : IsIsom B h) (hc : Commute X h) (hf : ∀ z ∈ X.eigenspace 1, h z = z) :
    h.IsSemisimple :=
  isSemisimple_of_commute_of_lieAbelian_of_forall hB hnd hX hss hL hc 1
    (fun z hz => by rw [one_smul]; exact hf z hz)
    (le_iSup_eigenspace_of_finrank_eq_two two_ne_zero hB hi)

/-- **Skew-adjoint endomorphisms commuting with a regular semisimple isometry are semisimple**: if
`X` is a semisimple isometry with `LieAbelian B X`, every skew-adjoint `h` commuting with `X` and
vanishing on `ker (X − 1)` is semisimple.  Lie-algebra form of
`isSemisimple_of_commute_of_lieAbelian`. -/
theorem isSemisimple_of_isSkewAdjoint_of_commute_of_lieAbelian (hB : B.IsSymm)
    (hnd : B.Nondegenerate) (hX : IsIsom B X) (hss : X.IsSemisimple) (hL : LieAbelian B X)
    {h : Module.End K V} (hi : B.IsSkewAdjoint h) (hc : Commute X h)
    (hf : ∀ z ∈ X.eigenspace 1, h z = 0) : h.IsSemisimple :=
  isSemisimple_of_commute_of_lieAbelian_of_forall hB hnd hX hss hL hc 0
    (fun z hz => by rw [zero_smul]; exact hf z hz)
    (le_iSup_eigenspace_of_finrank_eq_two_of_isSkewAdjoint two_ne_zero hB hi)

end IsomCent

end GSpinGGP
