/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TwistDescent

/-!
# Conjugator cocycles and Galois descent of conjugacy

Let `S ⊆ GL_m(F̄)` be a Galois-stable subgroup and `g ∈ GL_m(F̄)` with `g S g⁻¹` Galois-stable too.
Then `σ ↦ g⁻¹ σ(g)` is a continuous `1`-cocycle with values in the normalizer of `S`
(`conjCocycle`; Serre, *Cohomologie galoisienne*, I §5.3).  If `g, g'` lie in a Galois-stable
subgroup `A` and their cocycles are cohomologous in `N_A(S)`, then `g' S g'⁻¹` and `g S g⁻¹` are
conjugate by a Galois-fixed element of `A` (`exists_fixed_conj_of_rel`), i.e. by an element of
`A ∩ GL_m(F)` (`TwistDescent.exists_map_of_fixed`).
-/

noncomputable section

open scoped Classical

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

variable {m : ℕ}

set_option linter.unusedSectionVars false

theorem galGL_mul_apply (σ τ : GalF F) (g : GL (Fin m) Kb) :
    galGL m (σ * τ) g = galGL m σ (galGL m τ g) := by
  ext i j
  simp [coe_galGL]

theorem galGL_inv_apply (σ : GalF F) (g : GL (Fin m) Kb) :
    galGL m σ⁻¹ (galGL m σ g) = g := by
  rw [← galGL_mul_apply, inv_mul_cancel]
  ext i j
  simp [coe_galGL]

/-- A Galois-stable subgroup: `σ(S) ⊆ S` for every `σ` (hence `σ(S) = S`). -/
def IsGalStable (S : Subgroup (GL (Fin m) Kb)) : Prop :=
  ∀ σ : GalF F, ∀ s ∈ S, galGL m σ s ∈ S

theorem IsGalStable.mem_iff {S : Subgroup (GL (Fin m) Kb)} (hS : IsGalStable (F := F) S)
    (σ : GalF F) (s : GL (Fin m) Kb) : galGL m σ s ∈ S ↔ s ∈ S :=
  ⟨fun h => galGL_inv_apply σ s ▸ hS σ⁻¹ _ h, hS σ s⟩

/-- Every element of `GL_m(F̄)` is fixed by the Galois automorphisms that fix a finite extension:
its finitely many entries generate one. -/
theorem exists_finiteDimensional_galGL_eq (g : GL (Fin m) Kb) :
    ∃ E : IntermediateField F Kb, FiniteDimensional F E ∧
      ∀ σ τ : GalF F, (∀ e ∈ E, σ e = τ e) → galGL m σ g = galGL m τ g := by
  set T : Set Kb := Set.range fun p : Fin m × Fin m => (g : Matrix (Fin m) (Fin m) Kb) p.1 p.2
  have hT : T.Finite := Set.finite_range _
  refine ⟨IntermediateField.adjoin F T, ?_, fun σ τ h => ?_⟩
  · have := hT.fintype
    exact IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  · ext i j
    simp only [coe_galGL, Matrix.map_apply]
    exact h _ (IntermediateField.subset_adjoin F T ⟨(i, j), rfl⟩)

/-- `g⁻¹ σ(g)` normalizes `S` when `S` and `S' = g S g⁻¹` are Galois-stable. -/
theorem inv_mul_galGL_mem_normalizer {S S' : Subgroup (GL (Fin m) Kb)}
    (hS : IsGalStable (F := F) S) (hS' : IsGalStable (F := F) S') {g : GL (Fin m) Kb}
    (hg : S.map (MulAut.conj g).toMonoidHom = S') (σ : GalF F) :
    g⁻¹ * galGL m σ g ∈ Subgroup.normalizer (S : Set (GL (Fin m) Kb)) := by
  have hconj : ∀ x, x ∈ S' ↔ g⁻¹ * x * g ∈ S := fun x => by
    rw [← hg]
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa [mul_assoc] using hs
    · intro hx
      exact ⟨_, hx, by simp [mul_assoc]⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have e : g⁻¹ * galGL m σ g * h * (g⁻¹ * galGL m σ g)⁻¹ =
      g⁻¹ * galGL m σ (g * galGL m σ⁻¹ h * g⁻¹) * g := by
    have h1 : galGL m (1 : GalF F) h = h := by ext i j; simp [coe_galGL]
    rw [map_mul, map_mul, map_inv, ← galGL_mul_apply, mul_inv_cancel, h1]
    simp only [mul_inv_rev, inv_inv, mul_assoc]
  rw [e, ← hconj, hS'.mem_iff, hconj]
  simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  exact (hS.mem_iff _ _).symm

/-- **The conjugator cocycle** `σ ↦ g⁻¹ σ(g)`, with values in any subgroup `N` containing them. -/
def conjCocycle {N : Subgroup (GL (Fin m) Kb)} (g : GL (Fin m) Kb)
    (hg : ∀ σ : GalF F, g⁻¹ * galGL m σ g ∈ N) : GalCocycle N where
  toFun σ := g⁻¹ * galGL m σ g
  mem' := hg
  cocycle' σ τ := by
    rw [map_mul, map_inv, galGL_mul_apply]
    group
  continuous' := by
    obtain ⟨E, hE, h⟩ := exists_finiteDimensional_galGL_eq (F := F) g
    exact ⟨E, hE, fun σ τ hστ => by rw [h σ τ hστ]⟩

theorem conjCocycle_toFun {N : Subgroup (GL (Fin m) Kb)} (g : GL (Fin m) Kb)
    (hg : ∀ σ : GalF F, g⁻¹ * galGL m σ g ∈ N) (σ : GalF F) :
    (conjCocycle g hg).toFun σ = g⁻¹ * galGL m σ g := rfl

/-- **Galois descent of conjugacy.** If the conjugator cocycles of `g, g' ∈ A` are cohomologous in
`N ≤ N_A(S)`, then `h = g c g'⁻¹ ∈ A` (`c ∈ N` the coboundary) is Galois-fixed and conjugates
`g' S g'⁻¹` to `g S g⁻¹`. -/
theorem exists_fixed_conj_of_rel {A S N : Subgroup (GL (Fin m) Kb)} (hN : N ≤ Subgroup.normalizer (S : Set (GL (Fin m) Kb)) ⊓ A)
    {g g' : GL (Fin m) Kb} (hgA : g ∈ A) (hg'A : g' ∈ A)
    (hg : ∀ σ : GalF F, g⁻¹ * galGL m σ g ∈ N) (hg' : ∀ σ : GalF F, g'⁻¹ * galGL m σ g' ∈ N)
    (hrel : GalCocycle.Rel (conjCocycle g hg) (conjCocycle g' hg')) :
    ∃ h ∈ A, (∀ σ : GalF F, galGL m σ h = h) ∧
      (S.map (MulAut.conj g').toMonoidHom).map (MulAut.conj h).toMonoidHom =
        S.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨c, hc, hrel⟩ := hrel
  obtain ⟨hcS, hcA⟩ := hN hc
  have hcS : c ∈ Subgroup.normalizer (S : Set (GL (Fin m) Kb)) := hcS
  have hcA : c ∈ A := hcA
  refine ⟨g * c * g'⁻¹, A.mul_mem (A.mul_mem hgA hcA) (A.inv_mem hg'A), fun σ => ?_, ?_⟩
  · have h := hrel σ
    simp only [conjCocycle_toFun] at h
    rw [map_mul, map_mul, map_inv]
    have e : galGL m σ g' = g' * (c⁻¹ * (g⁻¹ * galGL m σ g) * galGL m σ c) := by
      rw [← h, mul_inv_cancel_left]
    rw [e]
    group
  · rw [Subgroup.map_map]
    have hcS' : S.map (MulAut.conj c).toMonoidHom = S := by
      ext x
      rw [Subgroup.mem_normalizer_iff] at hcS
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact (hcS s).1 hs
      · intro hx
        refine ⟨c⁻¹ * x * c, (hcS _).2 (by simpa [mul_assoc] using hx), ?_⟩
        simp [mul_assoc]
    conv_rhs => rw [← hcS', Subgroup.map_map]
    congr 1
    ext x
    simp [mul_assoc]

end GSpinGGP
