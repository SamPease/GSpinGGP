/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.SimpleModule.WedderburnArtin
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Modules over a simple algebra are determined by their dimension

Over a simple Artinian ring `A`, every module is isotypic (Mathlib `IsSimpleRing.isIsotypic`), so a
finitely generated module is `S^n` for the simple module `S`. For an algebra `A` over a field `F`,
two `A`-modules that are finite-dimensional over `F` are therefore isomorphic as soon as they have
the same `F`-dimension (`nonempty_linearEquiv_of_finrank_eq`).
-/

open Module

namespace GSpinGGP

variable {F A : Type*} [Field F] [Ring A] [Algebra F A] [IsSimpleRing A] [IsArtinianRing A]

/-- Two simple modules over a simple Artinian ring are isomorphic. -/
theorem nonempty_linearEquiv_of_isSimpleModule {S T : Type*} [AddCommGroup S] [Module A S]
    [AddCommGroup T] [Module A T] [IsSimpleModule A S] [IsSimpleModule A T] :
    Nonempty (S ≃ₗ[A] T) := by
  have hI := IsSimpleRing.isIsotypic A (S × T)
  have h₁ : IsSimpleModule A (LinearMap.range (LinearMap.inl A S T)) :=
    IsSimpleModule.congr (LinearEquiv.ofInjective _ LinearMap.inl_injective).symm
  have h₂ : IsSimpleModule A (LinearMap.range (LinearMap.inr A S T)) :=
    IsSimpleModule.congr (LinearEquiv.ofInjective _ LinearMap.inr_injective).symm
  obtain ⟨e⟩ := hI (LinearMap.range (LinearMap.inl A S T)) (LinearMap.range (LinearMap.inr A S T))
  exact ⟨(LinearEquiv.ofInjective _ LinearMap.inl_injective).trans
    (e.symm.trans (LinearEquiv.ofInjective _ LinearMap.inr_injective).symm)⟩

variable {M N : Type*} [AddCommGroup M] [Module A M] [Module F M] [IsScalarTower F A M]
  [FiniteDimensional F M] [AddCommGroup N] [Module A N] [Module F N] [IsScalarTower F A N]
  [FiniteDimensional F N]

omit [IsSimpleRing A] [IsArtinianRing A] in
/-- If `P ≅ T^k` with `T` simple, then `dim_F P = k · dim_F T` and `dim_F T > 0`. -/
theorem finrank_eq_mul_of_linearEquiv_fun {P : Type*} [AddCommGroup P] [Module A P] [Module F P]
    [IsScalarTower F A P] [FiniteDimensional F P] {k : ℕ} [NeZero k] {T : Submodule A P}
    [IsSimpleModule A T] (g : P ≃ₗ[A] (Fin k → T)) :
    finrank F P = k * finrank F T ∧ 0 < finrank F T := by
  have : Module.Finite F (Fin k → T) := Module.Finite.equiv (g.restrictScalars F)
  have : Module.Finite F T := Module.Finite.of_surjective (LinearMap.proj (R := F) (0 : Fin k))
    (fun y => ⟨fun _ => y, rfl⟩)
  have : Nontrivial T := IsSimpleModule.nontrivial A T
  refine ⟨?_, Module.finrank_pos⟩
  rw [(g.restrictScalars F).finrank_eq, Module.finrank_pi_fintype, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **Modules over a simple algebra of equal dimension are isomorphic.** -/
theorem nonempty_linearEquiv_of_finrank_eq (h : finrank F M = finrank F N) :
    Nonempty (M ≃ₗ[A] N) := by
  rcases subsingleton_or_nontrivial M with hM | hM
  · have : Subsingleton N := by
      rw [← Module.finrank_zero_iff (R := F), ← h]; exact finrank_zero_of_subsingleton
    exact ⟨LinearEquiv.ofSubsingleton M N⟩
  have : Nontrivial N := by
    rw [← Module.finrank_pos_iff (R := F), ← h]; exact Module.finrank_pos
  have : Module.Finite A M := Module.Finite.of_restrictScalars_finite F A M
  have : Module.Finite A N := Module.Finite.of_restrictScalars_finite F A N
  obtain ⟨n, hn, S, hS, ⟨e⟩⟩ := (IsSimpleRing.isIsotypic A M).linearEquiv_fun
  obtain ⟨n', hn', S', hS', ⟨e'⟩⟩ := (IsSimpleRing.isIsotypic A N).linearEquiv_fun
  obtain ⟨f⟩ := nonempty_linearEquiv_of_isSimpleModule (A := A) (S := S) (T := S')
  obtain ⟨h1, hpos⟩ := finrank_eq_mul_of_linearEquiv_fun (F := F) e
  obtain ⟨h2, -⟩ := finrank_eq_mul_of_linearEquiv_fun (F := F) e'
  have hT : finrank F S = finrank F S' := (f.restrictScalars F).finrank_eq
  have hnn : n = n' := by
    rw [h1, h2, hT] at h
    exact Nat.eq_of_mul_eq_mul_right (hT ▸ hpos) h
  subst hnn
  exact ⟨(e.trans (LinearEquiv.piCongrRight fun _ => f)).trans e'.symm⟩

end GSpinGGP
