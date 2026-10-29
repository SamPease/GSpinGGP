/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.Kottwitz

/-!
# Hilbert's Theorem 90 for `GL_m` (cited)

`H¹(F, GL_m) = 1`: every continuous `1`-cocycle of `Γ_F` with values in `GL_m(F̄)` is a
coboundary.  Used in `Main.existsUnique_twistIdx` (existence half: an `S_x`-valued cocycle is the
cocycle of a rational quadratic form, `TwistDescent.exists_twist_of_split`).  Mathlib (v4.35) has
only the case `m = 1` for finite Galois extensions
(`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`).
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

/-- **Hilbert's Theorem 90 for `GL_m`** (Serre, *Local Fields*, GTM 67, Ch. X §1, Prop. 3:
`H¹(Gal(L/K), GL_n(L)) = 1` for a finite Galois extension `L/K`; Serre, *Cohomologie galoisienne*,
Ch. III §1.1, Prop. 1 (`H¹(K, GL_n) = 0`, from Lemme 1) for the profinite version; theorem numbers
not checked against the books).  Conventions as in Serre: cocycle rule `a_{στ} = a_σ σ(a_τ)`,
coboundary `a_σ = b⁻¹ σ(b)`.  A continuous cocycle `σ ↦ a_σ ∈ GL_m(F̄)` of `Γ_F = Aut(F̄/F)` is a
coboundary: `a_σ = M⁻¹ σ(M)` for some `M ∈ GL_m(F̄)`.

Faithfulness of the packaging.  `GalCocycle` asks that `a_σ` depend only on `σ|_E` for a finite
`E/F`.  Let `L ⊇ E` be the normal closure (`F̄/F` is Galois, `F` having characteristic `0`).
First `a_1 = 1`, from the cocycle identity `a_1 = a_1 · 1(a_1) = a_1 a_1`.  For
`τ` fixing `L`: `a_τ = a_1 = 1` and `τσ|_E = σ|_E`, so `τ(a_σ) = a_{τσ} = a_σ`; hence every
`a_σ ∈ GL_m(L)` and `a` is inflated from a cocycle of `Gal(L/F)` in `GL_m(L)`, to which Serre's
proposition applies (`M ∈ GL_m(L)`).  The subgroup `S` plays no role (any `S`-valued cocycle is a
`GL_m`-valued one).  Degenerate instances (`hilbert90_GL_one`, `hilbert90_GL_zero` below): the
trivial cocycle (`M = 1`) and `m = 0` (`GL_0` is trivial). -/
axiom hilbert90_GL {m : ℕ} {S : Subgroup (GL (Fin m) (AlgebraicClosure F))} (a : GalCocycle S) :
    ∃ M : GL (Fin m) (AlgebraicClosure F), ∀ σ : GalF F, a.toFun σ = M⁻¹ * galGL m σ M

/-- Consistency check of `hilbert90_GL` at the trivial cocycle: `M = 1` works, independently of
the axiom. -/
theorem hilbert90_GL_one {m : ℕ} (S : Subgroup (GL (Fin m) (AlgebraicClosure F))) :
    ∃ M : GL (Fin m) (AlgebraicClosure F), ∀ σ : GalF F,
      (GalCocycle.one S).toFun σ = M⁻¹ * galGL m σ M :=
  ⟨1, fun _ => by simp [GalCocycle.one]⟩

/-- Consistency check of `hilbert90_GL` at `m = 0`: every cocycle is split by `M = 1`,
independently of the axiom (`GL_0` is trivial). -/
theorem hilbert90_GL_zero {S : Subgroup (GL (Fin 0) (AlgebraicClosure F))} (a : GalCocycle S) :
    ∃ M : GL (Fin 0) (AlgebraicClosure F), ∀ σ : GalF F, a.toFun σ = M⁻¹ * galGL 0 σ M :=
  ⟨1, fun σ => Subsingleton.elim _ _⟩

end GSpinGGP
