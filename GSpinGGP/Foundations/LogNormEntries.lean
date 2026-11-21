/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups
import GSpinGGP.Foundations.BasisNorm
import GSpinGGP.HarmonicAnalysis.LogNorm

/-!
# The log-norm `logNorm` and the matrix entries of `g` and `g⁻¹`

Let `A` be a finite-dimensional algebra over a `p`-adic field `F` and `G ⊆ Aˣ` a subgroup. The
log-norm `logNorm F G g = 1 + log max(1, ‖g‖, ‖g⁻¹‖)` (`Foundations/LocalGroups.lean`) is built
from operator norms of left multiplication. In the literature (Waldspurger, *La formule de
Plancherel pour les groupes `p`-adiques*, J. Inst. Math. Jussieu 2 (2003), §I.1 p. 242; Kottwitz,
*Harmonic analysis on reductive `p`-adic groups and Lie algebras*, Clay Math. Proc. 4 (2005),
§18.2, (18.2.1)) the norm of `g` is instead the largest absolute value of the matrix entries of
`τ(g)` and `τ(g)⁻¹` for a faithful representation `τ`.  For `τ(g) =` left multiplication by `g`
on `A`, written in a basis `b` of `A`, this is `entryMaxNorm b g`, and the two log-norms are
equivalent (`logNorm_equiv_entryMaxNorm`):

  `logNorm F G g ≤ C (1 + log entryMaxNorm b g)`, `1 + log entryMaxNorm b g ≤ C logNorm F G g`.

For `G = GSpin(W) × GSpin(V) ⊆ (C(W) × C(V))ˣ` this compares `GGPData.logNormG` (which is
`logNorm F d.G` by definition) with the log of the norm (18.2.1) of Kottwitz for the coordinate
functions `g ↦ (L_g)_{ij}`, `g ↦ (L_{g⁻¹})_{ij}`.
-/

noncomputable section

open Module

namespace GSpinGGP

section EntryNorm

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
  {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A]
  [IsModuleTopology F A] {n : ℕ} (b : Basis (Fin n) F A)

/-- `max(1, sup_{i,j} |(L_g)_{ij}|, sup_{i,j} |(L_{g⁻¹})_{ij}|)`: the largest absolute value of a
matrix entry of left multiplication by `g` or by `g⁻¹` on `A`, in the basis `b` (Waldspurger
2003, §I.1 p. 242, for `τ(g) = L_g`; Kottwitz 2005, (18.2.1)). -/
def entryMaxNorm (G : Subgroup Aˣ) (g : ↥G) : ℝ :=
  max 1 (max (basisOpNorm b (LinearMap.mulLeft F ((g : Aˣ) : A)))
    (basisOpNorm b (LinearMap.mulLeft F (((g⁻¹ : ↥G) : Aˣ) : A))))

omit [PAdicField F] [Module.Finite F A] [TopologicalSpace A] [IsModuleTopology F A] in
theorem one_le_entryMaxNorm (G : Subgroup Aˣ) (g : ↥G) : 1 ≤ entryMaxNorm b G g :=
  le_max_left _ _

/-- The matrix of `lmulPi a` in the transported basis is the matrix of `L_a` in `b`. -/
theorem basisOpNorm_lmulPi (a : A) :
    basisOpNorm (b.map (toPiCLE F A).toLinearEquiv) (lmulPi F a : _ →ₗ[F] _) =
      basisOpNorm b (LinearMap.mulLeft F a) := by
  simp [basisOpNorm, lmulPi_apply, Basis.map_equivFun]

/-- **`max(1, ‖g‖, ‖g⁻¹‖)` and `entryMaxNorm b g` are equivalent**: operator norms and sup norms
of matrices on the finite-dimensional space `A ≅ F^d` are equivalent. -/
theorem exists_maxNorm_equiv_entryMaxNorm (G : Subgroup Aˣ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ g : ↥G,
      maxNorm F G g ≤ C * entryMaxNorm b G g ∧ entryMaxNorm b G g ≤ C * maxNorm F G g := by
  set b' := b.map (toPiCLE F A).toLinearEquiv
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_toContinuousLinearMap_le_basisOpNorm b'
  obtain ⟨C₂, hC₂, h₂⟩ := exists_basisOpNorm_le_norm_toContinuousLinearMap b'
  set C := max 1 (max C₁ C₂)
  have hC : 1 ≤ C := le_max_left _ _
  have hC1 : C₁ ≤ C := le_max_of_le_right (le_max_left _ _)
  have hC2 : C₂ ≤ C := le_max_of_le_right (le_max_right _ _)
  -- `‖lmulPi a‖ ≤ C₁ ‖L_a‖_b` and `‖L_a‖_b ≤ C₂ ‖lmulPi a‖`
  have e1 : ∀ a : A, ‖lmulPi F a‖ ≤ C₁ * basisOpNorm b (LinearMap.mulLeft F a) := fun a => by
    have := h₁ (lmulPi F a : _ →ₗ[F] _)
    rwa [basisOpNorm_lmulPi,
      (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap _ _).2 rfl] at this
  have e2 : ∀ a : A, basisOpNorm b (LinearMap.mulLeft F a) ≤ C₂ * ‖lmulPi F a‖ := fun a => by
    have := h₂ (lmulPi F a : _ →ₗ[F] _)
    rwa [basisOpNorm_lmulPi,
      (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap _ _).2 rfl] at this
  refine ⟨C, hC, fun g => ⟨?_, ?_⟩⟩
  · have hE := one_le_entryMaxNorm b G g
    have hE0 : 0 ≤ entryMaxNorm b G g := zero_le_one.trans hE
    have k : ∀ x, x ≤ entryMaxNorm b G g → C₁ * x ≤ C * entryMaxNorm b G g := fun x hx =>
      (mul_le_mul_of_nonneg_left hx hC₁).trans (mul_le_mul_of_nonneg_right hC1 hE0)
    refine max_le (one_le_mul_of_one_le_of_one_le hC hE) (max_le ?_ ?_)
    · exact (e1 _).trans (k _ (le_max_of_le_right (le_max_left _ _)))
    · exact (e1 _).trans (k _ (le_max_of_le_right (le_max_right _ _)))
  · have hM := one_le_maxNorm (F := F) G g
    have hM0 : 0 ≤ maxNorm F G g := zero_le_one.trans hM
    have k : ∀ x, x ≤ maxNorm F G g → C₂ * x ≤ C * maxNorm F G g := fun x hx =>
      (mul_le_mul_of_nonneg_left hx hC₂).trans (mul_le_mul_of_nonneg_right hC2 hM0)
    refine max_le (one_le_mul_of_one_le_of_one_le hC hM) (max_le ?_ ?_)
    · exact (e2 _).trans (k _ (le_max_of_le_right (le_max_left _ _)))
    · exact (e2 _).trans (k _ (le_max_of_le_right (le_max_right _ _)))

/-- **`σ` and the log of the matrix-entry norm are equivalent**: there is `C` with
`logNorm F G g ≤ C (1 + log entryMaxNorm b g)` and `1 + log entryMaxNorm b g ≤ C logNorm F G g`
for all `g`. -/
theorem logNorm_equiv_entryMaxNorm (G : Subgroup Aˣ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : ↥G,
      logNorm F G g ≤ C * (1 + Real.log (entryMaxNorm b G g)) ∧
        1 + Real.log (entryMaxNorm b G g) ≤ C * logNorm F G g := by
  obtain ⟨C, hC, h⟩ := exists_maxNorm_equiv_entryMaxNorm b G
  refine ⟨1 + Real.log C + 1, by linarith [Real.log_nonneg hC], fun g => ⟨?_, ?_⟩⟩
  · have := one_add_log_le_of_le_mul_pow (n := 1) (one_le_maxNorm (F := F) G g)
      (one_le_entryMaxNorm b G g) hC (by simpa using (h g).1)
    simpa [logNorm] using this
  · have := one_add_log_le_of_le_mul_pow (n := 1) (one_le_entryMaxNorm b G g)
      (one_le_maxNorm (F := F) G g) hC (by simpa using (h g).2)
    simpa [logNorm] using this

end EntryNorm

end GSpinGGP
