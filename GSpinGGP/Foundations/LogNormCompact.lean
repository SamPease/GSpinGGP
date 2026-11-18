/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.ExpHaar

/-!
# Balls of the log-norm are compact

For a closed subgroup `G` of the units of a finite-dimensional algebra `A` over a `p`-adic field,
the sets `{g ∈ G ; σ(g) ≤ B}` of the log-norm `σ = logNorm F G` (BP §1.2, Thesis §2.2) are compact:
`σ(g) ≤ B` says that `g` and `g⁻¹` lie in a closed ball of `A`, and `Aˣ` carries the topology of
`A × Aᵐᵒᵖ` (`Units.embedProduct`). With the boundedness of `σ` on compact sets this says that `σ`
is proper; it supplies the compact sets of the polynomial growth estimates (BP (6.7.12)).
-/

noncomputable section

namespace GSpinGGP

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F] {A : Type*} [Ring A] [Algebra F A]
  [Module.Finite F A] [TopologicalSpace A] [IsModuleTopology F A]

/-- **The balls `{σ ≤ B}` of the log-norm of a closed subgroup `G ⊆ Aˣ` are compact.** -/
theorem isCompact_logNorm_le {G : Subgroup Aˣ} (hG : IsClosed (G : Set Aˣ)) (B : ℝ) :
    IsCompact {g : ↥G | logNorm F G g ≤ B} := by
  have := t2Space_of_moduleTopology F A
  have := isTopologicalRing_of_moduleTopology F A
  by_cases hB : B < 1
  · have : {g : ↥G | logNorm F G g ≤ B} = ∅ := Set.eq_empty_of_forall_notMem fun g hg =>
      absurd ((one_le_logNorm (F := F) G g).trans hg) (not_le.2 hB)
    rw [this]
    exact isCompact_empty
  set s := Real.exp (B - 1)
  have hs : 1 ≤ s := Real.one_le_exp (by linarith)
  set S : Set A := {a | ‖lmulPi F a‖ ≤ s}
  have hS : IsCompact S := isCompact_lmulPi_ball F s
  convert hG.isClosedEmbedding_subtypeVal.isCompact_preimage
    (Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hS.prod (hS.image MulOpposite.continuous_op))) using 1
  ext g
  have hpos : 0 < maxNorm F G g := zero_lt_one.trans_le (one_le_maxNorm G g)
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
    Set.mem_image, MulOpposite.op_inj, exists_eq_right, S]
  rw [logNorm, ← le_sub_iff_add_le', Real.log_le_iff_le_exp hpos, maxNorm, max_le_iff, max_le_iff,
    Subgroup.coe_inv]
  exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hs, h.1, h.2⟩⟩

end GSpinGGP
