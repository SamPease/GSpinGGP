/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Transport of centralizers and normalizers along group isomorphisms

* `Subgroup.map_equiv_centralizer_eq`: the image of a centralizer under an isomorphism is the
  centralizer of the image (the centralizer analogue of `Subgroup.map_equiv_normalizer_eq`);
* `Subgroup.relIndex_centralizer_normalizer_map_equiv`: the index `|N_G(S) : Z_G(S)|` is invariant
  under group isomorphisms.
-/

namespace GSpinGGP

variable {G G' : Type*} [Group G] [Group G']

/-- The image of the centralizer under an isomorphism is the centralizer of the image. -/
theorem _root_.Subgroup.map_equiv_centralizer_eq (s : Set G) (e : G ≃* G') :
    (Subgroup.centralizer s).map e.toMonoidHom = Subgroup.centralizer (e.toMonoidHom '' s) := by
  refine le_antisymm (Subgroup.map_centralizer_le_centralizer_image s e.toMonoidHom) ?_
  intro x hx
  refine ⟨e.symm x, fun y hy => ?_, by simp⟩
  have h := hx (e y) ⟨y, hy, rfl⟩
  apply e.injective
  simpa using h

/-- `|N_G(S) : Z_G(S)|` is invariant under group isomorphisms. -/
theorem _root_.Subgroup.relIndex_centralizer_normalizer_map_equiv (S : Subgroup G)
    (e : G ≃* G') :
    (Subgroup.centralizer ((S.map e.toMonoidHom : Subgroup G') : Set G')).relIndex
        (Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup G') : Set G')) =
      (Subgroup.centralizer (S : Set G)).relIndex (Subgroup.normalizer (S : Set G)) := by
  rw [← Subgroup.map_equiv_normalizer_eq, Subgroup.coe_map, ← Subgroup.map_equiv_centralizer_eq]
  exact Subgroup.relIndex_map_map_of_injective _ _ e.injective

end GSpinGGP
