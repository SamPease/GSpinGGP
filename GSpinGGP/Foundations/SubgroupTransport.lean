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
* `Subgroup.relIndex_eq_of_map_eq_of_comap_inf_eq`: `|B : A| = |B' : A'|` when `f(B) = B'` and
  `f⁻¹(A') ∩ B = A`.
* `Subgroup.relIndex_centralizer_normalizer_map_of_surjective`: `|N_G(T) : Z_G(T)|` is preserved by
  a surjection `f` whose kernel lies in `T`, provided `f(g)` centralizes `f(T)` only when `g`
  centralizes `T` (the kernel being central does not suffice: commutators may be nontrivial
  elements of the kernel).
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

/-- `|B : A| = |B' : A'|` for a homomorphism `f` with `f(B) = B'` and `f⁻¹(A') ∩ B = A`. -/
theorem _root_.Subgroup.relIndex_eq_of_map_eq_of_comap_inf_eq {f : G →* G'}
    {A B : Subgroup G} {A' B' : Subgroup G'} (hB : B.map f = B') (hA : A'.comap f ⊓ B = A) :
    A.relIndex B = A'.relIndex B' := by
  rw [← hB, ← Subgroup.relIndex_comap, ← hA, Subgroup.inf_relIndex_right]

/-- **`|N_G(T) : Z_G(T)|` along a surjection with kernel in `T`.**  If `f : G →* G'` is onto,
`ker f ≤ T`, and `f(g)` centralizes `f(T)` only when `g` centralizes `T`, then
`|N_{G'}(f T) : Z_{G'}(f T)| = |N_G(T) : Z_G(T)|`. -/
theorem _root_.Subgroup.relIndex_centralizer_normalizer_map_of_surjective {f : G →* G'}
    (hf : Function.Surjective f) {T : Subgroup G} (hker : f.ker ≤ T)
    (hZ : ∀ g, f g ∈ Subgroup.centralizer ((T.map f : Subgroup G') : Set G') →
      g ∈ Subgroup.centralizer (T : Set G)) :
    (Subgroup.centralizer ((T.map f : Subgroup G') : Set G')).relIndex
        (Subgroup.normalizer ((T.map f : Subgroup G') : Set G')) =
      (Subgroup.centralizer (T : Set G)).relIndex (Subgroup.normalizer (T : Set G)) := by
  have hT : (T.map f).comap f = T := by
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr hker]
  refine (Subgroup.relIndex_eq_of_map_eq_of_comap_inf_eq (f := f) ?_ ?_).symm
  · rw [← hT, ← Subgroup.comap_normalizer_eq_of_surjective _ hf,
      Subgroup.map_comap_eq_self_of_surjective hf, hT]
  · refine le_antisymm (fun g hg => hZ g hg.1) fun g hg =>
      ⟨?_, Subgroup.centralizer_le_normalizer _ hg⟩
    change f g ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hg t ht]

end GSpinGGP
