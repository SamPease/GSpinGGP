/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Lie.OfAssociative

/-!
# Centralizers under Lie algebra isomorphisms

* `LieAlgebra.ker_ad_lieEquiv`: an isomorphism `e : L ≃ L'` of Lie algebras maps the centralizer
  `ker (ad X)` of `X` onto the centralizer `ker (ad (e X))` of `e X`.
-/

namespace LieAlgebra

variable {R L L' : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

/-- An isomorphism of Lie algebras maps `ker (ad X)` onto `ker (ad (e X))`
(`ad (e X)` is the conjugate of `ad X` by `e`, `conj_ad_apply`). -/
theorem ker_ad_lieEquiv (e : L ≃ₗ⁅R⁆ L') (X : L) :
    LinearMap.ker (ad R L' (e X)) =
      (LinearMap.ker (ad R L X)).map (e.toLinearEquiv : L →ₗ[R] L') := by
  rw [← conj_ad_apply, LinearEquiv.conj_apply, LinearMap.ker_comp, LinearEquiv.ker_comp,
    Submodule.comap_equiv_eq_map_symm, LinearEquiv.symm_symm]

end LieAlgebra
