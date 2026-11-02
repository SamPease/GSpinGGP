/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.LocalGroups
import GSpinGGP.Foundations.GSpin

/-!
# Jordan decomposition in a finite-dimensional algebra

Over a perfect field `F`, every `x` in a finite-dimensional `F`-algebra `A` is `x = s + n` with
`s, n ∈ F[x]`, left multiplication by `s` semisimple and `n` nilpotent (`exists_jordan_algebra`,
from Mathlib's Jordan–Chevalley decomposition of `L_x`). Then `ad s = L_s − R_s` is the semisimple
part of `ad x`, hence a polynomial in `ad x` (`LieAlgebra.ad_mem_adjoin_of_isSemisimple_mulLeft`),
so it preserves every subspace
that `ad x` preserves (`mapsTo_of_mem_adjoin_singleton`). For `x ∈ gspin(V)` both parts lie in
`gspin(V)` (`exists_jordan_gspin`).
-/

noncomputable section

open Module LinearMap

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

variable {F : Type*} [Field F] [PerfectField F]
variable {A : Type*} [Ring A] [Algebra F A] [FiniteDimensional F A]

/-- **Jordan decomposition in `A`**: `x = s + n`, `s, n ∈ F[x]`, `L_s` semisimple, `n` nilpotent. -/
theorem exists_jordan_algebra (x : A) :
    ∃ s ∈ Algebra.adjoin F {x}, ∃ n ∈ Algebra.adjoin F {x},
      Module.End.IsSemisimple (LinearMap.mulLeft F s) ∧ IsNilpotent n ∧ x = s + n := by
  obtain ⟨n', hn', s', hs', hnil, hss, hx⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := LinearMap.mulLeft F x)
  -- `F[L_x] = L(F[x])`
  have hmap : Algebra.adjoin F {LinearMap.mulLeft F x} =
      (Algebra.adjoin F {x}).map (Algebra.lmul F A) := by
    rw [AlgHom.map_adjoin, Set.image_singleton]; rfl
  rw [hmap] at hn' hs'
  obtain ⟨n, hn, rfl⟩ := hn'
  obtain ⟨s, hs, rfl⟩ := hs'
  refine ⟨s, hs, n, hn, hss, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hnil
    refine ⟨k, Algebra.lmul_injective (R := F) ?_⟩
    rw [map_pow, map_zero]; exact hk
  · have := congrArg (fun f : Module.End F A => f 1) hx
    simpa [add_comm] using this

/-- If `L_s` is semisimple, so is `ad s = L_s − R_s`. -/
theorem LieAlgebra.ad_isSemisimple_of_isSemisimple_mulLeft {s : A}
    (hs : Module.End.IsSemisimple (LinearMap.mulLeft F s)) :
    Module.End.IsSemisimple (LieAlgebra.ad F A s) := by
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right]
  exact hs.sub_of_commute (LinearMap.commute_mulLeft_right s s)
    (isSemisimple_mulRight_of_mulLeft hs)

/-- **`ad s` is a polynomial in `ad x`**, for `s ∈ F[x]` with `L_s` semisimple and `x − s`
nilpotent: `ad x = ad (x − s) + ad s` is the Jordan decomposition of `ad x`. -/
theorem LieAlgebra.ad_mem_adjoin_of_isSemisimple_mulLeft {x s : A} (hsx : s ∈ Algebra.adjoin F {x})
    (hs : Module.End.IsSemisimple (LinearMap.mulLeft F s)) (hn : IsNilpotent (x - s)) :
    LieAlgebra.ad F A s ∈ Algebra.adjoin F {LieAlgebra.ad F A x} := by
  obtain ⟨n₀, hn₀, s₀, hs₀, hnil₀, hss₀, hx₀⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := LieAlgebra.ad F A x)
  have hc : Commute (x - s) s :=
    ((Algebra.commute_of_mem_adjoin_singleton_of_commute hsx (Commute.refl x)).symm.symm.sub_left
      (Commute.refl s))
  have hc₀ : Commute n₀ s₀ :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs₀
      (Algebra.commute_of_mem_adjoin_self hn₀).symm
  obtain ⟨-, hseq⟩ := Module.End.isNilpotent_isSemisimple_unique hnil₀ hss₀
    (LieAlgebra.ad_nilpotent_of_nilpotent (R := F) hn)
    (LieAlgebra.ad_isSemisimple_of_isSemisimple_mulLeft hs) hc₀
    (LieAlgebra.commute_ad_of_commute hc) (by rw [← hx₀, ← map_add, sub_add_cancel])
  rwa [hseq] at hs₀

/-- A polynomial in `f` preserves every submodule that `f` preserves. -/
theorem mapsTo_of_mem_adjoin_singleton {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    {f g : Module.End R M} {W : Submodule R M}
    (hf : Set.MapsTo f W W) (hg : g ∈ Algebra.adjoin R {f}) : Set.MapsTo g W W := by
  induction hg using Algebra.adjoin_induction with
  | mem x hx => rw [Set.mem_singleton_iff.1 hx]; exact hf
  | algebraMap r =>
    intro y hy
    rw [SetLike.mem_coe, Module.algebraMap_end_apply]
    exact W.smul_mem r hy
  | add a b _ _ ha hb => intro y hy; exact W.add_mem (ha hy) (hb hy)
  | mul a b _ _ ha hb => intro y hy; exact ha (hb hy)

section GSpin

variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Invertible (2 : F)]

/-- **Jordan decomposition in `gspin(V)`**: `x ∈ gspin(V)` has a Jordan decomposition `x = s + n`
(`s, n ∈ F[x]`, `L_s` semisimple, `n` nilpotent) with both parts in `gspin(V)` (`s` is even as a
polynomial in `x`; `[s, ι V] ⊆ ι V` because `ad s` is a polynomial in `ad x`). -/
theorem exists_jordan_gspin {Q : QuadraticForm F V} {x : CliffordAlgebra Q} (hx : x ∈ gspin Q) :
    ∃ s ∈ Algebra.adjoin F {x}, ∃ n ∈ Algebra.adjoin F {x},
      Module.End.IsSemisimple (LinearMap.mulLeft F s) ∧ IsNilpotent n ∧ x = s + n ∧
      s ∈ gspin Q ∧ n ∈ gspin Q := by
  obtain ⟨s, hs, n, hn, hss, hnil, rfl⟩ := exists_jordan_algebra (F := F) x
  have hadj : Algebra.adjoin F {s + n} ≤ CliffordAlgebra.even Q :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hx.1)
  have hW : Set.MapsTo (LieAlgebra.ad F _ (s + n)) (LinearMap.range (CliffordAlgebra.ι Q))
      (LinearMap.range (CliffordAlgebra.ι Q)) := by
    rintro _ ⟨v, rfl⟩
    exact hx.2 v
  have hsg : s ∈ gspin Q :=
    ⟨hadj hs, fun v => mapsTo_of_mem_adjoin_singleton hW
      (LieAlgebra.ad_mem_adjoin_of_isSemisimple_mulLeft hs hss (by rwa [add_sub_cancel_left]))
      ⟨v, rfl⟩⟩
  refine ⟨s, hs, n, hn, hss, hnil, rfl, hsg, ?_⟩
  have := (gspin Q).sub_mem hx hsg
  rwa [add_sub_cancel_left] at this

end GSpin

end GSpinGGP
