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
part of `ad x`, hence a polynomial in `ad x` (`adAlg_mem_adjoin`), so it preserves every subspace
that `ad x` preserves (`mapsTo_of_mem_adjoin_singleton`). For `x ∈ gspin(V)` both parts lie in
`gspin(V)` (`exists_jordan_gspin`).
-/

noncomputable section

open Module LinearMap

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

variable {F : Type*} [Field F] [PerfectField F]
variable {A : Type*} [Ring A] [Algebra F A] [FiniteDimensional F A]

/-- `ad x = L_x − R_x` on `A`. -/
abbrev adAlg (F : Type*) [Field F] [Algebra F A] (x : A) : Module.End F A :=
  LinearMap.mulLeft F x - LinearMap.mulRight F x

omit [PerfectField F] [FiniteDimensional F A] in
theorem adAlg_apply (x y : A) : adAlg F x y = x * y - y * x := rfl

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

omit [FiniteDimensional F A] in
/-- If `L_s` is semisimple, so is `R_s`, and hence `ad s = L_s − R_s`. -/
theorem isSemisimple_adAlg [FiniteDimensional F A] {s : A}
    (hs : Module.End.IsSemisimple (LinearMap.mulLeft F s)) :
    Module.End.IsSemisimple (adAlg F s) := by
  set p := minpoly F (LinearMap.mulLeft F s)
  have hp0 : Polynomial.aeval s p = 0 := by
    have h := minpoly.aeval F (LinearMap.mulLeft F s)
    rw [show LinearMap.mulLeft F s = Algebra.lmul F A s from rfl,
      Polynomial.aeval_algHom_apply] at h
    exact Algebra.lmul_injective (R := F) (h.trans (map_zero _).symm)
  have hR : Module.End.IsSemisimple (LinearMap.mulRight F s) :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hs.minpoly_squarefree
      (by rw [aeval_mulRight, hp0, LinearMap.mulRight_zero_eq_zero])
  exact Module.End.IsSemisimple.sub_of_commute (LinearMap.commute_mulLeft_right s s) hs hR

/-- **`ad s` is a polynomial in `ad x`**, for `s ∈ F[x]` with `L_s` semisimple and `x − s`
nilpotent:
`ad x = ad s + ad (x − s)` is the Jordan decomposition of `ad x`. -/
theorem adAlg_mem_adjoin {x s : A} (hsx : s ∈ Algebra.adjoin F {x})
    (hs : Module.End.IsSemisimple (LinearMap.mulLeft F s)) (hn : IsNilpotent (x - s)) :
    adAlg F s ∈ Algebra.adjoin F {adAlg F x} := by
  obtain ⟨n₀, hn₀, s₀, hs₀, hnil₀, hss₀, hx₀⟩ :=
    Module.End.exists_isNilpotent_isSemisimple (f := adAlg F x)
  set n := x - s
  have hsx' : Commute s x :=
    (Algebra.commute_of_mem_adjoin_singleton_of_commute hsx (Commute.refl x)).symm
  have hcomm : Commute n s := (hsx'.symm.sub_left (Commute.refl s))
  have hLL : Commute (LinearMap.mulLeft F n) (LinearMap.mulLeft F s) :=
    LinearMap.ext fun z => by simp [Module.End.mul_apply, ← mul_assoc, hcomm.eq]
  have hRR : Commute (LinearMap.mulRight F n) (LinearMap.mulRight F s) :=
    LinearMap.ext fun z => by simp [Module.End.mul_apply, mul_assoc, hcomm.eq]
  have hnS : Commute (adAlg F n) (adAlg F s) := by
    simp only [adAlg]
    exact (hLL.sub_right (LinearMap.commute_mulLeft_right n s)).sub_left
      ((LinearMap.commute_mulLeft_right s n).symm.sub_right hRR)
  have hnil : IsNilpotent (adAlg F n) := by
    obtain ⟨k, hk⟩ := hn
    have hL : IsNilpotent (LinearMap.mulLeft F n) :=
      ⟨k, by rw [LinearMap.pow_mulLeft, hk, LinearMap.mulLeft_zero_eq_zero]⟩
    have hR : IsNilpotent (LinearMap.mulRight F n) :=
      ⟨k, by rw [LinearMap.pow_mulRight, hk, LinearMap.mulRight_zero_eq_zero]⟩
    exact (LinearMap.commute_mulLeft_right n n).isNilpotent_sub hL hR
  have hsplit : adAlg F n + adAlg F s = n₀ + s₀ := by
    rw [← hx₀]; simp only [adAlg, n]; ext
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply]
    noncomm_ring
  have hc₀ : Commute n₀ s₀ :=
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hs₀ fun b hb => by
      rw [Set.mem_singleton_iff.1 hb]
      exact (Algebra.commute_of_mem_adjoin_singleton_of_commute hn₀ (Commute.refl _)).symm
  obtain ⟨-, hseq⟩ := Module.End.isNilpotent_isSemisimple_unique hnil (isSemisimple_adAlg hs)
    hnil₀ hss₀ hnS hc₀ hsplit
  rw [hseq]; exact hs₀

omit [PerfectField F] [FiniteDimensional F A] in
/-- A polynomial in `f` preserves every subspace that `f` preserves. -/
theorem mapsTo_of_mem_adjoin_singleton {f g : Module.End F A} {W : Submodule F A}
    (hf : Set.MapsTo f W W) (hg : g ∈ Algebra.adjoin F {f}) : Set.MapsTo g W W := by
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

/-- **Jordan decomposition in `gspin(V)`**: for `x ∈ gspin(V)`, the parts `x = s + n` of
`exists_jordan_algebra` lie in `gspin(V)` (`s` is even as a polynomial in `x`; `[s, ι V] ⊆ ι V`
because `ad s` is a polynomial in `ad x`, `adAlg_mem_adjoin`). -/
theorem exists_jordan_gspin {Q : QuadraticForm F V} {x : CliffordAlgebra Q} (hx : x ∈ gspin Q) :
    ∃ s ∈ Algebra.adjoin F {x}, ∃ n ∈ Algebra.adjoin F {x},
      Module.End.IsSemisimple (LinearMap.mulLeft F s) ∧ IsNilpotent n ∧ x = s + n ∧
      s ∈ gspin Q ∧ n ∈ gspin Q := by
  obtain ⟨s, hs, n, hn, hss, hnil, rfl⟩ := exists_jordan_algebra (F := F) x
  have hadj : Algebra.adjoin F {s + n} ≤ CliffordAlgebra.even Q :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hx.1)
  have hW : Set.MapsTo (adAlg F (s + n)) (LinearMap.range (CliffordAlgebra.ι Q))
      (LinearMap.range (CliffordAlgebra.ι Q)) := by
    rintro _ ⟨v, rfl⟩
    have := hx.2 v
    rwa [Ring.lie_def] at this
  have hsg : s ∈ gspin Q := by
    refine ⟨hadj hs, fun v => ?_⟩
    rw [Ring.lie_def]
    exact mapsTo_of_mem_adjoin_singleton hW
      (adAlg_mem_adjoin hs hss (by rwa [add_sub_cancel_left])) ⟨v, rfl⟩
  refine ⟨s, hs, n, hn, hss, hnil, rfl, hsg, ?_⟩
  have := (gspin Q).sub_mem hx hsg
  rwa [add_sub_cancel_left] at this

end GSpin

end GSpinGGP
