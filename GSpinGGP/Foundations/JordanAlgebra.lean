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

For a unit `x`, `s` is a unit, and `Ad s = L_s R_{s⁻¹}` is the semisimple part of
`Ad x = L_x R_{x⁻¹}`, hence a polynomial in `Ad x` (`conj_mem_adjoin_of_isSemisimple_mulLeft`).
For `x ∈ GSpin(V)` this gives the multiplicative Jordan decomposition `x = s u` in `GSpin(V)`
(`exists_jordan_GSpin`).
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

/-! ### Units: the multiplicative Jordan decomposition -/

section Units

omit [PerfectField F] [FiniteDimensional F A] in
/-- Elements of `F[x]` commute. -/
theorem commute_of_mem_adjoin_singleton {x p q : A} (hp : p ∈ Algebra.adjoin F {x})
    (hq : q ∈ Algebra.adjoin F {x}) : Commute p q :=
  Algebra.commute_of_mem_adjoin_singleton_of_commute hq
    (Algebra.commute_of_mem_adjoin_self hp).symm

omit [PerfectField F] [FiniteDimensional F A] in
/-- If `x` is a unit, `s ∈ F[x]` and `x − s` is nilpotent, then `s` is a unit. -/
theorem isUnit_of_mem_adjoin_of_isNilpotent_sub {x s : A} (hx : IsUnit x)
    (hs : s ∈ Algebra.adjoin F {x}) (hn : IsNilpotent (x - s)) : IsUnit s := by
  have h := (neg_sub x s ▸ hn.neg).isUnit_add_left_of_commute hx
    ((Algebra.commute_of_mem_adjoin_self hs).symm.sub_left (Commute.refl x))
  rwa [add_sub_cancel] at h

omit [PerfectField F] in
/-- For units `x`, `s` with `s ∈ F[x]` and `x − s` nilpotent, `s⁻¹ ∈ F[x⁻¹]` and `x⁻¹ − s⁻¹` is
nilpotent. -/
theorem inv_mem_adjoin_and_isNilpotent_sub {x s : Aˣ} (hs : (s : A) ∈ Algebra.adjoin F {(x : A)})
    (hn : IsNilpotent ((x : A) - s)) :
    ((s⁻¹ : Aˣ) : A) ∈ Algebra.adjoin F {((x⁻¹ : Aˣ) : A)} ∧
      IsNilpotent (((x⁻¹ : Aˣ) : A) - ((s⁻¹ : Aˣ) : A)) := by
  have hxi : ((x⁻¹ : Aˣ) : A) ∈ Algebra.adjoin F {(x : A)} :=
    TauCeti.Units.coe_inv_mem_adjoin x (IsIntegral.of_finite F _)
  have hsi : ((s⁻¹ : Aˣ) : A) ∈ Algebra.adjoin F {(x : A)} :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hs)
      (TauCeti.Units.coe_inv_mem_adjoin s (IsIntegral.of_finite F _))
  have hle : Algebra.adjoin F {(x : A)} ≤ Algebra.adjoin F {((x⁻¹ : Aˣ) : A)} := by
    refine Algebra.adjoin_le (Set.singleton_subset_iff.2 ?_)
    simpa using TauCeti.Units.coe_inv_mem_adjoin x⁻¹ (IsIntegral.of_finite F _)
  refine ⟨hle hsi, ?_⟩
  have hsx : (s : A) - x ∈ Algebra.adjoin F {(x : A)} :=
    Subalgebra.sub_mem _ hs (Algebra.self_mem_adjoin_singleton F _)
  have h : ((x⁻¹ : Aˣ) : A) - ((s⁻¹ : Aˣ) : A) =
      ((x⁻¹ : Aˣ) : A) * (((s : A) - x) * ((s⁻¹ : Aˣ) : A)) := by
    rw [sub_mul, Units.mul_inv, mul_sub, mul_one, ← mul_assoc, Units.inv_mul, one_mul]
  rw [h]
  have hn' : IsNilpotent ((s : A) - x) := by rw [← neg_sub]; exact hn.neg
  exact (commute_of_mem_adjoin_singleton hxi
    (Subalgebra.mul_mem _ hsx hsi)).isNilpotent_mul_left
      ((commute_of_mem_adjoin_singleton hsx hsi).isNilpotent_mul_right hn')

/-- **`Ad s` is a polynomial in `Ad x`** (`Ad y = L_y R_{y⁻¹}`), for units `x`, `s` with `s ∈ F[x]`,
`L_s` semisimple and `x − s` nilpotent: `Ad x = Ad s + (Ad x − Ad s)` is the Jordan decomposition of
`Ad x`. -/
theorem conj_mem_adjoin_of_isSemisimple_mulLeft {x s : Aˣ}
    (hs : (s : A) ∈ Algebra.adjoin F {(x : A)})
    (hss : Module.End.IsSemisimple (LinearMap.mulLeft F (s : A)))
    (hn : IsNilpotent ((x : A) - s)) :
    LinearMap.mulLeft F (s : A) * LinearMap.mulRight F ((s⁻¹ : Aˣ) : A) ∈
      Algebra.adjoin F {LinearMap.mulLeft F (x : A) * LinearMap.mulRight F ((x⁻¹ : Aˣ) : A)} := by
  set B := Algebra.adjoin F {(x : A)}
  have hxB : (x : A) ∈ B := Algebra.self_mem_adjoin_singleton F _
  have hxiB : ((x⁻¹ : Aˣ) : A) ∈ B := TauCeti.Units.coe_inv_mem_adjoin x (IsIntegral.of_finite F _)
  have hsiB : ((s⁻¹ : Aˣ) : A) ∈ B :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hs)
      (TauCeti.Units.coe_inv_mem_adjoin s (IsIntegral.of_finite F _))
  -- operators `L_p R_q` with `p, q ∈ F[x]` commute
  have hcomm : ∀ p ∈ B, ∀ q ∈ B, ∀ p' ∈ B, ∀ q' ∈ B,
      Commute (LinearMap.mulLeft F p * LinearMap.mulRight F q)
        (LinearMap.mulLeft F p' * LinearMap.mulRight F q') := by
    intro p hp q hq p' hp' q' hq'
    refine LinearMap.ext fun a => ?_
    simp only [Module.End.mul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    simp only [← mul_assoc]
    rw [(commute_of_mem_adjoin_singleton hp hp').eq, mul_assoc (p' * p * a) q' q,
      (commute_of_mem_adjoin_singleton hq' hq).eq, ← mul_assoc]
  set T := LinearMap.mulLeft F (x : A) * LinearMap.mulRight F ((x⁻¹ : Aˣ) : A)
  set C := LinearMap.mulLeft F (s : A) * LinearMap.mulRight F ((s⁻¹ : Aˣ) : A)
  set t₁ := LinearMap.mulLeft F ((x : A) - s) * LinearMap.mulRight F ((x⁻¹ : Aˣ) : A)
  set t₂ := LinearMap.mulLeft F (s : A) *
    LinearMap.mulRight F (((x⁻¹ : Aˣ) : A) - ((s⁻¹ : Aˣ) : A))
  have hxs : (x : A) - s ∈ B := Subalgebra.sub_mem _ hxB hs
  have hxsi : ((x⁻¹ : Aˣ) : A) - ((s⁻¹ : Aˣ) : A) ∈ B := Subalgebra.sub_mem _ hxiB hsiB
  have hTC : T - C = t₁ + t₂ := by
    refine LinearMap.ext fun a => ?_
    simp only [T, C, t₁, t₂, LinearMap.sub_apply, LinearMap.add_apply, Module.End.mul_apply,
      LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
    noncomm_ring
  have hn₁ : IsNilpotent t₁ :=
    (LinearMap.commute_mulLeft_right _ _).isNilpotent_mul_right
      (hn.map (Algebra.lmul F A))
  have hn₂ : IsNilpotent t₂ := by
    obtain ⟨k, hk⟩ := (inv_mem_adjoin_and_isNilpotent_sub hs hn).2
    exact (LinearMap.commute_mulLeft_right _ _).isNilpotent_mul_left
      ⟨k, by rw [LinearMap.pow_mulRight, hk, LinearMap.mulRight_zero_eq_zero]⟩
  have hnil : IsNilpotent (T - C) := by
    rw [hTC]
    exact (hcomm _ hxs _ hxiB _ hs _ hxsi).isNilpotent_add hn₁ hn₂
  have hc : Commute (T - C) C := by
    rw [hTC]
    exact (hcomm _ hxs _ hxiB _ hs _ hsiB).add_left (hcomm _ hs _ hxsi _ hs _ hsiB)
  obtain ⟨n₀, hn₀, s₀, hs₀, hnil₀, hss₀, hx₀⟩ := Module.End.exists_isNilpotent_isSemisimple (f := T)
  have hc₀ : Commute n₀ s₀ :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hs₀
      (Algebra.commute_of_mem_adjoin_self hn₀).symm
  obtain ⟨-, hseq⟩ := Module.End.isNilpotent_isSemisimple_unique hnil₀ hss₀ hnil
    (isSemisimple_conj_of_mulLeft hss) hc₀ hc (by rw [← hx₀, sub_add_cancel])
  rwa [hseq] at hs₀

end Units

/-! ### Kernels of powers -/

section Kernel

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- If `n` is nilpotent and commutes with `s`, then `s + n` is nilpotent on `ker s`:
`ker s ≤ ker (s + n)^(dim M)`. -/
theorem ker_le_ker_pow_add [FiniteDimensional K M] {s n : Module.End K M} (hc : Commute s n)
    (hn : IsNilpotent n) : LinearMap.ker s ≤ LinearMap.ker ((s + n) ^ finrank K M) := by
  intro x hx
  rw [LinearMap.mem_ker] at hx ⊢
  have key : ∀ k : ℕ, ((s + n) ^ k) x = (n ^ k) x := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, LinearMap.add_apply, ← Module.End.mul_apply,
        (hc.pow_right k).eq, Module.End.mul_apply, hx, map_zero, zero_add, ← Module.End.mul_apply,
        ← pow_succ']
  have hD : n ^ finrank K M = 0 := by
    have h := LinearMap.aeval_self_charpoly n
    rwa [hn.charpoly_eq_X_pow_finrank, Polynomial.aeval_X_pow] at h
  rw [key, hD, LinearMap.zero_apply]

/-- For `f` semisimple, `ker f^k = ker f` (`k > 0`). -/
theorem ker_pow_eq_ker_of_isSemisimple {f : Module.End K M} (hf : f.IsSemisimple) {k : ℕ}
    (hk : 0 < k) : LinearMap.ker (f ^ k) = LinearMap.ker f := by
  have h := hf.isFinitelySemisimple.genEigenspace_eq_eigenspace 0 (k := k) (by exact_mod_cast hk)
  rw [Module.End.genEigenspace_nat, Module.End.eigenspace_def, zero_smul, sub_zero] at h
  simpa using h

end Kernel

section GSpin

variable {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Invertible (2 : F)]

open CliffordAlgebra

/-- **The semisimple part of `x ∈ gspin(V)` lies in `gspin(V)`**: if `s ∈ F[x]` has `L_s` semisimple
and `x − s` nilpotent, then `s ∈ gspin(V)` (`s` is even as a polynomial in `x`; `[s, ι V] ⊆ ι V`
because `ad s` is a polynomial in `ad x`). -/
theorem mem_gspin_of_mem_adjoin {Q : QuadraticForm F V} {x s : CliffordAlgebra Q}
    (hx : x ∈ gspin Q) (hs : s ∈ Algebra.adjoin F {x})
    (hss : Module.End.IsSemisimple (LinearMap.mulLeft F s)) (hn : IsNilpotent (x - s)) :
    s ∈ gspin Q := by
  have hadj : Algebra.adjoin F {x} ≤ CliffordAlgebra.even Q :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hx.1)
  have hW : Set.MapsTo (LieAlgebra.ad F _ x) (LinearMap.range (CliffordAlgebra.ι Q))
      (LinearMap.range (CliffordAlgebra.ι Q)) := by
    rintro _ ⟨v, rfl⟩
    exact hx.2 v
  exact ⟨hadj hs, fun v => mapsTo_of_mem_adjoin_singleton hW
    (LieAlgebra.ad_mem_adjoin_of_isSemisimple_mulLeft hs hss hn) ⟨v, rfl⟩⟩

/-- **Jordan decomposition in `gspin(V)`**: `x ∈ gspin(V)` has a Jordan decomposition `x = s + n`
(`s, n ∈ F[x]`, `L_s` semisimple, `n` nilpotent) with both parts in `gspin(V)`
(`mem_gspin_of_mem_adjoin`). -/
theorem exists_jordan_gspin {Q : QuadraticForm F V} {x : CliffordAlgebra Q} (hx : x ∈ gspin Q) :
    ∃ s ∈ Algebra.adjoin F {x}, ∃ n ∈ Algebra.adjoin F {x},
      Module.End.IsSemisimple (LinearMap.mulLeft F s) ∧ IsNilpotent n ∧ x = s + n ∧
      s ∈ gspin Q ∧ n ∈ gspin Q := by
  obtain ⟨s, hs, n, hn, hss, hnil, rfl⟩ := exists_jordan_algebra (F := F) x
  have hsg : s ∈ gspin Q :=
    mem_gspin_of_mem_adjoin hx hs hss (by rwa [add_sub_cancel_left])
  refine ⟨s, hs, n, hn, hss, hnil, rfl, hsg, ?_⟩
  have := (gspin Q).sub_mem hx hsg
  rwa [add_sub_cancel_left] at this

/-- **The semisimple part of `x ∈ GSpin(V)` lies in `GSpin(V)`**: if the unit `s ∈ F[x]` has `L_s`
semisimple and `x − s` nilpotent, then `s ∈ GSpin(V)` (`s` is even as a polynomial in `x`;
`s V s⁻¹ ⊆ V` because `Ad s` is a polynomial in `Ad x`, and `s⁻¹ V s ⊆ V` likewise from `x⁻¹`). -/
theorem mem_GSpin_of_mem_adjoin {Q : QuadraticForm F V} {x s : (CliffordAlgebra Q)ˣ}
    (hx : x ∈ GSpin Q) (hs : (s : CliffordAlgebra Q) ∈ Algebra.adjoin F {(x : CliffordAlgebra Q)})
    (hss : Module.End.IsSemisimple (LinearMap.mulLeft F (s : CliffordAlgebra Q)))
    (hn : IsNilpotent ((x : CliffordAlgebra Q) - s)) : s ∈ GSpin Q := by
  have hW : ∀ {y t : (CliffordAlgebra Q)ˣ},
      (∀ v, (y : CliffordAlgebra Q) * ι Q v * ((y⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
        LinearMap.range (ι Q)) →
      (t : CliffordAlgebra Q) ∈ Algebra.adjoin F {(y : CliffordAlgebra Q)} →
      Module.End.IsSemisimple (LinearMap.mulLeft F (t : CliffordAlgebra Q)) →
      IsNilpotent ((y : CliffordAlgebra Q) - t) →
      ∀ v, (t : CliffordAlgebra Q) * ι Q v * ((t⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
        LinearMap.range (ι Q) := by
    intro y t hy ht hts htn v
    have hm : Set.MapsTo (LinearMap.mulLeft F (y : CliffordAlgebra Q) *
        LinearMap.mulRight F ((y⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
        (LinearMap.range (ι Q)) (LinearMap.range (ι Q)) := by
      rintro _ ⟨w, rfl⟩
      change (y : CliffordAlgebra Q) * (ι Q w * _) ∈ _
      rw [← mul_assoc]
      exact hy w
    have h := mapsTo_of_mem_adjoin_singleton hm
      (conj_mem_adjoin_of_isSemisimple_mulLeft ht hts htn) ⟨v, rfl⟩
    rwa [Module.End.mul_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply,
      ← mul_assoc] at h
  obtain ⟨hsi, hni⟩ := inv_mem_adjoin_and_isNilpotent_sub hs hn
  have hmem : Algebra.lmul F (CliffordAlgebra Q) ((s⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
      Algebra.adjoin F {Algebra.lmul F (CliffordAlgebra Q) (s : CliffordAlgebra Q)} := by
    rw [← AlgHom.map_adjoin_singleton]
    exact Subalgebra.mem_map.mpr
      ⟨_, TauCeti.Units.coe_inv_mem_adjoin s (IsIntegral.of_finite F _), rfl⟩
  have hssi := Module.End.IsSemisimple.of_mem_adjoin_singleton hss hmem
  refine ⟨Algebra.adjoin_le (Set.singleton_subset_iff.2 hx.1) hs, hW hx.2.1 hs hss hn, fun v => ?_⟩
  simpa using hW ((GSpin Q).inv_mem hx).2.1 hsi hssi hni v

/-- **Multiplicative Jordan decomposition in `GSpin(V)`**: `x = s u` with `s, u ∈ GSpin(V)`
commuting, `s ∈ F[x]` with `L_s` semisimple, and `u − 1` nilpotent. -/
theorem exists_jordan_GSpin {Q : QuadraticForm F V} {x : (CliffordAlgebra Q)ˣ} (hx : x ∈ GSpin Q) :
    ∃ s ∈ GSpin Q, ∃ u ∈ GSpin Q, x = s * u ∧ Commute s u ∧
      (s : CliffordAlgebra Q) ∈ Algebra.adjoin F {(x : CliffordAlgebra Q)} ∧
      Module.End.IsSemisimple (LinearMap.mulLeft F (s : CliffordAlgebra Q)) ∧
      IsNilpotent ((u : CliffordAlgebra Q) - 1) := by
  obtain ⟨s, hs, n, -, hss, hnil, hxsn⟩ := exists_jordan_algebra (F := F) (x : CliffordAlgebra Q)
  have hn : IsNilpotent ((x : CliffordAlgebra Q) - s) := by rwa [hxsn, add_sub_cancel_left]
  obtain ⟨s, rfl⟩ := isUnit_of_mem_adjoin_of_isNilpotent_sub x.isUnit hs hn
  have hsG := mem_GSpin_of_mem_adjoin hx hs hss hn
  have hc : Commute s x := Units.ext (Algebra.commute_of_mem_adjoin_self hs).symm.eq
  refine ⟨s, hsG, s⁻¹ * x, (GSpin Q).mul_mem ((GSpin Q).inv_mem hsG) hx, by group,
    (Commute.refl s).inv_right.mul_right hc, hs, hss, ?_⟩
  have h : ((s⁻¹ * x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) - 1 =
      ((s⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * ((x : CliffordAlgebra Q) - s) := by
    rw [mul_sub, Units.inv_mul, Units.val_mul]
  rw [h]
  exact (((Algebra.commute_of_mem_adjoin_self hs).symm.sub_right
    (Commute.refl _)).units_inv_left).isNilpotent_mul_left hn

omit [PerfectField F] [FiniteDimensional F V] in
/-- `ι((adV Y)^k v) = (ad Y)^k (ι v)` for `Y ∈ gspin(V)`. -/
theorem ι_adV_pow {Q : QuadraticForm F V} {Y : CliffordAlgebra Q} (hY : Y ∈ gspin Q) (k : ℕ)
    (v : V) : ι Q ((adV Q Y ^ k) v) = (LieAlgebra.ad F _ Y ^ k) (ι Q v) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ι_adV hY, ih, pow_succ', Module.End.mul_apply,
      LieAlgebra.ad_apply, Ring.lie_def]

/-- `adV Y` is semisimple for `Y ∈ gspin(V)` with `L_Y` semisimple on `C(V)` (`adV Y` is the
restriction of `ad Y` to `ι V`). -/
theorem isSemisimple_adV {Q : QuadraticForm F V}
    {Y : CliffordAlgebra Q} (hY : Y ∈ gspin Q)
    (hs : Module.End.IsSemisimple (LinearMap.mulLeft F Y)) : (adV Q Y).IsSemisimple := by
  have hR : Set.MapsTo (LieAlgebra.ad F _ Y) (LinearMap.range (ι Q)) (LinearMap.range (ι Q)) := by
    rintro _ ⟨v, rfl⟩
    exact hY.2 v
  have hss := (LieAlgebra.ad_isSemisimple_of_isSemisimple_mulLeft hs).restrict
    ((Module.End.mem_invtSubmodule _).2 hR)
  let e : V ≃ₗ[F] LinearMap.range (ι Q) := LinearEquiv.ofInjective (ι Q) (ι_injective Q)
  refine (LinearEquiv.isSemisimple_iff _ _ e (LinearMap.ext fun v => Subtype.ext ?_)).2 hss
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, e,
    LinearEquiv.ofInjective_apply]
  exact ι_adV hY v

end GSpin

end GSpinGGP
