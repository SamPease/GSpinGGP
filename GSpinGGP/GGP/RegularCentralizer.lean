/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.CentralizerSign
import GSpinGGP.GGP.LeviSubgroup

/-!
# Centralizers of regular semisimple elements of `GSpin(V)`

For `x ∈ GSpin(V)` regular semisimple (`x` semisimple on `C(V)` and `gspin(V)_x` abelian), the
centralizer `GSpin(V)_x` is a maximal torus; in particular it is commutative
(`commute_of_isRegular`, not yet proved).  From this: if moreover `x` lies in the Levi subgroup
`M_F = flagLevi b wt` of a flag stabilizer, then `GSpin(V)_x ⊆ M_F`
(`mem_flagLevi_of_commute_of_isRegular`; Waldspurger, Compos. Math. 146 (2010), §2.3,
`G_x = M_x ⊂ M`; Beuzart-Plessis, Astérisque 418, §1.10; Waldspurger's `G_x` is the neutral
component `Z_G(x)⁰`, which is the full centralizer here: centralizers of semisimple elements of
`GSpin` are connected, by Steinberg's theorem, as `Spin` is simply connected).  The argument for
the inclusion: a lift `T ∈ GSpin(V)` of the cocharacter `λ(2) : bᵢ ↦ 2^{wtᵢ} bᵢ`
(`IsFlagSplitting.exists_cochar_lift`) satisfies `T x T⁻¹ = ±x` (`P(T)` commutes with `P(x)`,
`CentralizerSign.exists_conj_eq_smul`), so
`T²` lies in `GSpin(V)_x`; every `g ∈ GSpin(V)_x` commutes with `T²`, so `P(g)` commutes with
`λ(4)`, whose eigenvalues `4^w` separate the weights; hence `P(g)` preserves each weight space.
-/

noncomputable section

open CliffordAlgebra Module

namespace GSpinGGP

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V}

/-- **The centralizer of a regular semisimple element of `GSpin(V)` is commutative**: for `x`
semisimple on `C(V)` with `gspin(V)_x` abelian, any two elements of `GSpin(V)` commuting with `x`
commute.  (The centralizer is a maximal torus: connected by Steinberg's theorem, as the derived
group `Spin(V)` is simply connected, with abelian Lie algebra.)

Not yet proved.  Sketch, without connectedness, by the explicit methods of `Steinberg.commute_iff`
and `Steinberg.commute_of_fixes_eigenspace_one`: (1) `P(x)` is semisimple
(`Steinberg.isSemisimple_specP_of_isSS`); commuting is detected after base change to `K̄`
(`bcGSpin_injective`), and the hypotheses base change (semisimplicity:
`isSemisimple_baseChange_algebraicClosure`; abelianness of `so(V)_{P(x)}`, which follows from that
of `gspin(V)_x` by `commute_of_isLieAbelian_lieCentralizer`, as the centralizer of `P(x)_{K̄}` is
`so(V)_{P(x)} ⊗ K̄`; the same passage to `K̄` is done for `GSpin(W)` and the moved part in
`commute_torusOf_of_commute_of_movedPartAbelian`, `isSemisimple_specP_baseChange` and
`lieAbelian_specP_baseChange_of_movedPartAbelian`, which would need generalizing); (2) over `K̄`,
`so(V)_{P(x)}` abelian gives `dim ker (P(x) − 1) ≤ 2`; (3) if `dim ker (P(x) − 1) ≤ 1`, every `t`
commuting with `x` acts trivially on `ker (P(x) − 1)`
(its determinant there is `1`, `det_restrict_one_eq_one_of_commute`), and
`Steinberg.commute_of_fixes_eigenspace_one` gives `Commute g t`; (4) if `ker (P(x) − 1)` is a
(hyperbolic) plane `⟨e₀, f₀⟩`, `P(g)` and `P(h)` act on it by `diag(c, c⁻¹)` (an isometry of
the plane of determinant `1`, `det_restrict_one_eq_one_of_commute`), and replacing `x` by
`x s` with `s` a pair element of `⟨e₀, f₀⟩` acting by `diag(a, a⁻¹)`, `a` avoiding `±1` and the
eigenvalues of `P(x)`, gives a regular `x s` with `ker (P(x s) − 1) = 0` whose centralizer contains
`g` and `h`; conclude by (3). -/
theorem commute_of_isRegular [CharZero K] [FiniteDimensional K V] (hQ : IsNondeg Q) (x : GSpin Q)
    (hss : Module.End.IsSemisimple
      (LinearMap.mulLeft K ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))
    (hab : IsLieAbelian
      (lieCentralizer (gspin Q) ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))
    {g h : GSpin Q} (hg : Commute g x) (hh : Commute h x) : Commute g h := by
  sorry

section FlagLevi

variable {F : IsotropicFlag Q} {ι : Type*} [Fintype ι] {b : Basis ι K V} {wt : ι → ℤ}

/-- **`GSpin(V)_x ⊆ M_F` for `x ∈ M_F` with commutative centralizer** (Waldspurger 2010, §2.3,
for `G_x = Z_G(x)⁰`, here the full centralizer since `Z_G(x)` is connected (Steinberg; `Spin` is
simply connected)):
if every two elements commuting with `x ∈ flagLevi b wt` commute, then every `g` commuting with
`x` lies in `flagLevi b wt`.  A lift `T` of `λ(2)` has `T x T⁻¹ = ±x`, so `T²` commutes with `x`,
hence with `g`; then `P(g)` commutes with `λ(4)` and preserves its eigenspaces, the weight
spaces. -/
theorem mem_flagLevi_of_commute [CharZero K] [FiniteDimensional K V] (hQ : IsNondeg Q)
    (hs : IsFlagSplitting F b wt) {x : GSpin Q} (hx : x ∈ flagLevi (Q := Q) b wt)
    (hcomm : ∀ g h : GSpin Q, Commute g x → Commute h x → Commute g h)
    {g : GSpin Q} (hg : Commute g x) : g ∈ flagLevi (Q := Q) b wt := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  obtain ⟨T, hT⟩ := hs.exists_cochar_lift hQ h2
  have hTc : (specP Q T : V →ₗ[K] V) = cochar b wt 2 :=
    b.ext fun i => by rw [cochar_basis]; exact hT i
  -- `P(T)` commutes with `P(x)`
  have hTx : Commute (specP Q T) (specP Q x) := by
    change specP Q T * specP Q x = specP Q x * specP Q T
    refine LinearEquiv.toLinearMap_injective ?_
    change (specP Q T : V →ₗ[K] V) ∘ₗ (specP Q x : V →ₗ[K] V) =
      (specP Q x : V →ₗ[K] V) ∘ₗ (specP Q T : V →ₗ[K] V)
    rw [hTc]
    exact cochar_comp_of_isHomog (mem_flagLevi_iff.1 hx) 2
  -- `T x T⁻¹ = c x` with `c² = 1`, so `T²` commutes with `x`
  obtain ⟨c, hc2, hc⟩ := CentralizerSign.exists_conj_eq_smul hQ hTx
  have hT2 : Commute (T * T) x := by
    have hcen := fun y => Subgroup.mem_center_iff.mp (scalarGSpin_mem_center Q c) y
    have e : T * T * x * (T * T)⁻¹ = x := by
      calc T * T * x * (T * T)⁻¹ = T * (T * x * T⁻¹) * T⁻¹ := by group
        _ = T * (scalarGSpin Q c * x) * T⁻¹ := by rw [hc]
        _ = scalarGSpin Q c * (T * x * T⁻¹) := by rw [← mul_assoc T, hcen T]; group
        _ = scalarGSpin Q c * (scalarGSpin Q c * x) := by rw [hc]
        _ = x := by rw [← mul_assoc, ← map_mul, ← pow_two, hc2, map_one, one_mul]
    exact (mul_inv_eq_iff_eq_mul.mp e)
  have hgT := hcomm g (T * T) hg hT2
  -- `P(g)` commutes with `λ(4)`
  have hP : (specP Q g : V →ₗ[K] V) ∘ₗ cochar b wt 4 =
      cochar b wt 4 ∘ₗ (specP Q g : V →ₗ[K] V) := by
    have h4 : cochar b wt (4 : K) = (specP Q (T * T) : V →ₗ[K] V) := by
      rw [map_mul, show ((specP Q T * specP Q T : V ≃ₗ[K] V) : V →ₗ[K] V) =
        (specP Q T : V →ₗ[K] V) ∘ₗ (specP Q T : V →ₗ[K] V) from rfl, hTc, cochar_mul]
      norm_num
    rw [h4, map_mul]
    have := congrArg (fun e : V ≃ₗ[K] V => (e : V →ₗ[K] V)) (congrArg (specP Q) hgT.eq)
    simp only [map_mul] at this
    exact this
  -- `4^w` separates the weights
  have hinj : Function.Injective fun w : ℤ => (4 : K) ^ w := by
    intro m n hmn
    have h : (((4 : ℚ) ^ m : ℚ) : K) = (((4 : ℚ) ^ n : ℚ) : K) := by
      simpa only [Rat.cast_zpow, Rat.cast_ofNat] using hmn
    exact zpow_right_injective₀ (by norm_num : (0 : ℚ) < 4) (by norm_num) (Rat.cast_injective h)
  exact mem_flagLevi_iff.2 (isHomog_of_comp_cochar hinj hP)

/-- **`GSpin(V)_x ⊆ M_F` for regular semisimple `x ∈ M_F`** (Waldspurger 2010, §2.3:
`G_x = M_x ⊂ M`; Beuzart-Plessis §1.10), from `mem_flagLevi_of_commute` and
`commute_of_isRegular`. -/
theorem mem_flagLevi_of_commute_of_isRegular [CharZero K] [FiniteDimensional K V]
    (hQ : IsNondeg Q) (hs : IsFlagSplitting F b wt) {x : GSpin Q}
    (hx : x ∈ flagLevi (Q := Q) b wt)
    (hss : Module.End.IsSemisimple
      (LinearMap.mulLeft K ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))
    (hab : IsLieAbelian
      (lieCentralizer (gspin Q) ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))
    {g : GSpin Q} (hg : Commute g x) : g ∈ flagLevi (Q := Q) b wt :=
  mem_flagLevi_of_commute hQ hs hx (fun _ _ => commute_of_isRegular hQ x hss hab) hg

end FlagLevi

end GSpinGGP
