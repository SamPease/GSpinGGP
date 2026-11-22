/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.CentralizerSign
import GSpinGGP.GGP.LeviSubgroup
import GSpinGGP.GGP.CentralizerBaseChange
import GSpinGGP.GGP.TorusCentral

/-!
# Centralizers of regular semisimple elements of `GSpin(V)`

For `x ∈ GSpin(V)` regular semisimple (`x` semisimple on `C(V)` and `gspin(V)_x` abelian), the
centralizer `GSpin(V)_x` is a maximal torus; in particular it is commutative
(`commute_of_isRegular`; over `K̄`, `Steinberg.commute_of_forall_skew_commute` in
`GGP/TorusCentral.lean`).  From this: if moreover `x` lies in the Levi subgroup
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
open scoped TensorProduct

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

variable {K : Type*} [Field K] [Invertible (2 : K)]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {Q : QuadraticForm K V}

/-- **The centralizer of a regular semisimple element of `GSpin(V)` is commutative**: for `x`
semisimple on `C(V)` with `gspin(V)_x` abelian, any two elements of `GSpin(V)` commuting with `x`
commute.  (The centralizer is a maximal torus: connected by Steinberg's theorem, as the derived
group `Spin(V)` is simply connected, with abelian Lie algebra.)

Proof, without connectedness, after base change to `K̄` (`bcGSpin_injective`): `P(x)_{K̄}` is
semisimple (`isSemisimple_specP_baseChange`), and the skew endomorphisms of `V_{K̄}` commuting
with `P(x)_{K̄}` (`soCent`) commute, since `gspin(V)_x` is abelian (`commute_baseChange_of_lie_eq_zero` with
`U = 0`); conclude by `Steinberg.commute_of_forall_skew_commute`. -/
theorem commute_of_isRegular [CharZero K] [FiniteDimensional K V] (hQ : IsNondeg Q) (x : GSpin Q)
    (hss : Module.End.IsSemisimple
      (LinearMap.mulLeft K ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))
    (hab : IsLieAbelian
      (lieCentralizer (gspin Q) ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))
    {g h : GSpin Q} (hg : Commute g x) (hh : Commute h x) : Commute g h := by
  have hQL := isNondeg_baseChange Q hQ
  have hssL : Module.End.IsSemisimple (specP _ (bcGSpin Q x) :
      AlgebraicClosure K ⊗[K] V →ₗ[AlgebraicClosure K] AlgebraicClosure K ⊗[K] V) := by
    rw [specP_bcGSpin]; exact isSemisimple_specP_baseChange x hss
  have habL : ∀ M₁ ∈ soCent (Q.baseChange (AlgebraicClosure K)) (specP _ (bcGSpin Q x) :
      AlgebraicClosure K ⊗[K] V →ₗ[AlgebraicClosure K] AlgebraicClosure K ⊗[K] V),
      ∀ M₂ ∈ soCent (Q.baseChange (AlgebraicClosure K)) (specP _ (bcGSpin Q x) :
        AlgebraicClosure K ⊗[K] V →ₗ[AlgebraicClosure K] AlgebraicClosure K ⊗[K] V),
      Commute M₁ M₂ := by
    intro Y₁ h₁ Y₂ h₂
    rw [mem_soCent, specP_bcGSpin] at h₁ h₂
    refine commute_baseChange_of_lie_eq_zero hQ x ⊥ (fun X hX Y hY _ _ => ?_)
      (LinearMap.isSkewAdjoint_iff.2 h₁.1) (LinearMap.isSkewAdjoint_iff.2 h₂.1) h₁.2.symm h₂.2.symm
      (fun w hw => by rw [(Submodule.mem_bot K).1 hw, TensorProduct.tmul_zero, map_zero])
      (fun w hw => by rw [(Submodule.mem_bot K).1 hw, TensorProduct.tmul_zero, map_zero])
    have h0 := congrArg Subtype.val (hab.trivial ⟨X, hX⟩ ⟨Y, hY⟩)
    rwa [LieSubalgebra.coe_bracket] at h0
  have key := Steinberg.commute_of_forall_skew_commute hQL hssL habL (hg.map (bcGSpin Q))
    (hh.map (bcGSpin Q))
  exact bcGSpin_injective Q (by rw [map_mul, map_mul, key.eq])

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
