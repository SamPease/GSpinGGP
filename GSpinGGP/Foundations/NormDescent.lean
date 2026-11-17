/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import GSpinGGP.Foundations.GSpin
import GSpinGGP.Foundations.LocalGroups
import GSpinGGP.Foundations.ExpHaar
import GSpinGGP.Foundations.QuadraticForms
import GSpinGGP.Foundations.BasisNorm
import TauCeti.Algebra.CentralSimple.Opposite
import TauCeti.LinearAlgebra.CliffordAlgebra.CentralSimple.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.CentralSimple.Even

/-!
# Norm descent along `GSpin(V) → SO(V)`

Kottwitz's norm-descent property (Kottwitz, *Harmonic analysis on reductive `p`-adic groups and
Lie algebras*, Clay Math. Proc. 4, Prop. 18.3; BP §1.2) for the projection `P : GSpin(V) → SO(V)`,
with an elementary proof. Write `‖x‖` for the operator norm of left multiplication by
`x ∈ C(V)` (`lmulPi`). Then for `g ∈ GSpin(V)`:

* `‖P(g)‖ ≪ ‖g‖ ‖g⁻¹‖`, since `ι(P(g) v) = g ι(v) g⁻¹` (`exists_norm_specP_le`);
* `‖g‖ ‖g⁻¹‖ ≪ max(1, ‖P(g)‖)ᴺ` (`exists_norm_mul_norm_inv_le`). Conjugation by `g` is the
  algebra automorphism `C(P(g))` of `C(V)`, so it is bounded by a power of `‖P(g)‖`; and for a
  central simple algebra `B`, `‖a‖ ‖b‖ ≪ ‖x ↦ a x b‖`, because `B ⊗ Bᵒᵖ → End(B)` is injective
  (Tau Ceti `IsSimpleRing.mulLeftRight_injective`). Here `B = C(V)` if `dim V` is even and
  `B = C⁰(V) ∋ g, g⁻¹` if `dim V` is odd (Tau Ceti `CliffordAlgebra.isSimpleRing_of_even_finrank`,
  `TauCeti.CliffordAlgebra.isSimpleRing_even_of_odd_finrank`).

Since `ker P` is the scalars and `‖c g‖ = |c| ‖g‖`, rescaling `g` by a scalar makes `‖g‖` and
`‖g⁻¹‖` both `≪ max(1, ‖P(g)‖)ᴺ` (`exists_scalar_norm_le`); this is used in
`TraceFormula/LogNormDescent.lean`.

## Main results

* `exists_norm_mul_norm_le_of_isSimpleRing`: `‖a‖ ‖b‖ ≤ C ‖(a sᵢ b)ᵢ‖` in a finite-dimensional
  central simple algebra, for a spanning family `(sᵢ)`.
* `exists_norm_specP_le`, `exists_norm_mul_norm_inv_le`: the two estimates above.
* `exists_scalar_norm_le`: the rescaled form.

The general lemmas hold over any complete nontrivially normed field; the `GSpin` estimates are
stated over a `p`-adic field, where `lmulPi` is defined.
-/

noncomputable section

open Module CliffordAlgebra
open scoped TensorProduct

namespace GSpinGGP

/-! ### Products of sup norms -/

/-- `‖x‖ ‖y‖ ≤ ‖x ⊗ y‖` for the sup norms (outer product `(xᵢ yⱼ)ᵢⱼ`) on `𝕜^ι`, `𝕜^κ`, `𝕜^{ι × κ}`. -/
theorem norm_mul_norm_le_norm_outer {𝕜 : Type*} [NormedField 𝕜] {ι κ : Type*} [Fintype ι]
    [Fintype κ] (x : ι → 𝕜) (y : κ → 𝕜) :
    ‖x‖ * ‖y‖ ≤ ‖fun p : ι × κ => x p.1 * y p.2‖ := by
  set T := ‖fun p : ι × κ => x p.1 * y p.2‖
  have hrow : ∀ i, ‖x i‖ * ‖y‖ ≤ T := by
    intro i
    rw [← norm_smul]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
    simpa using norm_le_pi_norm (fun p : ι × κ => x p.1 * y p.2) (i, j)
  rcases (norm_nonneg y).eq_or_lt with hy | hy
  · rw [← hy, mul_zero]; exact norm_nonneg _
  · rw [← le_div_iff₀ hy]
    exact (pi_norm_le_iff_of_nonneg (div_nonneg (norm_nonneg _) hy.le)).2 fun i =>
      (le_div_iff₀ hy).2 (hrow i)

/-! ### Central simple algebras -/

section CentralSimple

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {B : Type*} [Ring B] [Algebra 𝕜 B] [FiniteDimensional 𝕜 B] [Algebra.IsCentral 𝕜 B]
  [IsSimpleRing B]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

/-- **Two-sided multiplication in a central simple algebra is bounded below.** Let `B` be a
finite-dimensional central simple algebra over a complete field, `ν : B → X` an injective linear
map into a normed space (a norm on `B`) and `(sᵢ)` a finite spanning family. Then
`‖ν a‖ ‖ν b‖ ≤ C ‖(ν (a sᵢ b))ᵢ‖`. Proof: `a ⊗ b ↦ (x ↦ a x b)` is injective on `B ⊗ Bᵒᵖ`
(Tau Ceti `IsSimpleRing.mulLeftRight_injective`), so the coordinates `aᵢ bⱼ` of `a ⊗ b` are bounded
by the norm of `x ↦ a x b`. -/
theorem exists_norm_mul_norm_le_of_isSimpleRing (ν : B →ₗ[𝕜] X) (hν : Function.Injective ν)
    {ι : Type*} [Fintype ι] (s : ι → B) (hs : Submodule.span 𝕜 (Set.range s) = ⊤) :
    ∃ C, 0 ≤ C ∧ ∀ a b : B, ‖ν a‖ * ‖ν b‖ ≤ C * ‖fun i => ν (a * s i * b)‖ := by
  classical
  let e := Module.finBasis 𝕜 B
  let T := e.tensorProduct e.mulOpposite
  let φ : (B ⊗[𝕜] Bᵐᵒᵖ) →ₗ[𝕜] Module.End 𝕜 B := (AlgHom.mulLeftRight 𝕜 B).toLinearMap
  let f : (B ⊗[𝕜] Bᵐᵒᵖ) →ₗ[𝕜] (ι → X) :=
    LinearMap.pi fun i => ν ∘ₗ (LinearMap.applyₗ (s i)) ∘ₗ φ
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    have h0 : ∀ i, φ t (s i) = 0 := fun i => by
      have := congrFun ht i
      simpa [f] using hν (this.trans (map_zero ν).symm)
    have : φ t = 0 := LinearMap.ext_on_range hs (fun i => by simpa using h0 i)
    exact IsSimpleRing.mulLeftRight_injective 𝕜 B (by simpa [φ] using this)
  obtain ⟨C₁, hC₁, h₁⟩ := LinearMap.exists_norm_le_mul_norm_of_injective f
    T.equivFun.toLinearMap hf
  obtain ⟨C₂, hC₂, h₂⟩ := LinearMap.exists_norm_le_mul_norm_of_injective
    e.equivFun.toLinearMap ν e.equivFun.injective
  refine ⟨C₂ * C₂ * C₁, by positivity, fun a b => ?_⟩
  have hT : ‖e.equivFun a‖ * ‖e.equivFun b‖ ≤ ‖T.equivFun (a ⊗ₜ MulOpposite.op b)‖ := by
    refine (norm_mul_norm_le_norm_outer _ _).trans (le_of_eq ?_)
    congr 1
    funext p
    obtain ⟨i, j⟩ := p
    simp only [Basis.equivFun_apply, Basis.tensorProduct_repr_tmul_apply,
      Basis.mulOpposite_repr_op, smul_eq_mul, mul_comm, T]
  have hfab : f (a ⊗ₜ MulOpposite.op b) = fun i => ν (a * s i * b) := by
    funext i; simp [f, φ]
  have := h₁ (a ⊗ₜ MulOpposite.op b)
  rw [hfab] at this
  calc ‖ν a‖ * ‖ν b‖ ≤ (C₂ * ‖e.equivFun a‖) * (C₂ * ‖e.equivFun b‖) :=
        mul_le_mul (h₂ a) (h₂ b) (norm_nonneg _) (by positivity)
    _ = C₂ * C₂ * (‖e.equivFun a‖ * ‖e.equivFun b‖) := by ring
    _ ≤ C₂ * C₂ * (C₁ * ‖fun i => ν (a * s i * b)‖) :=
        mul_le_mul_of_nonneg_left (hT.trans this) (by positivity)
    _ = _ := by ring

end CentralSimple

/-! ### `GSpin(V)` and `SO(V)` -/

section GSpinNorm

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

/-- `‖f g‖ ≤ ‖f‖ ‖g‖` for the product `f * g = f ∘ g` of the group `V ≃ₗ V`. -/
theorem norm_toContinuousLinearMap_mul_le (f g : V ≃ₗ[F] V) :
    ‖LinearMap.toContinuousLinearMap ((f * g : V ≃ₗ[F] V) : V →ₗ[F] V)‖ ≤
      ‖LinearMap.toContinuousLinearMap (f : V →ₗ[F] V)‖ *
        ‖LinearMap.toContinuousLinearMap (g : V →ₗ[F] V)‖ := by
  have : LinearMap.toContinuousLinearMap ((f * g : V ≃ₗ[F] V) : V →ₗ[F] V) =
      (LinearMap.toContinuousLinearMap (f : V →ₗ[F] V)).comp
        (LinearMap.toContinuousLinearMap (g : V →ₗ[F] V)) := by
    ext v; rfl
  rw [this]
  exact ContinuousLinearMap.opNorm_comp_le _ _

/-- `‖ι(v)‖ ≤ C ‖v‖`. -/
theorem exists_norm_lmulPi_ι_le :
    ∃ C, 0 ≤ C ∧ ∀ v : V, ‖lmulPi F (ι Q v)‖ ≤ C * ‖v‖ :=
  LinearMap.exists_norm_le_mul_norm_of_injective LinearMap.id (lmulPiₗ F ∘ₗ ι Q)
    Function.injective_id

/-- The maximum `max(1, ‖P(g)‖)`. -/
local notation "Mx" g => max 1 ‖LinearMap.toContinuousLinearMap (specP Q g : V →ₗ[F] V)‖

/-- **Conjugation by `g ∈ GSpin(V)` is polynomially bounded in `P(g)`**: for each `x ∈ C(V)` there
are `C`, `N` with `‖g x g⁻¹‖ ≤ C max(1, ‖P(g)‖)ᴺ` for all `g`. (`x ↦ g x g⁻¹` is the algebra
automorphism `C(P(g))`; induction over the subalgebra generated by `ι(V)`, which is `C(V)`.) -/
theorem exists_norm_conj_le (x : CliffordAlgebra Q) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ g : GSpin Q,
      ‖lmulPi F (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * x *
        (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))‖ ≤
        C * (Mx g) ^ N := by
  obtain ⟨Cι, hCι, hι⟩ := exists_norm_lmulPi_ι_le (F := F) (Q := Q)
  have hx : x ∈ Algebra.adjoin F (Set.range (ι Q)) := by rw [adjoin_range_ι]; trivial
  have h1 : ∀ g : GSpin Q, 1 ≤ Mx g := fun g => le_max_left _ _
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    refine ⟨Cι * ‖v‖, 1, by positivity, fun g => ?_⟩
    rw [← ι_specP, pow_one]
    calc ‖lmulPi F (ι Q (specP Q g v))‖ ≤ Cι * ‖specP Q g v‖ := hι _
      _ ≤ Cι * (‖LinearMap.toContinuousLinearMap (specP Q g : V →ₗ[F] V)‖ * ‖v‖) :=
          mul_le_mul_of_nonneg_left
            ((LinearMap.toContinuousLinearMap (specP Q g : V →ₗ[F] V)).le_opNorm v) hCι
      _ ≤ Cι * ((Mx g) * ‖v‖) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)) hCι
      _ = Cι * ‖v‖ * (Mx g) := by ring
  | algebraMap r =>
    refine ⟨‖r‖, 0, norm_nonneg _, fun g => ?_⟩
    rw [← Algebra.commutes, mul_assoc, Units.mul_inv, mul_one, pow_zero, mul_one,
      Algebra.algebraMap_eq_smul_one]
    change ‖lmulPiₗ F (r • (1 : CliffordAlgebra Q))‖ ≤ _
    rw [map_smul, norm_smul]
    change ‖r‖ * ‖lmulPi F (1 : CliffordAlgebra Q)‖ ≤ _
    rw [lmulPi_one]
    exact mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le
  | add y z _ _ hy hz =>
    obtain ⟨C₁, N₁, hC₁, h₁⟩ := hy
    obtain ⟨C₂, N₂, hC₂, h₂⟩ := hz
    refine ⟨C₁ + C₂, N₁ + N₂, by positivity, fun g => ?_⟩
    have e1 : (Mx g) ^ N₁ ≤ (Mx g) ^ (N₁ + N₂) := pow_le_pow_right₀ (h1 g) (by omega)
    have e2 : (Mx g) ^ N₂ ≤ (Mx g) ^ (N₁ + N₂) := pow_le_pow_right₀ (h1 g) (by omega)
    rw [mul_add, add_mul]
    change ‖lmulPiₗ F (_ + _)‖ ≤ _
    rw [map_add]
    refine (norm_add_le _ _).trans ?_
    calc _ ≤ C₁ * (Mx g) ^ N₁ + C₂ * (Mx g) ^ N₂ := add_le_add (h₁ g) (h₂ g)
      _ ≤ C₁ * (Mx g) ^ (N₁ + N₂) + C₂ * (Mx g) ^ (N₁ + N₂) :=
          add_le_add (mul_le_mul_of_nonneg_left e1 hC₁) (mul_le_mul_of_nonneg_left e2 hC₂)
      _ = _ := by ring
  | mul y z _ _ hy hz =>
    obtain ⟨C₁, N₁, hC₁, h₁⟩ := hy
    obtain ⟨C₂, N₂, hC₂, h₂⟩ := hz
    refine ⟨C₁ * C₂, N₁ + N₂, by positivity, fun g => ?_⟩
    have : ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * (y * z) *
        (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
        (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * y *
          (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) *
        (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * z *
          (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) := by
      simp only [mul_assoc, Units.inv_mul_cancel_left]
    rw [this, lmulPi_mul, pow_add]
    refine (norm_mul_le _ _).trans ?_
    calc _ ≤ (C₁ * (Mx g) ^ N₁) * (C₂ * (Mx g) ^ N₂) :=
          mul_le_mul (h₁ g) (h₂ g) (norm_nonneg _) (by have := h1 g; positivity)
      _ = _ := by ring

/-- `exists_norm_conj_le` for a finite family. -/
theorem exists_norm_conj_family_le {ι : Type*} [Fintype ι] (s : ι → CliffordAlgebra Q) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ g : GSpin Q,
      ‖fun i => lmulPi F (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) * s i *
        (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))‖ ≤
        C * (Mx g) ^ N := by
  classical
  choose C N hC h using fun i => exists_norm_conj_le (F := F) (s i)
  refine ⟨∑ i, C i, ∑ i, N i, Finset.sum_nonneg fun i _ => hC i, fun g => ?_⟩
  have h1 : 1 ≤ Mx g := le_max_left _ _
  have hM : 0 ≤ (Mx g) ^ ∑ i, N i := pow_nonneg (zero_le_one.trans h1) _
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun j _ => hC j) hM)).2
    fun i => (h i g).trans ?_
  exact mul_le_mul (Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ i))
    (pow_le_pow_right₀ h1 (Finset.single_le_sum (fun j _ => Nat.zero_le (N j))
      (Finset.mem_univ i))) (pow_nonneg (zero_le_one.trans h1) _)
    (Finset.sum_nonneg fun j _ => hC j)

/-- **`‖g‖ ‖g⁻¹‖ ≪ max(1, ‖P(g)‖)ᴺ` on `GSpin(V)`** (the hard half of norm descent): there are
`C`, `N` with `‖g‖ ‖g⁻¹‖ ≤ C max(1, ‖P(g)‖)ᴺ` for all `g ∈ GSpin(V)`, `‖·‖` the norm of left
multiplication on `C(V)`. Two-sided multiplication is bounded below in the central simple algebra
`C(V)` (`dim V` even) or `C⁰(V)` (`dim V` odd; `g, g⁻¹ ∈ C⁰(V)`), and conjugation by `g` is
bounded by `exists_norm_conj_family_le`. -/
theorem exists_norm_mul_norm_inv_le (hQ : IsNondeg Q) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ g : GSpin Q,
      ‖lmulPi F ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)‖ *
        ‖lmulPi F (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)‖ ≤
        C * (Mx g) ^ N := by
  have hQ' : Q.Nondegenerate := (isNondeg_iff_nondegenerate Q).1 hQ
  rcases Nat.even_or_odd (finrank F V) with hV | hV
  · have := CliffordAlgebra.isCentral_of_even_finrank hQ' hV
    have := CliffordAlgebra.isSimpleRing_of_even_finrank hQ' hV
    let e := Module.finBasis F (CliffordAlgebra Q)
    obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_mul_norm_le_of_isSimpleRing (lmulPiₗ F)
      (lmulPi_injective F) e e.span_eq
    obtain ⟨C₂, N, hC₂, h₂⟩ := exists_norm_conj_family_le (F := F) e
    exact ⟨C₁ * C₂, N, by positivity, fun g => (h₁ _ _).trans
      ((mul_le_mul_of_nonneg_left (h₂ g) hC₁).trans_eq (by ring))⟩
  · have := TauCeti.CliffordAlgebra.isCentral_even_of_odd_finrank hQ' hV
    have := TauCeti.CliffordAlgebra.isSimpleRing_even_of_odd_finrank hQ' hV
    let e := Module.finBasis F (even Q)
    obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_mul_norm_le_of_isSimpleRing
      (lmulPiₗ F ∘ₗ (even Q).val.toLinearMap)
      ((lmulPi_injective F).comp Subtype.val_injective) e e.span_eq
    obtain ⟨C₂, N, hC₂, h₂⟩ := exists_norm_conj_family_le (F := F)
      fun i => (e i : CliffordAlgebra Q)
    refine ⟨C₁ * C₂, N, by positivity, fun g => ?_⟩
    have hg : ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈ even Q := g.2.1
    have hg' : (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) ∈
        even Q := (g⁻¹).2.1
    have := h₁ ⟨_, hg⟩ ⟨_, hg'⟩
    exact this.trans ((mul_le_mul_of_nonneg_left (h₂ g) hC₁).trans_eq (by ring))

/-- **`‖P(g)‖ ≪ ‖g‖ ‖g⁻¹‖` on `GSpin(V)`** (the easy half of norm descent), since
`ι(P(g) v) = g ι(v) g⁻¹`. -/
theorem exists_norm_specP_le :
    ∃ C, 0 ≤ C ∧ ∀ g : GSpin Q, ‖LinearMap.toContinuousLinearMap (specP Q g : V →ₗ[F] V)‖ ≤
      C * (‖lmulPi F ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)‖ *
        ‖lmulPi F (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) :
          CliffordAlgebra Q)‖) := by
  obtain ⟨Cι, hCι, hι⟩ := exists_norm_lmulPi_ι_le (F := F) (Q := Q)
  obtain ⟨C₀, hC₀, h₀⟩ := LinearMap.exists_norm_le_mul_norm_of_injective (lmulPiₗ F) (ιInv Q)
    (lmulPi_injective F)
  refine ⟨C₀ * Cι, by positivity, fun g => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  change ‖specP Q g v‖ ≤ _
  rw [specP_apply_eq, ← mul_assoc]
  refine (h₀ _).trans ?_
  change C₀ * ‖lmulPi F _‖ ≤ _
  rw [lmulPi_mul, lmulPi_mul]
  have := norm_mul_le (lmulPi F ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) *
    lmulPi F (ι Q v)) (lmulPi F (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) :
      CliffordAlgebra Q))
  have h2 := norm_mul_le (lmulPi F ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q))
    (lmulPi F (ι Q v))
  have h3 := hι v
  calc C₀ * ‖_‖ ≤ C₀ * (‖lmulPi F ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)‖ *
        (Cι * ‖v‖) * ‖lmulPi F (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) :
          CliffordAlgebra Q)‖) := by
        refine mul_le_mul_of_nonneg_left (this.trans ?_) hC₀
        exact mul_le_mul_of_nonneg_right (h2.trans
          (mul_le_mul_of_nonneg_left h3 (norm_nonneg _))) (norm_nonneg _)
    _ = _ := by ring

/-- **Norm descent on `GSpin(V)`**: every `g ∈ GSpin(V)` has a scalar multiple `c g` with
`‖c g‖, ‖(c g)⁻¹‖ ≤ C max(1, ‖P(g)‖)ᴺ` (`exists_norm_mul_norm_inv_le`, rescaled so that
`1 ≤ ‖c g‖ < ‖c₀‖` for a fixed `c₀ ∈ F` with `‖c₀‖ > 1`). -/
theorem exists_scalar_norm_le (hQ : IsNondeg Q) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ g : GSpin Q, ∃ c : Fˣ,
      ‖lmulPi F (((scalarGSpin Q c * g : GSpin Q) : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)‖
        ≤ C * (Mx g) ^ N ∧
      ‖lmulPi F ((((scalarGSpin Q c * g : GSpin Q) : (CliffordAlgebra Q)ˣ)⁻¹ :
        (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)‖ ≤ C * (Mx g) ^ N := by
  obtain ⟨CA, N, hCA, hA⟩ := exists_norm_mul_norm_inv_le (F := F) hQ
  obtain ⟨c₀, hc₀⟩ := NormedField.exists_one_lt_norm F
  have hc₀0 : c₀ ≠ 0 := norm_pos_iff.1 (zero_lt_one.trans hc₀)
  refine ⟨max ‖c₀‖ CA, N, le_max_of_le_right hCA, fun g => ?_⟩
  have hM : 1 ≤ (Mx g) ^ N := one_le_pow₀ (le_max_left _ _)
  set a := ‖lmulPi F ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)‖
  set b := ‖lmulPi F (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)‖
  have ha : 0 < a := norm_lmulPi_pos F (Units.ne_zero _)
  have hb : 0 ≤ b := norm_nonneg _
  obtain ⟨k, hk1, hk2⟩ := exists_mem_Ico_zpow ha hc₀
  let c : Fˣ := Units.mk0 (c₀ ^ (-k)) (zpow_ne_zero _ hc₀0)
  have hc : ‖(c : F)‖ = ‖c₀‖ ^ (-k) := by simp [c, norm_zpow]
  have hpos : 0 < ‖c₀‖ ^ k := zpow_pos (zero_lt_one.trans hc₀) k
  have hca1 : 1 ≤ ‖(c : F)‖ * a := by
    rw [hc, zpow_neg, ← div_eq_inv_mul, le_div_iff₀ hpos, one_mul]; exact hk1
  have hca2 : ‖(c : F)‖ * a ≤ ‖c₀‖ := by
    rw [hc, zpow_neg, ← div_eq_inv_mul, div_le_iff₀ hpos, ← zpow_one_add₀ (by positivity),
      add_comm]
    exact hk2.le
  refine ⟨c, ?_, ?_⟩
  · rw [coe_scalarGSpin_mul, norm_lmulPi_smul F]
    calc ‖(c : F)‖ * a ≤ ‖c₀‖ * 1 := by rw [mul_one]; exact hca2
      _ ≤ max ‖c₀‖ CA * (Mx g) ^ N :=
        mul_le_mul (le_max_left _ _) hM zero_le_one (le_max_of_le_left (norm_nonneg _))
  · rw [coe_inv_scalarGSpin_mul, norm_lmulPi_smul F]
    have hcpos : 0 < ‖(c : F)‖ := norm_pos_iff.2 c.ne_zero
    calc ‖((c⁻¹ : Fˣ) : F)‖ * b = (a * b) / (‖(c : F)‖ * a) := by
          rw [Units.val_inv_eq_inv_val, norm_inv]; field_simp
      _ ≤ a * b := div_le_self (by positivity) hca1
      _ ≤ CA * (Mx g) ^ N := hA g
      _ ≤ max ‖c₀‖ CA * (Mx g) ^ N :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end GSpinNorm

end GSpinGGP
