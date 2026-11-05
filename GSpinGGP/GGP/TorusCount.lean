/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TorusFrame

/-!
# Counting elements of `Γ(G,H)` torus by torus

Ingredients of the torus-class count (`torusClass_count`, Thesis (6.7.2)–(6.7.5)).

* `commute_torusOf_of_commute`: for `x ∈ Γ(G,H)`, an element of `GSpin(W)(F)` commuting with `x`
  commutes with all of `T_x(F)` (by base change, from `Steinberg.commute_of_fixes_eigenspace_one`).
  Consequently (not formalized here) `N(T_x)` acts freely, through `W(T_x) = N(T_x)/Z(T_x)`, on the
  elements `t` with `T_t = T_x`.
* `finite_conj_torusOf`: only finitely many `t ∈ T_x(F)` are `GSpin(W)(F̄)`-conjugate to `x`.
* `finite_weylQuot`, `weylCardOf_pos`: `W(T_x)` is finite, so `|W(T_x)| ≥ 1`.
-/

noncomputable section

open QuadraticMap
open scoped TensorProduct

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

set_option hygiene false in
local notation "Kb" => AlgebraicClosure F

namespace GGPData

variable {d : GGPData F}

/-- Base change maps `T_x(F)` into `T_x(F̄)`. -/
theorem bcGSpin_mem_torusFbar {x t : ↥(GSpin d.QW)} (ht : t ∈ d.torusOf x) :
    bcGSpin d.QW t ∈ d.torusFbar x := by
  refine ⟨?_, fun w hw => ?_⟩
  · have h := congrArg (fun g : ↥(GSpin d.QW) => bcUnits d.QW (g : (CliffordAlgebra d.QW)ˣ))
      (Subgroup.mem_centralizer_singleton_iff.1 ht.1)
    simp only [Subgroup.coe_mul, map_mul] at h
    exact h
  · change (specP _ (bcGSpin d.QW t) : _ →ₗ[Kb] _) w = w
    rw [specP_bcGSpin]
    obtain ⟨u, rfl⟩ := Submodule.toBaseChange_surjective' Kb _ hw
    clear hw
    induction u using TensorProduct.inductionOn with
    | tmul k v =>
      rw [Submodule.coe_toBaseChange_tmul, LinearMap.baseChange_tmul]
      congr 1
      exact ht.2 v v.2
    | add u v hu hv => rw [map_add, Submodule.coe_add, map_add, hu, hv]

/-- **Centralizers of elements of `Γ(G,H)` centralize their torus**: for `x ∈ Γ(G,H)`, an element
`z` of `GSpin(W)(F)` commuting with `x` commutes with every `t ∈ T_x(F)`. -/
theorem commute_torusOf_of_commute {x z t : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    (hzx : Commute z x) (ht : t ∈ d.torusOf x) : Commute z t := by
  have h := Steinberg.commute_of_fixes_eigenspace_one (x := bcGSpin d.QW x)
    (isNondeg_baseChange _ d.nondeg)
    (by rw [specP_bcGSpin]; exact isSemisimple_specP_baseChange x hx.1)
    (by rw [specP_bcGSpin]; exact lieAbelian_specP_baseChange x hx)
    (t := bcGSpin d.QW t) (z := bcGSpin d.QW z)
    (Subtype.ext (bcGSpin_mem_torusFbar ht).1.eq)
    (fun w hw => (bcGSpin_mem_torusFbar ht).2 w (by rwa [GGPData.eigenspace_bc_one] at hw))
    (hzx.map (bcGSpin d.QW))
  exact bcGSpin_injective d.QW (by rw [map_mul, map_mul, h.eq])

/-- Two `GSpin(W)(F̄)`-conjugates `t, t₀` of `x` with the same image in `SO(W)` differ by a
scalar `c` with `c ^ dim C(W) = 1` (`exists_eq_mul_scalarGSpin_of_specP_eq`,
`pow_finrank_eq_one_of_conj_eq_mul_scalarGSpin`). -/
theorem exists_pow_eq_one_of_conj_of_specP_eq {x t t₀ : ↥(GSpin d.QW)}
    (ht : ∃ g : ↥(GSpin (d.QW.baseChange Kb)), g * bcGSpin d.QW x * g⁻¹ = bcGSpin d.QW t)
    (ht₀ : ∃ g : ↥(GSpin (d.QW.baseChange Kb)), g * bcGSpin d.QW x * g⁻¹ = bcGSpin d.QW t₀)
    (hP : specP _ (bcGSpin d.QW t) = specP _ (bcGSpin d.QW t₀)) :
    ∃ c : Kbˣ, (c : Kb) ^ Module.finrank Kb (CliffordAlgebra (d.QW.baseChange Kb)) = 1 ∧
      bcGSpin d.QW t₀ * scalarGSpin _ c = bcGSpin d.QW t := by
  obtain ⟨c, htc⟩ := exists_eq_mul_scalarGSpin_of_specP_eq (isNondeg_baseChange _ d.nondeg) hP
  refine ⟨c, ?_, htc.symm⟩
  obtain ⟨g, hg⟩ := ht
  obtain ⟨g₀, hg₀⟩ := ht₀
  refine pow_finrank_eq_one_of_conj_eq_mul_scalarGSpin (u := bcGSpin d.QW t₀) (g := g * g₀⁻¹) ?_
  rw [← htc, ← hg, ← hg₀]
  group

-- elaborating the frame-scalar bookkeeping over `F̄` exceeds the default budget
set_option maxHeartbeats 400000 in
/-- **Finitely many conjugates of `x` in `T_x(F)`**: for `x ∈ Γ(G,H)`, only finitely many
`t ∈ T_x(F)` are `GSpin(W)(F̄)`-conjugate to `x`. Over `F̄`, `P(t)` acts on an eigen-frame of
`P(x)` by eigenvalues of `P(x)` (roots of its minimal polynomial), so takes finitely many values;
and two such `t` with the same `P(t)` differ by a scalar `c` with `c ^ N = 1`
(`pow_finrank_eq_one_of_conj_eq_smul`). -/
theorem finite_conj_torusOf {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) :
    {t : ↥(GSpin d.QW) | t ∈ d.torusOf x ∧ ∃ g : ↥(GSpin (d.QW.baseChange Kb)),
      g * bcGSpin d.QW x * g⁻¹ = bcGSpin d.QW t}.Finite := by
  classical
  set S := {t : ↥(GSpin d.QW) | t ∈ d.torusOf x ∧ ∃ g : ↥(GSpin (d.QW.baseChange Kb)),
      g * bcGSpin d.QW x * g⁻¹ = bcGSpin d.QW t}
  obtain ⟨n, e, f, hF, heq⟩ := exists_hypFrame_torusFbar x hx
  set X : Module.End Kb (Kb ⊗[F] (Fin d.m → F)) :=
    (specP _ (bcGSpin d.QW x) : Kb ⊗[F] (Fin d.m → F) →ₗ[Kb]
      Kb ⊗[F] (Fin d.m → F))
  set R : Set Kbˣ := {c | (minpoly Kb X).IsRoot (c : Kb)}
  have hR : R.Finite := ((Polynomial.finite_setOfPred_isRoot
    (minpoly.ne_zero (Algebra.IsIntegral.isIntegral X))).preimage Units.val_injective.injOn)
  have : Finite R := hR.to_subtype
  -- the frame scalars of `P(t)` are eigenvalues of `X`
  have hscal : ∀ t ∈ S, ∃ τ : Fin n → R, (∀ w ∈ Module.End.eigenspace X 1,
      specP _ (bcGSpin d.QW t) w = w) ∧
        ∀ i, specP _ (bcGSpin d.QW t) (e i) = ((τ i : Kbˣ) : Kb) • e i ∧
        specP _ (bcGSpin d.QW t) (f i) = ((((τ i : Kbˣ))⁻¹ : Kbˣ) : Kb) • f i := by
    rintro t ⟨ht, g, hg⟩
    obtain ⟨hW, τ, hτ⟩ : specP _ (bcGSpin d.QW t) ∈ hypTorus (Module.End.eigenspace X 1) e f :=
      heq ▸ Subgroup.mem_map_of_mem _ (bcGSpin_mem_torusFbar ht)
    have hmem : ∀ i, τ i ∈ R := fun i => by
      have he : e i ≠ 0 := fun h0 => by
        have := hF.polar_ef_self i; rw [h0, polar_zero_left] at this; exact zero_ne_one this
      set v := specP _ g⁻¹ (e i)
      have hv : v ≠ 0 := fun h0 => he (by
        have := congrArg (specP _ g) h0
        rw [map_zero, ← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one] at this
        exact this)
      have hXv : X v = ((τ i : Kbˣ) : Kb) • v := by
        have h1 : specP _ g⁻¹ * specP _ (bcGSpin d.QW t) =
            specP _ (bcGSpin d.QW x) * specP _ g⁻¹ := by
          rw [← map_mul, ← map_mul, ← hg]; congr 1; group
        have h2 := congrArg (fun φ => φ (e i)) h1
        simp only [LinearEquiv.mul_apply, (hτ i).1, map_smul] at h2
        exact h2.symm
      exact (Module.End.hasEigenvalue_iff_isRoot).1
        (Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hXv, hv⟩)
    exact ⟨fun i => ⟨τ i, hmem i⟩, hW, hτ⟩
  -- bucket the images `bc t` by their frame scalars
  set N := Module.finrank Kb (CliffordAlgebra (d.QW.baseChange Kb))
  have hN : 0 < N := Module.finrank_pos
  have hroots : {c : Kbˣ | (c : Kb) ^ N = 1}.Finite :=
    ((Polynomial.finite_setOfPred_isRoot (Polynomial.X_pow_sub_C_ne_zero hN 1)).preimage
      Units.val_injective.injOn).subset fun c (hc : (c : Kb) ^ N = 1) => by
        simp [Polynomial.IsRoot.def, hc]
  let fib : (Fin n → R) → Set ↥(GSpin (d.QW.baseChange Kb)) := fun τ =>
    {u | ∃ t ∈ S, u = bcGSpin d.QW t ∧ ∀ i, specP _ u (e i) = ((τ i : Kbˣ) :
      Kb) • e i ∧ specP _ u (f i) =
        ((((τ i : Kbˣ))⁻¹ : Kbˣ) : Kb) • f i}
  have hfib : ∀ τ, (fib τ).Finite := by
    intro τ
    rcases (fib τ).eq_empty_or_nonempty with h0 | ⟨u₀, t₀, ht₀, rfl, hτ₀⟩
    · rw [h0]; exact Set.finite_empty
    refine (hroots.image fun c => bcGSpin d.QW t₀ * scalarGSpin _ c).subset ?_
    rintro _ ⟨t, ht, rfl, hτ⟩
    obtain ⟨-, hW₀, -⟩ := hscal t₀ ht₀
    obtain ⟨-, hW, -⟩ := hscal t ht
    -- same `P`, so they differ by a scalar
    have hP : specP _ (bcGSpin d.QW t) = specP _ (bcGSpin d.QW t₀) :=
      LinearEquiv.toLinearMap_injective (hF.eq_of_scale (t := fun i => (τ i : Kbˣ))
        (fun w hw => hW w hw) hτ (fun w hw => hW₀ w hw) hτ₀)
    obtain ⟨c, hc, htc⟩ := exists_pow_eq_one_of_conj_of_specP_eq (x := x) ht.2 ht₀.2 hP
    exact ⟨c, hc, htc⟩
  -- conclude
  refine Set.Finite.of_finite_image ?_ (bcGSpin_injective d.QW).injOn
  refine (Set.finite_iUnion hfib).subset ?_
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨τ, -, hτ⟩ := hscal t ht
  exact Set.mem_iUnion.2 ⟨τ, t, ht, rfl, hτ⟩

/-- **`W(T_x)` is finite**, for `x ∈ Γ(G,H)`: `n ↦ n x n⁻¹` is injective on `N(T_x)/Z(T_x)`
(`commute_torusOf_of_commute`) with values in the finite set of `finite_conj_torusOf`. -/
theorem finite_weylQuot {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) :
    Finite (↥(Subgroup.normalizer (d.torusOf x : Set ↥(GSpin d.QW))) ⧸
      (Subgroup.centralizer (d.torusOf x : Set ↥(GSpin d.QW))).subgroupOf
        (Subgroup.normalizer (d.torusOf x : Set ↥(GSpin d.QW)))) := by
  have hfin := (finite_conj_torusOf hx).to_subtype
  let φ : ↥(Subgroup.normalizer (d.torusOf x : Set ↥(GSpin d.QW))) →
      {t : ↥(GSpin d.QW) | t ∈ d.torusOf x ∧ ∃ g : ↥(GSpin (d.QW.baseChange Kb)),
        g * bcGSpin d.QW x * g⁻¹ = bcGSpin d.QW t} := fun n =>
    ⟨n * x * (n : ↥(GSpin d.QW))⁻¹, (n.2 x).1 (d.self_mem_torusOf x),
      bcGSpin d.QW n, by rw [map_mul, map_mul, map_inv]⟩
  refine Finite.of_injective (Quotient.lift φ fun a b hab => ?_) fun a b hab => ?_
  · have hab' := QuotientGroup.leftRel_apply.mp hab
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hab'
    apply Subtype.ext
    have hc := hab' x (d.self_mem_torusOf x)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc
    show (a : ↥(GSpin d.QW)) * x * (a : ↥(GSpin d.QW))⁻¹ =
      (b : ↥(GSpin d.QW)) * x * (b : ↥(GSpin d.QW))⁻¹
    symm
    calc (b : ↥(GSpin d.QW)) * x * (b : ↥(GSpin d.QW))⁻¹ =
        a * (((a : ↥(GSpin d.QW))⁻¹ * b) * x) * (b : ↥(GSpin d.QW))⁻¹ := by group
      _ = a * (x * ((a : ↥(GSpin d.QW))⁻¹ * b)) * (b : ↥(GSpin d.QW))⁻¹ := by rw [hc]
      _ = _ := by group
  · induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    rename_i a b
    apply Quotient.sound
    refine QuotientGroup.leftRel_apply.mpr ?_
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    have h := congrArg Subtype.val hab
    simp only [Quotient.lift_mk, φ] at h
    have hc : Commute ((a : ↥(GSpin d.QW))⁻¹ * b) x := by
      change _ * _ = _ * _
      calc ((a : ↥(GSpin d.QW))⁻¹ * b) * x =
          (a : ↥(GSpin d.QW))⁻¹ * (b * x * (b : ↥(GSpin d.QW))⁻¹) * b := by group
        _ = x * ((a : ↥(GSpin d.QW))⁻¹ * b) := by rw [← h]; group
    intro t ht
    exact ((commute_torusOf_of_commute hx hc ht).eq).symm

/-- `|W(T_x)| ≥ 1` for `x ∈ Γ(G,H)`. -/
theorem weylCardOf_pos {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) :
    0 < weylCardOf d (d.torusOf x) := by
  have := finite_weylQuot hx
  exact Nat.card_pos

end GGPData

end GSpinGGP
