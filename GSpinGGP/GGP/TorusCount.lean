/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.GammaClassFinite
import GSpinGGP.GGP.TwistSymm

/-!
# Counting elements of `Γ(G,H)` torus by torus

Ingredients of the torus-class count (`torusClass_count`, Thesis (6.7.2)–(6.7.5)).

* `commute_torusOf_of_commute`: for `x ∈ Γ(G,H)`, an element of `GSpin(W)(F)` commuting with `x`
  commutes with all of `T_x(F)` (by base change, from `Steinberg.commute_of_fixes_eigenspace_one`).
  Consequently (not formalized here) `N(T_x)` acts freely, through `W(T_x) = N(T_x)/Z(T_x)`, on the
  elements `t` with `T_t = T_x`.
* `finite_conj_torusOf`: only finitely many `t ∈ T_x(F)` are `GSpin(W)(F̄)`-conjugate to `x`.
* `finite_weylQuot`, `weylCardOf_pos`: `W(T_x)` is finite, so `|W(T_x)| ≥ 1`.
* `torusOf_conj`, `isSS_conj`: conjugation moves tori and preserves semisimplicity.
* `card_quot_conjOn`: for `Y ⊆ Γ(G,H)` stable under conjugation, the number of rational classes of
  `Y` is `Σ_c |{y ∈ Y : T_y = T_c}| / |W(T_c)|` over the torus classes `c`
  (`card_classOn_mul_weylCard`: `N(T_c)` acts freely modulo `Z(T_c)`).
* `stableSet`, `stableWeight`, `Meets`, `card_quot_stableSet`: for `x ∈ Γ(G,H)` and an inner twist `τ`
  with torus transport (`HasTorusTransport`, from Thesis Prop. 6.6.1(ii)),
  `n_τ(x) = w(x) · Σ_{c meets x} |W(T_c)|⁻¹`; `meets_refl_iff`: the classes meeting `x` form a stable
  class of tori.
* `commute_of_commute_specP_of_fixes`, `GGPData.mem_torusOf_of_specP`: `S_x(F) ⊆ P(T_x(F))` (an
  element whose image commutes with `P(x)` and fixes `W'_x` commutes with `x`: Steinberg's
  description, with `det P(g)|_{W₋₁} = 1` from `det P(g) = 1`).
* `GGPData.exists_regular_movedCent`: a regular element `Z` of the moved Lie centralizer `𝔩_x`:
  `ker (ad Z) = W'_x` and every endomorphism commuting with `ad Z` commutes with `P(x)` (eigen-frame
  over `F̄`, and `F` infinite).
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

/-- `T_{gxg⁻¹} = g T_x g⁻¹` (one inclusion; `torusOf_conj`). -/
theorem conj_mem_torusOf_conj {x t : ↥(GSpin d.QW)} (g : ↥(GSpin d.QW)) (ht : t ∈ d.torusOf x) :
    g * t * g⁻¹ ∈ d.torusOf (g * x * g⁻¹) := by
  have hP : ∀ (a b : ↥(GSpin d.QW)) v, specP d.QW (a * b) v = specP d.QW a (specP d.QW b v) :=
    fun a b v => by rw [map_mul]; rfl
  have hgg : ∀ v, specP d.QW g (specP d.QW g⁻¹ v) = v := fun v => by
    rw [← hP, mul_inv_cancel, map_one]; rfl
  have hgg' : ∀ v, specP d.QW g⁻¹ (specP d.QW g v) = v := fun v => by
    rw [← hP, inv_mul_cancel, map_one]; rfl
  refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, fun w hw => ?_⟩
  · have h := Subgroup.mem_centralizer_singleton_iff.1 ht.1
    calc g * t * g⁻¹ * (g * x * g⁻¹) = g * (t * x) * g⁻¹ := by group
      _ = g * (x * t) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * (g * t * g⁻¹) := by group
  · rw [d.mem_fixedSub_iff] at hw
    have hu : specP d.QW g⁻¹ w ∈ fixedSub x := by
      rw [d.mem_fixedSub_iff]
      calc specP d.QW x (specP d.QW g⁻¹ w)
          = specP d.QW g⁻¹ (specP d.QW (g * x * g⁻¹) w) := by rw [hP, hP, hgg']
        _ = specP d.QW g⁻¹ w := by rw [hw]
    rw [hP, hP, ht.2 _ hu, hgg]

/-- **Tori of conjugates**: `T_{gxg⁻¹} = g T_x g⁻¹`. -/
theorem torusOf_conj (x g : ↥(GSpin d.QW)) :
    d.torusOf (g * x * g⁻¹) = (d.torusOf x).map (MulAut.conj g).toMonoidHom := by
  ext t
  rw [Subgroup.mem_map_equiv]
  change _ ↔ g⁻¹ * t * g⁻¹⁻¹ ∈ _
  constructor
  · intro ht
    have := conj_mem_torusOf_conj g⁻¹ ht
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
  · intro ht
    have := conj_mem_torusOf_conj g ht
    rwa [show g * (g⁻¹ * t * g⁻¹⁻¹) * g⁻¹ = t by group] at this

/-- Semisimplicity is invariant under conjugation by `GSpin(W)(F)` (`isSS_units_conj`). -/
theorem isSS_conj (x g : ↥(GSpin d.QW)) :
    IsSS F (((g * x * g⁻¹ : ↥(GSpin d.QW)) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) ↔
      IsSS F (((x : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW) :=
  isSS_units_conj (g : (CliffordAlgebra d.QW)ˣ) _

/-- Membership in `Γ(G,H)` depends only on semisimplicity and the torus: a semisimple `u`
with `T_u = T_z` for some `z ∈ Γ(G,H)` lies in `Γ(G,H)`. -/
theorem isGammaElt_of_torusOf_eq {z u : ↥(GSpin d.QW)} (hz : d.IsGammaElt z)
    (hu : IsSS F (((u : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW))
    (h : d.torusOf u = d.torusOf z) : d.IsGammaElt u :=
  ⟨hu, h ▸ hz.2.1, h ▸ hz.2.2⟩

/-- `GSpin(W)(F)`-conjugacy of the tori of `Γ(G,H)` is an equivalence relation. -/
theorem torusConj_equivalence : Equivalence d.TorusConj := by
  refine ⟨fun T => ⟨1, ?_⟩, fun {T T'} ⟨g, hg⟩ => ⟨g⁻¹, ?_⟩, fun {T T' T''} ⟨g, hg⟩ ⟨g', hg'⟩ =>
    ⟨g' * g, ?_⟩⟩
  · ext t; simp
  · rw [hg, Subgroup.map_map]
    ext t; simp [MulAut.conj_apply, mul_assoc]
  · rw [hg', hg, Subgroup.map_map]
    congr 1; ext t; simp [MulAut.conj_apply, mul_assoc]

/-- **Conjugating into the representative torus**: for `x ∈ Γ(G,H)` whose torus lies in the class
`c`, some rational conjugate `g x g⁻¹` lies in `Γ(G,H)` and has torus `T_c`. -/
theorem exists_conj_torusOf_eq_out {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) {c : GammaClass d}
    (hc : Quot.mk d.TorusConj ⟨d.torusOf x, x, hx, rfl⟩ = c) :
    ∃ g : ↥(GSpin d.QW), d.IsGammaElt (g * x * g⁻¹) ∧ d.torusOf (g * x * g⁻¹) = (Quot.out c).1 := by
  have h : Quot.mk d.TorusConj ⟨d.torusOf x, x, hx, rfl⟩ = Quot.mk _ (Quot.out c) :=
    hc.trans (Quot.out_eq c).symm
  obtain ⟨g, hg⟩ := torusConj_equivalence.eqvGen_iff.1 (Quot.eqvGen_exact h)
  have hT : d.torusOf (g * x * g⁻¹) = (Quot.out c).1 := by rw [torusOf_conj]; exact hg.symm
  obtain ⟨z, hz, hzT⟩ := (Quot.out c).2
  exact ⟨g, isGammaElt_of_torusOf_eq hz ((isSS_conj x g).2 hx.1) (hT.trans hzT.symm), hT⟩

section Count

variable (Y : Set ↥(GSpin d.QW))

/-- Rational conjugacy on a set `Y` of elements of `GSpin(W)(F)`. -/
def ConjOn (a b : Y) : Prop := ∃ g : ↥(GSpin d.QW), (b : ↥(GSpin d.QW)) = g * a * g⁻¹

/-- `ConjOn Y` is an equivalence relation. -/
theorem conjOn_equivalence : Equivalence (ConjOn Y) := by
  refine ⟨fun a => ⟨1, by simp⟩, fun {a b} ⟨g, hg⟩ => ⟨g⁻¹, by rw [hg]; group⟩,
    fun {a b c} ⟨g, hg⟩ ⟨g', hg'⟩ => ⟨g' * g, by rw [hg', hg]; group⟩⟩

/-- Equal rational classes are conjugate. -/
theorem conjOn_of_mk_eq {a b : Y} (h : Quot.mk (ConjOn Y) a = Quot.mk (ConjOn Y) b) :
    ConjOn Y a b :=
  (conjOn_equivalence Y).eqvGen_iff.1 (Quot.eqvGen_exact h)

variable {Y} (hYΓ : ∀ y ∈ Y, d.IsGammaElt y)

/-- The torus class of an element of `Y ⊆ Γ(G,H)`, on rational conjugacy classes. -/
noncomputable def classOn : Quot (ConjOn Y) → GammaClass d :=
  Quot.lift (fun y => Quot.mk _ ⟨d.torusOf y, y, hYΓ y y.2, rfl⟩) fun a b ⟨g, hg⟩ =>
    Quot.sound ⟨g, by simp only [hg, torusOf_conj]⟩

/-- The elements of `Y` whose torus is the chosen representative of `c`. -/
def fibOn (Y : Set ↥(GSpin d.QW)) (c : GammaClass d) : Set ↥(GSpin d.QW) :=
  {y | y ∈ Y ∧ d.torusOf y = (Quot.out c).1}

variable (hYc : ∀ y ∈ Y, ∀ g : ↥(GSpin d.QW), d.IsGammaElt (g * y * g⁻¹) → g * y * g⁻¹ ∈ Y)
include hYΓ hYc

/-- Every rational class of `Y` over `c` meets `fibOn c`. -/
theorem exists_fibOn_of_classOn {c : GammaClass d} (q : Quot (ConjOn Y)) (hq : classOn hYΓ q = c) :
    ∃ y : Y, (y : ↥(GSpin d.QW)) ∈ fibOn Y c ∧ Quot.mk _ y = q := by
  induction q using Quot.ind with
  | mk y =>
  obtain ⟨g, hΓ, hT⟩ := exists_conj_torusOf_eq_out (hYΓ y y.2) hq
  exact ⟨⟨g * y * g⁻¹, hYc y y.2 g hΓ⟩, ⟨hYc y y.2 g hΓ, hT⟩, Quot.sound ⟨g⁻¹, by group⟩⟩

/-- The map from `fibOn Y c` to the rational classes over `c`. -/
noncomputable def fibToClass (c : GammaClass d) (y : fibOn Y c) :
    {q : Quot (ConjOn Y) // classOn hYΓ q = c} :=
  ⟨Quot.mk _ ⟨y, y.2.1⟩, by
    change Quot.mk d.TorusConj ⟨d.torusOf y, y, hYΓ y y.2.1, rfl⟩ = c
    exact (congrArg (Quot.mk d.TorusConj) (Subtype.ext y.2.2)).trans
      (Quot.out_eq (c : Quot d.TorusConj))⟩

/-- `fibToClass` is onto (`exists_fibOn_of_classOn`). -/
theorem fibToClass_surjective (c : GammaClass d) : Function.Surjective (fibToClass hYΓ (Y := Y) c) := by
  rintro ⟨q, hq⟩
  obtain ⟨y, hy, rfl⟩ := exists_fibOn_of_classOn hYΓ hYc q hq
  exact ⟨⟨y, hy⟩, rfl⟩

/-- **Orbit count over one torus class**: the rational classes of `Y` over `c`, times `|W(T_c)|`,
number the elements of `Y` with torus `T_c` (`N(T_c)` acts on them by conjugation, freely modulo
`Z(T_c)`: `commute_torusOf_of_commute`). -/
theorem card_classOn_mul_weylCard (c : GammaClass d) (hfin : (fibOn Y c).Finite) :
    Nat.card {q : Quot (ConjOn Y) // classOn hYΓ q = c} * weylCard d c =
      Nat.card (fibOn Y c) := by
  classical
  set T := (Quot.out c).1 with hT
  have : Finite (fibOn Y c) := hfin.to_subtype
  have : Finite {q : Quot (ConjOn Y) // classOn hYΓ q = c} :=
    Finite.of_surjective _ (fibToClass_surjective hYΓ hYc c)
  let _ : Fintype {q : Quot (ConjOn Y) // classOn hYΓ q = c} := Fintype.ofFinite _
  -- each fibre of `fibToClass` is `N(T)/Z(T)`
  have hfib : ∀ q, Nat.card {y // fibToClass hYΓ c y = q} = weylCard d c := by
    intro q
    obtain ⟨y₀, rfl⟩ := fibToClass_surjective hYΓ hYc c q
    have hy₀Γ := hYΓ _ y₀.2.1
    have hy₀T : d.torusOf y₀ = T := y₀.2.2
    let N := Subgroup.normalizer (T : Set ↥(GSpin d.QW))
    let ψ0 : N → {y // fibToClass hYΓ c y = fibToClass hYΓ c y₀} := fun n =>
      have hT : d.torusOf (n * y₀ * (n : ↥(GSpin d.QW))⁻¹) = T := by
        rw [torusOf_conj, hy₀T]; exact Subgroup.mem_normalizer_iff_map_conj_eq.1 n.2
      ⟨⟨n * y₀ * (n : ↥(GSpin d.QW))⁻¹, hYc _ y₀.2.1 n (isGammaElt_of_torusOf_eq hy₀Γ
        ((isSS_conj _ _).2 hy₀Γ.1) (hT.trans hy₀T.symm)), hT⟩,
        Subtype.ext (Quot.sound ⟨(n : ↥(GSpin d.QW))⁻¹, by simp [mul_assoc]⟩)⟩
    have hcomm : ∀ a b : N, ψ0 a = ψ0 b ↔
        (a : ↥(GSpin d.QW))⁻¹ * b ∈ Subgroup.centralizer (T : Set ↥(GSpin d.QW)) := by
      intro a b
      constructor
      · intro hab
        have h : (a : ↥(GSpin d.QW)) * y₀ * (a : ↥(GSpin d.QW))⁻¹ =
            (b : ↥(GSpin d.QW)) * y₀ * (b : ↥(GSpin d.QW))⁻¹ :=
          congrArg (fun z => ((z.1 : fibOn Y c) : ↥(GSpin d.QW))) hab
        have hc : Commute ((a : ↥(GSpin d.QW))⁻¹ * b) (y₀ : ↥(GSpin d.QW)) := by
          change _ * _ = _ * _
          calc ((a : ↥(GSpin d.QW))⁻¹ * b) * y₀ =
              (a : ↥(GSpin d.QW))⁻¹ * (b * y₀ * (b : ↥(GSpin d.QW))⁻¹) * b := by group
            _ = y₀ * ((a : ↥(GSpin d.QW))⁻¹ * b) := by rw [← h]; group
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        rw [← hy₀T] at ht
        exact ((commute_torusOf_of_commute hy₀Γ hc ht).eq).symm
      · intro hab
        rw [Subgroup.mem_centralizer_iff] at hab
        have hc := hab y₀ (hy₀T ▸ d.self_mem_torusOf y₀)
        apply Subtype.ext; apply Subtype.ext
        change (a : ↥(GSpin d.QW)) * y₀ * (a : ↥(GSpin d.QW))⁻¹ =
          (b : ↥(GSpin d.QW)) * y₀ * (b : ↥(GSpin d.QW))⁻¹
        calc (a : ↥(GSpin d.QW)) * y₀ * (a : ↥(GSpin d.QW))⁻¹ =
            a * (y₀ * ((a : ↥(GSpin d.QW))⁻¹ * b)) * (b : ↥(GSpin d.QW))⁻¹ := by group
          _ = a * (((a : ↥(GSpin d.QW))⁻¹ * b) * y₀) * (b : ↥(GSpin d.QW))⁻¹ := by rw [hc]
          _ = _ := by group
    let ψ : N ⧸ (Subgroup.centralizer (T : Set ↥(GSpin d.QW))).subgroupOf N →
        {y // fibToClass hYΓ c y = fibToClass hYΓ c y₀} :=
      Quotient.lift ψ0 fun a b hab => (hcomm a b).2
        (by have := QuotientGroup.leftRel_apply.mp hab; rwa [Subgroup.mem_subgroupOf] at this)
    have hψ : Function.Bijective ψ := by
      refine ⟨fun a b hab => ?_, fun y => ?_⟩
      · induction a using Quotient.inductionOn
        induction b using Quotient.inductionOn
        exact Quotient.sound (QuotientGroup.leftRel_apply.mpr (by
          rw [Subgroup.mem_subgroupOf]; exact (hcomm _ _).1 hab))
      · obtain ⟨⟨y, hyY, hyT⟩, hy⟩ := y
        have hq := congrArg Subtype.val hy
        obtain ⟨g, hg⟩ := conjOn_of_mk_eq Y hq.symm
        have hgN : g ∈ N := Subgroup.mem_normalizer_iff_map_conj_eq.2 (by
          rw [← hy₀T]
          change (d.torusOf y₀).map (MulAut.conj g).toMonoidHom = d.torusOf y₀
          rw [← torusOf_conj]
          change d.torusOf (g * y₀ * g⁻¹) = d.torusOf y₀
          rw [← hg, hy₀T]; exact hyT)
        refine ⟨Quotient.mk _ ⟨g, hgN⟩, Subtype.ext (Subtype.ext ?_)⟩
        exact hg.symm
    rw [← Nat.card_congr (Equiv.ofBijective ψ hψ)]
    rfl
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (fibToClass hYΓ (Y := Y) c)), Nat.card_sigma]
  simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

/-- **The orbit count**: for `Y ⊆ Γ(G,H)` stable under rational conjugation with each `fibOn Y c`
finite, the number of rational classes of `Y` is `Σ_c |fibOn Y c| / |W(T_c)|`. -/
theorem card_quot_conjOn (hfin : ∀ c, (fibOn Y c).Finite) :
    (Nat.card (Quot (ConjOn Y)) : ℚ) =
      ∑' c : GammaClass d, (Nat.card (fibOn Y c) : ℚ) / weylCard d c := by
  classical
  have := finite_gammaClass d
  let _ : Fintype (GammaClass d) := Fintype.ofFinite _
  have hfinq : ∀ c, Finite {q : Quot (ConjOn Y) // classOn hYΓ q = c} := fun c =>
    have : Finite (fibOn Y c) := (hfin c).to_subtype
    Finite.of_surjective _ (fibToClass_surjective hYΓ hYc c)
  rw [tsum_fintype, ← Nat.card_congr (Equiv.sigmaFiberEquiv (classOn hYΓ (Y := Y))),
    Nat.card_sigma, Nat.cast_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hW : (weylCard d c : ℚ) ≠ 0 := by
    obtain ⟨x, hx, hxT⟩ := (Quot.out c).2
    have := weylCardOf_pos hx
    rw [hxT] at this
    exact_mod_cast this.ne'
  rw [eq_div_iff hW, ← card_classOn_mul_weylCard hYΓ hYc c (hfin c)]
  push_cast; ring

end Count

section StableCount

variable {d : GGPData F} (τ : InnerTwist d.QW)

/-- The elements `y ∈ Γ(G_τ,H_τ)` strongly stably conjugate to `x ∈ GSpin(W)(F)` through `τ`
(for `τ = τ_α` this is `stableFiber`, Thesis §6.7). -/
def stableSet (x : ↥(GSpin d.QW)) : Set ↥(GSpin (d.twist τ).QW) :=
  {y | (d.twist τ).IsGammaElt y ∧ d.StronglyStablyConjW τ x y}

/-- `w(x)`: the number of `t ∈ T_{x,♮}` strongly stably conjugate to `x` in `G`. -/
noncomputable def stableWeight (x : ↥(GSpin d.QW)) : ℕ :=
  Nat.card {t : ↥(d.torusOf x) // d.IsGammaElt t ∧ d.torusOf t = d.torusOf x ∧
    d.StronglyStablyConjW d.reflTwist x (t : ↥(GSpin d.QW))}

/-- The torus class `c` of `Γ(G_τ,H_τ)` meets the stable class of `x`: some `y` with `T_y = T_c` is
strongly stably conjugate to `x`. -/
def Meets (x : ↥(GSpin d.QW)) (c : GammaClass (d.twist τ)) : Prop :=
  (fibOn (stableSet τ x) c).Nonempty

/-- **Torus transport** (the part of Thesis Prop. 6.6.1(ii) used for counting): if `x ∼ y`
through `τ`, there is an isomorphism `e : T_x(F) ≃ T_y(F)` matching `T_{x,♮}` with `T_{y,♮}` with
`t ∼ e(t)` on `T_{x,♮}`. -/
def HasTorusTransport : Prop :=
  ∀ (x : ↥(GSpin d.QW)) (y : ↥(GSpin (d.twist τ).QW)), d.IsGammaElt x →
    (d.twist τ).IsGammaElt y → d.StronglyStablyConjW τ x y →
    ∃ e : ↥(d.torusOf x) ≃* ↥((d.twist τ).torusOf y),
      (∀ t : ↥(d.torusOf x), (d.IsGammaElt t ∧ d.torusOf t = d.torusOf x ↔
        (d.twist τ).IsGammaElt (e t) ∧ (d.twist τ).torusOf (e t) = (d.twist τ).torusOf y)) ∧
      (∀ t : ↥(d.torusOf x), d.IsGammaElt t → d.torusOf t = d.torusOf x →
        d.StronglyStablyConjW τ t (e t))

theorem stableSet_conj (x : ↥(GSpin d.QW)) : ∀ y ∈ stableSet τ x, ∀ g : ↥(GSpin (d.twist τ).QW),
    (d.twist τ).IsGammaElt (g * y * g⁻¹) → g * y * g⁻¹ ∈ stableSet τ x :=
  fun _ hy g hg => ⟨hg, d.stronglyStablyConjW_conj_right τ hy.2 g⟩

/-- Two elements strongly stably conjugate to the same `x` are conjugate over `F̄`. -/
theorem exists_bc_conj_of_stronglyStablyConjW {x : ↥(GSpin d.QW)} {y y' : ↥(GSpin (d.twist τ).QW)}
    (hy : d.StronglyStablyConjW τ x y) (hy' : d.StronglyStablyConjW τ x y') :
    ∃ g : ↥(GSpin ((d.twist τ).QW.baseChange Kb)),
      g * bcGSpin (d.twist τ).QW y * g⁻¹ = bcGSpin (d.twist τ).QW y' := by
  obtain ⟨⟨g₁, hg₁, e₁, -⟩, -⟩ := hy
  obtain ⟨⟨g₂, hg₂, e₂, -⟩, -⟩ := hy'
  have e₁' : g₁ * cliffUnits τ.φ (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ)) * g₁⁻¹ =
      bcUnits τ.Q' (y : (CliffordAlgebra τ.Q')ˣ) := e₁
  have e₂' : g₂ * cliffUnits τ.φ (bcUnits d.QW (x : (CliffordAlgebra d.QW)ˣ)) * g₂⁻¹ =
      bcUnits τ.Q' (y' : (CliffordAlgebra τ.Q')ˣ) := e₂
  refine ⟨⟨g₂ * g₁⁻¹, (GSpin _).mul_mem hg₂ ((GSpin _).inv_mem hg₁)⟩, Subtype.ext ?_⟩
  change g₂ * g₁⁻¹ * bcUnits τ.Q' (y : (CliffordAlgebra τ.Q')ˣ) * (g₂ * g₁⁻¹)⁻¹ =
    bcUnits τ.Q' (y' : (CliffordAlgebra τ.Q')ˣ)
  rw [← e₁', ← e₂']
  group

/-- The fibres of `stableSet τ x` over the torus classes are finite (`finite_conj_torusOf`). -/
theorem finite_fibOn_stableSet (x : ↥(GSpin d.QW)) (c : GammaClass (d.twist τ)) :
    (fibOn (stableSet τ x) c).Finite := by
  rcases (fibOn (stableSet τ x) c).eq_empty_or_nonempty with h | ⟨y₀, hy₀, hy₀T⟩
  · rw [h]; exact Set.finite_empty
  refine (finite_conj_torusOf hy₀.1).subset fun y ⟨hy, hyT⟩ => ⟨?_, ?_⟩
  · rw [hy₀T, ← hyT]; exact (d.twist τ).self_mem_torusOf y
  · exact exists_bc_conj_of_stronglyStablyConjW τ hy₀.2 hy.2

variable {τ}

/-- **The fibres have size `w(x)`**: if the class `c` meets the stable class of `x ∈ Γ(G,H)`, then
`|{y ∼ x : T_y = T_c}| = w(x)` (transport `T_x ≃ T_c` from any such `y`). -/
theorem card_fibOn_stableSet (hT : HasTorusTransport τ) {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    {c : GammaClass (d.twist τ)} {y₀ : ↥(GSpin (d.twist τ).QW)}
    (hy₀ : y₀ ∈ fibOn (stableSet τ x) c) :
    Nat.card (fibOn (stableSet τ x) c) = stableWeight x := by
  obtain ⟨e, he, het⟩ := hT x y₀ hx hy₀.1.1 hy₀.1.2
  let Φ : {t : ↥(d.torusOf x) // d.IsGammaElt t ∧ d.torusOf t = d.torusOf x ∧
      d.StronglyStablyConjW d.reflTwist x (t : ↥(GSpin d.QW))} → fibOn (stableSet τ x) c := fun t =>
    ⟨e t, ⟨((he t).1 ⟨t.2.1, t.2.2.1⟩).1,
      d.stronglyStablyConjW_trans_refl τ t.2.2.2 (het t t.2.1 t.2.2.1)⟩,
      ((he t).1 ⟨t.2.1, t.2.2.1⟩).2.trans hy₀.2⟩
  have hΦ : Function.Bijective Φ := by
    refine ⟨fun a b hab => ?_, fun y => ?_⟩
    · have h1 : ((e a : ↥((d.twist τ).torusOf y₀)) : ↥(GSpin (d.twist τ).QW)) = e b :=
        congrArg (fun z : fibOn (stableSet τ x) c => (z : ↥(GSpin (d.twist τ).QW))) hab
      exact Subtype.ext (e.injective (Subtype.ext h1))
    · obtain ⟨y, ⟨hyΓ, hxy⟩, hyT⟩ := y
      have hmem : y ∈ (d.twist τ).torusOf y₀ := by
        rw [hy₀.2, ← hyT]; exact (d.twist τ).self_mem_torusOf y
      set t := e.symm ⟨y, hmem⟩ with ht
      have het' : e t = ⟨y, hmem⟩ := by rw [ht, MulEquiv.apply_symm_apply]
      have hT' : d.IsGammaElt t ∧ d.torusOf t = d.torusOf x := (he t).2 (by
        rw [het']; exact ⟨hyΓ, hyT.trans hy₀.2.symm⟩)
      have hts : d.StronglyStablyConjW τ t y := by
        have := het t hT'.1 hT'.2; rwa [het'] at this
      refine ⟨⟨t, hT'.1, hT'.2, d.stronglyStablyConjW_refl_of_common τ hxy hts⟩, ?_⟩
      apply Subtype.ext
      change ((e t : ↥((d.twist τ).torusOf y₀)) : ↥(GSpin (d.twist τ).QW)) = y
      rw [het']
  exact (Nat.card_congr (Equiv.ofBijective Φ hΦ)).symm

/-- `w(x) ≥ 1` for `x ∈ Γ(G,H)` (`x` itself counts; the set is finite by `finite_conj_torusOf`). -/
theorem stableWeight_pos {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) : 0 < stableWeight x := by
  have := (finite_conj_torusOf hx).to_subtype
  have hfin : Finite {t : ↥(d.torusOf x) // d.IsGammaElt t ∧ d.torusOf t = d.torusOf x ∧
      d.StronglyStablyConjW d.reflTwist x (t : ↥(GSpin d.QW))} :=
    Finite.of_injective (β := {t : ↥(GSpin d.QW) | t ∈ d.torusOf x ∧
      ∃ g : ↥(GSpin (d.QW.baseChange Kb)), g * bcGSpin d.QW x * g⁻¹ = bcGSpin d.QW t})
      (fun t => ⟨t.1, t.1.2, exists_bc_conj_of_stronglyStablyConjW d.reflTwist
        (d.stronglyStablyConjW_refl_self x) t.2.2.2⟩)
      (fun a b h => by
        have h' : (a.1 : ↥(GSpin d.QW)) = b.1 :=
          congrArg (fun z : {t : ↥(GSpin d.QW) | t ∈ d.torusOf x ∧ ∃ g : ↥(GSpin (d.QW.baseChange Kb)),
            g * bcGSpin d.QW x * g⁻¹ = bcGSpin d.QW t} => (z : ↥(GSpin d.QW))) h
        exact Subtype.ext (Subtype.ext h'))
  have : Nonempty {t : ↥(d.torusOf x) // d.IsGammaElt t ∧ d.torusOf t = d.torusOf x ∧
      d.StronglyStablyConjW d.reflTwist x (t : ↥(GSpin d.QW))} :=
    ⟨⟨⟨x, d.self_mem_torusOf x⟩, hx, rfl, d.stronglyStablyConjW_refl_self x⟩⟩
  exact Nat.card_pos

open Classical in
/-- **The count `n_τ(x) = w(x) · Σ_{c meets x} |W(T_c)|⁻¹`** (`card_quot_conjOn`, with every
meeting fibre of size `w(x)`, `card_fibOn_stableSet`). -/
theorem card_quot_stableSet (hT : HasTorusTransport τ) {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) :
    (Nat.card (Quot (ConjOn (stableSet τ x))) : ℚ) =
      stableWeight x * ∑' c : GammaClass (d.twist τ),
        (if Meets τ x c then 1 else 0) / (weylCard (d.twist τ) c : ℚ) := by
  rw [card_quot_conjOn (Y := stableSet τ x) (fun y hy => hy.1) (stableSet_conj τ x)
      (finite_fibOn_stableSet τ x),
    ← tsum_mul_left]
  refine tsum_congr fun c => ?_
  by_cases h : Meets τ x c
  · obtain ⟨y₀, hy₀⟩ := h
    rw [card_fibOn_stableSet hT hx hy₀, if_pos ⟨y₀, hy₀⟩]
    ring
  · rw [if_neg h, Set.not_nonempty_iff_eq_empty.1 h]
    simp

/-- `Meets` depends only on the torus of `x`: if `T_u = T_z` (both in `Γ(G,H)`), a class meeting
the stable class of `z` meets that of `u` (transport `T_z ≃ T_y` sends `u` into `T_{y,♮}`). -/
theorem meets_of_torusOf_eq (hT : HasTorusTransport τ) {z u : ↥(GSpin d.QW)}
    (hz : d.IsGammaElt z) (hu : d.IsGammaElt u) (h : d.torusOf u = d.torusOf z)
    {c : GammaClass (d.twist τ)} (hm : Meets τ z c) : Meets τ u c := by
  obtain ⟨y, ⟨hyΓ, hzy⟩, hyT⟩ := hm
  obtain ⟨e, he, het⟩ := hT z y hz hyΓ hzy
  have hu' : u ∈ d.torusOf z := h ▸ d.self_mem_torusOf u
  obtain ⟨hΓ, hT'⟩ := (he ⟨u, hu'⟩).1 ⟨hu, h⟩
  exact ⟨e ⟨u, hu'⟩, ⟨hΓ, het ⟨u, hu'⟩ hu h⟩, hT'.trans hyT⟩

/-- `Meets` is invariant under rational conjugation of `x`. -/
theorem meets_conj {x : ↥(GSpin d.QW)} (g : ↥(GSpin d.QW)) {c : GammaClass (d.twist τ)}
    (hm : Meets τ x c) : Meets τ (g * x * g⁻¹) c := by
  obtain ⟨y, ⟨hyΓ, hxy⟩, hyT⟩ := hm
  have h1 := d.stronglyStablyConjW_refl_conj (g * x * g⁻¹) g⁻¹
  rw [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at h1
  exact ⟨y, ⟨hyΓ, d.stronglyStablyConjW_trans_refl τ h1 hxy⟩, hyT⟩

/-- **Stable classes of tori**: if `c` meets the stable class of `x`, then a torus class `c₂` of
`Γ(G,H)` with generator `x₂` meets the stable class of `x` (in `G`) iff `c` meets that of `x₂`. -/
theorem meets_refl_iff (hT : HasTorusTransport τ) {x x₂ : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    (hx₂ : d.IsGammaElt x₂) {c₂ : GammaClass d} (hx₂T : d.torusOf x₂ = (Quot.out c₂).1)
    {c : GammaClass (d.twist τ)} (hm : Meets τ x c) :
    Meets d.reflTwist x (c₂ : GammaClass (d.twist d.reflTwist)) ↔ Meets τ x₂ c := by
  obtain ⟨y, ⟨hyΓ, hxy⟩, hyT⟩ := hm
  constructor
  · rintro ⟨s, ⟨hsΓ, hxs⟩, hsT⟩
    have hsx : d.StronglyStablyConjW d.reflTwist s x :=
      d.stronglyStablyConjW_refl_of_common d.reflTwist (d.stronglyStablyConjW_refl_self s) hxs
    have hsy := d.stronglyStablyConjW_trans_refl τ hsx hxy
    exact meets_of_torusOf_eq hT hsΓ hx₂ (hx₂T.trans hsT.symm) ⟨y, ⟨hyΓ, hsy⟩, hyT⟩
  · rintro ⟨y', ⟨hy'Γ, hx₂y'⟩, hy'T⟩
    obtain ⟨e, he, het⟩ := hT x₂ y' hx₂ hy'Γ hx₂y'
    have hmem : y ∈ (d.twist τ).torusOf y' := by
      rw [hy'T, ← hyT]; exact (d.twist τ).self_mem_torusOf y
    set t := e.symm ⟨y, hmem⟩ with ht
    have het' : e t = ⟨y, hmem⟩ := by rw [ht, MulEquiv.apply_symm_apply]
    have hT' : d.IsGammaElt t ∧ d.torusOf t = d.torusOf x₂ := (he t).2 (by
      rw [het']; exact ⟨hyΓ, hyT.trans hy'T.symm⟩)
    have hts : d.StronglyStablyConjW τ t y := by
      have := het t hT'.1 hT'.2; rwa [het'] at this
    exact ⟨(t : ↥(GSpin d.QW)), ⟨hT'.1, d.stronglyStablyConjW_refl_of_common τ hxy hts⟩,
      hT'.2.trans hx₂T⟩

end StableCount

end GGPData

section SteinbergFix

variable {K : Type*} [Field K] [CharZero K] [Invertible (2 : K)]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

/-- **An element whose image commutes with `P(x)` and fixes `W'_x` commutes with `x`**, for `x`
semisimple: in Steinberg's description (`steinberg_centralizer_connected`) the determinant on
`W'_x` is `1` since `P(g)` is the identity there, and so the determinant on `W₋₁` is `1` since
`det P(g) = 1` is the product of the two (`det_eq_det_one_mul_det_neg_one_of_charZero`). -/
theorem commute_of_commute_specP_of_fixes (hQ : IsNondeg Q) (x : GSpin Q)
    (hx : Module.End.IsSemisimple
      (LinearMap.mulLeft K ((x : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)))
    {g : GSpin Q} (hc : Commute (specP Q g) (specP Q x))
    (hfix : ∀ v ∈ fixedSub x, specP Q g v = v) : Commute g x := by
  have hss := isSemisimple_specP_of_isSS Q x hx
  have hB : (bform Q).IsSymm := ⟨fun u v => bform_comm Q u v⟩
  have hdet := IsomCent.det_eq_det_one_mul_det_neg_one_of_charZero hB hQ
    (Steinberg.isIsom_specP x) hss (Steinberg.isIsom_specP g) (Steinberg.commute_toLinearMap hc)
  have hone : ∀ (E : Submodule K V) (hE : ∀ v ∈ E, specP Q g v = v)
      (h : Set.MapsTo (specP Q g : V →ₗ[K] V) E E),
      LinearMap.det ((specP Q g : V →ₗ[K] V).restrict h) = 1 := by
    intro E hE h
    have : (specP Q g : V →ₗ[K] V).restrict h = LinearMap.id :=
      LinearMap.ext fun v => Subtype.ext (hE v v.2)
    rw [this, LinearMap.det_id]
  have hE1 : ∀ v ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) 1, specP Q g v = v :=
    fun v hv => hfix v (by rw [Steinberg.fixedSub_eq_eigenspace]; exact hv)
  have h1 : LinearMap.det ((specP Q g : V →ₗ[K] V).restrict
      (IsomCent.mapsTo_eigenspace_of_commute (Steinberg.commute_toLinearMap hc) 1)) = 1 :=
    hone _ hE1 _
  rw [h1, one_mul, det_specP] at hdet
  have h := (Steinberg.commute_iff hQ x hx g).mpr ⟨hc,
    ⟨mapsTo_fixedSub_of_commute hc, hone _ hfix _⟩,
    ⟨mapsTo_negFixedSub_of_commute hc,
      (Steinberg.det_restrict_eq rfl (Steinberg.negFixedSub_eq_eigenspace x) _ _).trans
        hdet.symm⟩⟩
  exact Subtype.ext h

end SteinbergFix

namespace GGPData

section Regular

variable (d : GGPData F)

/-- **`S_x(F) ⊆ P(T_x(F))`**: for semisimple `x`, an element `g ∈ GSpin(W)(F)` with `P(g)`
commuting with `P(x)` and fixing `W'_x` pointwise lies in `T_x(F)`
(`commute_of_commute_specP_of_fixes`). -/
theorem mem_torusOf_of_specP {x : ↥(GSpin d.QW)}
    (hx : IsSS F (((x : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW)) {g : ↥(GSpin d.QW)}
    (hc : Commute (specP d.QW g) (specP d.QW x)) (hfix : ∀ v ∈ fixedSub x, specP d.QW g v = v) :
    g ∈ d.torusOf x :=
  ⟨Subgroup.mem_centralizer_singleton_iff.mpr
    (commute_of_commute_specP_of_fixes d.nondeg x hx hc hfix).eq, hfix⟩


open scoped TensorProduct


set_option hygiene false in
local notation "Wb" => AlgebraicClosure F ⊗[F] (Fin d.m → F)

set_option hygiene false in
local notation "Qb" => d.QW.baseChange (AlgebraicClosure F)

/-- **A regular element of the moved part of the Lie centralizer** (own work): for `x ∈ Γ(G,H)`
there is `Z ∈ gspin(W)` commuting with `x` with `ker (ad Z) = W'_x`, such that every endomorphism of
`W` commuting with `ad Z` commutes with `P(x)`.

Over `F̄`, `P(x)` is diagonal in a hyperbolic eigen-frame `eᵢ, fᵢ` with complement `W'_x ⊗ F̄`
(`exists_hypFrame_torusFbar`).  The moved Lie centralizer is abelian
(`lieAbelian_specP_baseChange`) and contains the regular diagonal map
`D = diag(i + 1 on eᵢ, −(i + 1) on fᵢ, 0 on W'_x)` (`IsHypFrame.exists_skew_diag`), so every
`(ad Z)_{F̄}`, `Z ∈ 𝔩_x`, is diagonal in the frame, `αᵢ(Z)` on `eᵢ` and `−αᵢ(Z)` on `fᵢ`.  The
functionals `αᵢ`, `αᵢ − αⱼ` (`i ≠ j`), `αᵢ + αⱼ` are nonzero at `D`, so some `Z ∈ 𝔩_x` avoids all
their kernels (`exists_movedCent_forall_ne_zero`).  Then `(ad Z)_{F̄}` is a regular frame-diagonal
map, and the conclusions follow from `IsHypFrame.mem_of_diag` and
`IsHypFrame.commute_of_commute_diag`. -/
theorem exists_regular_movedCent {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x) :
    ∃ Z ∈ gspin d.QW,
      ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) * Z =
        Z * ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) ∧
      LinearMap.ker (adV d.QW Z) = fixedSub x ∧
      ∀ s : Module.End F (Fin d.m → F), Commute s (adV d.QW Z) →
        Commute s (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) := by
  classical
  obtain ⟨n, e, f, hF, hT⟩ := exists_hypFrame_torusFbar x hx
  have hPw : ∀ w, specP Qb (bcGSpin d.QW x) w =
      (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb w := fun w =>
    LinearMap.congr_fun (specP_bcGSpin d.QW x) w
  rw [specP_bcGSpin] at hF hT
  -- `P(x)_{F̄}` is diagonal in the frame
  have hxT : specP Qb (bcGSpin d.QW x) ∈ hypTorus (Module.End.eigenspace
      ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb) 1) e f := by
    rw [← hT]; exact ⟨_, bcGSpin_mem_torusFbar (d.self_mem_torusOf x), rfl⟩
  obtain ⟨hxW, t, hxt⟩ := hxT
  generalize hPb : (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb = Pb
    at hF hPw hxW
  have hPW : ∀ w ∈ Module.End.eigenspace Pb 1, Pb w = (1 : Kb) • w := fun w hw => by
    rw [← hPw, hxW w hw, one_smul]
  have hPe : ∀ i, Pb (e i) = (t i : Kb) • e i := fun i => by rw [← hPw, (hxt i).1]
  have hPf : ∀ i, Pb (f i) = (((t i)⁻¹ : Kbˣ) : Kb) • f i := fun i => by rw [← hPw, (hxt i).2]
  -- the regular diagonal element `D`
  have ha0 : ∀ i : Fin n, (((i : ℕ) + 1 : ℕ) : Kb) ≠ 0 := fun i =>
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _)
  have hainj : Function.Injective fun i : Fin n => (((i : ℕ) + 1 : ℕ) : Kb) := fun i j hij => by
    simp only [Nat.cast_inj, add_left_inj] at hij; exact Fin.ext hij
  have hapos : ∀ i j : Fin n, (((i : ℕ) + 1 : ℕ) : Kb) + (((j : ℕ) + 1 : ℕ) : Kb) ≠ 0 :=
    fun i j => by rw [← Nat.cast_add]; exact Nat.cast_ne_zero.mpr (by omega)
  obtain ⟨D, hDW, hDe, hDf, hDs⟩ := hF.exists_skew_diag fun i => (((i : ℕ) + 1 : ℕ) : Kb)
  have hsD : IsomCent.IsSkew (bform Qb) D := (isSkew_associated_iff _ _).mpr hDs
  have hcD : Commute Pb D := hF.commute_of_diag hPW hPe hPf hDW hDe hDf
  have hfD : ∀ z ∈ Module.End.eigenspace Pb 1, D z = 0 := fun z hz => by
    rw [hDW z hz, zero_smul]
  have hL : IsomCent.LieAbelian (bform Qb) Pb := hPb ▸ lieAbelian_specP_baseChange x hx
  have hneg : ∀ i : Fin n, -(((i : ℕ) + 1 : ℕ) : Kb) ≠ 0 := fun i => neg_ne_zero.mpr (ha0 i)
  have hnegi : Function.Injective fun i : Fin n => -(((i : ℕ) + 1 : ℕ) : Kb) := fun i j h =>
    hainj (neg_inj.mp h)
  have hab : ∀ i j : Fin n, (((i : ℕ) + 1 : ℕ) : Kb) ≠ -(((j : ℕ) + 1 : ℕ) : Kb) :=
    fun i j h => hapos i j (by rw [h, neg_add_cancel])
  -- a skew map commuting with `P(x)_{F̄}` and killing `W'_x ⊗ F̄` is diagonal in the frame
  have hdiag : ∀ Y : Module.End Kb Wb, IsomCent.IsSkew (bform Qb) Y → Commute Pb Y →
      (∀ z ∈ Module.End.eigenspace Pb 1, Y z = 0) →
      (∀ i, Y (e i) = QuadraticMap.polar Qb (Y (e i)) (f i) • e i) ∧
      ∀ i, Y (f i) = (-QuadraticMap.polar Qb (Y (e i)) (f i)) • f i := by
    intro Y hsY hcY hfY
    have hcom : Commute D Y := (hL _ _ hsY hsD hcY hcD hfY hfD).symm
    have he := hF.eq_smul_e_of_commute_diag hDW hDe hDf ha0 hainj hab hcom
    have hf := hF.eq_smul_f_of_commute_diag hDW hDe hDf hneg hnegi hab hcom
    refine ⟨he, fun i => ?_⟩
    rw [hf i]
    congr 1
    set c := QuadraticMap.polar Qb (Y (e i)) (f i)
    have h1 : QuadraticMap.polar Qb (f i) (Y (e i)) = c := by
      calc QuadraticMap.polar Qb (f i) (Y (e i)) = QuadraticMap.polar Qb (f i) (c • e i) := by
            rw [← he i]
        _ = c := by rw [QuadraticMap.polar_smul_right, hF.polar_fe]; simp
    rw [(isSkew_associated_iff _ _).mp hsY, h1]
  -- the functionals `αᵢ`, `αᵢ − αⱼ`, `αᵢ + αⱼ`
  let β : Fin n → Module.End Kb Wb →ₗ[Kb] Kb := fun i =>
    { toFun := fun Y => QuadraticMap.polar Qb (Y (e i)) (f i)
      map_add' := fun Y Y' => by simp [QuadraticMap.polar_add_left]
      map_smul' := fun c Y => by simp [QuadraticMap.polar_smul_left] }
  have hβ : ∀ i Y, β i Y = QuadraticMap.polar Qb (Y (e i)) (f i) := fun _ _ => rfl
  have hβD : ∀ i, β i D = (((i : ℕ) + 1 : ℕ) : Kb) := fun i => by
    rw [hβ, hDe, QuadraticMap.polar_smul_left, hF.polar_ef]; simp
  let γ : Fin n ⊕ ({p : Fin n × Fin n // p.1 ≠ p.2} ⊕ (Fin n × Fin n)) →
      Module.End Kb Wb →ₗ[Kb] Kb :=
    Sum.elim β (Sum.elim (fun p => β p.1.1 - β p.1.2) (fun p => β p.1 + β p.2))
  have hγD : ∀ k, γ k D ≠ 0 := by
    rintro (i | ⟨⟨i, j⟩, hij⟩ | ⟨i, j⟩)
    · simp only [γ, Sum.elim_inl]; rw [hβD]; exact ha0 i
    · simp only [γ, Sum.elim_inr, Sum.elim_inl, LinearMap.sub_apply]
      rw [hβD, hβD, sub_ne_zero]; exact fun h => hij (hainj h)
    · simp only [γ, Sum.elim_inr, LinearMap.add_apply]
      rw [hβD, hβD]; exact hapos i j
  subst hPb
  obtain ⟨Z, hZ𝔩, hZγ⟩ := d.exists_movedCent_forall_ne_zero x γ fun k =>
    ⟨D, hsD, hcD, hfD, hγD k⟩
  obtain ⟨hsY, hcY, hYW0⟩ := d.movedCent_baseChange_props x hZ𝔩
  obtain ⟨hZe, hZf⟩ := hdiag _ hsY hcY hYW0
  set Y := (adV d.QW (Z : CliffordAlgebra d.QW)).baseChange Kb with hY
  set α : Fin n → Kb := fun i => QuadraticMap.polar Qb (Y (e i)) (f i) with hα
  have hYW : ∀ w ∈ Module.End.eigenspace
      ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)).baseChange Kb) 1,
      Y w = (0 : Kb) • w := fun w hw => by
    rw [hYW0 w hw, zero_smul]
  have hα0 : ∀ i, α i ≠ 0 := fun i => hZγ (.inl i)
  have hαn : ∀ i, -α i ≠ 0 := fun i => neg_ne_zero.mpr (hα0 i)
  have hαinj : Function.Injective α := fun i j h => by
    by_contra hij
    refine hZγ (.inr (.inl ⟨(i, j), hij⟩)) ?_
    simp only [γ, Sum.elim_inr, Sum.elim_inl, LinearMap.sub_apply, hβ]
    exact sub_eq_zero.mpr h
  have hαninj : Function.Injective fun i => -α i := fun i j h => hαinj (neg_inj.mp h)
  have hαab : ∀ i j, α i ≠ -α j := fun i j h => by
    refine hZγ (.inr (.inr (i, j))) ?_
    simp only [γ, Sum.elim_inr, LinearMap.add_apply, hβ]
    change α i + α j = 0
    rw [h, neg_add_cancel]
  obtain ⟨hcx, hfx⟩ := mem_ker_movedCentMap hZ𝔩
  refine ⟨_, Z.2, hcx, ?_, fun s hs => ?_⟩
  · ext v
    constructor
    · intro hv
      have h0 : Y (1 ⊗ₜ v) = (0 : Kb) • (1 ⊗ₜ v) := by
        rw [hY, LinearMap.baseChange_tmul, LinearMap.mem_ker.mp hv, TensorProduct.tmul_zero,
          zero_smul]
      have hmem := hF.mem_of_diag hYW hZe hZf hα0 hαn h0
      rw [Module.End.mem_eigenspace_iff, one_smul, LinearMap.baseChange_tmul] at hmem
      exact (d.mem_fixedSub_iff).mpr (Module.Flat.tensorProduct_mk_injective F _ Kb hmem)
    · intro hv
      rw [LinearMap.mem_ker, adV_apply, hfx v hv, sub_self, map_zero]
  · have hsb : Commute Y (s.baseChange Kb) := by
      rw [Commute, SemiconjBy, hY, ← LinearMap.baseChange_mul, ← LinearMap.baseChange_mul,
        hs.eq]
    have := hF.commute_of_commute_diag hYW hZe hZf hα0 hαn hαinj hαninj hαab hsb hPW hPe hPf
    exact (commute_of_commute_baseChange this).symm

end Regular

end GGPData

end GSpinGGP
