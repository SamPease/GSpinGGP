/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.HarishChandra
import GSpinGGP.Foundations.EvaluationSpan

/-!
# Separating the regular germs by finitely many points

Ingredients for the bound on `(D^G)^{1/2} c_{θ,O}` (Thesis Prop 12.1.1(i), proof of (12.1.2)).
At a semisimple `x ∈ G(F)`:

* `nilReg_coeff_eq_zero_of_sum_jHat_eq_zero`: the functions `ĵ(O, ·)`, `O ∈ Nil_reg(𝔤_x)`, are
  linearly independent modulo the non-regular ones on `ω ∩ 𝔤_{x,reg}(F)` for every neighbourhood
  `ω` of `0`: a vanishing finite combination `∑_O a_O ĵ(O, ·)` there has `a_O = 0` for every regular
  `O`.  This is the uniqueness of local expansions (`germ_unique`) applied to `θ = 0`.
* `exists_finset_bound_nilReg_coeff`: if `Nil_reg(𝔤_x)` is finite, then for each regular `O₀` there
  are finitely many points `X_1, …, X_n ∈ ω ∩ 𝔤_{x,reg}(F)` and a constant `C` with
  `|a_{O₀}| ≤ C · max_j |∑_{O ∈ Nil_reg(𝔤_x)} a_O ĵ(O, X_j)|` for every `a`
  (`exists_bound_coord_of_eval`).  The points depend only on `(G_x, 𝔤_x)`, not on `θ`.
-/

noncomputable section

open Topology Filter

set_option linter.unusedSectionVars false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]
variable (d : GGPData F) (ψ : NontrivialAddChar F)

/-- **Linear independence of the regular `ĵ(O, ·)` near `0`** (Harish-Chandra; BP Astérisque 418
§4.5): at a semisimple `x`, if a finite combination `∑_O a_O ĵ(O, X)` over `O ∈ Nil(𝔤_x)` vanishes
for all `X` in a neighbourhood `ω` of `0` that lie in `𝔤_x` and are regular there, then `a_O = 0`
for every `O ∈ Nil_reg(𝔤_x)`.  The vanishing says that `a` is the coefficient family of a local
expansion of `θ = 0` at `x`, as is `0`; uniqueness (`germ_unique`) gives the claim. -/
theorem nilReg_coeff_eq_zero_of_sum_jHat_eq_zero (x : ↥d.G)
    (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    (a : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) → ℂ)
    (ha : (Function.support a).Finite) {ω : Set d.ambient} (hω : ω ∈ 𝓝 (0 : d.ambient))
    (h : ∀ X ∈ ω, X ∈ lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient) →
      IsRegularSS (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) X →
      ∑ᶠ O, a O * jHat (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))
        d.bilin ψ O X = 0) :
    ∀ O ∈ NilReg (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)),
      a O = 0 := by
  have hexp : HasGermExpansion d.G d.lie d.bilin ψ 0 x a :=
    ⟨ha, ω, hω, fun X hX hXc hXr y _ => (h X hX hXc hXr).symm⟩
  exact germ_unique d ψ 0 x hx a 0 hexp (hasGermExpansion_zero d ψ x)

/-- **Bounding one regular coefficient by finitely many values** (Thesis Prop 12.1.1(i), proof of
(12.1.2)): at a semisimple `x` with `Nil_reg(𝔤_x)` finite, for every neighbourhood `ω` of `0` and
every `O₀ ∈ Nil_reg(𝔤_x)` there are finitely many points `X ∈ ω`, each in `𝔤_x` and regular there,
and a constant `C ≥ 0` such that, for every family `a` and every `M`,
`|∑_{O ∈ Nil_reg(𝔤_x)} a_O ĵ(O, X)| ≤ M` at these points implies `|a_{O₀}| ≤ C M`.
From `nilReg_coeff_eq_zero_of_sum_jHat_eq_zero` and `exists_bound_coord_of_eval`. -/
theorem exists_finset_bound_nilReg_coeff (x : ↥d.G) (hx : IsSS F ((x : d.ambientˣ) : d.ambient))
    (hfin : (NilReg (grpCentralizer d.G x)
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))).Finite)
    {ω : Set d.ambient} (hω : ω ∈ 𝓝 (0 : d.ambient))
    {O₀ : NilOrbit (grpCentralizer d.G x) (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))}
    (hO₀ : O₀ ∈ NilReg (grpCentralizer d.G x)
      (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient))) :
    ∃ (σ : Finset d.ambient) (C : ℝ), 0 ≤ C ∧
      (∀ X ∈ σ, X ∈ ω ∧ X ∈ lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient) ∧
        IsRegularSS (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) X) ∧
      ∀ (a : NilOrbit (grpCentralizer d.G x)
          (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) → ℂ) (M : ℝ),
        (∀ X ∈ σ, ‖∑ O ∈ hfin.toFinset, a O * jHat (grpCentralizer d.G x)
          (lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)) d.bilin ψ O X‖ ≤ M) →
        ‖a O₀‖ ≤ C * M := by
  classical
  let G' := grpCentralizer d.G x
  let 𝔤' := lieCentralizer d.lie ((x : d.ambientˣ) : d.ambient)
  let N := NilReg G' 𝔤'
  let _ : Fintype ↥N := hfin.fintype
  let S := {X : d.ambient // X ∈ ω ∧ X ∈ 𝔤' ∧ IsRegularSS 𝔤' X}
  let f : ↥N → S → ℂ := fun O X => jHat G' 𝔤' d.bilin ψ (O : NilOrbit G' 𝔤') (X : d.ambient)
  -- sums over `N` as a type and as the finset `hfin.toFinset`
  have hsum : ∀ (b : NilOrbit G' 𝔤' → ℂ) (X : d.ambient),
      ∑ O : ↥N, b O * jHat G' 𝔤' d.bilin ψ (O : NilOrbit G' 𝔤') X =
        ∑ O ∈ hfin.toFinset, b O * jHat G' 𝔤' d.bilin ψ O X := fun b X => by
    rw [← Finset.sum_coe_sort hfin.toFinset]
    exact Fintype.sum_equiv (Equiv.subtypeEquivRight fun O => by simp only [Set.Finite.mem_toFinset]; rfl) _ _ fun _ => rfl
  have hf : ∀ a : ↥N → ℂ, (∀ s : S, ∑ i, a i * f i s = 0) → a = 0 := by
    intro a ha
    let a' : NilOrbit G' 𝔤' → ℂ := fun O => if h : O ∈ N then a ⟨O, h⟩ else 0
    have hsupp : Function.support a' ⊆ N := fun O hO => by
      by_contra h
      exact hO (by simp [a', h])
    have ha' : ∀ O : ↥N, a' O = a O := fun O => by simp [a', O.2]
    have hz := nilReg_coeff_eq_zero_of_sum_jHat_eq_zero d ψ x hx a' (hfin.subset hsupp) hω
      (fun X hX hXc hXr => by
        rw [finsum_eq_sum_of_support_subset (s := hfin.toFinset) _ (fun O hO => by
          rw [Set.Finite.coe_toFinset]
          exact hsupp (Function.support_mul_subset_left _ _ hO)), ← hsum]
        simpa [ha'] using ha ⟨X, hX, hXc, hXr⟩)
    funext O
    rw [← ha' O]
    exact hz O O.2
  obtain ⟨σ, C, hC, hbound⟩ := exists_bound_coord_of_eval f hf ⟨O₀, hO₀⟩
  refine ⟨σ.map (Function.Embedding.subtype _), C, hC, fun X hX => ?_, fun a M hM => ?_⟩
  · obtain ⟨s, -, rfl⟩ := Finset.mem_map.mp hX
    exact s.2
  · refine hbound (fun O => a O) M fun s hs => ?_
    have := hM s (Finset.mem_map_of_mem _ hs)
    rwa [← hsum] at this
end GSpinGGP
