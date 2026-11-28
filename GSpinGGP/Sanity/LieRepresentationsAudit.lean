/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
-/
import GSpinGGP.Foundations.LieRepresentations
import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra

/-!
# Sanity checks for the representation theory of real Lie groups

The notions of `GSpinGGP/Foundations/LieRepresentations.lean` computed for the trivial
one-dimensional representation `1_G` of a real Lie group `G`:

* every vector is smooth and `dπ(X) = 0`, so the Fréchet seminorms reduce to the norm;
* `Hom_S(1_G, 1) = ℂ`: the multiplicity of the trivial character is `1`;
* `Hom_S(1_G, ξ) = 0` when `ξ(s) ≠ 1` for some `s`: the multiplicity is `0`;
* the constant function `1` is the character of `1_G`, with `π(f) = (∫ f) • 1` nuclear.

Then a concrete Lie structure: the multiplicative group `ℝˣ`, a one-dimensional real Lie group
(Mathlib's Lie group structure on the units of a complete normed algebra), with the multiplicity
of the trivial character `1` and of the sign character `0`.
-/

open MeasureTheory Manifold
open scoped ContDiff Manifold NNReal

namespace GSpinGGP.LieRep.Audit


attribute [local instance] RealLieStructure.normedAddCommGroup RealLieStructure.normedSpace
  RealLieStructure.finiteDimensional RealLieStructure.chartedSpace RealLieStructure.lieGroup

variable {G : Type} [Group G] [TopologicalSpace G]

/-- The trivial representation of `G` on `ℂ`. -/
noncomputable def trivialRep (G : Type) [Group G] [TopologicalSpace G] : UnitaryRep G :=
  UnitaryRep.ofMonoidHom ℂ 1 (fun _ => one_mem _) (fun _ => continuous_const)

local instance : FiniteDimensional ℂ (trivialRep G).H := inferInstanceAs (FiniteDimensional ℂ ℂ)

@[simp]
theorem trivialRep_ρ (g : G) (v : (trivialRep G).H) : (trivialRep G).ρ g v = v := rfl

variable (L : RealLieStructure G)

/-- Every vector of the trivial representation is smooth. -/
theorem smoothVectors_trivialRep : smoothVectors L (trivialRep G) = ⊤ :=
  eq_top_iff.2 fun _ _ => (mem_smoothVectors_iff L _).2 contMDiff_const

/-- A smooth vector of `1_G` as a complex number. -/
abbrev coeC (v : ↥(smoothVectors L (trivialRep G))) : ℂ := v.val

/-- The unit vector `1 ∈ ℂ`, as a smooth vector. -/
noncomputable def one : ↥(smoothVectors L (trivialRep G)) :=
  ⟨(1 : ℂ), by rw [smoothVectors_trivialRep]; trivial⟩

theorem eq_smul_one (v : ↥(smoothVectors L (trivialRep G))) :
    v = coeC L v • one L := Subtype.ext (mul_one (coeC L v)).symm

/-- The derived action of the trivial representation is `0`. -/
theorem derivative_trivialRep [T2Space G] (X : LeftInvariantDerivation 𝓘(ℝ, L.E) G) :
    derivative L (trivialRep G) X = 0 := by
  ext v
  rw [derivative_apply]
  simp

/-- The seminorms of `1_G` are the norm (empty list) and `0` (nonempty lists). -/
theorem smoothSeminorm_trivialRep_cons [T2Space G] (X : LeftInvariantDerivation 𝓘(ℝ, L.E) G)
    (Xs : List (LeftInvariantDerivation 𝓘(ℝ, L.E) G)) (v : ↥(smoothVectors L (trivialRep G))) :
    smoothSeminorm L (trivialRep G) (X :: Xs) v = 0 := by
  rw [smoothSeminorm_apply, derivedAction_cons, derivative_trivialRep, zero_mul]
  simp

/-- Every linear form on `1_G^∞ = ℂ` is continuous: `|ℓ(v)| ≤ |ℓ(1)| ‖v‖`. -/
theorem isContinuousForm_trivialRep [T2Space G]
    (ℓ : Module.Dual ℂ ↥(smoothVectors L (trivialRep G))) :
    IsContinuousForm L (trivialRep G) ℓ := by
  refine (isContinuousForm_iff L _ ℓ).2 ⟨{[]}, ‖ℓ (one L)‖₊, fun v => ?_⟩
  rw [Finset.sup_singleton, smoothSeminorm_nil, coe_nnNorm]
  conv_lhs => rw [eq_smul_one L v, map_smul, smul_eq_mul, norm_mul]
  rw [mul_comm]
  exact le_rfl

/-- For the trivial character, every linear form on `1_G^∞` is equivariant and continuous. -/
theorem equivariantForms_trivialRep_one [T2Space G] (S : Subgroup G) :
    equivariantForms L (trivialRep G) S (fun _ => 1) = ⊤ :=
  eq_top_iff.2 fun ℓ _ =>
    ⟨fun s v => by rw [one_mul]; rfl, isContinuousForm_trivialRep L ℓ⟩

/-- `m(1_G) = 1` for the trivial character. -/
theorem multiplicity_trivialRep_one [T2Space G] (S : Subgroup G) :
    multiplicity L (trivialRep G) S (fun _ => 1) = 1 := by
  have e : ↥(smoothVectors L (trivialRep G)) ≃ₗ[ℂ] ℂ :=
    LinearEquiv.ofTop _ (smoothVectors_trivialRep L)
  have : Module.Finite ℂ ↥(smoothVectors L (trivialRep G)) := Module.Finite.equiv e.symm
  rw [multiplicity, equivariantForms_trivialRep_one, rank_top, Module.dual_rank_eq,
    Cardinal.lift_id, e.rank_eq, Module.rank_self, map_one]

/-- If `ξ(s) ≠ 1` for some `s ∈ S`, then `1_G` has no `(S, ξ)`-equivariant form. -/
theorem multiplicity_trivialRep_eq_zero [T2Space G] {S : Subgroup G} {ξ : ↥S → ℂ} {s : ↥S}
    (hs : ξ s ≠ 1) : multiplicity L (trivialRep G) S ξ = 0 := by
  have hbot : equivariantForms L (trivialRep G) S ξ = ⊥ := by
    refine eq_bot_iff.2 fun ℓ hℓ => ?_
    ext v
    have h := hℓ.1 s v
    have hv : smoothAction L (trivialRep G) s v = v := Subtype.ext rfl
    rw [hv] at h
    have : (1 - ξ s) * ℓ v = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
    simpa [sub_ne_zero.2 hs.symm] using this
  rw [multiplicity, hbot, rank_bot, map_zero]

theorem not_hasModel_trivialRep [T2Space G] {S : Subgroup G} {ξ : ↥S → ℂ} {s : ↥S}
    (hs : ξ s ≠ 1) : ¬ HasModel L (trivialRep G) S ξ := by
  rw [hasModel_iff_multiplicity_ne_zero, multiplicity_trivialRep_eq_zero L hs, not_not]

section Character

variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

omit [T2Space G] in
theorem opOf_trivialRep {f : G → ℂ} (hf : f ∈ testFunctions L) :
    opOf (trivialRep G) f = (∫ g, f g ∂(Measure.haar : Measure G)) • 1 := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [opOf_apply _ (opIntegrable_of_mem_testFunctions L _ hf)]
  simp only [trivialRep_ρ]
  rw [integral_smul_const]
  rfl

omit [T2Space G] in
/-- The constant function `1` is the character of `1_G`: `π(f) = (∫ f) • 1` is nuclear (finite
rank) and `tr π(f) = ∫ f`. -/
theorem isCharacterOf_trivialRep_one : IsCharacterOf L (trivialRep G) (fun _ => 1) := by
  refine ⟨locallyIntegrable_const 1, fun f hf => ⟨?_, ?_⟩⟩
  · exact TauCeti.mem_nuclearOperators_of_finiteDimensional _
  · rw [traceOf, hilbertTrace_eq_trace, opOf_trivialRep L hf]
    simp [show Module.finrank ℂ (trivialRep G).H = 1 from Module.finrank_self ℂ]

end Character

/-! ### A concrete real Lie group: `ℝˣ` -/

/-- The real Lie group `ℝˣ`, with Mathlib's charts modelled on `ℝ`. -/
noncomputable def unitsReal : RealLieStructure ℝˣ where
  E := ℝ

/-- The sign character of `ℝˣ`. -/
noncomputable def sign (s : ↥(⊤ : Subgroup ℝˣ)) : ℂ := if 0 < ((s : ℝˣ) : ℝ) then 1 else -1

example : smoothVectors unitsReal (trivialRep ℝˣ) = ⊤ := smoothVectors_trivialRep _

example : multiplicity unitsReal (trivialRep ℝˣ) ⊤ (fun _ => 1) = 1 :=
  multiplicity_trivialRep_one _ _

example : multiplicity unitsReal (trivialRep ℝˣ) ⊤ sign = 0 :=
  multiplicity_trivialRep_eq_zero (s := ⟨-1, Subgroup.mem_top _⟩) _ (by norm_num [sign])

example : HasModel unitsReal (trivialRep ℝˣ) ⊤ (fun _ => 1) := by
  rw [hasModel_iff_multiplicity_ne_zero, multiplicity_trivialRep_one]
  exact one_ne_zero

end GSpinGGP.LieRep.Audit
