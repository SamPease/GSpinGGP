/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.GSpinExp

/-!
# `P(e^X) = e^{ad X}` near the identity

For `X ∈ gspin(V)` near `0` and `g = e^X ∈ GSpin(V)(F)`, the image `P(g) ∈ SO(V)` of `g` is the
exponential of `ad X = adV X ∈ so(V)` (`eventually_specP_eq_expA_adV`): conjugation by `e^X` on
`C(V)` is `e^{ad X}` (`expA_ad_eq`), and `e^{ad X}` restricts to `ι(V)` as `e^{ad X|_V}`, since
`ad X` preserves `ι(V)`.

* `eventually_map_expA_of_pow`: `φ(e^X) = e^{φ X}` near `0` for a linear map `φ` preserving the
  powers of the particular `X` (pointwise form of `eventually_map_expA`);
* `exists_nhds_expA_sub_expA_mem`: `e^Y − e^X ∈ I` near `0` when `Yⁿ − Xⁿ ∈ I` for all `n`
  (a closed subspace `I`, the exponential series converging);
* `eventually_specP_eq_expA_adV`: `P(e^X) = e^{ad X}`.
-/

noncomputable section

open Filter Topology Module CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

section MapExp

variable {A : Type*} [Ring A] [Algebra F A] [Module.Finite F A] [TopologicalSpace A]
  [IsModuleTopology F A]

/-- **`φ(e^X) = e^{φ X}` near `0`** for a linear map `φ` that preserves the powers of `X` (only
of this `X`; `eventually_map_expA` asks it for all `X`): both exponential series converge near
`0`, and `φ` is continuous. -/
lemma eventually_map_expA_of_pow {B : Type*} [Ring B] [Algebra F B] [Module.Finite F B]
    [TopologicalSpace B] [IsModuleTopology F B] (φ : A →ₗ[F] B) :
    ∀ᶠ X in 𝓝 (0 : A), (∀ n : ℕ, φ (X ^ n) = φ X ^ n) → φ (expA F X) = expA F (φ X) := by
  letI := isTopologicalRing_of_moduleTopology F A
  letI := isTopologicalRing_of_moduleTopology F B
  obtain ⟨U, hU, hA⟩ := expA_hasSum F (A := A)
  obtain ⟨V, hV, hB⟩ := expA_hasSum F (A := B)
  have hφc : Continuous φ := IsModuleTopology.continuous_of_linearMap φ
  have hV' : φ ⁻¹' V ∈ 𝓝 (0 : A) :=
    hφc.continuousAt.preimage_mem_nhds (by rwa [map_zero])
  haveI := t2Space_of_moduleTopology F B
  filter_upwards [hU, hV'] with X hX hX' hφ
  have h1 := (hA X hX).map φ hφc
  refine h1.unique ?_
  convert hB (φ X) hX' using 1
  funext n
  simp [map_smul, hφ]

/-- **`e^Y − e^X ∈ I` near `0`** when `Yⁿ − Xⁿ ∈ I` for every `n`: the difference of the two
convergent exponential series has its partial sums in `I`, which is closed (finite-dimensional). -/
lemma exists_nhds_expA_sub_expA_mem (I : Submodule F A) :
    ∃ U ∈ 𝓝 (0 : A), ∀ X ∈ U, ∀ Y ∈ U, (∀ n : ℕ, Y ^ n - X ^ n ∈ I) →
      expA F Y - expA F X ∈ I := by
  letI := isTopologicalRing_of_moduleTopology F A
  haveI := t2Space_of_moduleTopology F A
  obtain ⟨U, hU, h⟩ := expA_hasSum F (A := A)
  refine ⟨U, hU, fun X hX Y hY hI => ?_⟩
  have hs := ((h Y hY).sub (h X hX)).tendsto_sum_nat
  refine I.closed_of_finiteDimensional.mem_of_tendsto hs (Eventually.of_forall fun n => ?_)
  refine I.sum_mem fun k _ => ?_
  rw [← smul_sub]
  exact I.smul_mem _ (hI k)

end MapExp

section Clifford

variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] (Q : QuadraticForm F V)

/-- `ad X` on `C(V)` restricts to `adV X` on `ι(V)`, also for its powers: `(ad X)ⁿ ι(v) =
ι((adV X)ⁿ v)` for `X ∈ gspin(V)`. -/
theorem ad_pow_ι {X : CliffordAlgebra Q} (hX : X ∈ gspin Q) (n : ℕ) (v : V) :
    ((LinearMap.mulLeft F X - LinearMap.mulRight F X) ^ n) (ι Q v) = ι Q ((adV Q X ^ n) v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, pow_succ, Module.End.mul_apply, ← ih, ι_adV hX]
    rfl

/-- **`P(e^X) = e^{ad X}`** for `X ∈ gspin(V)` near `0` (Thesis §5.1.3: `ad : gspin(V) → so(V)` is
the differential of `P : GSpin(V) → SO(V)`): if `g ∈ GSpin(V)(F)` has `g = e^X` in `C(V)`, then
`P(g) = e^{adV X}` in `End(V)`.  Conjugation by `e^X` on `C(V)` is `e^{ad X}` (`expA_ad_eq`), and
`T ↦ ι⁻¹ ∘ T ∘ ι` maps the powers of `ad X` to those of `adV X` (`ad_pow_ι`). -/
theorem eventually_specP_eq_expA_adV [TopologicalSpace (Module.End F V)]
    [IsModuleTopology F (Module.End F V)] :
    ∀ᶠ X in 𝓝 (0 : CliffordAlgebra Q), X ∈ gspin Q → ∀ g : ↥(GSpin Q),
      ((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = expA F X →
        ((specP Q g : V ≃ₗ[F] V) : Module.End F V) = expA F (adV Q X) := by
  letI : TopologicalSpace (Module.End F (CliffordAlgebra Q)) :=
    moduleTopology F (Module.End F (CliffordAlgebra Q))
  haveI : IsModuleTopology F (Module.End F (CliffordAlgebra Q)) := ⟨rfl⟩
  let ρ : Module.End F (CliffordAlgebra Q) →ₗ[F] Module.End F V :=
    { toFun := fun T => ιInv Q ∘ₗ T ∘ₗ ι Q
      map_add' := fun S T => by ext v; simp
      map_smul' := fun c T => by ext v; simp }
  set ad : CliffordAlgebra Q →ₗ[F] Module.End F (CliffordAlgebra Q) :=
    (Algebra.lmul F (CliffordAlgebra Q)).toLinearMap - mulRightₗ with had
  have hadc : Continuous ad := IsModuleTopology.continuous_of_linearMap ad
  have h1 := (hadc.tendsto' 0 0 (map_zero ad)).eventually (eventually_map_expA_of_pow (F := F) ρ)
  obtain ⟨U₂, hU₂, hneg⟩ := expA_mul_expA_neg F (A := CliffordAlgebra Q)
  filter_upwards [h1, expA_ad_eq F (B := CliffordAlgebra Q), hU₂] with X hX1 hX2 hX3 hX g hg
  have hadX : ad X = LinearMap.mulLeft F X - LinearMap.mulRight F X := rfl
  have hginv : (((g : (CliffordAlgebra Q)ˣ)⁻¹ : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) =
      expA F (-X) := Units.inv_eq_of_mul_eq_one_right (by rw [hg]; exact hneg X hX3)
  have hpow : ∀ n : ℕ, ρ (ad X ^ n) = ρ (ad X) ^ n := by
    intro n
    ext v
    change ιInv Q ((ad X ^ n) (ι Q v)) = (ρ (ad X) ^ n) v
    have hρ : ρ (ad X) = adV Q X := rfl
    rw [hρ, hadX, ad_pow_ι Q hX, ιInv_ι]
  have key := hX1 hpow
  rw [hadX, hX2] at key
  change _ = expA F (ρ (ad X))
  rw [hadX, ← key]
  ext v
  change specP Q g v = ιInv Q (expA F X * (ι Q v * expA F (-X)))
  rw [specP_apply_eq, hg, hginv]

end Clifford

end GSpinGGP
