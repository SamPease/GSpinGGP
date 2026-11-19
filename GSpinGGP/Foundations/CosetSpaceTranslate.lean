/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.Measure

/-!
# Right translation on a coset space

Right translation `ι(S)γ' ↦ ι(S)γ'γ` is a homeomorphism of the coset space `ι(S)\Γ`
(`CosetSpace.mulRight`). If `ν` on `Γ` and `μ` on `S` are right invariant, the push-forward of a
Weil measure under it is again a Weil measure (`IsWeilMeasure.map_mulRight`). With the uniqueness
of the Weil measure this gives its right invariance (Bourbaki, *Intégration* VII §2 no. 6,
Thm 3), `IsWeilMeasure.isInvariantQuotient` in `TraceFormula/Basic.lean`. Nothing here uses an
axiom.
-/

open MeasureTheory Set Topology

noncomputable section

namespace GSpinGGP

namespace CosetSpace

variable {S Γ : Type*} [Group S] [Group Γ] (ι : S →* Γ)

/-- Right translation by `γ` on `ι(S)\Γ` (as a map). -/
def mulRightFun (γ : Γ) : CosetSpace ι → CosetSpace ι :=
  Quotient.map' (· * γ) fun a b h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    have e : b * γ * (a * γ)⁻¹ = b * a⁻¹ := by group
    rwa [e]

@[simp] theorem mulRightFun_mk (γ x : Γ) : mulRightFun ι γ (mk ι x) = mk ι (x * γ) := rfl

variable [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- Right translation by `γ` on `ι(S)\Γ`, as a homeomorphism. -/
def mulRight (γ : Γ) : CosetSpace ι ≃ₜ CosetSpace ι where
  toFun := mulRightFun ι γ
  invFun := mulRightFun ι γ⁻¹
  left_inv q := by induction q using CosetSpace.ind with | h x => simp
  right_inv q := by induction q using CosetSpace.ind with | h x => simp
  continuous_toFun := continuous_of_comp_mk ι
    (by
      have : mulRightFun ι γ ∘ mk ι = mk ι ∘ (· * γ) := rfl
      rw [this]; exact (continuous_mk ι).comp (by fun_prop : Continuous fun x : Γ => x * γ))
  continuous_invFun := continuous_of_comp_mk ι
    (by
      have : mulRightFun ι γ⁻¹ ∘ mk ι = mk ι ∘ (· * γ⁻¹) := rfl
      rw [this]; exact (continuous_mk ι).comp (by fun_prop : Continuous fun x : Γ => x * γ⁻¹))

@[simp] theorem mulRight_mk (γ x : Γ) : mulRight ι γ (mk ι x) = mk ι (x * γ) := rfl

@[simp] theorem mulRight_symm (γ : Γ) : (mulRight ι γ).symm = mulRight ι γ⁻¹ :=
  Homeomorph.ext fun _ => rfl

end CosetSpace

section Weil

variable {S Γ : Type*} [Group S] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [MeasurableSpace Γ] [BorelSpace Γ] [MeasurableSpace S] [MeasurableMul S]
  {ι : S →* Γ} {ν : Measure Γ} {μ : Measure S} {m : Measure (CosetSpace ι)}

/-- **The push-forward of a Weil measure under right translation is a Weil measure**, when `ν`
and `μ` are right invariant: `∫_{ι(S)\Γ} ∫_S φ(ι(s) out(qγ)) = ∫_Γ φ(gγ) dν = ∫_Γ φ dν`. -/
theorem IsWeilMeasure.map_mulRight [ν.IsMulRightInvariant] [μ.IsMulRightInvariant]
    (h : IsWeilMeasure ι ν μ m) (γ : Γ) :
    IsWeilMeasure ι ν μ (m.map (CosetSpace.mulRight ι γ)) := by
  intro φ hφ hφc
  have hmap : m.map (CosetSpace.mulRight ι γ) = m.map (CosetSpace.mulRight ι γ).toMeasurableEquiv :=
    rfl
  rw [hmap, integral_map_equiv]
  have hfib : ∀ q : CosetSpace ι,
      ∫ s, φ (ι s * CosetSpace.out ι ((CosetSpace.mulRight ι γ).toMeasurableEquiv q)) ∂μ =
        ∫ s, (fun x => φ (x * γ)) (ι s * CosetSpace.out ι q) ∂μ := by
    intro q
    have e : (CosetSpace.mulRight ι γ).toMeasurableEquiv q =
        CosetSpace.mk ι (CosetSpace.out ι q * γ) := by
      conv_lhs => rw [← CosetSpace.mk_out ι q]
      rfl
    rw [e, integral_fibre_out_mk ι μ φ]
    simp only [mul_assoc]
  simp_rw [hfib]
  rw [← h (fun x => φ (x * γ)) (hφ.comp (by fun_prop : Continuous fun x : Γ => x * γ))
    (hφc.comp_homeomorph (Homeomorph.mulRight γ))]
  exact (integral_mul_right_eq_self φ γ).symm

end Weil

end GSpinGGP
