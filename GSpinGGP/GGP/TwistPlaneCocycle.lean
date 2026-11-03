/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.TwistTorus

/-!
# A class of `H¹(F, S_x)` twisting `W` into the other form: the plane case

Assembles `exists_planeTwist` (twisting an anisotropic plane) and
`conj_blockDiagGL_mem_torusBarFbar` (the cocycle lies in `S_x`): if `W''_x` contains an `x`-stable
anisotropic plane on which `P(x)` has determinant `1` (`HasTwistPlane`), some `β ∈ H¹(F, S_x)` has
`W_{q_x(β)} ≇ W` (`exists_twistIdx_not_isometric_of_hasTwistPlane`; Thesis Prop. 6.5.1(iv), first
half, in this case).
-/

noncomputable section

open Matrix

namespace GSpinGGP

namespace TwistPlane

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F


/-- `W''_x` contains an `x`-stable anisotropic plane `Π ⊥ W'_x` on which `P(x)` has determinant
`1`, in rational coordinates `B` adapted to `W = Π ⊥ Π^⊥`. -/
def HasTwistPlane (d : GGPData F) (x : GSpin d.QW) : Prop :=
  ∃ (κ : Type) (_ : Fintype κ) (_ : DecidableEq κ) (e : Fin 2 ⊕ κ ≃ Fin d.m) (B : GL (Fin d.m) F)
    (Q₂ : QuadraticForm F (Fin 2 → F)) (G₃ : Matrix κ κ F) (A : Matrix (Fin 2) (Fin 2) F)
    (C : Matrix κ κ F),
    IsNondeg Q₂ ∧ (∀ v, Q₂ v = 0 → v = 0) ∧ G₃.IsSymm ∧
    d.QW.toMatrix' = (B : Matrix (Fin d.m) (Fin d.m) F)ᵀ * blockDiag e Q₂.toMatrix' G₃ * B ∧
    Aᵀ * Q₂.toMatrix' * A = Q₂.toMatrix' ∧ A.det = 1 ∧
    (B : Matrix (Fin d.m) (Fin d.m) F) *
      LinearMap.toMatrix' (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) =
        blockDiag e A C * B ∧
    ∀ v ∈ fixedSub x, ∀ i, ((B : Matrix (Fin d.m) (Fin d.m) F) *ᵥ v) (e (Sum.inl i)) = 0

/-- **The plane case of Thesis Prop. 6.5.1(iv), first half**: if `HasTwistPlane d x`, some
`β ∈ H¹(F, S_x)` twists `W` into a form `W_{q_x(β)} ≇ W`. -/
theorem exists_twistIdx_not_isometric_of_hasTwistPlane {d : GGPData F} (IF : InnerFormSystem d)
    (x : GSpin d.QW) (h : HasTwistPlane d x) :
    ∃ β α, TwistIdx IF x β α ∧ ¬ Nonempty (d.QW.IsometryEquiv (IF.twist α).Q') := by
  obtain ⟨κ, _, _, e, B, Q₂, G₃, A, C, hQ₂, haniso, hG₃, hB, hA, hAdet, hx, hfix⟩ := h
  obtain ⟨Q', X, hnd, hsd, hniso, hgram, hcoc, E, hE, hEX⟩ :=
    exists_planeTwist d.nondeg e B hQ₂ haniso G₃ hG₃ hB
  -- the cocycle `σ ↦ X⁻¹ σ(X)`, valued in `S_x`
  let a : GalCocycle (d.torusBarFbar x) :=
    { toFun := fun σ => X⁻¹ * galGL d.m σ X
      mem' := fun σ => by
        obtain ⟨R, hR, hRdet, hXR⟩ := hcoc σ
        rw [hXR]
        exact conj_blockDiagGL_mem_torusBarFbar x e B hQ₂ hB hA hAdet hx hfix R hR hRdet
      cocycle' := fun σ τ => by
        rw [galGL_mul, map_mul, map_inv]
        group
      continuous' := ⟨E, hE, fun σ τ hστ => by rw [hEX σ τ hστ]⟩ }
  have htw : IsTwistBy d.QW Q' a.toFun := (TwistDescent.isTwistBy_iff _ _ _).2
    ⟨TwistDescent.isoOfGL d.QW Q' X hgram, fun σ => by
      rw [TwistDescent.glOf_isoOfGL]⟩
  obtain ⟨α, ⟨ψ⟩, -⟩ := IF.classify Q' hnd hsd
  refine ⟨H1.mk a, α, ⟨a, rfl, TwistDescent.isTwistBy_of_isometryEquiv ψ htw⟩, fun ⟨φ⟩ => ?_⟩
  exact hniso ⟨φ.trans ψ.symm⟩

end TwistPlane

end GSpinGGP
