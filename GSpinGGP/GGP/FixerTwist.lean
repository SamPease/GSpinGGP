/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Literature.Kottwitz1986
import GSpinGGP.GGP.TwistDescent

/-!
# Twists of `W` fixing `W'_x`, and their descent to `S_x`

* `glOf_mem_fixerBar`: the matrix of an `F̄`-isometry of `W` of determinant `1` fixing `W'_x ⊗ F̄`
  lies in `(SO(W)_{W'_x})(F̄) = fixerBar d x` (lift through `P`, `gspin_specP_surjective_SO`).
* `isTwistBy_conj`: changing a twisting cocycle `c` to `h⁻¹ c σ(h)` with `h ∈ SO(W)(F̄)` keeps
  `IsTwistBy`.
* `exists_isTwistBy_torusBar_of_fixerBar`: a twist of `W` by a cocycle in `fixerBar d x` is also a
  twist by a cocycle in `S_x(F̄)`, for `x ∈ Γ(G,H)` (Kottwitz 1986, Lemma 10.2,
  `exists_rel_torusBar_of_fixerBar`).
-/

noncomputable section

open scoped TensorProduct

namespace GSpinGGP

namespace TwistDescent

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

variable {d : GGPData F} {x : ↥(GSpin d.QW)}

/-- An `F̄`-isometry of `W` of determinant `1` fixing `W'_x ⊗ F̄` has its matrix in
`fixerBar d x`: it is `P(g)` for some `g ∈ GSpin(W)(F̄)` (`gspin_specP_surjective_SO`), and `g`
fixes `W'_x ⊗ F̄`. -/
theorem glOf_mem_fixerBar (a : (d.QW.baseChange Kb).IsometryEquiv (d.QW.baseChange Kb))
    (hdet : ((glOf a : GL (Fin d.m) Kb) : Matrix (Fin d.m) (Fin d.m) Kb).det = 1)
    (hfix : ∀ w ∈ (fixedSub x).baseChange Kb, a w = w) : glOf a ∈ d.fixerBar x := by
  have hdet' : LinearMap.det (a.toLinearEquiv : (Kb ⊗[F] (Fin d.m → F)) →ₗ[Kb] _) = 1 := by
    rw [← LinearMap.det_toMatrix (bcBasis F d.m)]
    exact hdet
  obtain ⟨g, hg⟩ := gspin_specP_surjective_SO (d.QW.baseChange Kb)
    (isNondeg_baseChange d.QW d.nondeg) a.toLinearEquiv a.map_app hdet'
  have hga : ∀ w, specPIso g w = a w := fun w => by
    rw [specPIso_apply, hg]; rfl
  refine ⟨g, fun w hw => ?_, ?_⟩
  · change specPIso g w = w
    rw [hga]; exact hfix w hw
  · rw [← glOf_specPIso]; exact glOf_congr hga

/-- The isometry with matrix in `fixerBar d x` fixes `W'_x ⊗ F̄`. -/
theorem apply_eq_self_of_glOf_mem_fixerBar
    (a : (d.QW.baseChange Kb).IsometryEquiv (d.QW.baseChange Kb)) (ha : glOf a ∈ d.fixerBar x)
    {w : Kb ⊗[F] (Fin d.m → F)} (hw : w ∈ (fixedSub x).baseChange Kb) : a w = w := by
  obtain ⟨t, ht, hta⟩ := ha
  rw [apply_eq_of_glOf_eq (e' := specPIso t) (by rw [glOf_specPIso, hta]) w]
  exact ht w hw

/-- **Changing a twisting cocycle by a coboundary in `SO(W)(F̄)`**: if `c` is the cocycle of
`φ : W_{F̄} ≃ W'_{F̄}` and `h = P(g)`, then `h⁻¹ c_σ σ(h)` is the cocycle of `φ ∘ P(g)`. -/
theorem isTwistBy_conj {Q' : QuadraticForm F (Fin d.m → F)} {c : GalF F → GL (Fin d.m) Kb}
    (hc : IsTwistBy d.QW Q' c) {h : GL (Fin d.m) Kb} (hh : h ∈ (specMatFbar d.QW).range) :
    IsTwistBy d.QW Q' (fun σ => h⁻¹ * c σ * galGL d.m σ h) := by
  obtain ⟨φ, hφ⟩ := (isTwistBy_iff _ _ _).1 hc
  obtain ⟨g, rfl⟩ := hh
  refine (isTwistBy_iff _ _ _).2 ⟨(specPIso g).trans φ, fun σ => ?_⟩
  rw [glOf_trans, glOf_specPIso, hφ σ, map_mul]
  group

end TwistDescent

namespace GGPData

variable {F : Type*} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

/-- **Twists fixing `W'_x` descend to `S_x`** (Kottwitz 1986, Lemma 10.2,
`exists_rel_torusBar_of_fixerBar`): for `x ∈ Γ(G,H)`, if `W'` is the twist of `W` by a cocycle with
values in `(SO(W)_{W'_x})(F̄)`, it is also the twist of `W` by a cocycle with values in `S_x(F̄)`. -/
theorem exists_isTwistBy_torusBar_of_fixerBar (d : GGPData F) {x : ↥(GSpin d.QW)}
    (hx : d.IsGammaElt x) {Q' : QuadraticForm F (Fin d.m → F)} (c : GalCocycle (d.fixerBar x))
    (hc : IsTwistBy d.QW Q' c.toFun) :
    ∃ a : GalCocycle (d.torusBarFbar x), IsTwistBy d.QW Q' a.toFun := by
  obtain ⟨a, h, hh, ha⟩ := exists_rel_torusBar_of_fixerBar d x hx c
  obtain ⟨g, -, rfl⟩ := hh
  refine ⟨a, ?_⟩
  have := TwistDescent.isTwistBy_conj hc (h := specMatFbar d.QW g) ⟨g, rfl⟩
  convert this using 1
  funext σ
  exact ha σ

end GGPData

end GSpinGGP
