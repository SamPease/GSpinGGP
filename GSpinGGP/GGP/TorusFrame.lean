import GSpinGGP.GGP.GaloisTorus
import GSpinGGP.GGP.TorusCentral
import GSpinGGP.Foundations.EigenFrame
import GSpinGGP.Foundations.HypPlane

/-!
# `S_x(F̄)` is the split torus of an eigen-frame

For `x ∈ Γ(G,H)`, `X = P(x)_{F̄}` is a semisimple isometry of `W_{F̄}` of determinant `1`, so it has
a hyperbolic frame of eigenvectors `eᵢ, fᵢ` with orthogonal complement `W'_x ⊗ F̄ = ker (X − 1)`
(`IsomCent.exists_hypFrame_eigen`). The group `S_x(F̄) = P(T_x(F̄))` is the split torus of that
frame (`exists_hypFrame_torusFbar`):

* `⊇`: the lifts `h(t) = eᵢ fᵢ + t fᵢ eᵢ ∈ GSpin(W)(F̄)` of the one-pair tori (`hypGSpin`) commute
  with `x` (`commute_hypUnit`) and fix `W'_x ⊗ F̄`, and their products realize the torus;
* `⊆`: `S_x(F̄)` is commutative (`torusBarFbar_commute`), and an isometry fixing `ker (X − 1)` and
  commuting with a regular element of the torus lies in the torus
  (`IsHypFrame.mem_hypTorus_of_commute`).

Own work, standard (no Zariski density or Steinberg's theorem is needed beyond the commutativity
of `S_x(F̄)`, `torusBarFbar_commute`, which is proved from the Lie algebra).
-/

noncomputable section

open QuadraticMap Module

open scoped TensorProduct

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

local notation "Kb" => AlgebraicClosure F

namespace GGPData

variable {d : GGPData F}

set_option hygiene false in
local notation "Wb" => AlgebraicClosure F ⊗[F] (Fin d.m → F)

/-- `GL(W_{F̄}) → GL_m(F̄)`: the matrix in the rational basis `bcBasis`. -/
def matGL (d : GGPData F) :
    ((Wb) ≃ₗ[Kb] (Wb)) →* GL (Fin d.m) Kb :=
  (Units.map (LinearMap.toMatrixAlgEquiv (bcBasis F d.m)).toMonoidHom).comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv Kb (Wb)).symm.toMonoidHom

theorem specMatFbar_eq_matGL_comp : specMatFbar d.QW = (matGL d).comp (specP _) := rfl

theorem coe_matGL (g : (Wb) ≃ₗ[Kb] (Wb)) :
    ((matGL d g : GL (Fin d.m) Kb) : Matrix (Fin d.m) (Fin d.m) Kb) =
      LinearMap.toMatrix (bcBasis F d.m) (bcBasis F d.m) (g : _ →ₗ[Kb] _) := rfl

theorem matGL_injective : Function.Injective (matGL d) := fun g h hgh => by
  have := congrArg (fun u : GL (Fin d.m) Kb => (u : Matrix (Fin d.m) (Fin d.m) Kb)) hgh
  simp only [coe_matGL] at this
  exact LinearEquiv.toLinearMap_injective ((LinearMap.toMatrix _ _).injective this)

/-- `S_x(F̄)`, through `P : T_x(F̄) → GL(W_{F̄})`, then in matrices. -/
theorem torusBarFbar_eq_map (x : ↥(GSpin d.QW)) :
    d.torusBarFbar x = ((d.torusFbar x).map (specP _)).map (matGL d) := by
  rw [torusBarFbar, Subgroup.map_map]
  rfl

/-- Conjugation commutes with `matGL`. -/
theorem map_matGL_conj (A : Subgroup ((Wb) ≃ₗ[Kb] (Wb)))
    (g : (Wb) ≃ₗ[Kb] (Wb)) :
    (A.map (matGL d)).map (MulAut.conj (matGL d g)).toMonoidHom =
      (A.map (MulAut.conj g).toMonoidHom).map (matGL d) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext h : 1
  simp [map_mul, map_inv]

section Frame

variable (x : ↥(GSpin d.QW))

/-- `X = P(x)_{F̄}`. -/
local notation "XX" => (specP (d.QW.baseChange Kb) (bcGSpin d.QW x) :
  (Wb) →ₗ[Kb] (Wb))

theorem polarBilin_baseChange_nondegenerate :
    (polarBilin (d.QW.baseChange Kb)).Nondegenerate :=
  QuadraticMap.nondegenerate_polar_iff.mpr
    ((isNondeg_iff_nondegenerate _).1 (isNondeg_baseChange _ d.nondeg))

/-- Every element of the split torus of an eigen-frame is `P(g)` for some `g ∈ T_x(F̄)`: a
product of the pair elements. -/
theorem exists_torusFbar_scale {n : ℕ} {e f : Fin n → Wb}
    {μ : Fin n → Kbˣ}
    (hF : IsHypFrame (d.QW.baseChange Kb) (Module.End.eigenspace XX 1) e f)
    (hXef : ∀ i, XX (e i) = (μ i : Kb) • e i ∧
      XX (f i) = (((μ i)⁻¹ : Kbˣ) : Kb) • f i)
    (t : Fin n → Kbˣ) :
    ∃ g ∈ d.torusFbar x, (∀ w ∈ Module.End.eigenspace XX 1, specP _ g w = w) ∧
      ∀ j, specP _ g (e j) = (t j : Kb) • e j ∧
        specP _ g (f j) = (((t j)⁻¹ : Kbˣ) : Kb) • f j := by
  obtain ⟨g, hgx, hgW, hge, -⟩ := Steinberg.exists_frame_torus_elt hF hXef t
  exact ⟨g, ⟨congrArg Subtype.val hgx.eq,
    fun w hw => hgW w (by rw [GGPData.eigenspace_bc_one]; exact hw)⟩, hgW, hge⟩

/-- The split torus of an eigen-frame lies in `S_x(F̄)`. -/
theorem hypTorus_le_map_torusFbar {n : ℕ} {e f : Fin n → Wb}
    {μ : Fin n → Kbˣ}
    (hF : IsHypFrame (d.QW.baseChange Kb) (Module.End.eigenspace XX 1) e f)
    (hXef : ∀ i, XX (e i) = (μ i : Kb) • e i ∧
      XX (f i) = (((μ i)⁻¹ : Kbˣ) : Kb) • f i) :
    hypTorus (Module.End.eigenspace XX 1) e f ≤ (d.torusFbar x).map (specP _) := by
  rintro h ⟨hW, t, ht⟩
  obtain ⟨g, hg, hgW, hge⟩ := exists_torusFbar_scale x hF hXef t
  refine ⟨g, hg, LinearEquiv.toLinearMap_injective (hF.linearMap_ext (fun w hw => ?_)
    (fun j => ?_) (fun j => ?_))⟩
  · simp only [LinearEquiv.coe_coe, hgW w hw, hW w hw]
  · simp only [LinearEquiv.coe_coe, (hge j).1, (ht j).1]
  · simp only [LinearEquiv.coe_coe, (hge j).2, (ht j).2]

/-- **`S_x(F̄)` is the split torus of an eigen-frame of `P(x)_{F̄}`**, for `x ∈ Γ(G,H)`. -/
theorem exists_hypFrame_torusFbar (hx : d.IsGammaElt x) :
    ∃ (n : ℕ) (e f : Fin n → Wb),
      IsHypFrame (d.QW.baseChange Kb) (Module.End.eigenspace XX 1) e f ∧
        (d.torusFbar x).map (specP _) = hypTorus (Module.End.eigenspace XX 1) e f := by
  have hss : Module.End.IsSemisimple XX := by
    rw [specP_bcGSpin]; exact isSemisimple_specP_baseChange x hx.1
  obtain ⟨n, e, f, μ, hF, hXef⟩ := IsomCent.exists_hypFrame_eigen
    polarBilin_baseChange_nondegenerate
    (fun a b => Steinberg.polar_specP (bcGSpin d.QW x) a b) hss (det_specP _)
  refine ⟨n, e, f, hF, le_antisymm ?_ (hypTorus_le_map_torusFbar x hF hXef)⟩
  -- a regular element `k = P(gₖ)`
  obtain ⟨t, ht1, htinj, htinv⟩ := exists_regular_units Kb n
  obtain ⟨gk, hgk, hgkW, hgke⟩ := exists_torusFbar_scale x hF hXef t
  rintro _ ⟨g, hg, rfl⟩
  have hc : Commute (specP _ gk) (specP _ g) := by
    have h := torusBarFbar_commute x hx _ ⟨gk, hgk, rfl⟩ _ ⟨g, hg, rfl⟩
    rw [specMatFbar_eq_matGL_comp] at h
    simp only [MonoidHom.comp_apply] at h
    exact matGL_injective (by rw [map_mul, map_mul]; exact h.eq)
  refine hF.mem_hypTorus_of_commute (k := specP _ gk) hgkW hgke ht1 htinj htinv
    (fun a b => Steinberg.polar_specP g a b) (fun w hw => hg.2 w ?_) hc
  rw [← GGPData.eigenspace_bc_one]
  exact hw

/-- **`T_x(F̄)` is commutative**, for `x ∈ Γ(G,H)` (in `GSpin(W)(F̄)`, not only modulo scalars): a
special case of `Steinberg.commute_of_fixes_eigenspace_one`. -/
theorem torusFbar_commute (hx : d.IsGammaElt x) {s t : GSpin (d.QW.baseChange Kb)}
    (hs : s ∈ d.torusFbar x) (ht : t ∈ d.torusFbar x) : Commute s t :=
  Steinberg.commute_of_fixes_eigenspace_one (x := bcGSpin d.QW x) (isNondeg_baseChange _ d.nondeg)
    (by rw [specP_bcGSpin]; exact isSemisimple_specP_baseChange x hx.1)
    (by rw [specP_bcGSpin]; exact lieAbelian_specP_baseChange x hx) (Subtype.ext ht.1.eq)
    (fun w hw => ht.2 w (by rwa [GGPData.eigenspace_bc_one] at hw)) (Subtype.ext hs.1.eq)

end Frame

end GGPData

end GSpinGGP
