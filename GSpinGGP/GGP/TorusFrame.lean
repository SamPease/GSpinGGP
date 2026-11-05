import GSpinGGP.GGP.GaloisTorus
import GSpinGGP.GGP.EigenFrame
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
of `S_x(F̄)`, which is proved from the Lie algebra in `GGP/MovedCentralizer.lean`).
-/

noncomputable section

open scoped Classical

open QuadraticMap Module

open scoped TensorProduct

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable {d : GGPData F}

/-- `GL(W_{F̄}) → GL_m(F̄)`: the matrix in the rational basis `bcBasis`. -/
def matGL (d : GGPData F) :
    (((AlgebraicClosure F) ⊗[F] (Fin d.m → F)) ≃ₗ[(AlgebraicClosure F)] ((AlgebraicClosure F) ⊗[F] (Fin d.m → F))) →* GL (Fin d.m) (AlgebraicClosure F) :=
  (Units.map (LinearMap.toMatrixAlgEquiv (bcBasis F d.m)).toMonoidHom).comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (AlgebraicClosure F) ((AlgebraicClosure F) ⊗[F] (Fin d.m → F))).symm.toMonoidHom

theorem specMatFbar_eq_matGL_comp : specMatFbar d.QW = (matGL d).comp (specP _) := rfl

theorem coe_matGL (g : ((AlgebraicClosure F) ⊗[F] (Fin d.m → F)) ≃ₗ[(AlgebraicClosure F)] ((AlgebraicClosure F) ⊗[F] (Fin d.m → F))) :
    ((matGL d g : GL (Fin d.m) (AlgebraicClosure F)) : Matrix (Fin d.m) (Fin d.m) (AlgebraicClosure F)) =
      LinearMap.toMatrix (bcBasis F d.m) (bcBasis F d.m) (g : _ →ₗ[(AlgebraicClosure F)] _) := rfl

theorem matGL_injective : Function.Injective (matGL d) := fun g h hgh => by
  have := congrArg (fun u : GL (Fin d.m) (AlgebraicClosure F) => (u : Matrix (Fin d.m) (Fin d.m) (AlgebraicClosure F))) hgh
  simp only [coe_matGL] at this
  exact LinearEquiv.toLinearMap_injective ((LinearMap.toMatrix _ _).injective this)

/-- `S_x(F̄)`, through `P : T_x(F̄) → GL(W_{F̄})`, then in matrices. -/
theorem torusBarFbar_eq_map (x : ↥(GSpin d.QW)) :
    d.torusBarFbar x = ((d.torusFbar x).map (specP _)).map (matGL d) := by
  rw [torusBarFbar, Subgroup.map_map]
  rfl

/-- Conjugation commutes with `matGL`. -/
theorem map_matGL_conj (A : Subgroup (((AlgebraicClosure F) ⊗[F] (Fin d.m → F)) ≃ₗ[(AlgebraicClosure F)] ((AlgebraicClosure F) ⊗[F] (Fin d.m → F))))
    (g : ((AlgebraicClosure F) ⊗[F] (Fin d.m → F)) ≃ₗ[(AlgebraicClosure F)] ((AlgebraicClosure F) ⊗[F] (Fin d.m → F))) :
    (A.map (matGL d)).map (MulAut.conj (matGL d g)).toMonoidHom =
      (A.map (MulAut.conj g).toMonoidHom).map (matGL d) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext h : 1
  simp [map_mul, map_inv]

section Frame

variable (x : ↥(GSpin d.QW))

/-- `X = P(x)_{F̄}`. -/
local notation "XX" => (specP (d.QW.baseChange (AlgebraicClosure F)) (bcGSpin d.QW x) :
  ((AlgebraicClosure F) ⊗[F] (Fin d.m → F)) →ₗ[(AlgebraicClosure F)] ((AlgebraicClosure F) ⊗[F] (Fin d.m → F)))

theorem associated_eq_invOf_polar {V : Type*} [AddCommGroup V] [Module (AlgebraicClosure F) V]
    (Q : QuadraticForm (AlgebraicClosure F) V) (a b : V) : associated Q a b = ⅟2 * polar Q a b := by
  rw [associated_apply]; rfl

theorem polarBilin_nondegenerate :
    (polarBilin (d.QW.baseChange (AlgebraicClosure F))).Nondegenerate := by
  have hnd := isNondeg_baseChange _ d.nondeg
  unfold IsNondeg bform at hnd
  refine ⟨fun a ha => hnd.1 a fun b => ?_, fun a ha => hnd.2 a fun b => ?_⟩
  · rw [associated_eq_invOf_polar, show polar (d.QW.baseChange (AlgebraicClosure F)) a b = 0 from
      ha b, mul_zero]
  · rw [associated_eq_invOf_polar, show polar (d.QW.baseChange (AlgebraicClosure F)) b a = 0 from
      ha b, mul_zero]

theorem polar_specP (g : GSpin (d.QW.baseChange (AlgebraicClosure F))) (a b : (AlgebraicClosure F) ⊗[F] (Fin d.m → F)) :
    polar (d.QW.baseChange (AlgebraicClosure F)) (specP _ g a) (specP _ g b) = polar (d.QW.baseChange (AlgebraicClosure F)) a b := by
  simp only [polar, ← map_add, specP_isometry]

/-- The torus element `h(s) ∈ GSpin(W)(F̄)` of the pair `eᵢ, fᵢ` lies in `T_x(F̄)`, scales `eⱼ, fⱼ`
by `s⁻¹, s` for `j = i` and fixes them otherwise, and fixes `W'_x ⊗ F̄`. -/
theorem exists_pair_mem_torusFbar {n : ℕ} {e f : Fin n → (AlgebraicClosure F) ⊗[F] (Fin d.m → F)} {μ : Fin n → (AlgebraicClosure F)ˣ}
    (hF : IsHypFrame (d.QW.baseChange (AlgebraicClosure F)) (Module.End.eigenspace XX 1) e f)
    (hXef : ∀ i, XX (e i) = (μ i : (AlgebraicClosure F)) • e i ∧ XX (f i) = (((μ i)⁻¹ : (AlgebraicClosure F)ˣ) : (AlgebraicClosure F)) • f i)
    (i : Fin n) (s : (AlgebraicClosure F)ˣ) :
    ∃ g ∈ d.torusFbar x, (∀ w ∈ Module.End.eigenspace XX 1, specP _ g w = w) ∧
      ∀ j, specP _ g (e j) = (if j = i then ((s⁻¹ : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) else 1) • e j ∧
        specP _ g (f j) = (if j = i then (s : (AlgebraicClosure F)) else 1) • f j := by
  have h2 : (2 : (AlgebraicClosure F)) ≠ 0 := two_ne_zero
  have hQe : d.QW.baseChange (AlgebraicClosure F) (e i) = 0 := by
    have h := polar_self (d.QW.baseChange (AlgebraicClosure F)) (e i)
    rw [hF.polar_ee, nsmul_eq_mul, Nat.cast_ofNat] at h
    exact (mul_eq_zero.1 h.symm).resolve_left h2
  have hQf : d.QW.baseChange (AlgebraicClosure F) (f i) = 0 := by
    have h := polar_self (d.QW.baseChange (AlgebraicClosure F)) (f i)
    rw [hF.polar_ff, nsmul_eq_mul, Nat.cast_ofNat] at h
    exact (mul_eq_zero.1 h.symm).resolve_left h2
  have hp : polar (d.QW.baseChange (AlgebraicClosure F)) (e i) (f i) = 1 := by simp [hF.polar_ef]
  set g := hypGSpin hQe hQf hp s
  have hg : ∀ v, specP _ g v = v + (((s⁻¹ : (AlgebraicClosure F)ˣ) : (AlgebraicClosure F)) - 1) •
      (polar (d.QW.baseChange (AlgebraicClosure F)) (f i) v • e i) +
      ((s : (AlgebraicClosure F)) - 1) • (polar (d.QW.baseChange (AlgebraicClosure F)) (e i) v • f i) := specP_hypGSpin hQe hQf hp s
  have hW : ∀ w ∈ Module.End.eigenspace XX 1, specP _ g w = w := fun w hw => by
    have h := (hF.mem_iff w).1 hw i
    rw [hg, polar_comm _ (f i), polar_comm _ (e i), h.1, h.2]
    simp
  refine ⟨g, ⟨?_, fun w hw => hW w ?_⟩, hW, fun j => ⟨?_, ?_⟩⟩
  · have hc := commute_hypUnit hQe hQf hp (g := bcGSpin d.QW x) (s := μ i) (hXef i).1
      (hXef i).2 s
    refine Units.ext ?_
    exact hc.symm.eq
  · rw [GGPData.eigenspace_bc_one]
    exact hw
  · rw [hg, hF.polar_fe, hF.polar_ee]
    by_cases hj : j = i
    · subst hj; simp only [ite_true, smul_zero, add_zero, Units.val_inv_eq_inv_val]; module
    · simp [hj, Ne.symm hj]
  · rw [hg, hF.polar_ff, hF.polar_ef]
    by_cases hj : j = i
    · subst hj; simp only [ite_true, smul_zero, add_zero, Units.val_inv_eq_inv_val]; module
    · simp [hj, Ne.symm hj]

/-- Every element of the split torus of an eigen-frame is `P(g)` for some `g ∈ T_x(F̄)`: a
product of the pair elements. -/
theorem exists_torusFbar_scale {n : ℕ} {e f : Fin n → AlgebraicClosure F ⊗[F] (Fin d.m → F)}
    {μ : Fin n → (AlgebraicClosure F)ˣ}
    (hF : IsHypFrame (d.QW.baseChange (AlgebraicClosure F)) (Module.End.eigenspace XX 1) e f)
    (hXef : ∀ i, XX (e i) = (μ i : AlgebraicClosure F) • e i ∧
      XX (f i) = (((μ i)⁻¹ : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) • f i)
    (t : Fin n → (AlgebraicClosure F)ˣ) :
    ∃ g ∈ d.torusFbar x, (∀ w ∈ Module.End.eigenspace XX 1, specP _ g w = w) ∧
      ∀ j, specP _ g (e j) = (t j : AlgebraicClosure F) • e j ∧
        specP _ g (f j) = (((t j)⁻¹ : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) • f j := by
  have key : ∀ S : Finset (Fin n), ∃ g ∈ d.torusFbar x,
      (∀ w ∈ Module.End.eigenspace XX 1, specP _ g w = w) ∧
      ∀ j, specP _ g (e j) = (if j ∈ S then (t j : AlgebraicClosure F) else 1) • e j ∧
        specP _ g (f j) =
          (if j ∈ S then (((t j)⁻¹ : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) else 1) • f j := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, Subgroup.one_mem _, fun w _ => by simp, fun j => by simp⟩
    | insert i S hi ih =>
      obtain ⟨g, hg, hgW, hge⟩ := ih
      obtain ⟨p, hp, hpW, hpe⟩ := exists_pair_mem_torusFbar x hF hXef i (t i)⁻¹
      refine ⟨p * g, Subgroup.mul_mem _ hp hg, fun w hw => ?_, fun j => ⟨?_, ?_⟩⟩
      · rw [map_mul, LinearEquiv.mul_apply, hgW w hw, hpW w hw]
      · rw [map_mul, LinearEquiv.mul_apply, (hge j).1, map_smul, (hpe j).1, smul_smul]
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj]
      · rw [map_mul, LinearEquiv.mul_apply, (hge j).2, map_smul, (hpe j).2, smul_smul]
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj]
  obtain ⟨g, hg, hgW, hge⟩ := key Finset.univ
  exact ⟨g, hg, hgW, fun j => by simpa using hge j⟩

/-- The split torus of an eigen-frame lies in `S_x(F̄)`. -/
theorem hypTorus_le_map_torusFbar {n : ℕ} {e f : Fin n → AlgebraicClosure F ⊗[F] (Fin d.m → F)}
    {μ : Fin n → (AlgebraicClosure F)ˣ}
    (hF : IsHypFrame (d.QW.baseChange (AlgebraicClosure F)) (Module.End.eigenspace XX 1) e f)
    (hXef : ∀ i, XX (e i) = (μ i : AlgebraicClosure F) • e i ∧
      XX (f i) = (((μ i)⁻¹ : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) • f i) :
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
    ∃ (n : ℕ) (e f : Fin n → AlgebraicClosure F ⊗[F] (Fin d.m → F)),
      IsHypFrame (d.QW.baseChange (AlgebraicClosure F)) (Module.End.eigenspace XX 1) e f ∧
        (d.torusFbar x).map (specP _) = hypTorus (Module.End.eigenspace XX 1) e f := by
  have hss : Module.End.IsSemisimple XX := by
    rw [specP_bcGSpin]; exact isSemisimple_specP_baseChange x hx.1
  obtain ⟨n, e, f, μ, hF, hXef⟩ := IsomCent.exists_hypFrame_eigen polarBilin_nondegenerate
    (fun a b => polar_specP _ a b) hss (det_specP _)
  refine ⟨n, e, f, hF, le_antisymm ?_ (hypTorus_le_map_torusFbar x hF hXef)⟩
  -- a regular element `k = P(gₖ)`, `tᵢ = 2^{i+1}`
  have h2 : ∀ k : ℕ, ((2 : AlgebraicClosure F) ^ k) = ((2 ^ k : ℕ) : AlgebraicClosure F) := by
    intro k; push_cast; rfl
  let t : Fin n → (AlgebraicClosure F)ˣ := fun i =>
    Units.mk0 ((2 : AlgebraicClosure F) ^ (i.val + 1)) (pow_ne_zero _ two_ne_zero)
  have ht1 : ∀ i, (t i : AlgebraicClosure F) ≠ 1 := fun i => by
    simp only [t, Units.val_mk0, h2]
    exact_mod_cast (Nat.one_lt_two_pow (Nat.succ_ne_zero _)).ne'
  have htinj : ∀ i j, (t i : AlgebraicClosure F) = t j → i = j := fun i j hij => by
    simp only [t, Units.val_mk0, h2] at hij
    have : 2 ^ (i.val + 1) = 2 ^ (j.val + 1) := by exact_mod_cast hij
    exact Fin.ext (by have := Nat.pow_right_injective le_rfl this; omega)
  have htinv : ∀ i j, (t i : AlgebraicClosure F) * t j ≠ 1 := fun i j => by
    simp only [t, Units.val_mk0]
    rw [← pow_add, h2]
    exact_mod_cast (Nat.one_lt_two_pow (by omega : i.val + 1 + (j.val + 1) ≠ 0)).ne'
  obtain ⟨gk, hgk, hgkW, hgke⟩ := exists_torusFbar_scale x hF hXef t
  rintro _ ⟨g, hg, rfl⟩
  have hc : Commute (specP _ gk) (specP _ g) := by
    have h := torusBarFbar_commute x hx _ ⟨gk, hgk, rfl⟩ _ ⟨g, hg, rfl⟩
    rw [specMatFbar_eq_matGL_comp] at h
    simp only [MonoidHom.comp_apply] at h
    exact matGL_injective (by rw [map_mul, map_mul]; exact h.eq)
  refine hF.mem_hypTorus_of_commute (k := specP _ gk) hgkW hgke ht1 htinj htinv
    (fun a b => polar_specP g a b) (fun w hw => hg.2 w ?_) hc
  rw [← GGPData.eigenspace_bc_one]
  exact hw

end Frame

end GGPData

end GSpinGGP
