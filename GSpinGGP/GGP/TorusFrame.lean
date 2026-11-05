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

/-- The torus element `h(s) ∈ GSpin(W)(F̄)` of the pair `eᵢ, fᵢ` lies in `T_x(F̄)`, scales `eⱼ, fⱼ`
by `s⁻¹, s` for `j = i` and fixes them otherwise, and fixes `W'_x ⊗ F̄`. -/
theorem exists_pair_mem_torusFbar {n : ℕ} {e f : Fin n → Wb} {μ : Fin n → Kbˣ}
    (hF : IsHypFrame (d.QW.baseChange Kb) (Module.End.eigenspace XX 1) e f)
    (hXef : ∀ i, XX (e i) = (μ i : Kb) • e i ∧ XX (f i) = (((μ i)⁻¹ : Kbˣ) : Kb) • f i)
    (i : Fin n) (s : Kbˣ) :
    ∃ g ∈ d.torusFbar x, (∀ w ∈ Module.End.eigenspace XX 1, specP _ g w = w) ∧
      (∀ j, specP _ g (e j) = (if j = i then ((s⁻¹ : Kbˣ) : Kb) else 1) • e j ∧
        specP _ g (f j) = (if j = i then (s : Kb) else 1) • f j) ∧
      ∀ z : GSpin (d.QW.baseChange Kb), (∀ j, ∃ c : Kbˣ, specP _ z (e j) = (c : Kb) • e j ∧
        specP _ z (f j) = ((c⁻¹ : Kbˣ) : Kb) • f j) →
        Commute ((z : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb))
          ((g : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb)) := by
  have h2 : (2 : Kb) ≠ 0 := two_ne_zero
  have hQe : d.QW.baseChange Kb (e i) = 0 := by
    have h := polar_self (d.QW.baseChange Kb) (e i)
    rw [hF.polar_ee, nsmul_eq_mul, Nat.cast_ofNat] at h
    exact (mul_eq_zero.1 h.symm).resolve_left h2
  have hQf : d.QW.baseChange Kb (f i) = 0 := by
    have h := polar_self (d.QW.baseChange Kb) (f i)
    rw [hF.polar_ff, nsmul_eq_mul, Nat.cast_ofNat] at h
    exact (mul_eq_zero.1 h.symm).resolve_left h2
  have hp : polar (d.QW.baseChange Kb) (e i) (f i) = 1 := by simp [hF.polar_ef]
  set g := hypGSpin hQe hQf hp s
  have hg : ∀ v, specP _ g v = v + (((s⁻¹ : Kbˣ) : Kb) - 1) •
      (polar (d.QW.baseChange Kb) (f i) v • e i) +
      ((s : Kb) - 1) • (polar (d.QW.baseChange Kb) (e i) v • f i) := specP_hypGSpin hQe hQf hp s
  have hW : ∀ w ∈ Module.End.eigenspace XX 1, specP _ g w = w := fun w hw => by
    have h := (hF.mem_iff w).1 hw i
    rw [hg, polar_comm _ (f i), polar_comm _ (e i), h.1, h.2]
    simp
  refine ⟨g, ⟨?_, fun w hw => hW w ?_⟩, hW, fun j => ⟨?_, ?_⟩, fun z hz => ?_⟩
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
  · obtain ⟨c, hce, hcf⟩ := hz i
    exact commute_hypUnit hQe hQf hp hce hcf s

/-- Every element of the split torus of an eigen-frame is `P(g)` for some `g ∈ T_x(F̄)`: a
product of the pair elements. -/
theorem exists_torusFbar_scale {n : ℕ} {e f : Fin n → Wb}
    {μ : Fin n → Kbˣ}
    (hF : IsHypFrame (d.QW.baseChange Kb) (Module.End.eigenspace XX 1) e f)
    (hXef : ∀ i, XX (e i) = (μ i : Kb) • e i ∧
      XX (f i) = (((μ i)⁻¹ : Kbˣ) : Kb) • f i)
    (t : Fin n → Kbˣ) :
    ∃ g ∈ d.torusFbar x, (∀ w ∈ Module.End.eigenspace XX 1, specP _ g w = w) ∧
      (∀ j, specP _ g (e j) = (t j : Kb) • e j ∧
        specP _ g (f j) = (((t j)⁻¹ : Kbˣ) : Kb) • f j) ∧
      ∀ z : GSpin (d.QW.baseChange Kb), (∀ j, ∃ c : Kbˣ, specP _ z (e j) = (c : Kb) • e j ∧
        specP _ z (f j) = ((c⁻¹ : Kbˣ) : Kb) • f j) →
        Commute ((z : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb))
          ((g : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb)) := by
  have key : ∀ S : Finset (Fin n), ∃ g ∈ d.torusFbar x,
      (∀ w ∈ Module.End.eigenspace XX 1, specP _ g w = w) ∧
      (∀ j, specP _ g (e j) = (if j ∈ S then (t j : Kb) else 1) • e j ∧
        specP _ g (f j) =
          (if j ∈ S then (((t j)⁻¹ : Kbˣ) : Kb) else 1) • f j) ∧
      ∀ z : GSpin (d.QW.baseChange Kb), (∀ j, ∃ c : Kbˣ, specP _ z (e j) = (c : Kb) • e j ∧
        specP _ z (f j) = ((c⁻¹ : Kbˣ) : Kb) • f j) →
        Commute ((z : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb))
          ((g : (CliffordAlgebra (d.QW.baseChange Kb))ˣ) : CliffordAlgebra (d.QW.baseChange Kb)) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, Subgroup.one_mem _, fun w _ => by simp, fun j => by simp,
        fun z _ => Commute.one_right _⟩
    | insert i S hi ih =>
      obtain ⟨g, hg, hgW, hge, hgz⟩ := ih
      obtain ⟨p, hp, hpW, hpe, hpz⟩ := exists_pair_mem_torusFbar x hF hXef i (t i)⁻¹
      refine ⟨p * g, Subgroup.mul_mem _ hp hg, fun w hw => ?_, fun j => ⟨?_, ?_⟩,
        fun z hz => (hpz z hz).mul_right (hgz z hz)⟩
      · rw [map_mul, LinearEquiv.mul_apply, hgW w hw, hpW w hw]
      · rw [map_mul, LinearEquiv.mul_apply, (hge j).1, map_smul, (hpe j).1, smul_smul]
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj]
      · rw [map_mul, LinearEquiv.mul_apply, (hge j).2, map_smul, (hpe j).2, smul_smul]
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj]
  obtain ⟨g, hg, hgW, hge, hgz⟩ := key Finset.univ
  exact ⟨g, hg, hgW, fun j => by simpa using hge j, hgz⟩

/-- The split torus of an eigen-frame lies in `S_x(F̄)`. -/
theorem hypTorus_le_map_torusFbar {n : ℕ} {e f : Fin n → Wb}
    {μ : Fin n → Kbˣ}
    (hF : IsHypFrame (d.QW.baseChange Kb) (Module.End.eigenspace XX 1) e f)
    (hXef : ∀ i, XX (e i) = (μ i : Kb) • e i ∧
      XX (f i) = (((μ i)⁻¹ : Kbˣ) : Kb) • f i) :
    hypTorus (Module.End.eigenspace XX 1) e f ≤ (d.torusFbar x).map (specP _) := by
  rintro h ⟨hW, t, ht⟩
  obtain ⟨g, hg, hgW, hge, -⟩ := exists_torusFbar_scale x hF hXef t
  refine ⟨g, hg, LinearEquiv.toLinearMap_injective (hF.linearMap_ext (fun w hw => ?_)
    (fun j => ?_) (fun j => ?_))⟩
  · simp only [LinearEquiv.coe_coe, hgW w hw, hW w hw]
  · simp only [LinearEquiv.coe_coe, (hge j).1, (ht j).1]
  · simp only [LinearEquiv.coe_coe, (hge j).2, (ht j).2]

/-- A **regular** element of the split torus of an eigen-frame: `P(g)` scales `eᵢ, fᵢ` by `tᵢ, tᵢ⁻¹`
with `tᵢ ≠ 1`, the `tᵢ` distinct and `tᵢ tⱼ ≠ 1` (`tᵢ = 2^{i+1}`). -/
theorem exists_regular_torusFbar {n : ℕ} {e f : Fin n → Wb} {μ : Fin n → Kbˣ}
    (hF : IsHypFrame (d.QW.baseChange Kb) (Module.End.eigenspace XX 1) e f)
    (hXef : ∀ i, XX (e i) = (μ i : Kb) • e i ∧ XX (f i) = (((μ i)⁻¹ : Kbˣ) : Kb) • f i) :
    ∃ (t : Fin n → Kbˣ), ∃ g ∈ d.torusFbar x,
      (∀ w ∈ Module.End.eigenspace XX 1, specP _ g w = w) ∧
      (∀ j, specP _ g (e j) = (t j : Kb) • e j ∧ specP _ g (f j) = (((t j)⁻¹ : Kbˣ) : Kb) • f j) ∧
      (∀ i, (t i : Kb) ≠ 1) ∧ (∀ i j, (t i : Kb) = t j → i = j) ∧ (∀ i j, (t i : Kb) * t j ≠ 1) := by
  -- a regular element `k = P(gₖ)`, `tᵢ = 2^{i+1}`
  have h2 : ∀ k : ℕ, ((2 : Kb) ^ k) = ((2 ^ k : ℕ) : Kb) := by
    intro k; push_cast; rfl
  let t : Fin n → Kbˣ := fun i =>
    Units.mk0 ((2 : Kb) ^ (i.val + 1)) (pow_ne_zero _ two_ne_zero)
  have ht1 : ∀ i, (t i : Kb) ≠ 1 := fun i => by
    simp only [t, Units.val_mk0, h2]
    exact_mod_cast (Nat.one_lt_two_pow (Nat.succ_ne_zero _)).ne'
  have htinj : ∀ i j, (t i : Kb) = t j → i = j := fun i j hij => by
    simp only [t, Units.val_mk0, h2] at hij
    have : 2 ^ (i.val + 1) = 2 ^ (j.val + 1) := by exact_mod_cast hij
    exact Fin.ext (by have := Nat.pow_right_injective le_rfl this; omega)
  have htinv : ∀ i j, (t i : Kb) * t j ≠ 1 := fun i j => by
    simp only [t, Units.val_mk0]
    rw [← pow_add, h2]
    exact_mod_cast (Nat.one_lt_two_pow (by omega : i.val + 1 + (j.val + 1) ≠ 0)).ne'
  obtain ⟨gk, hgk, hgkW, hgke, -⟩ := exists_torusFbar_scale x hF hXef t
  exact ⟨t, gk, hgk, hgkW, hgke, ht1, htinj, htinv⟩

/-- **`S_x(F̄)` is the split torus of an eigen-frame of `P(x)_{F̄}`**, for `x ∈ Γ(G,H)`, with the
eigenvalues `μᵢ, μᵢ⁻¹` of the frame. -/
theorem exists_hypFrame_eigen_torusFbar (hx : d.IsGammaElt x) :
    ∃ (n : ℕ) (e f : Fin n → Wb) (μ : Fin n → Kbˣ),
      IsHypFrame (d.QW.baseChange Kb) (Module.End.eigenspace XX 1) e f ∧
        (∀ i, XX (e i) = (μ i : Kb) • e i ∧ XX (f i) = (((μ i)⁻¹ : Kbˣ) : Kb) • f i) ∧
        (d.torusFbar x).map (specP _) = hypTorus (Module.End.eigenspace XX 1) e f := by
  have hss : Module.End.IsSemisimple XX := by
    rw [specP_bcGSpin]; exact isSemisimple_specP_baseChange x hx.1
  obtain ⟨n, e, f, μ, hF, hXef⟩ := IsomCent.exists_hypFrame_eigen
    polarBilin_baseChange_nondegenerate
    (fun a b => Steinberg.polar_specP (bcGSpin d.QW x) a b) hss (det_specP _)
  refine ⟨n, e, f, μ, hF, hXef, le_antisymm ?_ (hypTorus_le_map_torusFbar x hF hXef)⟩
  obtain ⟨t, gk, hgk, hgkW, hgke, ht1, htinj, htinv⟩ := exists_regular_torusFbar x hF hXef
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


/-- **`S_x(F̄)` is the split torus of an eigen-frame of `P(x)_{F̄}`**, for `x ∈ Γ(G,H)`. -/
theorem exists_hypFrame_torusFbar (hx : d.IsGammaElt x) :
    ∃ (n : ℕ) (e f : Fin n → Wb),
      IsHypFrame (d.QW.baseChange Kb) (Module.End.eigenspace XX 1) e f ∧
        (d.torusFbar x).map (specP _) = hypTorus (Module.End.eigenspace XX 1) e f := by
  obtain ⟨n, e, f, -, hF, -, hT⟩ := exists_hypFrame_eigen_torusFbar x hx
  exact ⟨n, e, f, hF, hT⟩

/-- **`T_x(F̄)` is central in the centralizer of `x` in `GSpin(W)(F̄)`**, for `x ∈ Γ(G,H)`.  `P(z)`
commutes with a regular element of the split torus of an eigen-frame (`commute_of_lieAbelian_of_det`;
`det P(z)|_{W₋₁} = 1` by Steinberg), so it scales each frame pair `eᵢ, fᵢ` by `cᵢ, cᵢ⁻¹`; then `z`
commutes with the pair elements `h(s)` (`commute_hypUnit`), whose product is `t` up to a scalar. -/
theorem commute_of_mem_torusFbar (hx : d.IsGammaElt x) {t z : GSpin (d.QW.baseChange Kb)}
    (ht : t ∈ d.torusFbar x) (hz : Commute z (bcGSpin d.QW x)) : Commute z t := by
  have hQL := isNondeg_baseChange d.QW d.nondeg
  have hss : Module.End.IsSemisimple XX := by
    rw [specP_bcGSpin]; exact isSemisimple_specP_baseChange x hx.1
  have hL : IsomCent.LieAbelian (bform (d.QW.baseChange Kb)) XX := by
    rw [specP_bcGSpin]; exact lieAbelian_specP_baseChange x hx
  have hB : (bform (d.QW.baseChange Kb)).IsSymm := ⟨fun u v => bform_comm _ u v⟩
  have hiso : ∀ g : GSpin (d.QW.baseChange Kb), IsomCent.IsIsom (bform (d.QW.baseChange Kb))
      (specP _ g : Wb →ₗ[Kb] Wb) := fun g u v => bform_specP g u v
  obtain ⟨n, e, f, μ, hF, hXef, hT⟩ := exists_hypFrame_eigen_torusFbar x hx
  obtain ⟨tk, gk, hgk, hgkW, hgke, ht1, htinj, htinv⟩ := exists_regular_torusFbar x hF hXef
  -- `P(z)` commutes with `P(gₖ)`
  have hzX : Commute (specP _ z) (specP _ (bcGSpin d.QW x)) := hz.map (specP _)
  have hgkX : Commute (specP _ gk) (specP _ (bcGSpin d.QW x)) :=
    (show Commute gk (bcGSpin d.QW x) from Subtype.ext hgk.1).map (specP _)
  have hdz := (Steinberg.commute_iff_det_negFixedSub hQL (bcGSpin d.QW x) hss z hzX).1 hz
  have hcm := IsomCent.commute_of_lieAbelian_of_det hB hQL (hiso _) hss hL (hiso gk) (hiso z)
    (det_specP gk) (Steinberg.commute_toLinearMap hgkX) (Steinberg.commute_toLinearMap hzX)
    hgkW hdz
  have hcm' : Commute (specP _ gk) (specP _ z) :=
    LinearEquiv.toLinearMap_injective (by
      rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul]; exact hcm.eq)
  -- `P(z)` scales each frame pair
  have hE := hF.eq_smul_e_of_commute hgkW hgke ht1 htinj htinv hcm'
  have hFf := hF.eq_smul_f_of_commute hgkW hgke ht1 htinj htinv hcm'
  have hcc : ∀ i, polar (d.QW.baseChange Kb) (specP _ z (e i)) (f i) *
      polar (d.QW.baseChange Kb) (specP _ z (f i)) (e i) = 1 := fun i => by
    have h := Steinberg.polar_specP z (e i) (f i)
    rw [hE i, hFf i, polar_smul_left, polar_smul_right] at h
    simp only [hF.polar_ef, ↓reduceIte] at h
    simpa [smul_eq_mul, mul_comm] using h
  have hzs : ∀ j, ∃ c : Kbˣ, specP _ z (e j) = (c : Kb) • e j ∧
      specP _ z (f j) = ((c⁻¹ : Kbˣ) : Kb) • f j := fun j =>
    ⟨⟨_, _, hcc j, by rw [mul_comm]; exact hcc j⟩, hE j, hFf j⟩
  -- `t` is a product of pair elements, up to a scalar
  obtain ⟨-, u, hu⟩ : specP _ t ∈ hypTorus (Module.End.eigenspace XX 1) e f := hT ▸ ⟨t, ht, rfl⟩
  obtain ⟨g, -, hgW, hge, hgz⟩ := exists_torusFbar_scale x hF hXef u
  have hPtg : specP _ t = specP _ g := LinearEquiv.toLinearMap_injective
    (hF.linearMap_ext (fun w hw => by
      simp only [LinearEquiv.coe_coe, hgW w hw]
      exact ht.2 w (by rw [← GGPData.eigenspace_bc_one]; exact hw))
      (fun j => by simp only [LinearEquiv.coe_coe, (hge j).1, (hu j).1])
      (fun j => by simp only [LinearEquiv.coe_coe, (hge j).2, (hu j).2]))
  have hker : t * g⁻¹ ∈ (specP (d.QW.baseChange Kb)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hPtg, mul_inv_cancel]
  rw [ker_specP hQL] at hker
  obtain ⟨c, hc⟩ := hker
  have htg : t = scalarGSpin _ c * g := by rw [hc, inv_mul_cancel_right]
  rw [htg]
  refine Commute.mul_right ?_ (Subtype.ext (Units.ext (hgz z hzs)))
  exact ((scalarGSpin_mem_center _ c).comm z).symm

end Frame

end GGPData

end GSpinGGP
