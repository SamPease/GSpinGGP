/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.EigenFrame
import GSpinGGP.GGP.Steinberg
import GSpinGGP.Foundations.HypPlane

/-!
# The torus of a semisimple element is central in its centralizer

Over an algebraically closed field of characteristic `0`, let `x ∈ GSpin(V)` with `X = P(x)` semisimple
and the moved part of its Lie centralizer abelian.  Then every `t ∈ GSpin(V)` commuting with `x` and
acting trivially on `ker (X − 1)` commutes with every `z ∈ GSpin(V)` commuting with `x`
(`commute_of_fixes_eigenspace_one`).  Route: `V = ker (X − 1) ⊥ (hyperbolic frame of eigenvectors)`
(`IsomCent.exists_hypFrame_eigen`); `P(z)` commutes with a regular element of the split torus of the
frame (`IsomCent.commute_of_lieAbelian_of_det`, with `det P(z)|_{E₋₁} = 1` by Steinberg), so it
scales each pair `eᵢ, fᵢ` by `cᵢ, cᵢ⁻¹`, hence commutes with the pair elements `eᵢ fᵢ + s fᵢ eᵢ`
(`commute_hypUnit`); `P(t)` lies in the split torus (`IsHypFrame.mem_hypTorus_of_commute`), so `t`
is a product of pair elements up to a scalar.  Own work, elementary.
-/

noncomputable section

open QuadraticMap Module CliffordAlgebra

namespace GSpinGGP

namespace Steinberg

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [Invertible (2 : K)]
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}

omit [IsAlgClosed K] [FiniteDimensional K V] in
/-- The elements of the split torus of an eigen-frame of `P(x)` lift to products of pair elements:
they commute with `x`, and with every `z` whose `P(z)` scales each pair `eᵢ, fᵢ` by `c, c⁻¹`. -/
theorem exists_frame_torus_elt {x : GSpin Q} {n : ℕ} {e f : Fin n → V} {μ : Fin n → Kˣ}
    (hF : IsHypFrame Q (Module.End.eigenspace (specP Q x : V →ₗ[K] V) 1) e f)
    (hXef : ∀ i, specP Q x (e i) = (μ i : K) • e i ∧ specP Q x (f i) = (((μ i)⁻¹ : Kˣ) : K) • f i)
    (u : Fin n → Kˣ) :
    ∃ g : GSpin Q, Commute g x ∧
      (∀ w ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) 1, specP Q g w = w) ∧
      (∀ j, specP Q g (e j) = (u j : K) • e j ∧ specP Q g (f j) = (((u j)⁻¹ : Kˣ) : K) • f j) ∧
      ∀ z : GSpin Q, (∀ j, ∃ c : Kˣ, specP Q z (e j) = (c : K) • e j ∧
        specP Q z (f j) = ((c⁻¹ : Kˣ) : K) • f j) → Commute z g := by
  classical
  have hQe : ∀ i, Q (e i) = 0 := hF.apply_e_eq_zero
  have hQf : ∀ i, Q (f i) = 0 := hF.apply_f_eq_zero
  have hp : ∀ i, polar Q (e i) (f i) = 1 := hF.polar_ef_self
  -- the pair elements
  have pair : ∀ (i : Fin n) (s : Kˣ), ∃ g : GSpin Q, Commute g x ∧
      (∀ w ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) 1, specP Q g w = w) ∧
      (∀ j, specP Q g (e j) = (if j = i then ((s⁻¹ : Kˣ) : K) else 1) • e j ∧
        specP Q g (f j) = (if j = i then (s : K) else 1) • f j) ∧
      ∀ z : GSpin Q, (∀ j, ∃ c : Kˣ, specP Q z (e j) = (c : K) • e j ∧
        specP Q z (f j) = ((c⁻¹ : Kˣ) : K) • f j) → Commute z g := by
    intro i s
    set g := hypGSpin (hQe i) (hQf i) (hp i) s
    have hg : ∀ v, specP Q g v = v + (((s⁻¹ : Kˣ) : K) - 1) • (polar Q (f i) v • e i) +
        ((s : K) - 1) • (polar Q (e i) v • f i) := specP_hypGSpin (hQe i) (hQf i) (hp i) s
    refine ⟨g, ?_, fun w hw => ?_, fun j => ⟨?_, ?_⟩, fun z hz => ?_⟩
    · have hc := commute_hypUnit (hQe i) (hQf i) (hp i) (g := x) (hXef i).1 (hXef i).2 s
      exact Subtype.ext (Units.ext hc.symm.eq)
    · have h := (hF.mem_iff w).1 hw i
      rw [hg, polar_comm _ (f i), polar_comm _ (e i), h.1, h.2]
      simp
    · rw [hg, hF.polar_fe, hF.polar_ee]
      by_cases hj : j = i
      · subst hj; simp only [ite_true, Units.val_inv_eq_inv_val]; module
      · simp [hj]
    · rw [hg, hF.polar_ff, hF.polar_ef]
      by_cases hj : j = i
      · subst hj; simp only [ite_true, Units.val_inv_eq_inv_val]; module
      · simp [hj, Ne.symm hj]
    · obtain ⟨c, hce, hcf⟩ := hz i
      exact Subtype.ext (Units.ext (commute_hypUnit (hQe i) (hQf i) (hp i) hce hcf s))
  -- products of pair elements
  have key : ∀ S : Finset (Fin n), ∃ g : GSpin Q, Commute g x ∧
      (∀ w ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) 1, specP Q g w = w) ∧
      (∀ j, specP Q g (e j) = (if j ∈ S then (u j : K) else 1) • e j ∧
        specP Q g (f j) = (if j ∈ S then (((u j)⁻¹ : Kˣ) : K) else 1) • f j) ∧
      ∀ z : GSpin Q, (∀ j, ∃ c : Kˣ, specP Q z (e j) = (c : K) • e j ∧
        specP Q z (f j) = ((c⁻¹ : Kˣ) : K) • f j) → Commute z g := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, Commute.one_left _, fun w _ => by simp, fun j => by simp,
        fun z _ => Commute.one_right _⟩
    | insert i S hi ih =>
      obtain ⟨g, hgx, hgW, hge, hgz⟩ := ih
      obtain ⟨p, hpx, hpW, hpe, hpz⟩ := pair i (u i)⁻¹
      refine ⟨p * g, hpx.mul_left hgx, fun w hw => ?_, fun j => ⟨?_, ?_⟩,
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
  obtain ⟨g, hgx, hgW, hge, hgz⟩ := key Finset.univ
  exact ⟨g, hgx, hgW, fun j => by simpa using hge j, hgz⟩

/-- **The torus of `x` is central in its centralizer** (over an algebraically closed field of
characteristic `0`): if `P(x)` is semisimple with abelian moved Lie centralizer, then every `t`
commuting with `x` and acting trivially on `ker (P(x) − 1)` commutes with every `z` commuting with
`x`. -/
theorem commute_of_fixes_eigenspace_one (hQ : IsNondeg Q) {x : GSpin Q}
    (hss : Module.End.IsSemisimple (specP Q x : V →ₗ[K] V))
    (hL : IsomCent.LieAbelian (bform Q) (specP Q x : V →ₗ[K] V))
    {t z : GSpin Q} (htx : Commute t x)
    (htW : ∀ w ∈ Module.End.eigenspace (specP Q x : V →ₗ[K] V) 1, specP Q t w = w)
    (hzx : Commute z x) : Commute z t := by
  have hB : (bform Q).IsSymm := ⟨fun u v => bform_comm Q u v⟩
  have hiso : ∀ g : GSpin Q, (bform Q).IsOrthogonal (specP Q g : V →ₗ[K] V) :=
    fun g u v => bform_specP g u v
  have hpnd : (polarBilin Q).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr ((isNondeg_iff_nondegenerate _).1 hQ)
  obtain ⟨n, e, f, μ, hF, hXef⟩ := IsomCent.exists_hypFrame_eigen hpnd
    (fun a b => polar_specP x a b) hss (det_specP x)
  -- a regular element `gₖ` of the split torus
  obtain ⟨tk, ht1, htinj, htinv⟩ := exists_regular_units K n
  obtain ⟨gk, hgkx, hgkW, hgke, -⟩ := exists_frame_torus_elt hF hXef tk
  -- `P(z)` commutes with `P(gₖ)`, so it scales each frame pair
  have hdz := (commute_iff_det_negFixedSub hQ x hss z (hzx.map (specP Q))).1 hzx
  have hcm := IsomCent.commute_of_lieAbelian_of_det hB hQ (hiso x) hss hL (hiso gk) (hiso z)
    (det_specP gk) (commute_toLinearMap (hgkx.map (specP Q)))
    (commute_toLinearMap (hzx.map (specP Q))) hgkW hdz
  have hcm' : Commute (specP Q gk) (specP Q z) := LinearEquiv.toLinearMap_injective (by
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul]; exact hcm.eq)
  have hE := hF.eq_smul_e_of_commute hgkW hgke ht1 htinj htinv hcm'
  have hFf := hF.eq_smul_f_of_commute hgkW hgke ht1 htinj htinv hcm'
  have hcc : ∀ i, polar Q (specP Q z (e i)) (f i) * polar Q (specP Q z (f i)) (e i) = 1 :=
    fun i => by
    have h := polar_specP z (e i) (f i)
    rw [hE i, hFf i, polar_smul_left, polar_smul_right] at h
    simp only [hF.polar_ef, ↓reduceIte] at h
    simpa [smul_eq_mul, mul_comm] using h
  have hzs : ∀ j, ∃ c : Kˣ, specP Q z (e j) = (c : K) • e j ∧
      specP Q z (f j) = ((c⁻¹ : Kˣ) : K) • f j := fun j =>
    ⟨⟨_, _, hcc j, by rw [mul_comm]; exact hcc j⟩, hE j, hFf j⟩
  -- `P(t)` lies in the split torus, so `t` is a product of pair elements up to a scalar
  have hct := IsomCent.commute_of_lieAbelian hB hQ (hiso x) hss hL (hiso gk) (hiso t)
    (det_specP gk) (det_specP t) (commute_toLinearMap (hgkx.map (specP Q)))
    (commute_toLinearMap (htx.map (specP Q))) hgkW htW
  have hct' : Commute (specP Q gk) (specP Q t) := LinearEquiv.toLinearMap_injective (by
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul]; exact hct.eq)
  obtain ⟨-, u, hu⟩ := hF.mem_hypTorus_of_commute (k := specP Q gk) hgkW hgke ht1 htinj htinv
    (fun a b => polar_specP t a b) htW hct'
  obtain ⟨g, -, hgW, hge, hgz⟩ := exists_frame_torus_elt hF hXef u
  have hPtg : specP Q t = specP Q g := LinearEquiv.toLinearMap_injective
    (hF.linearMap_ext (fun w hw => by simp only [LinearEquiv.coe_coe, hgW w hw, htW w hw])
      (fun j => by simp only [LinearEquiv.coe_coe, (hge j).1, (hu j).1])
      (fun j => by simp only [LinearEquiv.coe_coe, (hge j).2, (hu j).2]))
  have hker : t * g⁻¹ ∈ (specP Q).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hPtg, mul_inv_cancel]
  rw [ker_specP hQ] at hker
  obtain ⟨c, hc⟩ := hker
  have htg : t = scalarGSpin Q c * g := by rw [hc, inv_mul_cancel_right]
  rw [htg]
  exact ((scalarGSpin_mem_center Q c).comm z).symm.mul_right (hgz z hzs)

end Steinberg

end GSpinGGP
