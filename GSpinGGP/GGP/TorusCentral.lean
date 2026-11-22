/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.EigenFrame
import GSpinGGP.GGP.Steinberg
import GSpinGGP.Foundations.HypPlane
import GSpinGGP.Foundations.SoCentralizer
import GSpinGGP.Foundations.QuadraticForms

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
      · rw [map_mul, mul_apply_eq_comp, hgW w hw, hpW w hw]
      · rw [map_mul, mul_apply_eq_comp, (hge j).1, map_smul, (hpe j).1, smul_smul]
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj]
      · rw [map_mul, mul_apply_eq_comp, (hge j).2, map_smul, (hpe j).2, smul_smul]
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

/-- **Regular centralizers are commutative**, over an algebraically closed field of
characteristic `0`: if `P(x)` is semisimple and `so(V)_{P(x)}` (`soCent`) is abelian, any two elements of
`GSpin(V)` commuting with `x` commute.  `so(V)_{P(x)} ⊇ so(ker (P(x) − 1))` forces
`dim ker (P(x) − 1) ≤ 2` (`IsomCent.finrank_eigenspace_neg_one_le_two` for `−P(x)`).  An element
commuting with `x` has determinant `1` on `ker (P(x) − 1)`
(`det_restrict_one_eq_one_of_commute`): in dimension `≤ 1` it fixes `ker (P(x) − 1)`, and
`commute_of_fixes_eigenspace_one` applies.  In dimension `2`, `ker (P(x) − 1)` is a hyperbolic
plane `⟨e, f⟩` on which `P(g)` acts by `diag(c, c⁻¹)` (`exists_smul_of_det_restrict_eq_one`); with
`s` the pair element of `⟨e, f⟩` acting by `diag(c⁻¹, c)`, `g s` fixes `ker (P(x) − 1)`, so
commutes with `h`, and `s` commutes with `h` (`commute_hypUnit`), hence so does `g`. -/
theorem commute_of_forall_skew_commute (hQ : IsNondeg Q) {x : GSpin Q}
    (hss : Module.End.IsSemisimple (specP Q x : V →ₗ[K] V))
    (hab : ∀ M₁ ∈ soCent Q (specP Q x : V →ₗ[K] V), ∀ M₂ ∈ soCent Q (specP Q x : V →ₗ[K] V),
      Commute M₁ M₂)
    {g h : GSpin Q} (hg : Commute g x) (hh : Commute h x) : Commute g h := by
  set X : Module.End K V := (specP Q x : V →ₗ[K] V) with hXdef
  have hB : (bform Q).IsSymm := ⟨fun u v => bform_comm Q u v⟩
  have hXo := isOrthogonal_specP x
  have hab' : ∀ Y₁ Y₂ : Module.End K V, (bform Q).IsSkewAdjoint Y₁ → (bform Q).IsSkewAdjoint Y₂ →
      Commute X Y₁ → Commute X Y₂ → Commute Y₁ Y₂ := fun Y₁ Y₂ h₁ h₂ c₁ c₂ =>
    hab Y₁ (mem_soCent.2 ⟨h₁.eq, c₁.eq.symm⟩) Y₂ (mem_soCent.2 ⟨h₂.eq, c₂.eq.symm⟩)
  have hL : IsomCent.LieAbelian (bform Q) X := fun Y₁ Y₂ h₁ h₂ c₁ c₂ _ _ => hab' Y₁ Y₂ h₁ h₂ c₁ c₂
  -- `dim ker (X − 1) ≤ 2`
  have hE : Module.End.eigenspace (-X) (-1) = Module.End.eigenspace X 1 := by
    ext v; simp
  have hdim : finrank K (Module.End.eigenspace X 1) ≤ 2 := by
    rw [← hE]
    refine IsomCent.finrank_eigenspace_neg_one_le_two hB hQ (fun u v => ?_)
      (Module.End.isSemisimple_neg.2 hss) ?_
    · simp only [LinearMap.neg_apply, map_neg, neg_neg]
      exact hXo u v
    · intro Y₁ Y₂ h₁ h₂ c₁ c₂ _ _
      exact hab' Y₁ Y₂ h₁ h₂ (by simpa using c₁.neg_left) (by simpa using c₂.neg_left)
  obtain ⟨hcg, hdg⟩ := det_restrict_one_eq_one_of_commute hQ x hss g hg
  obtain ⟨hch, hdh⟩ := det_restrict_one_eq_one_of_commute hQ x hss h hh
  rcases Nat.lt_or_ge (finrank K (Module.End.eigenspace X 1)) 2 with h1 | h2
  · -- `dim ≤ 1`: `P(g)` fixes `ker (X − 1)`
    refine (commute_of_fixes_eigenspace_one hQ hss hL hg (fun w hw => ?_) hh).symm
    rcases Nat.lt_succ_iff.1 h1 |> Nat.le_one_iff_eq_zero_or_eq_one.1 with h0 | h1
    · have : (⟨w, hw⟩ : Module.End.eigenspace X 1) = 0 :=
        (Module.finrank_zero_iff.1 h0).elim _ _
      rw [show w = 0 from congrArg Subtype.val this, map_zero]
    · obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one h1
        ((specP Q g : V →ₗ[K] V).restrict
          (IsomCent.mapsTo_eigenspace_of_commute (commute_toLinearMap hcg) 1))
      rw [hc, LinearMap.det_smul, LinearMap.det_id, h1, pow_one, mul_one] at hdg
      have := congrArg Subtype.val (LinearMap.congr_fun hc ⟨w, hw⟩)
      rw [hdg, one_smul, LinearMap.coe_restrict_apply] at this
      exact this
  · -- `dim = 2`: a hyperbolic plane
    have h2 : finrank K (Module.End.eigenspace X 1) = 2 := le_antisymm hdim h2
    have hnd : ∀ u ∈ Module.End.eigenspace X 1,
        (∀ u' ∈ Module.End.eigenspace X 1, polar Q u u' = 0) → u = 0 := by
      intro u hu h0
      have h := (IsomCent.pairing_eigenspace hB hQ hXo hss 1).2 u hu
      rw [inv_one] at h
      refine h fun w hw => ?_
      have := h0 w hw
      rw [polar_eq_two_mul_bform] at this
      exact (mul_eq_zero.1 this).resolve_left two_ne_zero
    obtain ⟨e, he, f, hf, hQe, hQf, hef⟩ := exists_hypPair_of_finrank_eq_two h2 hnd
    have hee : polar Q e e = 0 := by rw [polar_self, hQe, smul_zero]
    have hff : polar Q f f = 0 := by rw [polar_self, hQf, smul_zero]
    obtain ⟨c, hce, hcf⟩ := exists_smul_of_det_restrict_eq_one (specP_isometry g) h2 _ he hf hQe
      hQf hef hdg
    obtain ⟨d, hde, hdf⟩ := exists_smul_of_det_restrict_eq_one (specP_isometry h) h2 _ he hf hQe
      hQf hef hdh
    have hfe : polar Q f e = 1 := by rw [polar_comm, hef]
    set s := hypGSpin hQe hQf hef c
    have hs : ∀ v, specP Q s v = v + (((c⁻¹ : Kˣ) : K) - 1) • (polar Q f v • e) +
        ((c : K) - 1) • (polar Q e v • f) := specP_hypGSpin hQe hQf hef c
    -- `s` commutes with `x` and `h`
    have hxe : specP Q x e = ((1 : Kˣ) : K) • e := by
      rw [Units.val_one, one_smul]; exact Module.End.mem_eigenspace_iff.1 he |>.trans (one_smul _ _)
    have hxf : specP Q x f = (((1 : Kˣ)⁻¹ : Kˣ) : K) • f := by
      rw [inv_one, Units.val_one, one_smul]
      exact Module.End.mem_eigenspace_iff.1 hf |>.trans (one_smul _ _)
    have hsx : Commute s x :=
      Subtype.ext (Units.ext (commute_hypUnit hQe hQf hef hxe hxf c).symm.eq)
    have hhs : Commute h s := Subtype.ext (Units.ext (commute_hypUnit hQe hQf hef hde hdf c))
    -- `g s` fixes `ker (X − 1)`, so commutes with `h`
    have hse : specP Q s e = ((c⁻¹ : Kˣ) : K) • e := by rw [hs, hfe, hee]; module
    have hsf : specP Q s f = (c : K) • f := by rw [hs, hff, hef]; module
    have hgs : ∀ w ∈ Module.End.eigenspace X 1, specP Q (g * s) w = w := by
      intro w hw
      obtain ⟨α, β, rfl⟩ := exists_eq_smul_add_smul_of_hypPair h2 he hf hQe hQf hef hw
      have hce' : specP Q g e = (c : K) • e := hce
      have hcf' : specP Q g f = ((c⁻¹ : Kˣ) : K) • f := hcf
      rw [map_mul, mul_apply_eq_comp, map_add, map_smul, map_smul, hse, hsf, map_add,
        map_smul, map_smul, map_smul, map_smul, hce', hcf', smul_smul, smul_smul]
      simp
    have hhgs := commute_of_fixes_eigenspace_one hQ hss hL (hg.mul_left hsx) hgs hh
    have hgh : Commute h g := by
      have e1 : g = g * s * s⁻¹ := by group
      rw [e1]
      exact hhgs.mul_right hhs.inv_right
    exact hgh.symm

end Steinberg

end GSpinGGP
