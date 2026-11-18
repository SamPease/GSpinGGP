/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.Interface
import GSpinGGP.TraceFormula.TorusDescent
import GSpinGGP.TraceFormula.ExpCompatT
import GSpinGGP.Foundations.ExpDet
import GSpinGGP.Foundations.GSpinExpAd

/-!
# Integrability of `Δ^{s−1/2}` on the tori of `Γ(G,H)` (Thesis Prop 12.1.1)

`bp_integrable_deltaGGP_rpow`: for `x ∈ Γ(G,H)` and `s > 0`,
`∫_{T_x(F)/A_{G,H}(F)} 1_{T_♮}(t) Δ(t)^{s−1/2} dt < ∞` (Thesis Prop 12.1.1(i), proof of (12.1.2):
"a straightforward application of" BP Astérisque 418, Lemma B.1.2(i)).

**What is not stated, and why.**  BP Lemma B.1.2(i) says: for a torus `T` over `F` and linearly
independent characters `χ_1, …, χ_n ∈ X^*(T)` (over `F̄`), `t ↦ ∏ |χ_i(t) − 1|^{s−1}` is locally
integrable on `T(F)` for `Re s > 0`.  This development has no algebraic tori or character
lattices, and the statement with continuous homomorphisms in place of algebraic characters is
false (on `F^×`, `χ_1(t) = t` and `χ_2(t) = t^a` on `1 + pℤ_p` with `a ∈ ℤ_p` irrational are
ℤ-independent, but `|t − 1|^{2s−2}` is not locally integrable near `1` for `s ≤ 1/2`).  So
B.1.2(i) itself is not stated; BP states it without proof.

**The proof here.**  `T_x(F)/A_{G,H}(F)` is compact and the `exp` chart of `𝔱⁰(F) = Lie(T_x)`
carries an additive Haar measure to its Haar measure (`exists_expA_chart_torusOf`), so by
`integrable_of_chart` it suffices to bound the integrand near every `q₀ = t₀ A_{G,H}(F)` in the
chart `X ↦ t₀ e^X`.  There `Δ(t₀ e^X) = |det(P(t₀) e^{ad X} − 1)|_{W''_x}|_F`, which is comparable
to `|det(ad X|_K)|_F` with `K = W''_x ∩ ker(P(t₀) − 1)` (`exists_absF_det_mul_expA_sub_one`).  The
remaining Lie-algebra statement, `locallyIntegrable_absF_det_adV_rpow` (local integrability of
`|det(ad X|_K)|^a` on `𝔱⁰(F)` for `a > −1/2`, from the eigencharacters of `𝔱⁰` and the general
gauge lemma `locallyIntegrable_prod_gauge_rpow`), is a `sorry` theorem.  Measurability of the
integrand comes from `TraceFormula/TorusDescent.lean`.

Consistency check: at `x = 1` the conclusion is also proved directly
(`TraceFormula/MGeom.lean`, `integrable_delta_rpow_torusOf_one`).
-/

open MeasureTheory Topology Filter

noncomputable section

set_option linter.style.haveILetI false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

/-- An endomorphism commuting with `P(x)` preserves `W''_x = im(P(x) − 1)`. -/
theorem mapsTo_movedSub_of_commute {x : ↥(GSpin d.QW)} {M : Module.End F (Fin d.m → F)}
    (h : Commute (specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) M) :
    ∀ u ∈ movedSub x, M u ∈ movedSub x := by
  rintro _ ⟨w, rfl⟩
  refine ⟨M w, ?_⟩
  have e : ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) - LinearMap.id) * M =
      M * ((specP d.QW x : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) - LinearMap.id) :=
    h.sub_left (Commute.one_left M)
  exact LinearMap.congr_fun e w

/-- An endomorphism commuting with `A` preserves `ker(A − 1)`. -/
theorem mapsTo_ker_sub_one_of_commute {V : Type*} [AddCommGroup V] [Module F V]
    {A M : Module.End F V} (h : Commute A M) :
    ∀ v ∈ LinearMap.ker (A - 1), M v ∈ LinearMap.ker (A - 1) := by
  intro v hv
  rw [LinearMap.mem_ker] at hv ⊢
  have e : (A - 1) * M = M * (A - 1) := h.sub_left (Commute.one_left M)
  rw [← Module.End.mul_apply, e, Module.End.mul_apply, hv, map_zero]

/-- `P(g)` commutes with `adV X` when `g` commutes with `X ∈ gspin(W)`. -/
theorem commute_specP_adV {g : ↥(GSpin d.QW)} {X : CliffordAlgebra d.QW} (hX : X ∈ gspin d.QW)
    (hgX : (((g : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW) * X =
      X * (((g : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW)) :
    Commute (specP d.QW g : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) (adV d.QW X) := by
  refine LinearMap.ext fun v => CliffordAlgebra.ι_injective d.QW ?_
  set u : CliffordAlgebra d.QW := (((g : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW)
  set ui : CliffordAlgebra d.QW :=
    (((g : (CliffordAlgebra d.QW)ˣ)⁻¹ : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW)
  have hiX : ui * X = X * ui := by
    have h1 : ui * u = 1 := Units.inv_mul _
    have h2 : u * ui = 1 := Units.mul_inv _
    calc ui * X = ui * X * (u * ui) := by rw [h2, mul_one]
      _ = ui * (X * u) * ui := by noncomm_ring
      _ = ui * (u * X) * ui := by rw [hgX]
      _ = (ui * u) * X * ui := by noncomm_ring
      _ = X * ui := by rw [h1, one_mul]
  simp only [Module.End.mul_apply, LinearEquiv.coe_coe]
  rw [ι_specP, ι_adV hX, ι_adV hX, ι_specP]
  change u * (X * CliffordAlgebra.ι d.QW v - CliffordAlgebra.ι d.QW v * X) * ui =
    X * (u * CliffordAlgebra.ι d.QW v * ui) - u * CliffordAlgebra.ι d.QW v * ui * X
  rw [mul_sub, sub_mul, ← mul_assoc, hgX]
  simp only [mul_assoc, hiX]

/-- For `t₀ ∈ T_x`, the elements of `𝔱⁰ = Lie(T_x)` preserve `W''_x ∩ ker(P(t₀) − 1)`. -/
theorem adV_mapsTo_movedSub_inf_ker {x t₀ : ↥(GSpin d.QW)} (ht₀ : t₀ ∈ d.torusOf x)
    (X : ↥(d.lieTorus (d.torusOf x))) :
    ∀ v ∈ movedSub x ⊓ LinearMap.ker ((specP d.QW t₀ : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) - 1),
      adV d.QW (X : CliffordAlgebra d.QW) v ∈
        movedSub x ⊓ LinearMap.ker ((specP d.QW t₀ : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) - 1) := by
  have hxT : x ∈ d.torusOf x := ⟨Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff] at hh; rw [hh], fun v hv => by
    simpa [sub_eq_zero] using LinearMap.mem_ker.mp hv⟩
  have hXg := X.2.1.1
  rintro v ⟨hv1, hv2⟩
  exact ⟨d.mapsTo_movedSub_of_commute (d.commute_specP_adV hXg (X.2.2.1 x hxT)) v hv1,
    mapsTo_ker_sub_one_of_commute (d.commute_specP_adV hXg (X.2.2.1 t₀ ht₀)) v hv2⟩

/-- **The Lie-algebra form of BP Lemma B.1.2(i) at `t₀ ∈ T_x`**: for `x ∈ Γ(G,H)`, `t₀ ∈ T_x` and
`a > −1/2`, the function `X ↦ |det(ad X |_{K})|_F^a` on `𝔱⁰(F) = Lie(T_x)`, where
`K = W''_x ∩ ker(P(t₀) − 1)`, is locally integrable for an additive Haar measure.

Over `F̄`, `W''_x` has a basis `e_i, f_i` (`1 ≤ i ≤ n = dim W''_x/2`) on which `𝔱⁰` acts by
`ad X e_i = μ_i(X) e_i`, `ad X f_i = −μ_i(X) f_i` with `μ_1, …, μ_n` linearly independent (`T_x` is
a maximal torus of `GSpin(W''_x)`, Thesis §6.5), and `K ⊗ F̄` is spanned by the `e_i, f_i` with
`λ_i(t₀) = 1`; so `det(ad X|_K) = ∏_{i ∈ I} (−μ_i(X)²)`.  Grouping the `i ∈ I` by the simple
`𝔱⁰`-submodules `K_j` of `K`, `|det(ad X|_K)|^a = ∏_j |det(ad X|_{K_j})|^a`, each factor a gauge of
degree `dim K_j` (positive off the kernel, `ad X` acting on `K_j` through a field), and
`2 · rank (ad|_{K_j})_{j ∈ J} ≥ ∑_{j ∈ J} dim K_j` (each `μ_i` counted once for the pair `e_i, f_i`);
`locallyIntegrable_prod_gauge_rpow` then applies since `2a > −1`.
Status: SORRY (own work: the eigencharacter computation of Thesis Prop 12.1.1(i), with the rank
condition from the maximality of `T_x`). -/
theorem locallyIntegrable_absF_det_adV_rpow {x t₀ : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    (ht₀ : t₀ ∈ d.torusOf x) {a : ℝ} (ha : -(1 / 2) < a)
    (μ : Measure ↥(d.lieTorus (d.torusOf x))) [μ.IsAddHaarMeasure] :
    LocallyIntegrable (fun X : ↥(d.lieTorus (d.torusOf x)) =>
      absF (LinearMap.det ((adV d.QW (X : CliffordAlgebra d.QW)).restrict
        (d.adV_mapsTo_movedSub_inf_ker ht₀ X))) ^ a) μ := by
  sorry

/-- **The determinant estimate at `t₀ ∈ T_x`, in the `exp` chart**: for `x ∈ Γ(G,H)`, `t₀ ∈ T_x`
and `X ∈ 𝔱⁰(F)` near `0`, if `h ∈ T_x` has `h = e^X` and `t₀ h ∈ T_♮`, then `Δ(t₀ h)` is bounded
above by a constant and is comparable to `|det(ad X|_K)|_F`, `K = W''_x ∩ ker(P(t₀) − 1)`.
On `W''_x`, `P(t₀ h) − 1 = A e^Y − 1` with `A = P(t₀)|_{W''_x}` semisimple and
`Y = ad X|_{W''_x}` (`P(e^X) = e^{ad X}`), so `exists_absF_det_mul_expA_sub_one` applies. -/
theorem exists_eventually_deltaGGP_bounds {x t₀ : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    (ht₀ : t₀ ∈ d.torusOf x) :
    ∃ c C C' : ℝ, 0 < c ∧ ∀ᶠ X in 𝓝 (0 : ↥(d.lieTorus (d.torusOf x))), ∀ h : ↥(GSpin d.QW),
      h ∈ d.torusOf x →
      (((h : (CliffordAlgebra d.QW)ˣ)) : CliffordAlgebra d.QW) = expA F (X : CliffordAlgebra d.QW) →
      d.IsGammaElt (t₀ * h) ∧ d.torusOf (t₀ * h) = d.torusOf x →
      c * absF (LinearMap.det ((adV d.QW (X : CliffordAlgebra d.QW)).restrict
          (d.adV_mapsTo_movedSub_inf_ker ht₀ X))) ≤ deltaGGP d (t₀ * h) ∧
        deltaGGP d (t₀ * h) ≤ C * absF (LinearMap.det ((adV d.QW (X : CliffordAlgebra d.QW)).restrict
          (d.adV_mapsTo_movedSub_inf_ker ht₀ X))) ∧
        deltaGGP d (t₀ * h) ≤ C' := by
  classical
  letI : TopologicalSpace (Module.End F (Fin d.m → F)) := moduleTopology F _
  haveI : IsModuleTopology F (Module.End F (Fin d.m → F)) := ⟨rfl⟩
  set W'' := movedSub x with hW''def
  letI : TopologicalSpace (Module.End F ↥W'') := moduleTopology F _
  haveI : IsModuleTopology F (Module.End F ↥W'') := ⟨rfl⟩
  haveI : ContinuousAdd (Module.End F (Fin d.m → F)) := IsModuleTopology.toContinuousAdd F _
  haveI : ContinuousAdd (Module.End F ↥W'') := IsModuleTopology.toContinuousAdd F _
  set P : ↥(GSpin d.QW) → Module.End F (Fin d.m → F) :=
    fun g => (specP d.QW g : (Fin d.m → F) →ₗ[F] (Fin d.m → F)) with hPdef
  have hxT : x ∈ (d.torusOf x) := ⟨Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff] at hh; rw [hh], fun v hv => by
    simpa [sub_eq_zero] using LinearMap.mem_ker.mp hv⟩
  have hPmaps : ∀ t : ↥(GSpin d.QW), t ∈ (d.torusOf x) → ∀ u ∈ W'', P t u ∈ W'' := by
    intro t ht
    have hc : Commute x t := (Subgroup.mem_centralizer_singleton_iff.mp ht.1).symm
    exact d.mapsTo_movedSub_of_commute (Steinberg.commute_toLinearMap ((hc.map (specP d.QW)).symm))
  -- `(Fin d.m → F) = W'_x ⊕ W''_x` and the compression `φ : End (Fin d.m → F) → End W''`
  have hss : Module.End.IsSemisimple (P x - 1) :=
    Module.End.IsSemisimple.sub_of_commute (Commute.one_right _)
      (isSemisimple_specP_of_isSS d.QW x hx.1) Module.End.isSemisimple_id
  have hcompl : IsCompl W'' (fixedSub x) := (isCompl_ker_range_of_isSemisimple hss).symm
  obtain ⟨π, hπ⟩ : ∃ π : (Fin d.m → F) →ₗ[F] ↥W'', ∀ w : W'', π w = w :=
    ⟨_, fun w => Submodule.linearProjOfIsCompl_apply_left hcompl w⟩
  let φ : Module.End F (Fin d.m → F) →ₗ[F] Module.End F ↥W'' :=
    (LinearMap.llcomp F ↥W'' (Fin d.m → F) ↥W'' π).comp (LinearMap.lcomp F (Fin d.m → F) W''.subtype)
  have hφr : ∀ (M : Module.End F (Fin d.m → F)) (h : ∀ v ∈ W'', M v ∈ W''), φ M = M.restrict h :=
    fun M h => compress_eq_restrict hπ h
  have hφc : Continuous φ := IsModuleTopology.continuous_of_linearMap φ
  have hadc : Continuous (adV d.QW : CliffordAlgebra d.QW → Module.End F (Fin d.m → F)) :=
    IsModuleTopology.continuous_of_linearMap (adV d.QW)
  have hcoe : Tendsto (fun X : ↥(d.lieTorus (d.torusOf x)) => (X : CliffordAlgebra d.QW)) (𝓝 0) (𝓝 0) :=
    continuous_subtype_val.tendsto' 0 0 rfl
  have hadT : Tendsto (fun X : ↥(d.lieTorus (d.torusOf x)) => adV d.QW (X : CliffordAlgebra d.QW))
      (𝓝 0) (𝓝 0) := (hadc.tendsto' 0 0 (map_zero _)).comp hcoe
  have hφT : Tendsto (fun X : ↥(d.lieTorus (d.torusOf x)) => φ (adV d.QW (X : CliffordAlgebra d.QW)))
      (𝓝 0) (𝓝 0) := (hφc.tendsto' 0 0 (map_zero _)).comp hadT
  -- the determinant estimate at `A = P(t₀)|_{W''}`
  have hA : Module.End.IsSemisimple ((P t₀).restrict (hPmaps t₀ ht₀)) :=
    Module.End.IsSemisimple.restrict (hPmaps t₀ ht₀)
      (isSemisimple_specP_of_isSS d.QW t₀ (isSS_of_mem_torusOf d hx ht₀))
  obtain ⟨A, hAdef⟩ : ∃ A : Module.End F ↥W'', A = (P t₀).restrict (hPmaps t₀ ht₀) :=
    ⟨_, rfl⟩
  have hA' : A.IsSemisimple := hAdef ▸ hA
  obtain ⟨c, C, C', hc, hev⟩ := exists_absF_det_mul_expA_sub_one (F := F) (V := ↥W'') hA'
  let dK : ↥(d.lieTorus (d.torusOf x)) → ℝ := fun X => absF (LinearMap.det
    ((adV d.QW (X : CliffordAlgebra d.QW)).restrict (d.adV_mapsTo_movedSub_inf_ker ht₀ X)))
  have hKeq : (LinearMap.ker (A - 1)).map W''.subtype =
      W'' ⊓ LinearMap.ker (P t₀ - 1) := by
    ext v
    simp only [Submodule.mem_map, LinearMap.mem_ker, Submodule.mem_inf, Submodule.subtype_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w.2, ?_⟩
      have := congrArg Subtype.val hw
      simpa [hAdef, LinearMap.coe_restrict_apply] using this
    · rintro ⟨hv1, hv2⟩
      refine ⟨⟨v, hv1⟩, Subtype.ext ?_, rfl⟩
      simpa [hAdef, LinearMap.coe_restrict_apply] using hv2
  have hdK : ∀ (X : ↥(d.lieTorus (d.torusOf x))) (Y : Module.End F ↥W'')
      (hW : ∀ v ∈ W'', adV d.QW (X : CliffordAlgebra d.QW) v ∈ W''),
      Y = (adV d.QW (X : CliffordAlgebra d.QW)).restrict hW →
      ∀ hY : (∀ v ∈ LinearMap.ker (A - 1), Y v ∈ LinearMap.ker (A - 1)),
      absF (LinearMap.det (Y.restrict hY)) = dK X := by
    intro X Y hW hYe hY
    subst hYe
    have hK' : ∀ v ∈ (LinearMap.ker (A - 1)).map W''.subtype,
        adV d.QW (X : CliffordAlgebra d.QW) v ∈ (LinearMap.ker (A - 1)).map W''.subtype := by
      rw [hKeq]; exact d.adV_mapsTo_movedSub_inf_ker ht₀ X
    rw [det_restrict_restrict hW hY hK']
    exact congrArg absF (Steinberg.det_restrict_eq rfl hKeq _ _)
  refine ⟨c, C, C', hc, ?_⟩
  have E2 := hcoe.eventually (eventually_specP_eq_expA_adV (F := F) d.QW)
  have E3 := hadT.eventually (eventually_map_expA_of_pow (F := F) (B := Module.End F ↥W'') φ)
  have E4 := hφT.eventually hev
  filter_upwards [E2, E3, E4] with X hX2 hX3 hX4 h hhT hh ht
  have hXg : (X : CliffordAlgebra d.QW) ∈ gspin d.QW := X.2.1.1
  have hW : ∀ v ∈ W'', adV d.QW (X : CliffordAlgebra d.QW) v ∈ W'' :=
    d.mapsTo_movedSub_of_commute (d.commute_specP_adV hXg (X.2.2.1 x hxT))
  have hPh : P h = expA F (adV d.QW (X : CliffordAlgebra d.QW)) := hX2 hXg h hh
  have hpow : ∀ n : ℕ, φ (adV d.QW (X : CliffordAlgebra d.QW) ^ n) =
      φ (adV d.QW (X : CliffordAlgebra d.QW)) ^ n := by
    intro n
    rw [hφr _ hW, hφr _ (Module.End.pow_apply_mem_of_forall_mem n hW), Module.End.pow_restrict]
  have hexpY : expA F (φ (adV d.QW (X : CliffordAlgebra d.QW))) =
      (P h).restrict (hPmaps h hhT) := by
    rw [← hX3 hpow, ← hPh, hφr]
  obtain ⟨Y, hYdef⟩ : ∃ Y, Y = φ (adV d.QW (X : CliffordAlgebra d.QW)) := ⟨_, rfl⟩
  rw [← hYdef] at hexpY hX4
  have hYr : Y = (adV d.QW (X : CliffordAlgebra d.QW)).restrict hW := hYdef.trans (hφr _ hW)
  have hAY : Commute A Y := by
    rw [hYr, hAdef]
    have hc := d.commute_specP_adV hXg (X.2.2.1 t₀ ht₀)
    refine LinearMap.ext fun w => Subtype.ext ?_
    simpa [LinearMap.coe_restrict_apply] using LinearMap.congr_fun hc.eq w
  have hY := mapsTo_ker_sub_one_of_commute hAY
  obtain ⟨h1, h2, h3⟩ := hX4 hAY hY
  have hm : ∀ u ∈ W'', (P (t₀ * h) - 1) u ∈ W'' := fun u hu =>
    W''.sub_mem (hPmaps _ ((d.torusOf x).mul_mem ht₀ hhT) u hu) hu
  have hΔ := deltaGGP_eq_absF_det_movedSub d hx ht.2 hm
  have heq : (P (t₀ * h) - 1).restrict hm = A * expA F Y - 1 := by
    rw [hexpY]
    refine LinearMap.ext fun w => Subtype.ext ?_
    simp [hAdef, hPdef, LinearMap.coe_restrict_apply, map_mul]
  rw [hΔ, heq, ← hdK X Y hW hYr hY]
  exact ⟨h1, h2, h3⟩

end GGPData

/-- **Integrability of `Δ^{s−1/2}` on `T_x(F)/A_{G,H}(F)`** (BP Astérisque 418, Lemma B.1.2(i),
applied as in Thesis Prop 12.1.1(i), proof of (12.1.2): "a straightforward application of
Lemma B.1.2(i)"; the same step in BP's proof of their Prop 11.2.1).

For `x ∈ Γ(G,H)` with torus `T = T_x`, `T_♮ = {t ∈ T | t ∈ Γ(G,H), T_t = T}` and `s > 0`, the
function `t ↦ 1_{T_♮}(t) Δ(t)^{s−1/2}` on `T(F)` (it is `A_{G,H}(F)`-invariant: `P(ct) = P(t)`),
evaluated on coset representatives, is integrable on the compact group `T(F)/A_{G,H}(F)` for its
probability Haar measure.

The thesis's step: on `T_♮` the eigenvalues of `P(t)` on `W'' = W''_x` are `λ_i(t)^{±1}`,
`1 ≤ i ≤ n = dim W''/2`, with `λ_1, …, λ_n` linearly independent characters of `T` (`T_x` is a
maximal torus of `GSpin(W''_x)`), so `Δ^{s−1/2} = ∏ |λ_i − 1|^{2s−1}`, locally integrable by
B.1.2(i) at `2s`, hence integrable on the compact quotient.  On `T_♮`, `Δ(t)` is computed on
`W''_x` (`deltaGGP_eq_absF_det_movedSub`).

Proof here (B.1.2(i) is not stated, see the module docstring): `integrable_of_chart` with the
`exp` chart `exists_expA_chart_torusOf`; near `t₀`, `Δ(t₀ e^X) ≍ |det(ad X|_K)|_F`,
`K = W''_x ∩ ker(P(t₀) − 1)` (`exists_absF_det_mul_expA_sub_one`), so for `s < 1/2` the integrand
is dominated by `|det(ad X|_K)|^{s−1/2}`, locally integrable by
`locallyIntegrable_absF_det_adV_rpow` (SORRY); for `s ≥ 1/2` it is locally bounded.
Exact source: arXiv:1506.01452 (BP), App. B.1, Lemma B.1.2(i) (Astérisque 418, p. 281), for `F`
any local field of characteristic `0` other than `ℂ`.

Stated for `Γ`-tori only (`T = T_x`, `x ∈ Γ(G,H)`); for any other subgroup the integrand is `0`
(`TraceFormula/MGeom.lean`, `integrable_delta_rpow`). -/
theorem bp_integrable_deltaGGP_rpow (d : GGPData F) {x : ↥(GSpin d.QW)} (hx : d.IsGammaElt x)
    {s : ℝ} (hs : 0 < s) :
    letI : MeasurableSpace (d.TorusQuot (d.torusOf x)) := borel _
    haveI : BorelSpace (d.TorusQuot (d.torusOf x)) := ⟨rfl⟩
    Integrable (fun q : d.TorusQuot (d.torusOf x) =>
      Set.indicator {t : ↥(GSpin d.QW) | d.IsGammaElt t ∧ d.torusOf t = d.torusOf x}
        (fun t => deltaGGP d t ^ (s - 1 / 2))
        ((Quotient.out q : ↥(d.torusOf x)) : ↥(GSpin d.QW)))
      (probHaar (d.TorusQuot (d.torusOf x))) := by
  classical
  obtain ⟨μ, hμ, Φ, U, hUo, hU0, hΦc, hΦn, hΦU, hμS⟩ := d.exists_expA_chart_torusOf hx
  haveI := hμ
  letI : MeasurableSpace (d.TorusQuot (d.torusOf x)) := borel _
  haveI : BorelSpace (d.TorusQuot (d.torusOf x)) := ⟨rfl⟩
  haveI : CompactSpace (d.TorusQuot (d.torusOf x)) := hx.2.2
  set ν := probHaar (d.TorusQuot (d.torusOf x))
  set a : ℝ := s - 1 / 2 with hadef
  set Snat := {t : ↥(GSpin d.QW) | d.IsGammaElt t ∧ d.torusOf t = (d.torusOf x)}
  set f₀ : ↥(d.torusOf x) → ℝ := fun t => Snat.indicator (fun t => deltaGGP d t ^ a) (t : ↥(GSpin d.QW))
  have hf₀0 : ∀ t, 0 ≤ f₀ t := fun t =>
    Set.indicator_nonneg (fun t _ => Real.rpow_nonneg (deltaGGP_nonneg d t) _) _
  -- invariance under the scalars
  have hinv : ∀ t : ↥(d.torusOf x), ∀ n ∈ d.scalarsIn (d.torusOf x), f₀ (t * n) = f₀ t := by
    intro t n hn
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp hn
    have e : ((t * n : ↥(d.torusOf x)) : ↥(GSpin d.QW)) = scalarGSpin d.QW c * (t : ↥(GSpin d.QW)) := by
      rw [Subgroup.coe_mul, ← hc, (scalarGSpin_commute d.QW c _).eq]
    simp only [f₀, e, Snat, Set.indicator, Set.mem_ofPred_eq, isGammaElt_scalar_mul_iff,
      torusOf_scalar_mul, deltaGGP_scalar_mul]
  -- the chart
  refine integrable_of_chart ν μ Φ hUo hU0 hΦc hΦn (fun S hS hSm => hμS S hS hSm) ?_ ?_
  · -- measurability
    set fC : ↥(d.torusOf x) → ℂ := fun t => (f₀ t : ℂ)
    have hm := aestronglyMeasurable_comp_out (d.scalarsIn (d.torusOf x)) ν (f := fC)
      (fun t n hn => by simp only [fC, hinv t n hn]) (isOpen_torusNat d (d.torusOf x))
      (fun t ht => by simp only [fC, f₀, Set.indicator_of_notMem (s := Snat) ht, Complex.ofReal_zero])
      ((continuousOn_deltaGGP_rpow d (d.torusOf x) s).congr fun t ht => by
        simp only [fC, f₀, Set.indicator_of_mem (s := Snat) ht, hadef])
    have := Complex.continuous_re.comp_aestronglyMeasurable hm
    simpa [fC] using this
  · intro q₀
    set t₀ : ↥(d.torusOf x) := Quotient.out q₀ with ht₀def
    have hq₀ : q₀ = (t₀ : d.TorusQuot (d.torusOf x)) := (QuotientGroup.out_eq' q₀).symm
    obtain ⟨c, C, C', hc, hev⟩ := d.exists_eventually_deltaGGP_bounds hx t₀.2
    let dK : ↥(d.lieTorus (d.torusOf x)) → ℝ := fun X => absF (LinearMap.det
      ((adV d.QW (X : CliffordAlgebra d.QW)).restrict (d.adV_mapsTo_movedSub_inf_ker t₀.2 X)))
    have key : ∀ᶠ X in 𝓝 (0 : ↥(d.lieTorus (d.torusOf x))), ∃ t : ↥(d.torusOf x),
        ‖f₀ (Quotient.out (q₀ * Φ X))‖ = f₀ t ∧ ((t : ↥(GSpin d.QW)) ∈ Snat →
          c * dK X ≤ deltaGGP d t ∧ deltaGGP d t ≤ C * dK X ∧ deltaGGP d t ≤ C') := by
      filter_upwards [hUo.mem_nhds hU0, hev] with X hXU hX
      obtain ⟨h, hh, hΦh⟩ := hΦU X hXU
      refine ⟨t₀ * h, ?_, fun ht => hX h h.2 hh ht⟩
      rw [hq₀, hΦh, ← QuotientGroup.mk_mul,
        comp_out_mk_of_invariant (d.scalarsIn (d.torusOf x)) hinv, Real.norm_of_nonneg (hf₀0 _)]
    by_cases ha : 0 ≤ a
    · refine ⟨fun _ => |C'| ^ a, (locallyIntegrable_const _) 0, ?_⟩
      filter_upwards [key] with X ⟨t, hnorm, hb⟩
      rw [hnorm]
      by_cases ht : (t : ↥(GSpin d.QW)) ∈ Snat
      · simp only [f₀, Set.indicator_of_mem ht]
        exact Real.rpow_le_rpow (deltaGGP_nonneg d _) ((hb ht).2.2.trans (le_abs_self _)) ha
      · simp only [f₀, Set.indicator_of_notMem ht]
        positivity
    · push Not at ha
      have hL := d.locallyIntegrable_absF_det_adV_rpow hx t₀.2 (a := a) (by rw [hadef]; linarith) μ
      obtain ⟨V, hV, hint⟩ := hL 0
      refine ⟨fun X => c ^ a * dK X ^ a, ⟨V, hV, hint.const_mul (c ^ a)⟩, ?_⟩
      filter_upwards [key] with X ⟨t, hnorm, hb⟩
      rw [hnorm]
      by_cases ht : (t : ↥(GSpin d.QW)) ∈ Snat
      · simp only [f₀, Set.indicator_of_mem ht]
        obtain ⟨h1, h2, -⟩ := hb ht
        have hΔ0 : 0 < deltaGGP d t := deltaGGP_pos d _ ht.1.1
        have hdK0 : 0 < dK X := by
          by_contra hneg
          have h0 : dK X = 0 := le_antisymm (not_lt.mp hneg) (absF_nonneg _)
          have : C * dK X = 0 := by rw [h0, mul_zero]
          linarith
        rw [← Real.mul_rpow hc.le hdK0.le]
        exact Real.rpow_le_rpow_of_nonpos (by positivity) h1 ha.le
      · simp only [f₀, Set.indicator_of_notMem ht]
        exact mul_nonneg (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg (absF_nonneg _) _)

end GSpinGGP
