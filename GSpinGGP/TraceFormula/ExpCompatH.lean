/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.ExpCompatT
import GSpinGGP.TraceFormula.ExpIntertwine

/-!
# The `exp`-compatible measure on `𝔥⁰(F)`

* `eventually_exists_sub_algebraMap_mem_lieH0`: near `0`, `e^W ∈ H(F)` forces
  `W ∈ 𝔥⁰ ⊕ F·(1,1)` (the logarithm direction of `Lie(H) = 𝔥⁰ ⊕ Lie(A_{G,H})`, Thesis §5.2).
* `exists_isExpCompatH`: an additive Haar measure on `𝔥⁰(F)` compatible through `exp` with
  `Measure.haar` on `H(F)/A_{G,H}(F)` (`IsExpCompatH`, defined in `TraceFormula/LieAlgebra.lean`).
-/

noncomputable section

open MeasureTheory Topology Filter Module CliffordAlgebra

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

namespace GGPData

variable (d : GGPData F)

-- the proof juggles two auxiliary subalgebras and several `exp` neighbourhoods
set_option maxHeartbeats 400000 in
/-- **`Lie(H) = 𝔥⁰ ⊕ F·(1,1)` near `0`, the logarithm direction** (Thesis §5.2): for `W` near `0`
with `e^W ∈ H(F)`, `W − (t, t) ∈ 𝔥⁰` for a scalar `t`. Write `W = (a₁ + S₁, a₂ + S₂)` with `aᵢ`
scalars and `Sᵢ ∈ so` (`W ∈ 𝔤`, `eventually_mem_lie_of_expA_mem`), and `φ : C(W) → C(V)`.
* `a₁ = a₂`: the `(x, y)` with `y − φ x ∈ C(V)_{≥1}` form a subalgebra containing `H(F)`
  (`h = (x, φ(x) n)`, `n − 1 ∈ C(V)_{≥1}`), hence `W` (`exists_nhds_mem_of_expA_mem`); so
  `W₂ − φ W₁ = (a₂ − a₁) + (S₂ − φ S₁)` is nilpotent, of trace `0`.
* `S₂ − φ S₁ ∈ 𝔫`: in `End V × End V`, the pairs `(A, B)` stabilizing the flag and `Z_rᗮ` with
  `B − A` flag-raising form a subalgebra containing `(P(x), P(φ(x) n))`
  `= (e^{ad φ W₁}, e^{ad W₂})` (`eventually_specP_eq_expA_adV`), hence `(ad φ W₁, ad W₂)`. -/
theorem eventually_exists_sub_algebraMap_mem_lieH0 :
    ∀ᶠ W in 𝓝 (0 : d.ambient), ∀ h : ↥d.H,
      (((h : ↥d.G) : d.ambientˣ) : d.ambient) = expA F W →
      ∃ t : F, W - algebraMap F d.ambient t ∈ d.lieH0 := by
  haveI : IsModuleTopology F (Module.End F d.V) := ⟨rfl⟩
  haveI := isTopologicalRing_of_moduleTopology F (Module.End F d.V)
  haveI : Module.Finite F (Module.End F d.V × Module.End F d.V) := inferInstance
  haveI : IsModuleTopology F (Module.End F d.V × Module.End F d.V) := inferInstance
  obtain ⟨U₁, hU₁, hB⟩ := exists_nhds_mem_of_expA_mem F (A := d.ambient)
  obtain ⟨U₂, hU₂, hR⟩ :=
    exists_nhds_mem_of_expA_mem F (A := Module.End F d.V × Module.End F d.V)
  have hp1 := eventually_map_expA (F := F) (A := Module.End F d.V × Module.End F d.V)
    (LinearMap.fst F (Module.End F d.V) (Module.End F d.V)) (fun X n => Prod.pow_fst X n)
  have hp2 := eventually_map_expA (F := F) (A := Module.End F d.V × Module.End F d.V)
    (LinearMap.snd F (Module.End F d.V) (Module.End F d.V)) (fun X n => Prod.pow_snd X n)
  set φ := CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ) with hφ
  set Fl := d.flag with hFl
  set O := (bform d.QV).orthogonal Fl.top with hO
  -- the subalgebra `{(x, y) : y − φ x ∈ C(V)_{≥1}}` of `C(W) × C(V)`
  have hφ0 : ∀ x, φ x ∈ wtFil d.QV (flagWt Fl) 0 := d.map_inl_mem_wtFil_zero
  let B : Subalgebra F d.ambient :=
    { carrier := {p | p.2 - φ p.1 ∈ wtFil d.QV (flagWt Fl) 1}
      mul_mem' := by
        rintro p q hp hq
        have hq0 : q.2 ∈ wtFil d.QV (flagWt Fl) 0 := by
          have : q.2 = (q.2 - φ q.1) + φ q.1 := by abel
          rw [this]; exact add_mem (wtFil_anti (by norm_num) hq) (hφ0 _)
        have e : (p * q).2 - φ (p * q).1 = (p.2 - φ p.1) * q.2 + φ p.1 * (q.2 - φ q.1) := by
          simp only [Prod.snd_mul, Prod.fst_mul, map_mul]; noncomm_ring
        rw [Set.mem_ofPred_eq, e]
        exact add_mem (by simpa using mul_mem_wtFil hp hq0)
          (by simpa using mul_mem_wtFil (hφ0 _) hq)
      add_mem' := by
        rintro p q hp hq
        have e : (p + q).2 - φ (p + q).1 = (p.2 - φ p.1) + (q.2 - φ q.1) := by
          simp only [Prod.snd_add, Prod.fst_add, map_add]; abel
        rw [Set.mem_ofPred_eq, e]; exact add_mem hp hq
      algebraMap_mem' := fun c => by
        change (algebraMap F d.ambient c).2 - φ (algebraMap F d.ambient c).1 ∈
          wtFil d.QV (flagWt Fl) 1
        rw [Prod.algebraMap_apply, AlgHom.commutes, sub_self]; exact zero_mem _ }
  -- the subalgebra `R ⊆ End V × End V`
  let S : Set (Module.End F d.V) :=
    {T | (∀ i, ∀ v ∈ Fl.sub i, T v ∈ Fl.sub i) ∧ ∀ v ∈ O, T v ∈ O}
  let I : Set (Module.End F d.V) :=
    {T | (∀ i : Fin Fl.len, ∀ v ∈ Fl.sub i.succ, T v ∈ Fl.sub i.castSucc) ∧ ∀ v ∈ O, T v ∈ Fl.top}
  have hSI : ∀ T ∈ S, ∀ U ∈ I, T * U ∈ I := fun T hT U hU =>
    ⟨fun i v hv => hT.1 _ _ (hU.1 i v hv), fun v hv => hT.1 _ _ (hU.2 v hv)⟩
  have hIS : ∀ T ∈ I, ∀ U ∈ S, T * U ∈ I := fun T hT U hU =>
    ⟨fun i v hv => hT.1 i _ (hU.1 _ v hv), fun v hv => hT.2 _ (hU.2 v hv)⟩
  have hSmul : ∀ T ∈ S, ∀ U ∈ S, T * U ∈ S := fun T hT U hU =>
    ⟨fun i v hv => hT.1 i _ (hU.1 i v hv), fun v hv => hT.2 _ (hU.2 v hv)⟩
  have hIadd : ∀ T ∈ I, ∀ U ∈ I, T + U ∈ I := fun T hT U hU =>
    ⟨fun i v hv => add_mem (hT.1 i v hv) (hU.1 i v hv), fun v hv => add_mem (hT.2 v hv) (hU.2 v hv)⟩
  let R : Subalgebra F (Module.End F d.V × Module.End F d.V) :=
    { carrier := {p | p.1 ∈ S ∧ p.2 ∈ S ∧ p.2 - p.1 ∈ I}
      mul_mem' := by
        rintro p q ⟨hp1, hp2, hp3⟩ ⟨hq1, hq2, hq3⟩
        refine ⟨hSmul _ hp1 _ hq1, hSmul _ hp2 _ hq2, ?_⟩
        have e : (p * q).2 - (p * q).1 = (p.2 - p.1) * q.2 + p.1 * (q.2 - q.1) := by
          simp only [Prod.snd_mul, Prod.fst_mul]; rw [sub_mul, mul_sub]; abel
        rw [e]; exact hIadd _ (hIS _ hp3 _ hq2) _ (hSI _ hp1 _ hq3)
      add_mem' := by
        rintro p q ⟨hp1, hp2, hp3⟩ ⟨hq1, hq2, hq3⟩
        refine ⟨⟨fun i v hv => add_mem (hp1.1 i v hv) (hq1.1 i v hv),
            fun v hv => add_mem (hp1.2 v hv) (hq1.2 v hv)⟩,
          ⟨fun i v hv => add_mem (hp2.1 i v hv) (hq2.1 i v hv),
            fun v hv => add_mem (hp2.2 v hv) (hq2.2 v hv)⟩, ?_⟩
        have e : (p + q).2 - (p + q).1 = (p.2 - p.1) + (q.2 - q.1) := by
          simp only [Prod.snd_add, Prod.fst_add]; abel
        rw [e]; exact hIadd _ hp3 _ hq3
      algebraMap_mem' := fun c => by
        have hc : algebraMap F (Module.End F d.V) c ∈ S :=
          ⟨fun i v hv => by
            rw [Module.algebraMap_end_apply]; exact (Fl.sub i).smul_mem c hv,
          fun v hv => by rw [Module.algebraMap_end_apply]; exact O.smul_mem c hv⟩
        refine ⟨hc, hc, ?_⟩
        rw [Prod.algebraMap_apply, sub_self]
        exact ⟨fun i v _ => by rw [LinearMap.zero_apply]; exact zero_mem _,
          fun v _ => by rw [LinearMap.zero_apply]; exact zero_mem _⟩ }
  -- `P(g) ∈ S` for `g` stabilizing the flag
  have hPS : ∀ g : GSpin d.QV, g ∈ flagStab Fl →
      ((specP d.QV g : d.V ≃ₗ[F] d.V) : Module.End F d.V) ∈ S := fun g hg =>
    ⟨fun i v hv => flagStab_mapsTo hg _ hv, fun v hv => flagStab_mapsTo_orthogonal hg hv⟩
  -- the continuous linear map `W ↦ (ad φ W₁, ad W₂)`
  let ψl : d.ambient →ₗ[F] Module.End F d.V × Module.End F d.V :=
    ((adV d.QV) ∘ₗ φ.toLinearMap ∘ₗ LinearMap.fst F _ _).prod
      ((adV d.QV) ∘ₗ LinearMap.snd F _ _)
  have hψc : Continuous ψl := IsModuleTopology.continuous_of_linearMap _
  let M : d.ambient →ₗ[F] CliffordAlgebra d.QV := φ.toLinearMap ∘ₗ LinearMap.fst F _ _
  have hMc : Continuous M := IsModuleTopology.continuous_of_linearMap _
  have e1 := (hψc.tendsto' 0 0 (map_zero _)).eventually
    ((hp1.and hp2).and (show ∀ᶠ p in 𝓝 (0 : Module.End F d.V × Module.End F d.V), p ∈ U₂ from hU₂))
  have hmap := eventually_map_expA (F := F) (A := CliffordAlgebra d.QW)
    (B := CliffordAlgebra d.QV) φ.toLinearMap (fun X n => map_pow φ X n)
  have e2 := (_root_.continuous_fst.tendsto (0 : d.ambient)).eventually hmap
  have e3 := (hMc.tendsto' 0 0 (map_zero M)).eventually
    (eventually_specP_eq_expA_adV (F := F) d.QV)
  have e4 := (_root_.continuous_snd.tendsto (0 : d.ambient)).eventually
    (eventually_specP_eq_expA_adV (F := F) d.QV)
  filter_upwards [e1, e2, e3, e4, eventually_expA_ambient d, eventually_mem_lie_of_expA_mem d,
    hU₁] with W h1 h2 h3 h4 h0 hlie hWU h hh
  set g : ↥d.G := (h : ↥d.G) with hg
  have hn : d.nPart g ∈ flagUnip Fl := h.2
  have hfst : (((d.fst g : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) =
      expA F W.1 := by rw [← h0.1, ← hh]; rfl
  have hsnd : (((d.snd g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) =
      expA F W.2 := by rw [← h0.2, ← hh]; rfl
  have hincl : (((d.incl (d.fst g) : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) :
      CliffordAlgebra d.QV) = φ (((d.fst g : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) :
        CliffordAlgebra d.QW) := by
    rw [incl, GSpin.coe_map]
  have hsplit : d.snd g = d.incl (d.fst g) * d.nPart g := by
    simp only [nPart, mul_inv_cancel_left]
  -- `W ∈ B`
  have hWB : W ∈ B := by
    refine hB W hWU B ?_
    rw [← hh]
    change (((g : d.ambientˣ) : d.ambient)).2 - φ (((g : d.ambientˣ) : d.ambient)).1 ∈
      wtFil d.QV (flagWt Fl) 1
    have e2' : (((g : d.ambientˣ) : d.ambient)).2 =
        (((d.snd g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) := rfl
    have e1' : (((g : d.ambientˣ) : d.ambient)).1 =
        (((d.fst g : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) := rfl
    rw [e2', e1', ← hincl, hsplit, Subgroup.coe_mul, Units.val_mul]
    have key : ∀ x n : CliffordAlgebra d.QV, x * n - x = x * (n - 1) := fun x n => by
      rw [mul_sub, mul_one]
    rw [key, hincl]
    have hmem := mul_mem_wtFil (hφ0 (((d.fst g : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) :
      CliffordAlgebra d.QW)) (sub_one_mem_wtFil_of_mem_flagUnip d.nondeg_QV hn)
    simpa only [zero_add] using hmem
  -- split `Wᵢ = aᵢ + Sᵢ`
  have hW1 : W.1 ∈ Submodule.span F {(1 : CliffordAlgebra d.QW)} ⊔ (soSub d.QW).toSubmodule := by
    rw [← gspin_eq_span_one_sup_soSub]; exact (hlie g hh).1
  have hW2 : W.2 ∈ Submodule.span F {(1 : CliffordAlgebra d.QV)} ⊔ (soSub d.QV).toSubmodule := by
    rw [← gspin_eq_span_one_sup_soSub]; exact (hlie g hh).2
  obtain ⟨a₁, ha₁, S₁, hS₁, hW1e⟩ := Submodule.mem_sup.mp hW1
  obtain ⟨a₂, ha₂, S₂, hS₂, hW2e⟩ := Submodule.mem_sup.mp hW2
  obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp ha₁
  obtain ⟨c₂, hc₂⟩ := Submodule.mem_span_singleton.mp ha₂
  rw [← hc₁] at hW1e
  rw [← hc₂] at hW2e
  have hS₁' : S₁ ∈ soSub d.QW := hS₁
  have hS₂' : S₂ ∈ soSub d.QV := hS₂
  have hφS₁ : φ S₁ ∈ soSub d.QV := map_mem_soSub d.nondeg _ hS₁'
  have hφW1 : φ W.1 = c₁ • (1 : CliffordAlgebra d.QV) + φ S₁ := by
    rw [← hW1e, map_add, map_smul, map_one]
  -- `c₁ = c₂` (traces)
  have hc : c₁ = c₂ := by
    have hdiff : W.2 - φ W.1 = (c₂ - c₁) • (1 : CliffordAlgebra d.QV) + (S₂ - φ S₁) := by
      rw [hφW1, ← hW2e, sub_smul]; abel
    have hnil := isNilpotent_of_mem_wtFil_one Fl.isWtFil (show W.2 - φ W.1 ∈ _ from hWB)
    have htr0 : cliffTrace d.QV (W.2 - φ W.1) = 0 := by
      have hL : IsNilpotent (LinearMap.mulLeft F (W.2 - φ W.1)) := by
        obtain ⟨k, hk⟩ := hnil
        exact ⟨k, by rw [LinearMap.pow_mulLeft, hk]; ext; simp⟩
      exact (LinearMap.isNilpotent_trace_of_isNilpotent hL).eq_zero
    have hS0 : cliffTrace d.QV (S₂ - φ S₁) = 0 := (sub_mem hS₂' hφS₁).2
    rw [hdiff, cliffTrace_add, hS0, add_zero, cliffTrace_smul, cliffTrace_one] at htr0
    have hn0 := cast_finrank_cliffordAlgebra_ne_zero d.QV
    have : c₂ - c₁ = 0 := (mul_eq_zero.mp htr0).resolve_right hn0
    linear_combination -this
  subst hc
  -- `ad(S₂ − φ S₁)` is flag-raising
  have hMW : M W = φ W.1 := rfl
  have hφg : φ W.1 ∈ gspin d.QV := by
    rw [hφW1]
    exact add_mem ((gspin d.QV).smul_mem c₁ (one_mem_gspin d.QV)) hφS₁.1
  have hW2g : W.2 ∈ gspin d.QV := by
    rw [← hW2e]; exact add_mem ((gspin d.QV).smul_mem c₁ (one_mem_gspin d.QV)) hS₂'.1
  have hPa : ((specP d.QV (d.incl (d.fst g)) : d.V ≃ₗ[F] d.V) : Module.End F d.V) =
      expA F (adV d.QV (φ W.1)) := by
    refine h3 (by rw [hMW]; exact hφg) _ ?_
    rw [hincl, hfst]; exact h2
  have hPb : ((specP d.QV (d.snd g) : d.V ≃ₗ[F] d.V) : Module.End F d.V) =
      expA F (adV d.QV W.2) := h4 hW2g _ hsnd
  have hψW : ψl W = (adV d.QV (φ W.1), adV d.QV W.2) := rfl
  have hRexp : expA F (ψl W) ∈ R := by
    have e : expA F (ψl W) = (expA F (ψl W).1, expA F (ψl W).2) := Prod.ext h1.1.1 h1.1.2
    rw [e, hψW]
    dsimp only
    rw [← hPa, ← hPb]
    have hstab : d.incl (d.fst g) ∈ flagStab Fl := d.incl_mem_flagStab _
    have hnstab : d.nPart g ∈ flagStab Fl := hn.1
    refine ⟨hPS _ hstab, ?_, ?_⟩
    · rw [hsplit]; exact hPS _ ((flagStab Fl).mul_mem hstab hnstab)
    · have e' : ((specP d.QV (d.snd g) : d.V ≃ₗ[F] d.V) : Module.End F d.V) -
          ((specP d.QV (d.incl (d.fst g)) : d.V ≃ₗ[F] d.V) : Module.End F d.V) =
          ((specP d.QV (d.incl (d.fst g)) : d.V ≃ₗ[F] d.V) : Module.End F d.V) *
            (((specP d.QV (d.nPart g) : d.V ≃ₗ[F] d.V) : Module.End F d.V) - 1) := by
        rw [hsplit, map_mul, mul_sub, mul_one]; rfl
      rw [e']
      refine hSI _ (hPS _ hstab) _ ⟨fun i v hv => ?_, fun v hv => ?_⟩
      · simpa using hn.2.1 i v hv
      · simpa using hn.2.2.1 v hv
  have hRW : ψl W ∈ R := hR _ h1.2 R hRexp
  have hI : adV d.QV W.2 - adV d.QV (φ W.1) ∈ I := by
    have := hRW.2.2; rwa [hψW] at this
  have had : adV d.QV (S₂ - φ S₁) = adV d.QV W.2 - adV d.QV (φ W.1) := by
    rw [hφW1, ← hW2e, map_add, map_add, Algebra.smul_def, mul_one, adV_algebraMap, map_sub]
    abel
  refine ⟨c₁, ⟨?_, ?_⟩⟩
  · refine ⟨?_, ?_⟩
    · show W.1 - algebraMap F _ c₁ ∈ soSub d.QW
      rw [← hW1e, Algebra.algebraMap_eq_smul_one, add_sub_cancel_left]; exact hS₁'
    · show W.2 - algebraMap F _ c₁ ∈ soSub d.QV
      rw [← hW2e, Algebra.algebraMap_eq_smul_one, add_sub_cancel_left]; exact hS₂'
  · show (W.2 - algebraMap F _ c₁) - φ (W.1 - algebraMap F _ c₁) ∈ lieFlagUnip d.flag
    have e : (W.2 - algebraMap F _ c₁) - φ (W.1 - algebraMap F _ c₁) = S₂ - φ S₁ := by
      rw [← hW2e, ← hW1e, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        add_sub_cancel_left, add_sub_cancel_left]
    rw [e]
    refine ⟨sub_mem hS₂' hφS₁, fun i v hv => ?_, fun v hv => ?_⟩
    · rw [had]; exact hI.1 i v hv
    · rw [had]; exact hI.2 v hv

/-- **An `exp`-compatible Haar measure on `𝔥⁰(F)` exists** (BP §1.6, Thesis §10.1, §12.4): near
`0`, `X ↦ e^X` is a homeomorphism from a neighbourhood of `0` in `𝔥⁰(F)` onto a neighbourhood of
`1` in `H(F)/A_{G,H}(F)` (`𝔥 = Lie(A_{G,H}) ⊕ 𝔥⁰`), and on a small enough lattice it carries an
additive Haar measure to a Haar measure (the Jacobian `j^H` is `1` near `0` in the `p`-adic case).
Proved via the isometry chart (`exists_isAddHaarMeasure_eq_expA_image`, with
`j : H(F) → (C(W) × C(V))ˣ`, the scalars `A_{G,H}(F) ⊆ H(F)`, `exp` into `H(F)` by
`eventually_exists_mem_H_eq_expA` and the logarithm by
`eventually_exists_sub_algebraMap_mem_lieH0`). -/
theorem exists_isExpCompatH : ∃ μ, d.IsExpCompatH μ := by
  letI := isTopologicalRing_of_moduleTopology F d.ambient
  haveI := t2Space_of_moduleTopology F d.ambient
  haveI := submodule_isTopologicalAddGroup d.lieH0
  obtain ⟨_, _, _, _, _⟩ := submodule_topology d.lieH0
  let j : ↥d.H →* d.ambientˣ := d.G.subtype.comp d.H.subtype
  have hj : Topology.IsEmbedding fun h : ↥d.H => ((j h : d.ambientˣ) : d.ambient) :=
    (isEmbedding_units_val F).comp
      (Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal)
  have hdiag : ∀ c : Fˣ, (((d.diag (scalarGSpin d.QW c) : ↥d.G) : d.ambientˣ) : d.ambient) =
      algebraMap F d.ambient (c : F) := by
    intro c
    refine Prod.ext ?_ ?_
    · rfl
    · change (((d.incl (scalarGSpin d.QW c) : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) :
        CliffordAlgebra d.QV) = algebraMap F (CliffordAlgebra d.QV) c
      rw [incl, GSpin.coe_map]
      exact AlgHom.commutes _ _
  have hZ : ∀ h : ↥d.H, h ∈ d.AGHinH ↔
      ((j h : d.ambientˣ) : d.ambient) ∈ Set.range (algebraMap F d.ambient) := by
    intro h
    rw [Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨(c : F), ?_⟩
      rw [← hdiag c]
      exact congrArg (fun g : ↥d.G => ((g : d.ambientˣ) : d.ambient)) hc
    · rintro ⟨c, hc⟩
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [map_zero] at hc
        exact Units.ne_zero _ hc.symm
      refine ⟨Units.mk0 c hc0, Subtype.ext (Units.ext ?_)⟩
      change (((d.diag (scalarGSpin d.QW (Units.mk0 c hc0)) : ↥d.G) : d.ambientˣ) : d.ambient) = _
      rw [hdiag]; exact hc
  have hscal : ∀ c : F, c ≠ 0 → ∃ h : ↥d.H,
      ((j h : d.ambientˣ) : d.ambient) = algebraMap F d.ambient c :=
    fun c hc => ⟨⟨d.diag (scalarGSpin d.QW (Units.mk0 c hc)), d.AGH_le_H ⟨_, rfl⟩⟩,
      hdiag (Units.mk0 c hc)⟩
  have h𝔤 : ∀ t : F, algebraMap F d.ambient t ∈ d.lieH0 → t = 0 := by
    intro t ht
    have ht1 : algebraMap F (CliffordAlgebra d.QW) t ∈ soSub d.QW := ht.1.1
    have h1 : algebraMap F (CliffordAlgebra d.QW) t ∈
        Submodule.span F {(1 : CliffordAlgebra d.QW)} := by
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    have h0 := Submodule.disjoint_def.mp (disjoint_span_one_soSub d.QW) _ h1 ht1
    rw [Algebra.algebraMap_eq_smul_one, smul_eq_zero] at h0
    exact h0.resolve_right one_ne_zero
  obtain ⟨μ, hμ, U, hU, hUS⟩ := exists_isAddHaarMeasure_eq_expA_image j hj d.AGHinH hZ hscal
    d.lieH0 h𝔤 d.eventually_exists_mem_H_eq_expA d.eventually_exists_sub_algebraMap_mem_lieH0
    (Measure.haar : Measure d.HmodAGH)
  exact ⟨μ, hμ, U, hU, hUS⟩

end GGPData

end GSpinGGP
