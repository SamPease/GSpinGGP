/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.Foundations.GSpinExpAd
import GSpinGGP.TraceFormula.LuoTorus

/-!
# The exponential and `G → Ḡ`, `H`, `𝔥⁰`

* `eventually_toGbarU_eq_expA_toSOLin`: for `X ∈ 𝔤` near `0` and `g = e^X ∈ G(F)`, the image of
  `g` in `Ḡ(F) = SO(W) × SO(V)` is `e^{ad X}` (`eventually_specP_eq_expA_adV` on each factor);
  `eventually_toGbarU_diag_eq_expA` is the diagonal case `x = e^X ∈ GSpin(W)`.
* `mem_wtFil_one_of_mem_lieFlagUnip`: `𝔫_F ⊆ C(V)_{≥1}`, the elements of the nilpotent radical of
  the parabolic subalgebra of an isotropic flag have positive weight in the Clifford algebra.
* `eventually_expA_mem_H`: for `X ∈ 𝔥⁰` near `0`, `e^X ∈ G(F)` lies in `H(F)` (Thesis §5.2);
  `eventually_exists_mem_H_eq_expA`: such an `e^X ∈ H(F)` exists.
-/

noncomputable section

open MeasureTheory Topology Filter Module CliffordAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace GSpinGGP

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-! ### Flags: `P(e^{-A} e^{A + N})` and `𝔫 ⊆ C(V)_{≥1}` -/

section Flag

variable {V : Type*} [AddCommGroup V] [Module F V] [Module.Finite F V] {Q : QuadraticForm F V}

/-- **`e^{-A} e^{A+N} ∈ N_F^{SO}`** for `A ∈ gspin(V)` preserving the flag and `N ∈ 𝔫_F`, both
near `0`: in `End(V)`, `P(e^{-A} e^{A+N}) − 1 = e^{-ad A}(e^{ad A + ad N} − e^{ad A})`, and
`(ad A + ad N)ⁿ − (ad A)ⁿ` lies in the two-sided ideal `𝔫_F` of the flag-stabilizing subalgebra,
which is closed. -/
theorem eventually_mul_mem_flagUnipSO (Fl : IsotropicFlag Q) :
    ∀ᶠ p : CliffordAlgebra Q × CliffordAlgebra Q in 𝓝 0, p.1 ∈ gspin Q →
      (∀ i, ∀ v ∈ Fl.sub i, adV Q p.1 v ∈ Fl.sub i) → p.2 ∈ lieFlagUnip Fl →
      ∀ a b : ↥(GSpin Q), ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = expA F (-p.1) →
        ((b : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = expA F (p.1 + p.2) →
        a * b ∈ flagUnipSO Fl := by
  haveI : IsModuleTopology F (Module.End F V) := ⟨rfl⟩
  set O := (bform Q).orthogonal Fl.top with hO
  -- the flag-stabilizing subalgebra `S` and its ideal `I = 𝔫_F` in `End(V)`
  let S : Subalgebra F (Module.End F V) :=
    { carrier := {T | (∀ i, ∀ v ∈ Fl.sub i, T v ∈ Fl.sub i) ∧ ∀ v ∈ O, T v ∈ O}
      mul_mem' := fun hS hT =>
        ⟨fun i v hv => hS.1 i _ (hT.1 i v hv), fun v hv => hS.2 _ (hT.2 v hv)⟩
      add_mem' := fun hS hT => ⟨fun i v hv => add_mem (hS.1 i v hv) (hT.1 i v hv),
        fun v hv => add_mem (hS.2 v hv) (hT.2 v hv)⟩
      algebraMap_mem' := fun c => ⟨fun i v hv => by
          simpa [Module.algebraMap_end_apply] using (Fl.sub i).smul_mem c hv,
        fun v hv => by simpa [Module.algebraMap_end_apply] using O.smul_mem c hv⟩ }
  let I : Submodule F (Module.End F V) :=
    { carrier := {T | (∀ i : Fin Fl.len, ∀ v ∈ Fl.sub i.succ, T v ∈ Fl.sub i.castSucc) ∧
        ∀ v ∈ O, T v ∈ Fl.top}
      add_mem' := fun hS hT => ⟨fun i v hv => add_mem (hS.1 i v hv) (hT.1 i v hv),
        fun v hv => add_mem (hS.2 v hv) (hT.2 v hv)⟩
      zero_mem' := ⟨fun i v _ => zero_mem _, fun v _ => zero_mem _⟩
      smul_mem' := fun c T hT => ⟨fun i v hv => (Fl.sub _).smul_mem c (hT.1 i v hv),
        fun v hv => Fl.top.smul_mem c (hT.2 v hv)⟩ }
  have htopO : Fl.top ≤ O := Fl.sub_le_orthogonal _ _
  have hIS : ∀ T ∈ I, T ∈ S := by
    intro T hT
    refine ⟨fun i => ?_, fun v hv => htopO (hT.2 v hv)⟩
    induction i using Fin.cases with
    | zero => intro v hv; rw [Fl.sub_zero, Submodule.mem_bot] at hv; simp [hv]
    | succ j =>
      intro v hv
      exact Fl.sub_mono Fin.castSucc_lt_succ.le (hT.1 j v hv)
  have hSI : ∀ T ∈ S, ∀ U ∈ I, T * U ∈ I := fun T hT U hU =>
    ⟨fun i v hv => hT.1 _ _ (hU.1 i v hv), fun v hv => hT.1 _ _ (hU.2 v hv)⟩
  have hIS' : ∀ T ∈ I, ∀ U ∈ S, T * U ∈ I := fun T hT U hU =>
    ⟨fun i v hv => hT.1 i _ (hU.1 _ v hv), fun v hv => hT.2 _ (hU.2 v hv)⟩
  have hpowI : ∀ {A N : Module.End F V}, A ∈ S → N ∈ I → ∀ n : ℕ, (A + N) ^ n - A ^ n ∈ I := by
    intro A N hA hN n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : (A + N) ^ (n + 1) - A ^ (n + 1) = (A + N) * ((A + N) ^ n - A ^ n) + N * A ^ n := by
        rw [pow_succ', pow_succ']; noncomm_ring
      rw [e]
      exact add_mem (hSI _ (S.add_mem hA (hIS N hN)) _ ih) (hIS' N hN _ (S.pow_mem hA n))
  -- neighbourhoods
  obtain ⟨UI, hUI, hexpI⟩ := exists_nhds_expA_sub_expA_mem (F := F) I
  obtain ⟨Un, hUn, hneg⟩ := expA_mul_expA_neg F (A := Module.End F V)
  have hadc : Continuous (adV Q) := IsModuleTopology.continuous_of_linearMap _
  have hP := eventually_specP_eq_expA_adV (F := F) Q
  have c1 : Continuous fun p : CliffordAlgebra Q × CliffordAlgebra Q => -p.1 :=
    continuous_fst.neg
  have c2 : Continuous fun p : CliffordAlgebra Q × CliffordAlgebra Q => p.1 + p.2 :=
    continuous_fst.add continuous_snd
  have e1 := (c1.tendsto' 0 0 (by simp)).eventually hP
  have e2 := (c2.tendsto' 0 0 (by simp)).eventually hP
  have hnegU : ∀ᶠ A in 𝓝 (0 : Module.End F V), -A ∈ Un :=
    (continuous_neg.tendsto' (0 : Module.End F V) 0 neg_zero).eventually hUn
  have hUI' : ∀ᶠ A in 𝓝 (0 : Module.End F V), A ∈ UI := hUI
  have hc3 : Continuous fun p : CliffordAlgebra Q × CliffordAlgebra Q => adV Q p.1 :=
    hadc.comp continuous_fst
  have hc4 : Continuous fun p : CliffordAlgebra Q × CliffordAlgebra Q => adV Q (p.1 + p.2) :=
    hadc.comp c2
  have e3 := (hc3.tendsto' 0 0 (map_zero (adV Q))).eventually (hUI'.and hnegU)
  have e4 := (hc4.tendsto' 0 0
    (by rw [Prod.fst_zero, Prod.snd_zero, add_zero, map_zero])).eventually hUI'
  filter_upwards [e1, e2, e3, e4] with p hp1 hp2 hp3 hp4 hA hAflag hN a b ha hb
  obtain ⟨hN0, hN1, hN2⟩ := hN
  have hNgs : p.2 ∈ gspin Q := hN0.1
  set A := adV Q p.1 with hAdef
  set N := adV Q p.2 with hNdef
  have hAS : A ∈ S := by
    refine ⟨hAflag, fun v hv => ?_⟩
    rw [hO, LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
    intro t ht
    change bform Q t (A v) = 0
    rw [bform_comm, bform_adV hA, bform_comm]
    have := hv (A t) (hAflag _ t ht)
    change bform Q (A t) v = 0 at this
    rw [this, neg_zero]
  have hNI : N ∈ I := ⟨hN1, hN2⟩
  have hPa := hp1 (neg_mem hA) a ha
  have hPb := hp2 (add_mem hA hNgs) b hb
  rw [map_neg] at hPa
  rw [map_add] at hPb
  -- `P(ab) − 1 ∈ I`
  have hT : ((specP Q (a * b) : V ≃ₗ[F] V) : Module.End F V) - 1 ∈ I := by
    have e : ((specP Q (a * b) : V ≃ₗ[F] V) : Module.End F V) - 1 =
        expA F (-A) * (expA F (A + N) - expA F A) + (expA F (-A) * expA F (-(-A)) - 1) := by
      rw [map_mul, neg_neg]
      change ((specP Q a : V ≃ₗ[F] V) : Module.End F V) * (specP Q b : V ≃ₗ[F] V) - 1 = _
      rw [hPa, hPb]; noncomm_ring
    rw [e, hneg _ hp3.2, sub_self, add_zero]
    exact hSI _ (expA_mem_subalgebra S (S.neg_mem hAS)) _
      (hexpI A hp3.1 (A + N) (by simpa only [map_add] using hp4) (hpowI hAS hNI))
  have hmov : ∀ v, specP Q (a * b) v =
      v + (((specP Q (a * b) : V ≃ₗ[F] V) : Module.End F V) - 1) v :=
    fun v => by simp
  refine ⟨mem_flagStab_iff.mpr fun i v hv => ?_, fun i v hv => ?_, fun v hv => ?_⟩
  · rw [hmov]; exact add_mem hv ((hIS _ hT).1 i v hv)
  · rw [hmov, add_sub_cancel_left]; exact hT.1 i v hv
  · rw [hmov, add_sub_cancel_left]; exact hT.2 v hv

/-- **`𝔫_F ⊆ C(V)_{≥1}`**: an element `Z` of the nilpotent radical `𝔫_F` of the parabolic
subalgebra of an isotropic flag has positive weight for the weight filtration of `C(V)` attached
to the flag (the Lie-algebra form of `sub_one_mem_wtFil_of_mem_flagUnip`).  For small `t ≠ 0`,
`e^{tZ} ∈ N_F^{SO}` (`eventually_mul_mem_flagUnipSO`), so `e^{tZ}` is a scalar plus positive
weight (`exists_sub_algebraMap_mem_wtFil_of_raisesFil`); the scalars plus positive weight form a
subalgebra, so `tZ` is in it (`exists_nhds_mem_of_expA_mem`), and the scalar is `0` since `tZ`
and positive-weight elements (nilpotent) are traceless on `C(V)`. -/
theorem mem_wtFil_one_of_mem_lieFlagUnip (hQ : IsNondeg Q) {Fl : IsotropicFlag Q}
    {Z : CliffordAlgebra Q} (hZ : Z ∈ lieFlagUnip Fl) : Z ∈ wtFil Q (flagWt Fl) 1 := by
  -- scalars plus positive weight
  let T : Subalgebra F (CliffordAlgebra Q) :=
    { carrier := {x | ∃ c : F, x - algebraMap F _ c ∈ wtFil Q (flagWt Fl) 1}
      mul_mem' := by
        rintro x y ⟨c, hc⟩ ⟨c', hc'⟩
        refine ⟨c * c', ?_⟩
        have e : x * y - algebraMap F _ (c * c') =
            (x - algebraMap F _ c) * (y - algebraMap F _ c') + c • (y - algebraMap F _ c') +
              c' • (x - algebraMap F _ c) := by
          simp only [map_mul, Algebra.smul_def]
          rw [show algebraMap F (CliffordAlgebra Q) c' * (x - algebraMap F _ c) =
            (x - algebraMap F _ c) * algebraMap F (CliffordAlgebra Q) c' from
            Algebra.commutes _ _]
          noncomm_ring
        rw [e]
        refine add_mem (add_mem (wtFil_anti (by norm_num) (mul_mem_wtFil hc hc'))
          (Submodule.smul_mem _ _ hc')) (Submodule.smul_mem _ _ hc)
      add_mem' := by
        rintro x y ⟨c, hc⟩ ⟨c', hc'⟩
        refine ⟨c + c', ?_⟩
        rw [map_add, add_sub_add_comm]
        exact add_mem hc hc'
      algebraMap_mem' := fun c => ⟨c, by simp⟩ }
  obtain ⟨U₁, hU₁, hG⟩ := MovedPart.exists_nhds_expA_mem_GSpin (F := F) Q
  obtain ⟨U₂, hU₂, hsub⟩ := exists_nhds_mem_of_expA_mem F (A := CliffordAlgebra Q)
  have hcZ : Continuous fun t : F => t • Z := continuous_id.smul continuous_const
  have hcp : Continuous fun t : F => ((0 : CliffordAlgebra Q), t • Z) :=
    continuous_const.prodMk hcZ
  have h0 : ∀ᶠ t in 𝓝 (0 : F), t • Z ∈ U₁ ∩ U₂ ∧
      (((0 : CliffordAlgebra Q), t • Z) : CliffordAlgebra Q × CliffordAlgebra Q) ∈
        {p | p.1 ∈ gspin Q → (∀ i, ∀ v ∈ Fl.sub i, adV Q p.1 v ∈ Fl.sub i) →
          p.2 ∈ lieFlagUnip Fl →
          ∀ a b : ↥(GSpin Q), ((a : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = expA F (-p.1) →
            ((b : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q) = expA F (p.1 + p.2) →
            a * b ∈ flagUnipSO Fl} :=
    ((hcZ.tendsto' 0 0 (zero_smul F Z)).eventually (inter_mem hU₁ hU₂)).and
      ((hcp.tendsto' 0 0 (by simp)).eventually (eventually_mul_mem_flagUnipSO Fl))
  obtain ⟨t, ⟨⟨ht1, ht2⟩, ht3⟩, ht0⟩ := Filter.Eventually.exists (f := 𝓝[≠] (0 : F))
    ((h0.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin)
  have ht0' : t ≠ 0 := ht0
  have htZ : t • Z ∈ lieFlagUnip Fl := Submodule.smul_mem _ t hZ
  obtain ⟨b, hb⟩ := hG _ ht1 htZ.1.1
  have hb1 : (1 * b : ↥(GSpin Q)) ∈ flagUnipSO Fl :=
    ht3 (zero_mem _) (fun i v _ => by simp) htZ 1 b (by simp [expA_zero_eq_one]) (by simpa using hb)
  rw [one_mul] at hb1
  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_wtFil_of_raisesFil hQ (g := b)
    (fun w v hv => by simpa using Fl.specP_sub_mem_flagWt hb1 w v hv)
  have hmem : t • Z ∈ T := hsub _ ht2 T (by rw [← hb]; exact ⟨c, hc⟩)
  obtain ⟨c', hc'⟩ := hmem
  -- the scalar is `0`: traces
  have hnil := isNilpotent_of_mem_wtFil_one Fl.isWtFil hc'
  have htr0 : cliffTrace Q (t • Z - algebraMap F _ c') = 0 := by
    have hL : IsNilpotent (LinearMap.mulLeft F (t • Z - algebraMap F (CliffordAlgebra Q) c')) := by
      obtain ⟨k, hk⟩ := hnil
      exact ⟨k, by rw [LinearMap.pow_mulLeft, hk]; ext; simp⟩
    exact (LinearMap.isNilpotent_trace_of_isNilpotent hL).eq_zero
  have hZtr : cliffTrace Q (t • Z) = 0 := (htZ.1).2
  have halg : cliffTrace Q (algebraMap F (CliffordAlgebra Q) c') =
      c' * (finrank F (CliffordAlgebra Q) : F) := by
    rw [Algebra.algebraMap_eq_smul_one, cliffTrace_smul, cliffTrace_one]
  rw [sub_eq_add_neg, cliffTrace_add, hZtr, ← neg_one_smul F (algebraMap F _ c'),
    cliffTrace_smul, halg] at htr0
  have hc0 : c' = 0 := by
    have hn := cast_finrank_cliffordAlgebra_ne_zero Q
    have : c' * (finrank F (CliffordAlgebra Q) : F) = 0 := by linear_combination -htr0
    exact (mul_eq_zero.mp this).resolve_right hn
  rw [hc0, map_zero, sub_zero] at hc'
  have := Submodule.smul_mem _ t⁻¹ hc'
  rwa [smul_smul, inv_mul_cancel₀ ht0', one_smul] at this

end Flag

namespace GGPData

variable (d : GGPData F)

/-! ### `P(e^X) = e^{ad X}` on `G` -/

/-- **`G(F) → Ḡ(F)` intertwines the exponentials near the identity** (Thesis §5.1.3, §5.2): for
`X ∈ 𝔤 = gspin(W) × gspin(V)` near `0` and `g ∈ G(F)` with `g = e^X`, the image `(P(g_W), P(g_V))`
of `g` in `SO(W) × SO(V) ⊆ End W × End V` is `e^{(ad X_W, ad X_V)}` (`eventually_specP_eq_expA_adV`
on each factor). -/
theorem eventually_toGbarU_eq_expA_toSOLin :
    ∀ᶠ X in 𝓝 (0 : d.ambient), X ∈ d.lie → ∀ g : ↥d.G,
      ((g : d.ambientˣ) : d.ambient) = expA F X →
        ((d.toGbarU g : d.luoOf.Ambˣ) : d.luoOf.Amb) = expA F (d.toSOLin X) := by
  haveI : IsModuleTopology F (Module.End F d.luoOf.W) := ⟨rfl⟩
  haveI : IsModuleTopology F (Module.End F d.luoOf.V) := ⟨rfl⟩
  have hf := eventually_map_expA (F := F) (A := d.luoOf.Amb) d.luoOf.fstA.toLinearMap
    (fun X n => map_pow d.luoOf.fstA X n)
  have hs := eventually_map_expA (F := F) (A := d.luoOf.Amb) d.luoOf.sndA.toLinearMap
    (fun X n => map_pow d.luoOf.sndA X n)
  have hc : Continuous d.toSOLin := IsModuleTopology.continuous_of_linearMap _
  have e0 := (hc.tendsto' 0 0 (map_zero _)).eventually (hf.and hs)
  have e1 := (_root_.continuous_fst.tendsto (0 : d.ambient)).eventually
    (eventually_specP_eq_expA_adV (F := F) d.QW)
  have e2 := (_root_.continuous_snd.tendsto (0 : d.ambient)).eventually
    (eventually_specP_eq_expA_adV (F := F) d.QV)
  filter_upwards [e0, e1, e2, eventually_expA_ambient d] with X h0 h1 h2 h3 hX g hg
  rw [d.toGbarU_val]
  have k1 := h1 (by simpa using hX.1) (d.fst g) (by rw [← h3.1, ← hg]; rfl)
  have k2 := h2 (by simpa using hX.2) (d.snd g) (by rw [← h3.2, ← hg]; rfl)
  refine Prod.ext ?_ ?_
  · change _ = d.luoOf.fstA (expA F (d.toSOLin X))
    rw [show d.luoOf.fstA (expA F (d.toSOLin X)) = _ from h0.1, k1]; rfl
  · change _ = d.luoOf.sndA (expA F (d.toSOLin X))
    rw [show d.luoOf.sndA (expA F (d.toSOLin X)) = _ from h0.2, k2]; rfl

/-- The diagonal case of `eventually_toGbarU_eq_expA_toSOLin`: for `X ∈ so(W)` near `0` and
`x = e^X ∈ GSpin(W)(F)`, the image of `(x, x) ∈ G(F)` in `Ḡ(F)` is `e^{ad (X, X)}` (`C(W) → C(V)`
is an algebra map, so it commutes with `exp`). -/
theorem eventually_toGbarU_diag_eq_expA :
    ∀ᶠ X in 𝓝 (0 : CliffordAlgebra d.QW), X ∈ soSub d.QW → ∀ x : ↥(GSpin d.QW),
      ((x : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) = expA F X →
        ((d.toGbarU (d.diag x) : d.luoOf.Ambˣ) : d.luoOf.Amb) =
          expA F (d.toSOLin (d.diagLie X)) := by
  have hmap := eventually_map_expA (F := F) (A := CliffordAlgebra d.QW)
    (B := CliffordAlgebra d.QV)
    (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)).toLinearMap
    (fun X n => map_pow (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)) X n)
  have hc : Continuous d.diagLie := by
    refine continuous_id.prodMk ?_
    exact IsModuleTopology.continuous_of_linearMap
      (CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ)).toLinearMap
  have e0 := (hc.tendsto' 0 0 (by simp [diagLie])).eventually
    (d.eventually_toGbarU_eq_expA_toSOLin)
  have e1 := (hc.tendsto' 0 0 (by simp [diagLie])).eventually (eventually_expA_ambient d)
  filter_upwards [e0, e1, hmap] with X h0 h1 h2 hX x hx
  have hmem : d.diagLie X ∈ d.lie :=
    ⟨hX.1, (map_mem_soSub d.nondeg _ hX).1⟩
  refine h0 hmem (d.diag x) (Prod.ext ?_ ?_)
  · rw [h1.1]; exact hx
  · rw [h1.2]
    change (((d.incl x : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) = _
    rw [incl, GSpin.coe_map, hx]
    exact h2

/-! ### `e^X ∈ H(F)` for `X ∈ 𝔥⁰` near `0` -/

/-- **`e^X ∈ H(F)` for `X ∈ 𝔥⁰` near `0`** (Thesis §5.2: `𝔥⁰ = so(W) ⊕ 𝔫` is the Lie algebra of
`H = GSpin(W) ⋉ N`): if `g ∈ G(F)` has `g = e^X` with `X = (X_W, X_V) ∈ 𝔥⁰` small, then `g ∈ H(F)`.
With `M = X_W ⊆ C(V)` and `Z = X_V − M ∈ 𝔫`, `n = a⁻¹ b = e^{-M} e^{M + Z}`: its image in
`SO(V)` lies in `N_F^{SO}` (`eventually_mul_mem_flagUnipSO`), and `n − 1 = e^{-M}(e^{M+Z} − e^M)`
has positive weight (`M` has weight `≥ 0`, `Z` weight `≥ 1` by
`mem_wtFil_one_of_mem_lieFlagUnip`), so it is nilpotent. -/
theorem eventually_expA_mem_H :
    ∀ᶠ X in 𝓝 (0 : d.ambient), X ∈ d.lieH0 → ∀ g : ↥d.G,
      ((g : d.ambientˣ) : d.ambient) = expA F X → g ∈ d.H := by
  set φ := CliffordAlgebra.map (QuadraticMap.Isometry.inl d.QW d.QZ) with hφ
  let M : d.ambient →ₗ[F] CliffordAlgebra d.QV :=
    φ.toLinearMap ∘ₗ LinearMap.fst F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV)
  let Zl : d.ambient →ₗ[F] CliffordAlgebra d.QV :=
    LinearMap.snd F (CliffordAlgebra d.QW) (CliffordAlgebra d.QV) - M
  have hcM : Continuous M := IsModuleTopology.continuous_of_linearMap _
  have hcZ : Continuous Zl := IsModuleTopology.continuous_of_linearMap _
  have hcp : Continuous fun X : d.ambient => (M X, Zl X) := hcM.prodMk hcZ
  have hmap := eventually_map_expA (F := F) (A := CliffordAlgebra d.QW)
    (B := CliffordAlgebra d.QV) φ.toLinearMap (fun X n => map_pow φ X n)
  obtain ⟨UW, hUW, hW⟩ := exists_nhds_expA_sub_expA_mem (F := F) (wtFil d.QV (flagWt d.flag) 1)
  obtain ⟨Un, hUn, hneg⟩ := expA_mul_expA_neg F (A := CliffordAlgebra d.QV)
  have e1 := (hcp.tendsto' 0 0 (by simp)).eventually (eventually_mul_mem_flagUnipSO d.flag)
  have e2 := (_root_.continuous_fst.tendsto (0 : d.ambient)).eventually hmap
  have e3 := (hcM.tendsto' 0 0 (map_zero M)).eventually
    ((show ∀ᶠ Y in 𝓝 (0 : CliffordAlgebra d.QV), Y ∈ UW from hUW).and
      ((continuous_neg.tendsto' (0 : CliffordAlgebra d.QV) 0 neg_zero).eventually hUn))
  have e4 := (_root_.continuous_snd.tendsto (0 : d.ambient)).eventually
    (show ∀ᶠ Y in 𝓝 (0 : CliffordAlgebra d.QV), Y ∈ UW from hUW)
  filter_upwards [e1, e2, e3, e4, eventually_expA_ambient d] with X h1 h2 h3 h4 h0 hX g hg
  obtain ⟨hX0, hXn⟩ := hX
  have hXW : X.1 ∈ soSub d.QW := hX0.1
  have hMX : M X = φ X.1 := rfl
  have hZX : Zl X = X.2 - φ X.1 := rfl
  have hMg : M X ∈ gspin d.QV := (map_mem_soSub d.nondeg _ hXW).1
  have hfst : (((d.fst g : GSpin d.QW) : (CliffordAlgebra d.QW)ˣ) : CliffordAlgebra d.QW) =
      expA F X.1 := by rw [← h0.1, ← hg]; rfl
  have hsnd : (((d.snd g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) =
      expA F X.2 := by rw [← h0.2, ← hg]; rfl
  have hincl : (((d.incl (d.fst g) : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) :
      CliffordAlgebra d.QV) = expA F (M X) := by
    rw [incl, GSpin.coe_map, hfst, hMX]; exact h2
  have hneg'' : expA F (-(M X)) * expA F (M X) = 1 := by
    have := hneg _ h3.2; rwa [neg_neg] at this
  have hneg' : expA F (M X) * expA F (-(M X)) = 1 :=
    (commute_expA_of_commute (commute_expA_of_commute
      ((Commute.refl (M X)).neg_left)).symm).eq.trans hneg''
  have hinv : ((((d.incl (d.fst g))⁻¹ : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) :
      CliffordAlgebra d.QV) = expA F (-(M X)) := by
    rw [Subgroup.coe_inv]
    exact Units.inv_eq_of_mul_eq_one_right (by rw [hincl]; exact hneg')
  have hX2 : X.2 = M X + Zl X := by rw [hZX, hMX]; abel
  have hSO : d.nPart g ∈ flagUnipSO d.flag := by
    refine h1 hMg (fun i v hv => ?_) (by rw [hZX]; exact hXn) _ _ hinv (by rw [hsnd, ← hX2])
    obtain ⟨v1, v2⟩ := v
    have hv1 : v1 = 0 := (d.span_flag_le _ hv).1
    subst hv1
    rw [hMX, adV_map_inl d hX0.1.1, map_zero]
    exact zero_mem _
  -- `n − 1` has positive weight
  have hZ1 : Zl X ∈ wtFil d.QV (flagWt d.flag) 1 :=
    mem_wtFil_one_of_mem_lieFlagUnip d.nondeg_QV (by rw [hZX]; exact hXn)
  have hM0 : M X ∈ wtFil d.QV (flagWt d.flag) 0 := d.map_inl_mem_wtFil_zero X.1
  have hpow : ∀ k : ℕ, X.2 ^ k - M X ^ k ∈ wtFil d.QV (flagWt d.flag) 1 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : X.2 ^ (k + 1) - M X ^ (k + 1) = X.2 * (X.2 ^ k - M X ^ k) + Zl X * M X ^ k := by
        rw [hX2, pow_succ', pow_succ']; noncomm_ring
      have hpw : ∀ k : ℕ, M X ^ k ∈ wtFil d.QV (flagWt d.flag) 0 := fun k => by
        induction k with
        | zero => simpa using algebraMap_mem_wtFil (Q := d.QV) (Vf := flagWt d.flag) 1 le_rfl
        | succ k ihk => rw [pow_succ]; simpa using mul_mem_wtFil ihk hM0
      have hX2w : X.2 ∈ wtFil d.QV (flagWt d.flag) 0 := by
        rw [hX2]; exact add_mem hM0 (wtFil_anti (by norm_num) hZ1)
      rw [e]
      exact add_mem (by simpa using mul_mem_wtFil hX2w ih)
        (by simpa using mul_mem_wtFil hZ1 (hpw k))
  have hdiff := hW (M X) h3.1 X.2 h4 hpow
  have hnegM0 : expA F (-(M X)) ∈ wtFil d.QV (flagWt d.flag) 0 := by
    let S0 : Subalgebra F (CliffordAlgebra d.QV) :=
      { carrier := wtFil d.QV (flagWt d.flag) 0
        mul_mem' := fun hx hy => by simpa using mul_mem_wtFil hx hy
        add_mem' := fun hx hy => add_mem hx hy
        algebraMap_mem' := fun c => algebraMap_mem_wtFil c le_rfl }
    exact expA_mem_subalgebra S0 (S0.neg_mem (show M X ∈ S0 from hM0))
  have hval : (((d.nPart g : GSpin d.QV) : (CliffordAlgebra d.QV)ˣ) : CliffordAlgebra d.QV) - 1 =
      expA F (-(M X)) * (expA F X.2 - expA F (M X)) := by
    simp only [nPart, Subgroup.coe_mul, Units.val_mul]
    rw [hinv, hsnd, mul_sub, hneg'']
  refine ⟨hSO.1, hSO.2.1, hSO.2.2, isNilpotent_of_mem_wtFil_one d.flag.isWtFil ?_⟩
  rw [hval]
  simpa using mul_mem_wtFil hnegM0 hdiff

/-- **`exp` maps a neighbourhood of `0` in `𝔥⁰(F)` into `H(F)`**: for `X ∈ 𝔥⁰` near `0` there is
`h ∈ H(F)` with `h = e^X` (`eventually_expA_mem_G` and `eventually_expA_mem_H`). -/
theorem eventually_exists_mem_H_eq_expA :
    ∀ᶠ X in 𝓝 (0 : d.ambient), X ∈ d.lieH0 →
      ∃ h : ↥d.H, (((h : ↥d.G) : d.ambientˣ) : d.ambient) = expA F X := by
  filter_upwards [eventually_expA_mem_G d, d.eventually_expA_mem_H] with X hG hH hX
  obtain ⟨g, hg⟩ := hG (d.lie0_le_lie hX.1)
  exact ⟨⟨g, hH hX g hg⟩, hg⟩

end GGPData

end GSpinGGP
