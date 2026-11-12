/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.TraceFormula.LuoTorus
import GSpinGGP.TraceFormula.SOLieFacts

/-!
# Towards (L4): the measures of `J^Lie` on `H(F)\G(F)/A_G(F)` and on `H̄(F)\Ḡ(F)`

Ingredients for `exists_JLie_transfer` (`TraceFormula/LuoTransfer.lean`), which identifies
`J^Lie` of the general spin triple with Luo's `J^Lie` of the special orthogonal triple when
neither `W` nor `V` is a hyperbolic plane.

* `CosetSpace.mapEquiv`, `IsWeilMeasure.map`: Weil measures are transported by isomorphisms of
  topological groups compatible with the embeddings.
-/

noncomputable section

open MeasureTheory Topology Filter

set_option linter.unusedSectionVars false

namespace GSpinGGP

/-! ## Transport of Weil measures -/

section CosetSpaceMap

variable {S Γ S' Γ' : Type*} [Group S] [Group Γ] [Group S'] [Group Γ']

namespace CosetSpace

/-- The bijection `ι(S)\Γ ≃ ι'(S')\Γ'` induced by group isomorphisms `eS : S ≃* S'`,
`eΓ : Γ ≃* Γ'` with `ι' ∘ eS = eΓ ∘ ι`: `ι(S)γ ↦ ι'(S') eΓ(γ)`. -/
def mapEquiv (ι : S →* Γ) (ι' : S' →* Γ') (eS : S ≃* S') (eΓ : Γ ≃* Γ')
    (h : ∀ s, ι' (eS s) = eΓ (ι s)) : CosetSpace ι ≃ CosetSpace ι' :=
  Quotient.congr eΓ.toEquiv fun x y => by
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    constructor
    · rintro ⟨s, hs⟩
      refine ⟨eS s, ?_⟩
      rw [h, hs]
      simp [map_mul, map_inv]
    · rintro ⟨s, hs⟩
      refine ⟨eS.symm s, ?_⟩
      apply eΓ.injective
      have h' : ι' s = eΓ (ι (eS.symm s)) := by rw [← h, MulEquiv.apply_symm_apply]
      rw [← h', hs]
      simp [map_mul, map_inv]

theorem mapEquiv_mk (ι : S →* Γ) (ι' : S' →* Γ') (eS : S ≃* S') (eΓ : Γ ≃* Γ')
    (h : ∀ s, ι' (eS s) = eΓ (ι s)) (γ : Γ) :
    mapEquiv ι ι' eS eΓ h (mk ι γ) = mk ι' (eΓ γ) := rfl

variable [TopologicalSpace Γ] [TopologicalSpace Γ']

/-- `mapEquiv` is a homeomorphism when `eΓ` is. -/
def mapHomeomorph (ι : S →* Γ) (ι' : S' →* Γ') (eS : S ≃* S') (eΓ : Γ ≃ₜ* Γ')
    (h : ∀ s, ι' (eS s) = eΓ (ι s)) : CosetSpace ι ≃ₜ CosetSpace ι' where
  toEquiv := mapEquiv ι ι' eS eΓ.toMulEquiv h
  continuous_toFun := continuous_of_comp_mk ι ((continuous_mk ι').comp eΓ.continuous)
  continuous_invFun := continuous_of_comp_mk ι' <| by
    have : ((mapEquiv ι ι' eS eΓ.toMulEquiv h).symm ∘ mk ι') = mk ι ∘ eΓ.symm := by
      funext γ'
      apply (mapEquiv ι ι' eS eΓ.toMulEquiv h).injective
      rw [Function.comp_apply, Equiv.apply_symm_apply, Function.comp_apply, mapEquiv_mk]
      simp
    change Continuous (⇑(mapEquiv ι ι' eS eΓ.toMulEquiv h).symm ∘ mk ι')
    rw [this]
    exact (continuous_mk ι).comp eΓ.symm.continuous

@[simp] theorem mapHomeomorph_mk (ι : S →* Γ) (ι' : S' →* Γ') (eS : S ≃* S') (eΓ : Γ ≃ₜ* Γ')
    (h : ∀ s, ι' (eS s) = eΓ (ι s)) (γ : Γ) :
    mapHomeomorph ι ι' eS eΓ h (mk ι γ) = mk ι' (eΓ γ) := rfl

end CosetSpace

section Integral

variable [TopologicalSpace Γ] [TopologicalSpace Γ']

/-- Integrals over `ι'(S')\Γ'` of a left `ι'(S')`-invariant function at the chosen representatives,
against a push-forward along `CosetSpace.mapHomeomorph`, are integrals over `ι(S)\Γ` at `eΓ` of the
representatives. -/
theorem integral_map_mapHomeomorph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : S →* Γ} {ι' : S' →* Γ'} (eS : S ≃* S') (eΓ : Γ ≃ₜ* Γ')
    (h : ∀ s, ι' (eS s) = eΓ (ι s)) (m : Measure (CosetSpace ι)) (K : Γ' → E)
    (hK : ∀ s x, K (ι' s * x) = K x) :
    ∫ q, K (CosetSpace.out ι' q) ∂(m.map (CosetSpace.mapHomeomorph ι ι' eS eΓ h)) =
      ∫ q, K (eΓ (CosetSpace.out ι q)) ∂m := by
  set ē := CosetSpace.mapHomeomorph ι ι' eS eΓ h
  rw [ē.measurableEmbedding.integral_map]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  change K (CosetSpace.out ι' (ē q)) = K (eΓ (CosetSpace.out ι q))
  have hq : ē q = CosetSpace.mk ι' (eΓ (CosetSpace.out ι q)) := by
    conv_lhs => rw [← CosetSpace.mk_out ι q]
    rfl
  obtain ⟨s₀, hs₀⟩ := (CosetSpace.rel_iff ι' _ _).1
    ((CosetSpace.mk_eq_mk_iff ι' _ _).1 ((CosetSpace.mk_out ι' (ē q)).trans hq))
  have : CosetSpace.out ι' (ē q) = ι' s₀⁻¹ * eΓ (CosetSpace.out ι q) := by
    rw [hs₀, map_inv, inv_mul_cancel_left]
  rw [this, hK]

end Integral

variable [TopologicalSpace S] [TopologicalSpace Γ] [TopologicalSpace S'] [TopologicalSpace Γ']
  [MeasurableSpace S] [BorelSpace S] [MeasurableSpace Γ] [BorelSpace Γ]
  [MeasurableSpace S'] [BorelSpace S'] [MeasurableSpace Γ'] [BorelSpace Γ']

/-- **Transport of Weil measures** along isomorphisms of topological groups `eS : S ≃ₜ* S'`,
`eΓ : Γ ≃ₜ* Γ'` with `ι' ∘ eS = eΓ ∘ ι`: if `m` is a Weil measure on `ι(S)\Γ` for `ν` and a
right invariant `μ`, then its push-forward to `ι'(S')\Γ'` is a Weil measure for the push-forwards
of `ν` and `μ`.  The representatives `out (ē q)` and `eΓ (out q)` differ by an element of
`ι'(S')`, absorbed by right invariance of `μ`. -/
theorem IsWeilMeasure.map [MeasurableMul S] {ι : S →* Γ} {ι' : S' →* Γ'} {ν : Measure Γ}
    {μ : Measure S} (hμ : μ.IsMulRightInvariant) {m : Measure (CosetSpace ι)}
    (hm : IsWeilMeasure ι ν μ m) (eS : S ≃ₜ* S') (eΓ : Γ ≃ₜ* Γ')
    (h : ∀ s, ι' (eS s) = eΓ (ι s)) :
    IsWeilMeasure ι' (ν.map eΓ) (μ.map eS)
      (m.map (CosetSpace.mapHomeomorph ι ι' eS.toMulEquiv eΓ h)) := by
  intro φ hφ hφc
  have := hμ
  set ē := CosetSpace.mapHomeomorph ι ι' eS.toMulEquiv eΓ h
  have hΓ : ∫ g, φ g ∂(ν.map eΓ) = ∫ g, φ (eΓ g) ∂ν :=
    integral_map_equiv (eΓ.toHomeomorph.toMeasurableEquiv) φ
  rw [hΓ, show (∫ g, φ (eΓ g) ∂ν) = ∫ g, (φ ∘ eΓ) g ∂ν from rfl,
    hm (φ ∘ eΓ) (hφ.comp eΓ.continuous) (hφc.comp_homeomorph eΓ.toHomeomorph),
    show m.map ⇑ē = m.map ⇑ē.toMeasurableEquiv from rfl, integral_map_equiv ē.toMeasurableEquiv]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  change ∫ s, φ (eΓ (ι s * CosetSpace.out ι q)) ∂μ =
    ∫ s', φ (ι' s' * CosetSpace.out ι' (ē q)) ∂(μ.map eS)
  rw [show μ.map ⇑eS = μ.map ⇑eS.toHomeomorph.toMeasurableEquiv from rfl,
    integral_map_equiv (eS.toHomeomorph.toMeasurableEquiv)]
  -- `out (ē q) = ι'(eS s₀) · eΓ (out q)`
  have hq : ē q = CosetSpace.mk ι' (eΓ (CosetSpace.out ι q)) := by
    conv_lhs => rw [← CosetSpace.mk_out ι q]
    rfl
  obtain ⟨s₀, hs₀⟩ := (CosetSpace.rel_iff ι' _ _).1
    ((CosetSpace.mk_eq_mk_iff ι' _ _).1 ((CosetSpace.mk_out ι' (ē q)).trans hq))
  obtain ⟨t₀, rfl⟩ := eS.surjective s₀
  have e : ∀ s, ι' (eS s) * CosetSpace.out ι' (ē q) = eΓ (ι (s * t₀⁻¹) * CosetSpace.out ι q) := by
    intro s
    have h1 : CosetSpace.out ι' (ē q) = (ι' (eS t₀))⁻¹ * eΓ (CosetSpace.out ι q) := by
      rw [hs₀]; group
    rw [h1, h, h, map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc]
  simp only [Homeomorph.toMeasurableEquiv_coe]
  change ∫ s, φ (eΓ (ι s * CosetSpace.out ι q)) ∂μ = ∫ s, φ (ι' (eS s) * CosetSpace.out ι' (ē q)) ∂μ
  simp_rw [e]
  exact (integral_mul_right_eq_self (fun s => φ (eΓ (ι s * CosetSpace.out ι q))) t₀⁻¹).symm

end CosetSpaceMap

/-! ## Scalar multiples of elements of `K^× · N_F` -/

section FlagUnip

variable {K : Type*} [Field K] [Invertible (2 : K)] {V : Type*} [AddCommGroup V] [Module K V]
  [Module.Finite K V] {Q : QuadraticForm K V}

/-- **Every element of `K^× · N_F` has a scalar multiple in `N_F`**: for `g` with `P(g)` trivial on
the graded pieces of the flag, `g − c` has positive weight for some `c ∈ K`
(`exists_sub_algebraMap_mem_wtFil_of_raisesFil`), `c ≠ 0` since `g` is a unit and positive weight
is nilpotent, so `c⁻¹ g − 1` is nilpotent. -/
theorem exists_smul_sub_one_isNilpotent_of_mem_flagUnipSO (hQ : IsNondeg Q)
    {Fl : IsotropicFlag Q} {g : GSpin Q} (hg : g ∈ flagUnipSO Fl) :
    ∃ c : Kˣ, IsNilpotent ((c : K) • (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) - 1) := by
  obtain ⟨c, hc⟩ := exists_sub_algebraMap_mem_wtFil_of_raisesFil (F := Fl) hQ (g := g)
    (fun w v hv => by simpa using Fl.specP_sub_mem_flagWt hg w v hv)
  have hnil := isNilpotent_of_mem_wtFil_one Fl.isWtFil hc
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, sub_zero] at hnil
    exact (Units.isUnit _).not_isNilpotent hnil
  refine ⟨Units.mk0 c⁻¹ (inv_ne_zero hc0), ?_⟩
  have e : ((Units.mk0 c⁻¹ (inv_ne_zero hc0) : Kˣ) : K) •
      (((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) - 1 =
      c⁻¹ • ((((g : (CliffordAlgebra Q)ˣ) : CliffordAlgebra Q)) - algebraMap K _ c) := by
    rw [Units.val_mk0, smul_sub, Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ hc0,
      one_smul]
  rw [e]
  exact hnil.smul _

end FlagUnip

/-! ## `H(F)/A_{G,H}(F) ≃ H̄(F)` -/

namespace GGPData

variable {F : Type} [NontriviallyNormedField F] [PAdicField F] (d : GGPData F)

theorem luoScale_ne_zero (i : ℤ) : d.luoScale i ≠ 0 := by
  unfold luoScale
  split_ifs <;> exact zpow_ne_zero _ d.ν.ne_zero

/-- Luo's flag `Z_k = ⟨z^L_r, …, z^L_{r-k+1}⟩` is the flag `⟨z_r, …, z_{r-k+1}⟩` of `d`
(the basis vectors are rescaled by nonzero scalars). -/
theorem luoOf_flagSub {k : ℕ} (hk : k ≤ d.r) :
    d.luoOf.flagSub k = d.flag.sub ⟨k, Nat.lt_succ_of_le hk⟩ := by
  show Submodule.span F (Set.range fun j : Fin k => d.luoOf.zV ((d.r : ℤ) - (j : ℕ))) =
    Submodule.span F (Set.range fun j : Fin k => d.zV ((d.r : ℤ) - (j : ℕ)))
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have h := Submodule.smul_mem (Submodule.span F (Set.range fun j : Fin k =>
      d.zV ((d.r : ℤ) - (j : ℕ)))) (d.luoScale ((d.r : ℤ) - (j : ℕ)))
      (Submodule.subset_span ⟨j, rfl⟩)
    have e : d.luoOf.zV ((d.r : ℤ) - (j : ℕ)) = d.luoScale ((d.r : ℤ) - (j : ℕ)) •
      d.zV ((d.r : ℤ) - (j : ℕ)) := d.luoOf_zV _
    simp only []; rw [e]; exact h
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    have h := Submodule.smul_mem (Submodule.span F (Set.range fun j : Fin k =>
      d.luoOf.zV ((d.r : ℤ) - (j : ℕ)))) (d.luoScale ((d.r : ℤ) - (j : ℕ)))⁻¹
      (Submodule.subset_span ⟨j, rfl⟩)
    have e : d.luoOf.zV ((d.r : ℤ) - (j : ℕ)) = d.luoScale ((d.r : ℤ) - (j : ℕ)) •
      d.zV ((d.r : ℤ) - (j : ℕ)) := d.luoOf_zV _
    have e2 : (d.luoScale ((d.r : ℤ) - (j : ℕ)))⁻¹ • d.luoOf.zV ((d.r : ℤ) - (j : ℕ)) =
        d.zV ((d.r : ℤ) - (j : ℕ)) := by
      have h0 := d.luoScale_ne_zero ((d.r : ℤ) - (j : ℕ))
      unfold LuoDatum.zV GGPData.zV
      refine Prod.ext (smul_zero _) ?_
      exact inv_smul_smul₀ h0 _
    simp only []; rw [← e2]; exact h

theorem luoOf_flagSub_r : d.luoOf.flagSub d.r = d.flag.top :=
  d.luoOf_flagSub le_rfl

/-- `P(b)` as a unit of `End V`. -/
theorem specPV_mem_SOu (b : GSpin d.QV) {n : (Module.End F d.luoOf.V)ˣ}
    (hn : (n : Module.End F d.luoOf.V) = (specP d.QV b : d.V →ₗ[F] d.V)) :
    n ∈ LuoDatum.SOu d.luoOf.QV := by
  change LinearMap.GeneralLinearGroup.generalLinearEquiv F _ n ∈ SOGrp d.QV
  have e : LinearMap.GeneralLinearGroup.generalLinearEquiv F d.luoOf.V n = specP d.QV b :=
    LinearEquiv.ext fun v => by
      show (n : Module.End F d.luoOf.V) v = _
      rw [hn]; rfl
  rw [e, ← range_specP_eq_SOGrp d.nondeg_QV]
  exact ⟨b, rfl⟩

/-- **`P(b) ∈ N` (Luo's unipotent radical) iff `b ∈ F^× · N_F`** (`flagUnipSO`). -/
theorem mem_Nset_iff_mem_flagUnipSO {b : GSpin d.QV} {n : (Module.End F d.luoOf.V)ˣ}
    (hn : (n : Module.End F d.luoOf.V) = (specP d.QV b : d.V →ₗ[F] d.V)) :
    n ∈ d.luoOf.Nset ↔ b ∈ flagUnipSO d.flag := by
  have hP : ∀ v : d.V, @Eq d.V ((n : Module.End F d.luoOf.V) v) (specP d.QV b v) :=
    fun v => by rw [hn]; rfl
  have hsub : ∀ (k : ℕ) (hk : k ≤ d.r) (v : d.V),
      v ∈ d.luoOf.flagSub k ↔ v ∈ d.flag.sub ⟨k, Nat.lt_succ_of_le hk⟩ := fun k hk v => by
    rw [d.luoOf_flagSub hk]; rfl
  have horth : ∀ v : d.V, v ∈ (bform d.luoOf.QV).orthogonal (d.luoOf.flagSub d.luoOf.r) ↔
      v ∈ (bform d.QV).orthogonal d.flag.top := fun v => by
    show v ∈ (bform d.QV).orthogonal (d.luoOf.flagSub d.r) ↔ _
    rw [d.luoOf_flagSub_r]
  constructor
  · rintro ⟨-, h1, h2⟩
    have hU : ∀ i : Fin d.flag.len, ∀ v ∈ d.flag.sub i.succ,
        specP d.QV b v - v ∈ d.flag.sub i.castSucc := by
      intro i v hv
      have := (hsub i i.2.le _).1 (h1 i i.2 v ((hsub (i + 1) i.2 v).2 hv))
      rwa [hP] at this
    refine ⟨mem_flagStab_iff.mpr fun i v hv => ?_, hU, fun v hv => ?_⟩
    · obtain ⟨i, hi⟩ := i
      cases i with
      | zero =>
        have h0 : d.flag.sub ⟨0, hi⟩ = ⊥ := d.flag.sub_zero
        rw [h0, Submodule.mem_bot] at hv
        rw [hv, map_zero]; exact zero_mem _
      | succ k =>
        have hk : k < d.flag.len := Nat.lt_of_succ_lt_succ hi
        have h := hU ⟨k, hk⟩ v hv
        have hle : d.flag.sub (Fin.castSucc ⟨k, hk⟩) ≤ d.flag.sub (Fin.succ ⟨k, hk⟩) :=
          d.flag.strictMono.monotone (Fin.castSucc_le_succ _)
        have := add_mem (hle h) hv
        rwa [sub_add_cancel] at this
    · have := (hsub d.r le_rfl _).1 (h2 v ((horth v).2 hv))
      rwa [hP] at this
  · rintro ⟨-, h1, h2⟩
    refine ⟨d.specPV_mem_SOu b hn, fun k hk (v : d.V) hv => ?_, fun (v : d.V) hv => ?_⟩
    · have := h1 ⟨k, hk⟩ v ((hsub (k + 1) hk v).1 hv)
      rw [← hP] at this
      exact (hsub k hk.le _).2 this
    · have := h2 v ((horth v).1 hv)
      rw [← hP] at this
      exact (hsub d.r le_rfl _).2 this

/-- `P(b)` as a unit of `End V`. -/
abbrev specPVU (b : GSpin d.QV) : (Module.End F d.luoOf.V)ˣ :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv F d.luoOf.V).symm (specP d.QV b)

theorem coe_specPVU (b : GSpin d.QV) :
    ((d.specPVU b : (Module.End F d.luoOf.V)ˣ) : Module.End F d.luoOf.V) =
      (specP d.QV b : d.V →ₗ[F] d.V) := rfl

/-- `(1, b) ↦ (1, P(b))`. -/
theorem toGbarU_inr (b : GSpin d.QV) : d.toGbarU (d.inr b) = d.luoOf.inrU (d.specPVU b) := by
  apply Units.ext
  rw [toGbarU_val, LuoDatum.val_inrU, fst_inr_eq_one, snd_inr, map_one]
  rfl

/-- **`P(H) ⊆ H̄`**: `h = (a, a)(1, n)` with `n ∈ N`, and `P(n) ∈ N` (Luo's). -/
theorem toGbarU_mem_HbarU {g : ↥d.G} (hg : g ∈ d.H) : d.toGbarU g ∈ d.luoOf.HbarU := by
  have hn : d.nPart g ∈ d.N := hg
  have e : g = d.diag (d.fst g) * d.inr (d.nPart g) := by
    apply d.G_ext
    · exact ((map_mul d.fst _ _).trans (mul_one _)).symm
    · exact ((map_mul d.snd _ _).trans (mul_inv_cancel_left _ _)).symm
  rw [e, map_mul]
  refine d.luoOf.HbarU.mul_mem ?_ ?_
  · rw [← MonoidHom.comp_apply, toGbarU_comp_diag, MonoidHom.comp_apply]
    exact Subgroup.subset_closure (Or.inl ⟨_, d.specPU_mem_SOu _, rfl⟩)
  rw [toGbarU_inr]
  refine Subgroup.subset_closure (Or.inr ⟨_, ?_, rfl⟩)
  exact (d.mem_Nset_iff_mem_flagUnipSO (d.coe_specPVU _)).2 (flagUnip_le_flagUnipSO _ hn)

/-- **`H̄ ⊆ P(H)`**: write `u = (s, (s ⊕ 1) n)` (`mem_HbarU_iff`), lift `s = P(t)` and `n = P(b)`;
then `b ∈ F^× · N_F`, and a scalar multiple of `b` lies in `N_F`
(`exists_smul_sub_one_isNilpotent_of_mem_flagUnipSO`). -/
theorem exists_mem_H_toGbarU_eq {u : d.luoOf.Ambˣ} (hu : u ∈ d.luoOf.HbarU) :
    ∃ g ∈ d.H, d.toGbarU g = u := by
  obtain ⟨s, hs, n, hn, rfl⟩ := d.luoOf.mem_HbarU_iff.1 hu
  obtain ⟨t, ht⟩ := d.exists_specP_eq_of_mem_SOu hs
  have hnSO : LinearMap.GeneralLinearGroup.generalLinearEquiv F d.luoOf.V n ∈ SOGrp d.QV := hn.1
  rw [← range_specP_eq_SOGrp d.nondeg_QV] at hnSO
  obtain ⟨b, hb⟩ := hnSO
  have hbn : d.specPVU b = n := by
    rw [specPVU, hb]; exact MulEquiv.symm_apply_apply _ _
  have hbSO : b ∈ flagUnipSO d.flag :=
    (d.mem_Nset_iff_mem_flagUnipSO (n := n) (hbn ▸ d.coe_specPVU b)).1 hn
  obtain ⟨c, hc⟩ := exists_smul_sub_one_isNilpotent_of_mem_flagUnipSO d.nondeg_QV hbSO
  have hSO' := (flagUnipSO d.flag).mul_mem hbSO (scalarGSpin_mem_flagUnipSO d.flag c)
  have hbN : b * scalarGSpin d.QV c ∈ d.N :=
    ⟨hSO'.1, hSO'.2.1, hSO'.2.2, by rw [coe_mul_scalarGSpin]; exact hc⟩
  refine ⟨d.diag t * d.inr (b * scalarGSpin d.QV c),
    d.H.mul_mem (d.diag_mem_H t) (d.inr_mem_H hbN), ?_⟩
  have hst : d.specPU t = s := Units.ext ht
  have hsc : d.specPVU (b * scalarGSpin d.QV c) = d.specPVU b := by
    simp only [specPVU, map_mul, specP_scalarGSpin_eq_one, mul_one]
  rw [map_mul, toGbarU_inr, hsc, hbn, ← hst]
  exact congrArg (· * d.luoOf.inrU n) (DFunLike.congr_fun d.toGbarU_comp_diag t)

/-- `A_G(F) ⊆ ker(G(F) → Ḡ(F))` when neither `W` nor `V` is a hyperbolic plane (`AGbar_eq_bot`). -/
theorem toGbar_eq_one_of_mem_AG (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) {a : ↥d.G}
    (ha : a ∈ d.AG) : d.toGbar a = 1 := by
  have hm : d.Pbar a ∈ d.AGbar := ⟨a, ha, rfl⟩
  rw [d.AGbar_eq_bot hW hV, Subgroup.mem_bot] at hm
  apply Subtype.ext
  change d.toGbarU a = 1
  apply Units.ext
  have h1 : specP d.QW (d.fst a) = 1 :=
    congrArg (fun p : d.GbarGrp => (p.1 : (Fin d.m → F) ≃ₗ[F] (Fin d.m → F))) hm
  have h2 : specP d.QV (d.snd a) = 1 := congrArg (fun p : d.GbarGrp => (p.2 : d.V ≃ₗ[F] d.V)) hm
  rw [toGbarU_val, h1, h2]
  rfl

/-- For `e = (x ↦ toGbar (out x))`, `e (g A_G) = toGbar g`. -/
theorem toGbar_out_mk (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) (g : ↥d.G) :
    d.toGbar (Quotient.out (QuotientGroup.mk g : d.GmodAG)) = d.toGbar g := by
  have h : (g)⁻¹ * Quotient.out (QuotientGroup.mk g : d.GmodAG) ∈ d.AG :=
    QuotientGroup.eq.1 (QuotientGroup.out_eq' (QuotientGroup.mk g : d.GmodAG)).symm
  have h1 := d.toGbar_eq_one_of_mem_AG hW hV h
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm

/-- **`H(F)/A_{G,H}(F) ≃ H̄(F)` as topological groups**, compatibly with
`G(F)/A_G(F) ≃ Ḡ(F)`: `toGmodAG` is a closed embedding (`isClosedEmbedding_toGmodAG`), and the
image of `H(F)` in `Ḡ(F)` is `H̄(F)` (`toGbarU_mem_HbarU`, `exists_mem_H_toGbarU_eq`). -/
theorem exists_continuousMulEquiv_HmodAGH (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV)
    (e : d.GmodAG ≃ₜ* ↥d.luoOf.Gbar) (he : ⇑e = fun x : d.GmodAG => d.toGbar (Quotient.out x)) :
    ∃ eH : d.HmodAGH ≃ₜ* ↥d.luoOf.Hbar,
      ∀ q, ((eH q : ↥d.luoOf.Gbar)) = e (d.toGmodAG q) := by
  set f : d.HmodAGH →* ↥d.luoOf.Gbar := e.toMulEquiv.toMonoidHom.comp d.toGmodAG
  have hfmk : ∀ h : ↥d.H, f (QuotientGroup.mk h) = d.toGbar (h : ↥d.G) := by
    intro h
    show e (QuotientGroup.mk (h : ↥d.G)) = _
    rw [he]
    exact d.toGbar_out_mk hW hV _
  have hmem : ∀ q, f q ∈ d.luoOf.Hbar := by
    intro q
    induction q using QuotientGroup.induction_on with | H h => ?_
    rw [hfmk]
    exact d.toGbarU_mem_HbarU h.2
  set φ : d.HmodAGH →* ↥d.luoOf.Hbar := f.codRestrict d.luoOf.Hbar hmem
  have hfemb : IsEmbedding f :=
    (e.toHomeomorph.isClosedEmbedding.comp d.isClosedEmbedding_toGmodAG).isEmbedding
  have hφc : Continuous φ := continuous_induced_rng.2 hfemb.continuous
  have hφemb : IsEmbedding φ := IsEmbedding.of_comp hφc continuous_subtype_val hfemb
  have hsurj : Function.Surjective φ := by
    intro u
    obtain ⟨g, hg, hgu⟩ := d.exists_mem_H_toGbarU_eq (u := ((u : ↥d.luoOf.Gbar) : d.luoOf.Ambˣ))
      (Subgroup.mem_subgroupOf.1 u.2)
    refine ⟨QuotientGroup.mk ⟨g, hg⟩, Subtype.ext (Subtype.ext ?_)⟩
    show ((f (QuotientGroup.mk ⟨g, hg⟩) : ↥d.luoOf.Gbar) : d.luoOf.Ambˣ) = _
    rw [hfmk]
    exact hgu
  let h := hφemb.toHomeomorphOfSurjective hsurj
  let eM : d.HmodAGH ≃* ↥d.luoOf.Hbar := MulEquiv.ofBijective φ ⟨hφemb.injective, hsurj⟩
  exact ⟨{ eM with continuous_toFun := hφc, continuous_invFun := h.symm.continuous },
    fun q => rfl⟩

set_option maxHeartbeats 3000000 in
-- diagnosing: instance unification on the coset spaces
/-- **The measures of `J` and `J^Lie` on `H̄(F)\Ḡ(F)`**: there are an isomorphism of topological
groups `H(F)/A_{G,H}(F) ≃ H̄(F)` (`exists_continuousMulEquiv_HmodAGH`), the Haar measure
`μ_H` it carries `Measure.haar` to, and a Weil measure `m` on `H̄(F)\Ḡ(F)` for `muG` and `μ_H`
(the push-forward of `weilMeasureHG`, `IsWeilMeasure.map`), such that integrals over
`H(F)\G(F)/A_G(F)` of a function evaluated at the chosen representatives become integrals over
`H̄(F)\Ḡ(F)` of any left `H̄(F)`-invariant function `K` on `Ḡ(F)` with `K ∘ toGbar = k`. -/
theorem exists_weil_Hbar (hW : ¬ IsHypPlane d.QW) (hV : ¬ IsHypPlane d.QV) :
    ∃ (eH : d.HmodAGH ≃ₜ* ↥d.luoOf.Hbar) (m : Measure (CosetSpace d.luoOf.Hbar.subtype)),
      (∀ h : ↥d.H, ((eH (QuotientGroup.mk h) : ↥d.luoOf.Gbar)) = d.toGbar (h : ↥d.G)) ∧
      IsWeilMeasure d.luoOf.Hbar.subtype d.muG ((Measure.haar : Measure d.HmodAGH).map eH) m ∧
      ∀ (K : ↥d.luoOf.Gbar → ℂ) (k : ↥d.G → ℂ), (∀ g, K (d.toGbar g) = k g) →
        (∀ h ∈ d.luoOf.Hbar, ∀ x, K (h * x) = K x) →
        ∫ q : d.HGQuot, k (Quotient.out (CosetSpace.out d.toGmodAG q : d.GmodAG))
            ∂d.weilMeasureHG =
          ∫ q, K (CosetSpace.out d.luoOf.Hbar.subtype q) ∂m := by
  obtain ⟨e, he⟩ := d.exists_continuousMulEquiv_toGbar hW hV
  obtain ⟨eH, heH⟩ := d.exists_continuousMulEquiv_HmodAGH hW hV e he
  have hcomp : ∀ s, d.luoOf.Hbar.subtype (eH s) = e (d.toGmodAG s) := fun s => heH s
  let ē := CosetSpace.mapHomeomorph d.toGmodAG d.luoOf.Hbar.subtype eH.toMulEquiv e hcomp
  have hR := d.isMulRightInvariant_haar_HmodAGH
  have i1 : BorelSpace d.GmodAG := d.borelSpace_GmodAG
  have i2 : BorelSpace d.HmodAGH := d.borelSpace_HmodAGH
  refine ⟨eH, Measure.map ē d.weilMeasureHG, ?_, ?_, ?_⟩
  · intro h
    exact (heH _).trans ((congrFun he _).trans (d.toGbar_out_mk hW hV _))
  · have hMM : MeasurableMul d.HmodAGH := ContinuousMul.measurableMul
    have h0 := d.weilMeasureHG_spec
    have h2 := IsWeilMeasure.map (ι := d.toGmodAG) (ι' := d.luoOf.Hbar.subtype) hR h0 eH e hcomp
    refine (congrArg (fun ν => IsWeilMeasure d.luoOf.Hbar.subtype ν _ _) ?_).mpr h2
    unfold muG
    congr 1
    exact he.symm
  · intro K k hK hinv
    have hK' : ∀ (s : ↥d.luoOf.Hbar) (x : ↥d.luoOf.Gbar), K (d.luoOf.Hbar.subtype s * x) = K x :=
      fun s x => hinv (s : ↥d.luoOf.Gbar) s.2 x
    have hI := integral_map_mapHomeomorph (ι := d.toGmodAG) (ι' := d.luoOf.Hbar.subtype)
      eH.toMulEquiv e hcomp d.weilMeasureHG K hK'
    refine Eq.trans ?_ hI.symm
    refine integral_congr_ae (Eventually.of_forall fun q => ?_)
    exact ((congrArg K (congrFun he _)).trans (hK _)).symm

/-! ## `𝔥⁰ ≃ 𝔥 = so(W) ⊕ 𝔫` -/

/-- **`ad` carries `𝔫_F` onto Luo's `𝔫`**: for `Z ∈ so_Cliff(V)`, `ad Z ∈ 𝔫` iff `Z ∈ 𝔫_F`
(the flags agree, `luoOf_flagSub`). -/
theorem adV_mem_lieN_iff {Z : CliffordAlgebra d.QV} (hZ : Z ∈ soSub d.QV) :
    adV d.QV Z ∈ d.luoOf.lieN ↔ Z ∈ lieFlagUnip d.flag := by
  have hsub : ∀ (k : ℕ) (hk : k ≤ d.r) (v : d.V),
      v ∈ d.luoOf.flagSub k ↔ v ∈ d.flag.sub ⟨k, Nat.lt_succ_of_le hk⟩ := fun k hk v => by
    rw [d.luoOf_flagSub hk]; rfl
  have horth : ∀ v : d.V, v ∈ (bform d.luoOf.QV).orthogonal (d.luoOf.flagSub d.luoOf.r) ↔
      v ∈ (bform d.QV).orthogonal d.flag.top := fun v => by
    show v ∈ (bform d.QV).orthogonal (d.luoOf.flagSub d.r) ↔ _
    rw [d.luoOf_flagSub_r]
  constructor
  · rintro ⟨-, h1, h2⟩
    refine ⟨hZ, fun i (v : d.V) hv => ?_, fun (v : d.V) hv => ?_⟩
    · exact (hsub i i.2.le _).1 (h1 i i.2 v ((hsub (i + 1) i.2 v).2 hv))
    · exact (hsub d.r le_rfl _).1 (h2 v ((horth v).2 hv))
  · rintro ⟨-, h1, h2⟩
    refine ⟨adV_mem_skewAdjoint hZ.1, fun k hk (v : d.V) hv => ?_, fun (v : d.V) hv => ?_⟩
    · exact (hsub k hk.le _).2 (h1 ⟨k, hk⟩ v ((hsub (k + 1) hk v).1 hv))
    · exact (hsub d.r le_rfl _).2 (h2 v ((horth v).1 hv))

/-- **`ad` carries `𝔥⁰` onto `𝔥 = so(W) ⊕ 𝔫`**: for `X ∈ 𝔤⁰`,
`ad X_V − (ad X_W ⊕ 0) = ad (X_V − X_W)` (`toSOLin_diagLie`), and `adV_mem_lieN_iff`. -/
theorem toSOLin_mem_lieH_iff {X : d.ambient} (hX : X ∈ d.lieZero) :
    d.toSOLin X ∈ d.luoOf.lieH ↔ X ∈ d.lieH0 := by
  have hW : X.1 ∈ gspin d.QW := hX.1.1
  have hdiag : d.luoOf.extLie (adV d.QW X.1) = adV d.QV (d.diagLie X.1).2 :=
    (congrArg d.luoOf.sndA (d.toSOLin_diagLie hW)).symm
  have hZ : X.2 - (d.diagLie X.1).2 ∈ soSub d.QV :=
    sub_mem hX.2 (map_mem_soSub d.nondeg _ hX.1)
  have e : d.luoOf.sndA (d.toSOLin X) - d.luoOf.extLie (d.luoOf.fstA (d.toSOLin X)) =
      adV d.QV (X.2 - (d.diagLie X.1).2) := by
    rw [sndA_toSOLin, fstA_toSOLin, hdiag, map_sub]
    rfl
  constructor
  · rintro ⟨-, hN⟩
    rw [e] at hN
    exact ⟨hX, (d.adV_mem_lieN_iff hZ).1 hN⟩
  · rintro ⟨-, hN⟩
    refine ⟨d.toSO_mem ⟨X, hX⟩, ?_⟩
    rw [e]
    exact (d.adV_mem_lieN_iff hZ).2 hN

/-- `ad : 𝔥⁰ ≃ 𝔥` as a linear equivalence. -/
def toSOH : ↥d.lieH0 ≃ₗ[F] ↥d.luoOf.lieH where
  toFun X := ⟨d.toSOLin X, (d.toSOLin_mem_lieH_iff (d.lieH0_le_lie0 X.2)).2 X.2⟩
  map_add' X Y := Subtype.ext (map_add d.toSOLin _ _)
  map_smul' c X := Subtype.ext (map_smul d.toSOLin _ _)
  invFun Y := ⟨(d.toSO.symm ⟨Y, Y.2.1⟩ : d.ambient), (d.toSOLin_mem_lieH_iff
      (d.toSO.symm ⟨Y, Y.2.1⟩).2).1 (by rw [toSOLin_toSO_symm]; exact Y.2)⟩
  left_inv X := Subtype.ext <| by
    have h := d.toSO.symm_apply_apply ⟨X, d.lieH0_le_lie0 X.2⟩
    exact (congrArg Subtype.val h : _)
  right_inv Y := Subtype.ext (d.toSOLin_toSO_symm ⟨Y, Y.2.1⟩)

@[simp] theorem coe_toSOH (X : ↥d.lieH0) : (d.toSOH X : d.luoOf.Amb) = d.toSOLin X := rfl

/-- `ad : 𝔥⁰ ≃ 𝔥` is a homeomorphism (finite dimension). -/
def toSOHCLE : ↥d.lieH0 ≃L[F] ↥d.luoOf.lieH :=
  haveI := t2Space_of_moduleTopology F d.ambient
  haveI := isTopologicalRing_of_moduleTopology F d.ambient
  haveI := IsModuleTopology.toContinuousSMul F d.ambient
  haveI := t2Space_of_moduleTopology F d.luoOf.Amb
  haveI := isTopologicalRing_of_moduleTopology F d.luoOf.Amb
  haveI := IsModuleTopology.toContinuousSMul F d.luoOf.Amb
  d.toSOH.toContinuousLinearEquiv

@[simp] theorem coe_toSOHCLE (X : ↥d.lieH0) :
    ((d.toSOHCLE X : ↥d.luoOf.lieH) : d.luoOf.Amb) = d.toSOLin X := rfl

section Kernel

variable (ψ : NontrivialAddChar F)

/-- `extFn (f ∘ toSO⁻¹)` at `ad Z` is `f Z`. -/
theorem extFn_toSOLin (f : ↥d.lieZero → ℂ) (Z : ↥d.lieZero) :
    d.luoOf.extFn (f ∘ d.toSO.symm) (d.toSOLin Z) = f Z := by
  unfold LuoDatum.extFn
  rw [dif_pos (d.toSO_mem Z)]
  simp only [Function.comp_apply]
  congr 1
  exact d.toSO.symm_apply_eq.2 (Subtype.ext rfl)

/-- **The kernels of `J^Lie` agree at matched points**: with `μ_𝔥 = ad_* dX`,
`K^Lie_Luo(f ∘ ad⁻¹, P(g)) = K^Lie(f, g)` (change of variables `ad : 𝔥⁰ ≃ 𝔥`;
`ad(g⁻¹ X g) = P(g)⁻¹ ad(X) P(g)`, `toSOLin_adLie0_inv`; `λ ∘ ad = λ`, `lam_toSO`). -/
theorem kernelLie_toGbar (μ : Measure ↥d.lieH0) (f : ↥d.lieZero → ℂ) (g : ↥d.G) :
    d.luoOf.kernelLie ψ (μ.map d.toSOHCLE) (f ∘ d.toSO.symm) (d.toGbar g) =
      ∫ X : ↥d.lieH0, f (d.adLie0 g⁻¹ (d.lieH0Incl X)) * d.xiLie ψ (X : d.ambient) ∂μ := by
  unfold LuoDatum.kernelLie
  have hme : MeasurableEmbedding (d.toSOHCLE : ↥d.lieH0 → ↥d.luoOf.lieH) :=
    d.toSOHCLE.toHomeomorph.measurableEmbedding
  rw [hme.integral_map]
  refine integral_congr_ae (Eventually.of_forall fun X => ?_)
  have h1 := d.toSOLin_adLie0_inv g (d.lieH0Incl X)
  change d.luoOf.extFn (f ∘ d.toSO.symm) (d.luoOf.conjInv (d.toGbar g)
      (d.toSOLin (d.lieH0Incl X : d.ambient))) * ψ (d.luoOf.lam (d.toSOLin X)) =
    f (d.adLie0 g⁻¹ (d.lieH0Incl X)) * ψ (d.lamLie X)
  rw [← h1, d.extFn_toSOLin, ← d.lam_toSO]

end Kernel

end GGPData

end GSpinGGP
