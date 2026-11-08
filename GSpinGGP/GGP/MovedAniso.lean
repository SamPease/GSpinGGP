/-
Copyright (c) 2026 Samantha Pease. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GSpinGGP.GGP.Descent
import GSpinGGP.Foundations.QuadraticForms
import GSpinGGP.Foundations.HypPlane

/-!
# The moved space of an element of `GSpin`

For `x ∈ GSpin(V)` with `V = V'_x ⊕ V''_x`, `V''_x = (V'_x)^⊥` (`V'_x = ker(P(x) − 1)`):
* `finrank_orthogonal_fixedSub_ne_one`: `V''_x` is not a line (on a line `P(x)` would be the
  reflection in it, of determinant `−1`, while `det P(x) = 1`, `det_specP`).
* `exists_eigen_hypPair`: on a plane `V''_x` with hyperbolic pair `f, f'`, `P(x)` is diagonal.
* `anisotropic_orthogonal_fixedSub_of_isGammaElt`: for `x ∈ Γ(G,H)`, a plane `W''_x` is anisotropic
  (its hyperbolic torus would lie in the compact-mod-centre `T_x(F)`).
-/

noncomputable section

open Module

namespace GSpinGGP

variable {K V : Type*} [Field K] [CharZero K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

/-- **`V''_x` is not a line**: for `x ∈ GSpin(V)` with `V = V'_x ⊕ (V'_x)^⊥`. -/
theorem finrank_orthogonal_fixedSub_ne_one {Q : QuadraticForm K V} (hQ : IsNondeg Q)
    (x : GSpin Q) (hc : IsCompl (fixedSub x) ((bform Q).orthogonal (fixedSub x))) :
    finrank K ↥((bform Q).orthogonal (fixedSub x)) ≠ 1 := by
  intro h1
  set U := (bform Q).orthogonal (fixedSub x) with hUdef
  set P : Module.End K V := (specP Q x : Module.End K V) with hPdef
  obtain ⟨⟨u, huU⟩, hu0, hspan⟩ := finrank_eq_one_iff'.1 h1
  have hu0' : u ≠ 0 := fun h => hu0 (Subtype.ext h)
  have hmemU : ∀ v ∈ U, ∃ c : K, c • u = v := fun v hv => by
    obtain ⟨c, hc⟩ := hspan ⟨v, hv⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  -- `bform(u, ·) = 0` on `V'_x`
  have huW : ∀ w ∈ fixedSub x, bform Q u w = 0 := fun w hw => by
    rw [QuadraticMap.associated_isSymm]; exact huU w hw
  -- `Q u ≠ 0`
  have hQu : Q u ≠ 0 := by
    intro hQ0
    apply hu0'
    refine hQ.1 u fun v => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
    obtain ⟨c, rfl⟩ := hmemU b hb
    rw [map_add, map_smul, huW a ha, zero_add, smul_eq_mul,
      QuadraticMap.associated_eq_self_apply, hQ0, mul_zero]
  -- `P u = -u`
  obtain ⟨μ, hμ⟩ := hmemU _ (specP_mem_orthogonal_fixedSub x huU)
  have hμ1 : μ ≠ 1 := by
    rintro rfl
    have : u ∈ fixedSub x ⊓ U := ⟨(mem_fixedSub_iff x u).2 (by rw [← hμ, one_smul]), huU⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at this
    exact hu0' this
  have hμsq : μ * μ = 1 := by
    have h : Q (μ • u) = Q u := by rw [hμ]; exact (specPIso x).map_app u
    rw [QuadraticMap.map_smul, smul_eq_mul] at h
    exact mul_right_cancel₀ hQu (h.trans (one_mul _).symm)
  have hμm : μ = -1 := by
    have : (μ - 1) * (μ + 1) = 0 := by linear_combination hμsq
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (sub_eq_zero.1 h) hμ1
    · linear_combination h
  -- `P = s_u`
  have hPs : P = quadReflection Q u := by
    ext v
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
    obtain ⟨c, rfl⟩ := hmemU b hb
    have hPa : P a = a := (mem_fixedSub_iff x a).1 ha
    have hpa : QuadraticMap.polar Q u a = 0 := by rw [polar_eq_two_mul_bform, huW a ha, mul_zero]
    have hpu : QuadraticMap.polar Q u u = 2 * Q u := by
      rw [polar_eq_two_mul_bform, QuadraticMap.associated_eq_self_apply]
    have hPu : P u = μ • u := hμ.symm
    rw [map_add, map_smul, hPa, map_add, map_smul, quadReflection_apply, quadReflection_apply, hpa,
      hpu, hPu, hμm]
    have h2 : (Q u)⁻¹ * (2 * Q u) = 2 := by field_simp
    simp only [smul_smul, h2, zero_smul, smul_zero, sub_zero]
    module
  have hdet := det_specP x
  rw [← hPdef, hPs, det_quadReflection hQu] at hdet
  norm_num at hdet

omit [CharZero K] [Invertible (2 : K)] in
/-- In a plane `U` containing a hyperbolic pair `f, f'`, every `u ∈ U` is
`polar(f', u) f + polar(f, u) f'`. -/
theorem eq_of_mem_hypPlane {Q : QuadraticForm K V} {U : Submodule K V} (h2 : finrank K U = 2)
    {f f' : V} (hfU : f ∈ U) (hf'U : f' ∈ U) (hf : Q f = 0) (hf' : Q f' = 0)
    (hp : QuadraticMap.polar Q f f' = 1) {u : V} (hu : u ∈ U) :
    u = QuadraticMap.polar Q f' u • f + QuadraticMap.polar Q f u • f' := by
  have hff : QuadraticMap.polar Q f f = 0 := by rw [QuadraticMap.polar_self, hf, smul_zero]
  have hf'f' : QuadraticMap.polar Q f' f' = 0 := by rw [QuadraticMap.polar_self, hf', smul_zero]
  have hf'f : QuadraticMap.polar Q f' f = 1 := by rw [QuadraticMap.polar_comm, hp]
  -- `f, f'` are independent, hence span `U`
  have hli : LinearIndependent K ![f, f'] := linearIndependent_hyperbolicPair hf hf' hp
  have hspan : Submodule.span K (Set.range ![f, f']) = U := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      fin_cases i <;> simp [hfU, hf'U]
    · rw [finrank_span_eq_card hli, h2]; rfl
  rw [← hspan] at hu
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hu
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    QuadraticMap.polar_add_right, QuadraticMap.polar_smul_right, hf'f, hf'f', hff, hp,
    smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]

/-- **`P(x)` is diagonal on a hyperbolic pair of `V''_x`**: if `V''_x = (V'_x)^⊥` is a plane with
hyperbolic pair `f, f'`, then `P(x) f = λ f`, `P(x) f' = λ⁻¹ f'` (swapping the two isotropic lines
would make `P(x)` the reflection in `f − μ f'`, of determinant `−1`). -/
theorem exists_eigen_hypPair {Q : QuadraticForm K V} (x : GSpin Q)
    (hc : IsCompl (fixedSub x) ((bform Q).orthogonal (fixedSub x)))
    (h2 : finrank K ↥((bform Q).orthogonal (fixedSub x)) = 2) {f f' : V}
    (hfU : f ∈ (bform Q).orthogonal (fixedSub x)) (hf'U : f' ∈ (bform Q).orthogonal (fixedSub x))
    (hf : Q f = 0) (hf' : Q f' = 0) (hp : QuadraticMap.polar Q f f' = 1) :
    ∃ μ : K, μ ≠ 0 ∧ (specP Q x : Module.End K V) f = μ • f ∧
      (specP Q x : Module.End K V) f' = μ⁻¹ • f' := by
  set U := (bform Q).orthogonal (fixedSub x) with hUdef
  set P : Module.End K V := (specP Q x : Module.End K V) with hPdef
  have hdec := fun {u : V} (hu : u ∈ U) => eq_of_mem_hypPlane h2 hfU hf'U hf hf' hp hu
  have hff : QuadraticMap.polar Q f f = 0 := by rw [QuadraticMap.polar_self, hf, smul_zero]
  have hf'f' : QuadraticMap.polar Q f' f' = 0 := by rw [QuadraticMap.polar_self, hf', smul_zero]
  have hf'f : QuadraticMap.polar Q f' f = 1 := by rw [QuadraticMap.polar_comm, hp]
  have hQP : ∀ v, Q (P v) = Q v := fun v => (specPIso x).map_app v
  have hpolP : ∀ v w, QuadraticMap.polar Q (P v) (P w) = QuadraticMap.polar Q v w :=
    fun v w => polar_isometry (specPIso x).toIsometry v w
  -- `Q(a f + b f') = a b`
  have hQab : ∀ a b : K, Q (a • f + b • f') = a * b := fun a b => by
    rw [QuadraticMap.map_add Q (a • f) (b • f'), QuadraticMap.map_smul, QuadraticMap.map_smul,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hf, hf', hp]
    simp
  set α := QuadraticMap.polar Q f' (P f)
  set β := QuadraticMap.polar Q f (P f)
  set γ := QuadraticMap.polar Q f' (P f')
  set δ := QuadraticMap.polar Q f (P f')
  have hPf : P f = α • f + β • f' := hdec (specP_mem_orthogonal_fixedSub x hfU)
  have hPf' : P f' = γ • f + δ • f' := hdec (specP_mem_orthogonal_fixedSub x hf'U)
  have hαβ : α * β = 0 := by rw [← hQab, ← hPf, hQP, hf]
  have hγδ : γ * δ = 0 := by rw [← hQab, ← hPf', hQP, hf']
  have hpol : α * δ + β * γ = 1 := by
    have h := hpolP f f'
    rw [hPf, hPf', hp] at h
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hff, hf'f', hp, hf'f,
      smul_eq_mul] at h
    linear_combination h
  by_cases hβ : β = 0
  · have hαδ : α * δ = 1 := by rw [hβ, zero_mul, add_zero] at hpol; exact hpol
    have hα : α ≠ 0 := left_ne_zero_of_mul_eq_one hαδ
    have hδ : δ ≠ 0 := right_ne_zero_of_mul_eq_one hαδ
    have hγ : γ = 0 := (mul_eq_zero.1 hγδ).resolve_right hδ
    refine ⟨α, hα, by rw [hPf, hβ, zero_smul, add_zero], ?_⟩
    rw [hPf', hγ, zero_smul, zero_add, eq_inv_of_mul_eq_one_right hαδ]
  · exfalso
    have hα : α = 0 := (mul_eq_zero.1 hαβ).resolve_right hβ
    have hβγ : β * γ = 1 := by rw [hα, zero_mul, zero_add] at hpol; exact hpol
    have hδ : δ = 0 := (mul_eq_zero.1 hγδ).resolve_left (right_ne_zero_of_mul_eq_one hβγ)
    have hγ' : γ = β⁻¹ := eq_inv_of_mul_eq_one_right hβγ
    set r := f - β • f' with hrdef
    have hQr : Q r = -β := by
      have : r = (1 : K) • f + (-β) • f' := by rw [hrdef, one_smul, neg_smul, sub_eq_add_neg]
      rw [this, hQab]
      ring
    have hQr0 : Q r ≠ 0 := by rw [hQr]; exact neg_ne_zero.2 hβ
    have hpW : ∀ v ∈ U, ∀ a ∈ fixedSub x, QuadraticMap.polar Q v a = 0 := fun v hv a ha => by
      rw [polar_eq_two_mul_bform, QuadraticMap.associated_isSymm, hv a ha, mul_zero]
    have hPs : P = quadReflection Q r := by
      ext v
      obtain ⟨a, ha, b, hb, rfl⟩ :=
        Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
      have hPa : P a = a := (mem_fixedSub_iff x a).1 ha
      have hra : QuadraticMap.polar Q r a = 0 := by
        rw [hrdef, QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, hpW f hfU a ha,
          hpW f' hf'U a ha, smul_zero, sub_zero]
      obtain ⟨p₁, p₂, rfl⟩ : ∃ p₁ p₂ : K, b = p₁ • f + p₂ • f' := ⟨_, _, hdec hb⟩
      have hsa : quadReflection Q r a = a := by
        rw [quadReflection_apply, hra, zero_smul, smul_zero, sub_zero]
      have hrf : QuadraticMap.polar Q r f = -β := by
        rw [hrdef, QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, hff, hf'f]; simp
      have hrf' : QuadraticMap.polar Q r f' = 1 := by
        rw [hrdef, QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, hp, hf'f']; simp
      have hsf : quadReflection Q r f = β • f' := by
        rw [quadReflection_apply, hrf, hQr, hrdef, smul_smul, inv_mul_cancel₀ (neg_ne_zero.2 hβ),
          one_smul]
        abel
      have hsf' : quadReflection Q r f' = β⁻¹ • f := by
        rw [quadReflection_apply, hrf', hQr, hrdef, one_smul, smul_sub, smul_smul,
          inv_neg, neg_mul, inv_mul_cancel₀ hβ]
        module
      rw [map_add, map_add, map_add, map_add, map_smul, map_smul, map_smul, map_smul, hPa, hsa, hPf,
        hPf', hsf, hsf', hα, hδ, hγ', zero_smul, zero_add, zero_smul, add_zero]
    have hdet := det_specP x
    rw [← hPdef, hPs, det_quadReflection hQr0] at hdet
    norm_num at hdet

section Gamma

variable {F : Type} [NontriviallyNormedField F] [PAdicField F]

/-- **For `x ∈ Γ(G,H)`, a plane `W''_x` is anisotropic**: otherwise, with a hyperbolic pair `f, f'`
of `W''_x`, `P(x)` is diagonal on `f, f'` (`exists_eigen_hypPair`), so the lifts `h(s)` of the
hyperbolic torus (`hypGSpin`: `P(h(s)) = s` on `f`, `s⁻¹` on `f'`, `1` on `W'_x`) commute with `x`
(`commute_hypUnit`) and lie in `T_x(F)`; but `t ↦ polar(f', P(t) f)` is continuous on the compact
`T_x(F)/A(F)`, hence bounded, while it takes the value `s` at `h(s)`. -/
theorem anisotropic_orthogonal_fixedSub_of_isGammaElt (d : GGPData F) (x : ↥(GSpin d.QW))
    (hx : d.IsGammaElt x) (h2 : finrank F ↥((bform d.QW).orthogonal (fixedSub x)) = 2) :
    (d.QW.comp ((bform d.QW).orthogonal (fixedSub x)).subtype).Anisotropic := by
  classical
  set U := (bform d.QW).orthogonal (fixedSub x) with hUdef
  have hc : IsCompl (fixedSub x) U :=
    isCompl_fixedSub_orthogonal d.nondeg x (fixedSub_inf_movedSub_of_isSS x hx.1)
  have hpW : ∀ v ∈ U, ∀ a ∈ fixedSub x, QuadraticMap.polar d.QW v a = 0 := fun v hv a ha => by
    rw [polar_eq_two_mul_bform, QuadraticMap.associated_isSymm, hv a ha, mul_zero]
  -- `U` is nondegenerate
  have hUnd : IsNondeg (d.QW.comp U.subtype) := by
    refine (isNondeg_iff _).2 fun u hu => Subtype.ext ((isNondeg_iff d.QW).1 d.nondeg u fun v => ?_)
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      Submodule.mem_sup.1 (hc.sup_eq_top ▸ Submodule.mem_top (x := v))
    have h1 : bform d.QW u a = 0 := by rw [QuadraticMap.associated_isSymm]; exact u.2 a ha
    have h2 : bform d.QW u b = 0 := by rw [← bform_comp_subtype d.QW U u ⟨b, hb⟩]; exact hu ⟨b, hb⟩
    rw [map_add, h1, h2, add_zero]
  intro u hu0
  by_contra hne
  obtain ⟨f'', hf''0, hpol⟩ := exists_hyperbolicPair_of_isotropic hUnd hne hu0
  have hp : QuadraticMap.polar d.QW (u : Fin d.m → F) (f'' : Fin d.m → F) = 1 := by
    rw [← hpol]; rfl
  obtain ⟨μ, hμ0, hPf, hPf'⟩ := exists_eigen_hypPair x hc h2 u.2 f''.2 hu0 hf''0 hp
  -- the hyperbolic torus of `W''_x` lies in `T_x(F)` (`hypGSpin`, `commute_hypUnit`)
  have key : ∀ s : Fˣ, ∃ t ∈ d.torusOf x,
      specP d.QW t (u : Fin d.m → F) = (s : F) • (u : Fin d.m → F) := by
    intro s
    have hp' : QuadraticMap.polar d.QW (f'' : Fin d.m → F) u = 1 := by
      rw [QuadraticMap.polar_comm, hp]
    have hpuu : QuadraticMap.polar d.QW (u : Fin d.m → F) u = 0 := by
      rw [QuadraticMap.polar_self, show d.QW (u : Fin d.m → F) = 0 from hu0, smul_zero]
    have hfa : d.QW (u : Fin d.m → F) = 0 := hu0
    have hf'a : d.QW (f'' : Fin d.m → F) = 0 := hf''0
    set t := hypGSpin (Q := d.QW) hfa hf'a hp s⁻¹ with htdef
    have hcx := commute_hypUnit (Q := d.QW) hfa hf'a hp (g := x) (s := Units.mk0 μ hμ0)
      (by simpa using hPf) (by simpa using hPf') s⁻¹
    refine ⟨t, ⟨?_, fun v hv => ?_⟩, ?_⟩
    · change t ∈ Subgroup.centralizer {x}
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Units.ext hcx.eq.symm)
    · have h1 : QuadraticMap.polar d.QW (f'' : Fin d.m → F) v = 0 := hpW _ f''.2 v hv
      have h2 : QuadraticMap.polar d.QW (u : Fin d.m → F) v = 0 := hpW _ u.2 v hv
      rw [htdef, specP_hypGSpin, h1, h2]
      simp
    · rw [htdef, specP_hypGSpin, hp', hpuu]
      simp only [inv_inv, one_smul]
      module
  -- boundedness on the compact `T_x(F)/A(F)`
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ t ∈ d.torusOf x,
      ‖QuadraticMap.polar d.QW (f'' : Fin d.m → F) (specP d.QW t (u : Fin d.m → F))‖ ≤ R := by
    have : CompactSpace (d.TorusQuot (d.torusOf x)) := hx.2.2
    let φ : ↥(d.torusOf x) → F := fun t =>
      QuadraticMap.polar d.QW (f'' : Fin d.m → F) (specP d.QW (t : ↥(GSpin d.QW)) (u : Fin d.m → F))
    have hPc : Continuous fun t : ↥(d.torusOf x) =>
        specP d.QW (t : ↥(GSpin d.QW)) (u : Fin d.m → F) := by
      have hn : Continuous fun t : ↥(d.torusOf x) =>
          ((t : ↥(GSpin d.QW)) : (CliffordAlgebra d.QW)ˣ) :=
        continuous_subtype_val.comp continuous_subtype_val
      simp only [specP_apply_eq]
      exact (IsModuleTopology.continuous_of_linearMap (CliffordAlgebra.ιInv d.QW)).comp
        ((Units.continuous_val.comp hn).mul (continuous_const.mul (Units.continuous_coe_inv.comp hn)))
    have hφc : Continuous φ :=
      (LinearMap.continuous_of_finiteDimensional
        (QuadraticMap.polarBilin d.QW (f'' : Fin d.m → F))).comp hPc
    have hφinv : ∀ a b : ↥(d.torusOf x),
        (QuotientGroup.leftRel (d.scalarsIn (d.torusOf x))) a b → φ a = φ b := by
      intro a b hab
      obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf).1 (QuotientGroup.leftRel_apply.1 hab)
      have hb : (b : ↥(GSpin d.QW)) = (a : ↥(GSpin d.QW)) * scalarGSpin d.QW c := by
        rw [hc]; simp
      simp only [φ, hb, map_mul, specP_scalarGSpin_eq_one, mul_one]
    let ψ : d.TorusQuot (d.torusOf x) → F := Quotient.lift φ hφinv
    have hψc : Continuous ψ := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr hφc
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hψc.continuousOn
    exact ⟨C, fun t ht => hC (QuotientGroup.mk ⟨t, ht⟩) (Set.mem_univ _)⟩
  obtain ⟨s, hs⟩ := NormedField.exists_lt_norm F (max R 1)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hs
    linarith [le_max_right R 1]
  obtain ⟨t, ht, htf⟩ := key (Units.mk0 s hs0)
  have hb := hR t ht
  rw [htf, Units.val_mk0, QuadraticMap.polar_smul_right, QuadraticMap.polar_comm, hp, smul_eq_mul,
    mul_one] at hb
  linarith [le_max_left R 1]

end Gamma

end GSpinGGP
